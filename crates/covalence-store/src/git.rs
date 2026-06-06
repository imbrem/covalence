//! Git-style header-prefixed tagged storage.
//!
//! [`GitPrefixStore`] wraps any [`ContentStore<K>`] and stores data with
//! `"{type} {len}\0"` headers — the same format git uses for loose objects
//! (minus the zlib compression).
//!
//! [`ContentStore::get`] only returns blob-typed entries;
//! [`TaggedStore::get_repr`] strips the header unconditionally.

use std::fmt;

use covalence_hash::O256;

use crate::{
    AnyObject, BlobInfo, ContentStore, Object, ObjectKind, ObjectStore, StoreError, TaggedStore,
    clip_slice,
};

// ---------------------------------------------------------------------------
// GitObjectType — string wrapper for forward compatibility
// ---------------------------------------------------------------------------

/// Git object type tag — a string wrapper for forward compatibility.
///
/// Represents the type field in a git object header (`"blob"`, `"tree"`,
/// `"commit"`, `"tag"`, or any future type string).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct GitObjectType(Box<str>);

impl GitObjectType {
    pub fn new(s: impl Into<Box<str>>) -> Self {
        Self(s.into())
    }

    pub fn blob() -> Self {
        Self("blob".into())
    }

    pub fn tree() -> Self {
        Self("tree".into())
    }

    pub fn commit() -> Self {
        Self("commit".into())
    }

    pub fn tag() -> Self {
        Self("tag".into())
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for GitObjectType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl From<ObjectKind> for GitObjectType {
    fn from(kind: ObjectKind) -> Self {
        match kind {
            ObjectKind::Blob => Self::blob(),
            ObjectKind::Tree => Self::tree(),
            ObjectKind::Commit => Self::commit(),
            ObjectKind::Tag => Self::tag(),
        }
    }
}

impl GitObjectType {
    /// Try to convert this git type string to an [`ObjectKind`].
    ///
    /// Returns `None` for forward-compatible unknown types.
    pub fn to_object_kind(&self) -> Option<ObjectKind> {
        match self.as_str() {
            "blob" => Some(ObjectKind::Blob),
            "tree" => Some(ObjectKind::Tree),
            "commit" => Some(ObjectKind::Commit),
            "tag" => Some(ObjectKind::Tag),
            _ => None,
        }
    }
}

// ---------------------------------------------------------------------------
// Header encoding / decoding
// ---------------------------------------------------------------------------

/// Format data with a git object header: `"{type} {len}\0{data}"`.
fn git_object_bytes(kind: &str, data: &[u8]) -> Vec<u8> {
    let header = format!("{kind} {}\0", data.len());
    let mut buf = Vec::with_capacity(header.len() + data.len());
    buf.extend_from_slice(header.as_bytes());
    buf.extend_from_slice(data);
    buf
}

/// Parse a git object header, returning `(type_str, body)`.
fn parse_git_header(raw: &[u8]) -> Option<(&str, &[u8])> {
    let null_pos = raw.iter().position(|&b| b == 0)?;
    let header = std::str::from_utf8(&raw[..null_pos]).ok()?;
    let space_pos = header.find(' ')?;
    let kind = &header[..space_pos];
    Some((kind, &raw[null_pos + 1..]))
}

/// Parse `(kind, header_len, body_len)` from a prefix that contains at
/// least the header (`"{type} {len}\0"`). Lets ranged backends learn
/// where the body starts without fetching it.
fn parse_git_header_meta(raw: &[u8]) -> Option<(&str, u64, u64)> {
    let null_pos = raw.iter().position(|&b| b == 0)?;
    let header = std::str::from_utf8(&raw[..null_pos]).ok()?;
    let space_pos = header.find(' ')?;
    let kind = &header[..space_pos];
    let body_len: u64 = header[space_pos + 1..].parse().ok()?;
    Some((kind, (null_pos + 1) as u64, body_len))
}

/// Upper bound on the length of a git object header. `"blob "` (5) +
/// max u64 decimal (20) + `\0` (1) = 26; round up to 32 for slack.
const MAX_GIT_HEADER_LEN: u64 = 32;

// ---------------------------------------------------------------------------
// GitPrefixStore<S> — header-prefixed wrapper
// ---------------------------------------------------------------------------

/// Wrapper that stores data with git-style `"{type} {len}\0"` headers.
///
/// Implements [`ContentStore<K>`] (blob-only view) and
/// [`TaggedStore<K, GitObjectType>`] (type-aware view) by prefixing all
/// data with a git object header before passing to the inner store.
///
/// Works with any `ContentStore<K>` — e.g. a [`SharedMemoryStore`],
/// a `SqliteStore`, or a git object store backed by a real `.git/objects`
/// directory.
///
/// [`SharedMemoryStore`]: crate::SharedMemoryStore
pub struct GitPrefixStore<S> {
    inner: S,
}

impl<S> GitPrefixStore<S> {
    pub fn new(inner: S) -> Self {
        Self { inner }
    }

    pub fn inner(&self) -> &S {
        &self.inner
    }

    pub fn into_inner(self) -> S {
        self.inner
    }
}

impl<K: Send + Sync, S: ContentStore<K>> ContentStore<K> for GitPrefixStore<S> {
    /// Retrieve blob data only — returns `None` for non-blob objects.
    fn get(&self, key: &K) -> Option<Vec<u8>> {
        let raw = self.inner.get(key)?;
        let (kind, body) = parse_git_header(&raw)?;
        if kind == "blob" {
            Some(body.to_vec())
        } else {
            None
        }
    }

    fn put(&self, key: K, data: &[u8]) -> Result<(), StoreError> {
        let prefixed = git_object_bytes("blob", data);
        self.inner.put(key, &prefixed)
    }

    fn insert(&self, data: &[u8]) -> Result<K, StoreError> {
        let prefixed = git_object_bytes("blob", data);
        self.inner.insert(&prefixed)
    }

    /// Check whether a key exists (any object type).
    fn contains(&self, key: &K) -> bool {
        self.inner.contains(key)
    }

    fn len(&self) -> Option<usize> {
        self.inner.len()
    }

    /// Probe the header from the inner store (`get_slice(0..32)`) and
    /// parse the length. If the inner store has a native ranged read,
    /// this avoids fetching the body entirely.
    fn head(&self, key: &K) -> Option<BlobInfo> {
        let probe = self.inner.get_slice(key, 0..MAX_GIT_HEADER_LEN).ok()?;
        let (kind, _header_len, body_len) = parse_git_header_meta(&probe)?;
        if kind != "blob" {
            return None;
        }
        Some(BlobInfo { size: body_len })
    }

    /// Two ranged reads on the inner store: ~32-byte header probe, then
    /// the body slice at its actual offset. For a `SqliteStore` inner,
    /// this fetches only `header_len + range_size` bytes total instead
    /// of the whole blob.
    fn get_slice(
        &self,
        key: &K,
        range: std::ops::Range<u64>,
    ) -> Result<Vec<u8>, StoreError> {
        let probe = match self.inner.get_slice(key, 0..MAX_GIT_HEADER_LEN) {
            Ok(p) => p,
            Err(StoreError::NotFound) => return Err(StoreError::NotFound),
            Err(e) => return Err(e),
        };
        let Some((kind, header_len, body_len)) = parse_git_header_meta(&probe) else {
            return Err(StoreError::Io("malformed git header".into()));
        };
        if kind != "blob" {
            // Non-blob keys are invisible to ContentStore::get, so they
            // look "missing" through this interface too.
            return Err(StoreError::NotFound);
        }
        let Some(body_indices) = clip_slice(body_len, range)? else {
            return Ok(Vec::new());
        };
        let inner_start = header_len + body_indices.start as u64;
        let inner_end = header_len + body_indices.end as u64;
        self.inner.get_slice(key, inner_start..inner_end)
    }
}

impl<K: Send + Sync, S: ContentStore<K>> TaggedStore<K, GitObjectType> for GitPrefixStore<S> {
    /// Get body data by key, stripping the header unconditionally.
    fn get_repr(&self, key: &K) -> Option<Vec<u8>> {
        let raw = self.inner.get(key)?;
        let (_, body) = parse_git_header(&raw)?;
        Some(body.to_vec())
    }

    fn get_tag(&self, key: &K) -> Option<GitObjectType> {
        let raw = self.inner.get(key)?;
        let (kind, _) = parse_git_header(&raw)?;
        Some(GitObjectType::new(kind))
    }

    fn insert_tagged(&self, tag: GitObjectType, data: &[u8]) -> Result<K, StoreError> {
        let prefixed = git_object_bytes(tag.as_str(), data);
        self.inner.insert(&prefixed)
    }

    fn get_repr_with(&self, tag: &GitObjectType, key: &K) -> Option<Vec<u8>> {
        let raw = self.inner.get(key)?;
        let (kind, body) = parse_git_header(&raw)?;
        if kind == tag.as_str() {
            Some(body.to_vec())
        } else {
            None
        }
    }

    fn get_tag_with(&self, tag: &GitObjectType, key: &K) -> Option<GitObjectType> {
        let raw = self.inner.get(key)?;
        let (kind, _) = parse_git_header(&raw)?;
        if kind == tag.as_str() {
            Some(GitObjectType::new(kind))
        } else {
            None
        }
    }
}

// ---------------------------------------------------------------------------
// GitTaggedObjectStore<S> — ObjectStore adapter over TaggedStore<O256, GitObjectType>
// ---------------------------------------------------------------------------

/// Adapter exposing any [`TaggedStore<O256, GitObjectType>`] as an [`ObjectStore`].
///
/// Works the same as the git-backend [`ObjectStore`] in `covalence-git`, but
/// backed by any tagged store (e.g. a [`GitPrefixStore`] over a memory store)
/// rather than a real `.git/objects` directory.
///
/// All object types (blob, tree, commit, tag) are stored via
/// [`TaggedStore::insert_tagged`] with the corresponding [`GitObjectType`].
#[derive(Clone)]
pub struct GitTaggedObjectStore<S> {
    inner: S,
}

impl<S> GitTaggedObjectStore<S> {
    pub fn new(inner: S) -> Self {
        Self { inner }
    }

    pub fn inner(&self) -> &S {
        &self.inner
    }

    pub fn into_inner(self) -> S {
        self.inner
    }
}

impl<T: Object, S: TaggedStore<O256, GitObjectType>> ObjectStore<O256, T>
    for GitTaggedObjectStore<S>
{
    fn get(&self, key: &O256) -> Result<Option<T>, StoreError> {
        let expected = GitObjectType::from(T::KIND);
        match self.inner.get_repr_with(&expected, key) {
            Some(data) => Ok(Some(T::from_data(data))),
            None => {
                // Distinguish "not found" from "wrong type"
                match self.inner.get_tag(key) {
                    Some(actual) => match actual.to_object_kind() {
                        Some(got) => Err(StoreError::KindMismatch {
                            expected: T::KIND,
                            got,
                        }),
                        None => Err(StoreError::Io(format!(
                            "type mismatch: expected {:?}, got unknown type \"{}\"",
                            T::KIND,
                            actual
                        ))),
                    },
                    None => Ok(None),
                }
            }
        }
    }

    fn insert(&self, obj: &T) -> Result<O256, StoreError> {
        let git_type = GitObjectType::from(T::KIND);
        self.inner.insert_tagged(git_type, obj.data())
    }

    fn put(&self, key: O256, obj: &T) -> Result<(), StoreError> {
        let computed = ObjectStore::insert(self, obj)?;
        if computed != key {
            return Err(StoreError::Io(format!(
                "hash mismatch: expected {key}, computed {computed}"
            )));
        }
        Ok(())
    }

    fn contains(&self, key: &O256) -> bool {
        self.inner.contains(key)
    }
}

impl<S: TaggedStore<O256, GitObjectType>> GitTaggedObjectStore<S> {
    /// Retrieve an object without static type checking.
    pub fn get_any(&self, key: &O256) -> Result<Option<AnyObject>, StoreError> {
        match self.inner.get_tag(key) {
            Some(git_type) => {
                let data = self
                    .inner
                    .get_repr(key)
                    .ok_or_else(|| StoreError::Io("tag exists but data missing".into()))?;
                let kind = git_type
                    .to_object_kind()
                    .ok_or_else(|| StoreError::Io(format!("unknown git type: {git_type}")))?;
                Ok(Some(AnyObject { kind, data }))
            }
            None => Ok(None),
        }
    }

    /// Store a dynamically-typed object.
    pub fn insert_any(&self, obj: &AnyObject) -> Result<O256, StoreError> {
        let git_type = GitObjectType::from(obj.kind);
        self.inner.insert_tagged(git_type, &obj.data)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // -- GitObjectType unit tests --

    #[test]
    fn git_object_type_display() {
        assert_eq!(GitObjectType::blob().to_string(), "blob");
        assert_eq!(GitObjectType::tree().to_string(), "tree");
        assert_eq!(GitObjectType::commit().to_string(), "commit");
        assert_eq!(GitObjectType::tag().to_string(), "tag");
        assert_eq!(GitObjectType::new("widget").to_string(), "widget");
    }

    #[test]
    fn git_object_type_equality() {
        assert_eq!(GitObjectType::blob(), GitObjectType::new("blob"));
        assert_ne!(GitObjectType::blob(), GitObjectType::tree());
    }

    // -- Header format tests --

    #[test]
    fn git_object_bytes_format() {
        assert_eq!(git_object_bytes("blob", b"hi"), b"blob 2\0hi");
        assert_eq!(git_object_bytes("tree", b""), b"tree 0\0");
        assert_eq!(git_object_bytes("commit", b"abc"), b"commit 3\0abc");
    }

    #[test]
    fn parse_git_header_valid() {
        let (kind, body) = parse_git_header(b"blob 5\0hello").unwrap();
        assert_eq!(kind, "blob");
        assert_eq!(body, b"hello");
    }

    #[test]
    fn parse_git_header_empty_body() {
        let (kind, body) = parse_git_header(b"tree 0\0").unwrap();
        assert_eq!(kind, "tree");
        assert_eq!(body, b"");
    }

    #[test]
    fn parse_git_header_no_null() {
        assert!(parse_git_header(b"blob 5 hello").is_none());
    }

    #[test]
    fn parse_git_header_no_space() {
        assert!(parse_git_header(b"blob\0hello").is_none());
    }

    #[test]
    fn parse_git_header_binary_body() {
        let mut data = b"blob 4\0".to_vec();
        data.extend_from_slice(&[0, 1, 0, 255]);
        let (kind, body) = parse_git_header(&data).unwrap();
        assert_eq!(kind, "blob");
        assert_eq!(body, &[0, 1, 0, 255]);
    }

    #[test]
    fn round_trip_format_parse() {
        let original = b"some data with \0 nulls inside";
        let encoded = git_object_bytes("tree", original);
        let (kind, decoded) = parse_git_header(&encoded).unwrap();
        assert_eq!(kind, "tree");
        assert_eq!(decoded, original);
    }

    // -- Store integration tests --

    #[cfg(feature = "memory")]
    mod with_memory {
        use super::*;
        use crate::{ContentStore, SharedMemoryStore, TaggedStore};

        fn store() -> GitPrefixStore<SharedMemoryStore> {
            GitPrefixStore::new(SharedMemoryStore::new())
        }

        #[test]
        fn blob_round_trip() {
            let s = store();
            let key = s.insert(b"hello").unwrap();
            assert_eq!(s.get(&key).unwrap(), b"hello");
        }

        #[test]
        fn blob_via_tagged_matches_insert() {
            let s = store();
            let k1 = s.insert(b"data").unwrap();
            let k2 = s.insert_tagged(GitObjectType::blob(), b"data").unwrap();
            assert_eq!(k1, k2);
        }

        #[test]
        fn tree_invisible_to_get() {
            let s = store();
            let key = s
                .insert_tagged(GitObjectType::tree(), b"not a tree")
                .unwrap();

            // ContentStore::get returns None for non-blob types
            assert_eq!(ContentStore::get(&s, &key), None);

            // but the key still exists
            assert!(s.contains(&key));

            // get_repr strips header unconditionally
            assert_eq!(s.get_repr(&key).unwrap(), b"not a tree");
        }

        #[test]
        fn get_tag_returns_type() {
            let s = store();

            let blob_key = s.insert(b"blob data").unwrap();
            assert_eq!(s.get_tag(&blob_key), Some(GitObjectType::blob()));

            let tree_key = s
                .insert_tagged(GitObjectType::tree(), b"tree data")
                .unwrap();
            assert_eq!(s.get_tag(&tree_key), Some(GitObjectType::tree()));

            let commit_key = s
                .insert_tagged(GitObjectType::commit(), b"commit data")
                .unwrap();
            assert_eq!(s.get_tag(&commit_key), Some(GitObjectType::commit()));
        }

        #[test]
        fn get_repr_works_for_all_types() {
            let s = store();

            let k_blob = s.insert(b"B").unwrap();
            let k_tree = s.insert_tagged(GitObjectType::tree(), b"T").unwrap();
            let k_tag = s.insert_tagged(GitObjectType::tag(), b"G").unwrap();

            assert_eq!(s.get_repr(&k_blob).unwrap(), b"B");
            assert_eq!(s.get_repr(&k_tree).unwrap(), b"T");
            assert_eq!(s.get_repr(&k_tag).unwrap(), b"G");
        }

        #[test]
        fn get_repr_with_validates_type() {
            let s = store();
            let key = s.insert_tagged(GitObjectType::tree(), b"data").unwrap();

            // Correct tag → data
            assert_eq!(
                s.get_repr_with(&GitObjectType::tree(), &key).unwrap(),
                b"data"
            );

            // Wrong tag → None
            assert_eq!(s.get_repr_with(&GitObjectType::blob(), &key), None);
        }

        #[test]
        fn head_strips_header_returns_body_size() {
            let s = store();
            let key = s.insert(b"hello world").unwrap();
            assert_eq!(s.head(&key), Some(crate::BlobInfo { size: 11 }));
        }

        #[test]
        fn head_returns_none_for_tree() {
            // Non-blob objects are invisible through the ContentStore interface.
            let s = store();
            let key = s.insert_tagged(GitObjectType::tree(), b"data").unwrap();
            assert_eq!(s.head(&key), None);
        }

        #[test]
        fn get_slice_strips_header() {
            let s = store();
            let key = s.insert(b"0123456789").unwrap();
            assert_eq!(s.get_slice(&key, 0..4).unwrap(), b"0123");
            assert_eq!(s.get_slice(&key, 5..10).unwrap(), b"56789");
            // Over-long end clamps to body length, not raw length.
            assert_eq!(s.get_slice(&key, 8..999).unwrap(), b"89");
        }

        #[test]
        fn get_slice_missing_is_not_found() {
            let s = store();
            let missing = covalence_hash::O256::blob(b"absent");
            assert!(matches!(
                s.get_slice(&missing, 0..5),
                Err(StoreError::NotFound)
            ));
        }

        #[test]
        fn get_slice_on_tree_is_not_found() {
            // Same "non-blob looks missing" rule as `get`.
            let s = store();
            let key = s.insert_tagged(GitObjectType::tree(), b"tree").unwrap();
            assert!(matches!(
                s.get_slice(&key, 0..2),
                Err(StoreError::NotFound)
            ));
        }

        #[test]
        fn forward_compat_unknown_type() {
            let s = store();
            let custom = GitObjectType::new("widget");
            let key = s.insert_tagged(custom.clone(), b"payload").unwrap();

            assert_eq!(s.get_tag(&key), Some(custom.clone()));
            assert_eq!(s.get_repr(&key).unwrap(), b"payload");

            // ContentStore::get returns None (not a blob)
            assert_eq!(ContentStore::get(&s, &key), None);
        }

        #[test]
        fn inner_store_sees_prefixed_data() {
            let s = store();
            let key = s.insert(b"raw").unwrap();

            // The inner store has the full git object bytes
            let raw = s.inner().get(&key).unwrap();
            assert_eq!(raw, b"blob 3\0raw");
        }

        #[test]
        fn different_types_different_keys() {
            let s = store();
            let data = b"same data";

            let k_blob = s.insert_tagged(GitObjectType::blob(), data).unwrap();
            let k_tree = s.insert_tagged(GitObjectType::tree(), data).unwrap();

            // Different type prefixes → different hashes
            assert_ne!(k_blob, k_tree);
        }

        #[test]
        fn get_missing_key_returns_none() {
            let s = store();
            let missing = covalence_hash::O256::blob(b"not stored");
            assert_eq!(ContentStore::get(&s, &missing), None);
            assert_eq!(s.get_repr(&missing), None);
            assert_eq!(s.get_tag(&missing), None);
        }

        #[test]
        fn get_tag_with_validates() {
            let s = store();
            let key = s.insert_tagged(GitObjectType::commit(), b"data").unwrap();

            assert_eq!(
                s.get_tag_with(&GitObjectType::commit(), &key),
                Some(GitObjectType::commit())
            );
            assert_eq!(s.get_tag_with(&GitObjectType::blob(), &key), None);
        }

        #[test]
        fn contains_sees_all_types() {
            let s = store();
            let k_blob = s.insert(b"b").unwrap();
            let k_tree = s.insert_tagged(GitObjectType::tree(), b"t").unwrap();

            assert!(s.contains(&k_blob));
            assert!(s.contains(&k_tree));
        }

        // -- TaggedBlobStore wrapper --

        #[test]
        fn tagged_blobstore_over_git_prefix() {
            let s = crate::TaggedBlobStore::new(store());

            let key = s.insert_tagged(GitObjectType::tree(), b"tree").unwrap();
            assert_eq!(s.get_repr(&key).unwrap(), b"tree");
            assert_eq!(s.get_tag(&key), Some(GitObjectType::tree()));
            assert_eq!(ContentStore::get(&s, &key), None);

            let blob_key = ContentStore::insert(&s, b"blob").unwrap();
            assert_eq!(ContentStore::get(&s, &blob_key).unwrap(), b"blob");
        }

        #[test]
        fn git_prefix_wraps_blobstore() {
            // The user's primary pattern: wrap a BlobStore in a GitPrefixStore
            let inner = crate::BlobStore::new(SharedMemoryStore::new());
            let s = GitPrefixStore::new(inner);

            let tree_key = s.insert_tagged(GitObjectType::tree(), b"data").unwrap();
            assert_eq!(s.get_repr(&tree_key).unwrap(), b"data");
            assert_eq!(s.get_tag(&tree_key), Some(GitObjectType::tree()));
            assert_eq!(ContentStore::get(&s, &tree_key), None);

            let blob_key = s.insert(b"blob").unwrap();
            assert_eq!(s.get(&blob_key).unwrap(), b"blob");
        }

        // -- GitTaggedObjectStore tests --

        use crate::{Blob, Commit, ObjectKind, ObjectStore, Tree};

        fn object_store() -> GitTaggedObjectStore<GitPrefixStore<SharedMemoryStore>> {
            GitTaggedObjectStore::new(store())
        }

        #[test]
        fn object_store_blob_round_trip() {
            let os = object_store();
            let blob = Blob(b"hello world".to_vec());
            let key = ObjectStore::insert(&os, &blob).unwrap();
            let got: Blob = ObjectStore::get(&os, &key).unwrap().unwrap();
            assert_eq!(got.0, b"hello world");
        }

        #[test]
        fn object_store_tree_round_trip() {
            let os = object_store();
            let tree = Tree(b"tree bytes".to_vec());
            let key = ObjectStore::insert(&os, &tree).unwrap();
            let got: Tree = ObjectStore::get(&os, &key).unwrap().unwrap();
            assert_eq!(got.0, b"tree bytes");
        }

        #[test]
        fn object_store_commit_round_trip() {
            let os = object_store();
            let commit = Commit(b"commit bytes".to_vec());
            let key = ObjectStore::insert(&os, &commit).unwrap();
            let got: Commit = ObjectStore::get(&os, &key).unwrap().unwrap();
            assert_eq!(got.0, b"commit bytes");
        }

        #[test]
        fn object_store_kind_mismatch() {
            let os = object_store();
            let tree = Tree(b"tree data".to_vec());
            let key = ObjectStore::insert(&os, &tree).unwrap();

            // Try reading as a Blob → KindMismatch
            let result: Result<Option<Blob>, _> = ObjectStore::get(&os, &key);
            match result {
                Err(StoreError::KindMismatch { expected, got }) => {
                    assert_eq!(expected, ObjectKind::Blob);
                    assert_eq!(got, ObjectKind::Tree);
                }
                other => panic!("expected KindMismatch, got {other:?}"),
            }
        }

        #[test]
        fn object_store_get_missing() {
            let os = object_store();
            let missing = covalence_hash::O256::blob(b"not stored");
            let result: Result<Option<Blob>, _> = ObjectStore::get(&os, &missing);
            assert!(matches!(result, Ok(None)));
        }

        #[test]
        fn object_store_contains() {
            let os = object_store();
            let blob = Blob(b"exists".to_vec());
            let key = ObjectStore::insert(&os, &blob).unwrap();
            assert!(ObjectStore::<_, Blob>::contains(&os, &key));

            let missing = covalence_hash::O256::blob(b"nope");
            assert!(!ObjectStore::<_, Blob>::contains(&os, &missing));
        }

        #[test]
        fn object_store_different_types_different_keys() {
            let os = object_store();
            let data = b"same data";
            let blob_key = ObjectStore::insert(&os, &Blob(data.to_vec())).unwrap();
            let tree_key = ObjectStore::insert(&os, &Tree(data.to_vec())).unwrap();
            assert_ne!(blob_key, tree_key);
        }

        #[test]
        fn object_store_get_any() {
            let os = object_store();
            let tree = Tree(b"tree bytes".to_vec());
            let key = ObjectStore::insert(&os, &tree).unwrap();

            let any = os.get_any(&key).unwrap().unwrap();
            assert_eq!(any.kind, ObjectKind::Tree);
            assert_eq!(any.data, b"tree bytes");
        }

        #[test]
        fn object_store_insert_any() {
            let os = object_store();
            let any = crate::AnyObject {
                kind: ObjectKind::Blob,
                data: b"any blob".to_vec(),
            };
            let key = os.insert_any(&any).unwrap();
            let blob: Blob = ObjectStore::get(&os, &key).unwrap().unwrap();
            assert_eq!(blob.0, b"any blob");
        }

        #[test]
        fn object_store_put_matching_hash() {
            let os = object_store();
            let blob = Blob(b"put test".to_vec());
            let key = ObjectStore::insert(&os, &blob).unwrap();
            // put with same key is idempotent
            ObjectStore::put(&os, key, &blob).unwrap();
        }

        #[test]
        fn object_store_put_wrong_hash() {
            let os = object_store();
            let blob = Blob(b"data".to_vec());
            let wrong_key = covalence_hash::O256::blob(b"wrong");
            assert!(ObjectStore::put(&os, wrong_key, &blob).is_err());
        }

        #[test]
        fn object_store_over_tagged_blobstore() {
            // Wrap a TaggedBlobStore in GitTaggedObjectStore
            let tagged = crate::TaggedBlobStore::new(store());
            let os = GitTaggedObjectStore::new(tagged);

            let tree = Tree(b"tree data".to_vec());
            let key = ObjectStore::insert(&os, &tree).unwrap();
            let got: Tree = ObjectStore::get(&os, &key).unwrap().unwrap();
            assert_eq!(got.0, b"tree data");
        }
    }
}
