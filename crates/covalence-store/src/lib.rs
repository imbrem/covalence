use std::sync::Arc;

pub use covalence_hash::O256;

mod object;
pub use object::{
    AnyObject, Blob, Commit, KeyedObjectStore, Object, ObjectKind, ObjectStore, Tag, Tree,
};

mod range;
pub use range::{BlobInfo, ByteRange, ResolvedRange, clip_slice, slice_range};

mod overlay;
pub use overlay::{DEFAULT_SIZE_THRESHOLD, OverlayStore, SizeRouter};

// ---------------------------------------------------------------------------
// TreeStore — POSIX-style virtual filesystem trait
// ---------------------------------------------------------------------------

/// Hierarchical store of byte values addressed by raw byte keys, with
/// named child subtrees — structurally a POSIX-style virtual filesystem
/// (or a collection of them, via [`ns`](Self::ns)).
///
/// Designed to be object-safe for use behind `Arc<dyn TreeStore>`.
/// Keys and values are raw byte slices — type tagging (if needed)
/// is the caller's responsibility.
///
/// Distinct from [`covalence_kv::KvStore`]: that's a flat key/value
/// blob store (S3-shaped). This is a tree of namespaces with read
/// tracking, suited to kernel-internal scaffolding.
pub trait TreeStore: Send + Sync {
    /// Insert or overwrite a value.
    fn set(&self, key: &[u8], value: &[u8]);

    /// Look up a value by key.
    fn get(&self, key: &[u8]) -> Option<Vec<u8>>;

    /// Mark a key as touched (set was called with this bare key).
    fn touch(&self, key: &[u8]);

    /// Check whether a key has been touched.
    fn touched(&self, key: &[u8]) -> bool;

    /// Navigate to a child namespace. Returns the same child on
    /// repeated calls with the same key (shared state).
    fn ns(&self, key: &[u8]) -> Arc<dyn TreeStore>;

    /// Duplicate this handle (same underlying data).
    fn dup(&self) -> Arc<dyn TreeStore>;
}

/// Errors from store operations.
#[derive(Debug, thiserror::Error)]
pub enum StoreError {
    #[error("store I/O error: {0}")]
    Io(String),

    #[error("type mismatch: expected {expected:?}, got {got:?}")]
    KindMismatch {
        expected: ObjectKind,
        got: ObjectKind,
    },

    /// The requested key does not exist.
    ///
    /// Async `get` / `get_range` / `head` surface "missing" as this error
    /// instead of `Ok(None)` to match the kv pattern: missing-key and
    /// network-error are both per-call failures on remote backends, and
    /// callers usually want to handle them together.
    #[error("not found")]
    NotFound,

    /// A range request was unsatisfiable against the blob's actual size.
    ///
    /// Mirrors HTTP `416 Range Not Satisfiable`. The HTTP layer can build
    /// `Content-Range: bytes */{total}` directly from `total`.
    #[error("range not satisfiable: blob length {total}")]
    RangeNotSatisfiable { total: u64 },
}

/// Content-addressed store trait. Object-safe behind `Arc<dyn ContentStore<K>>`.
///
/// The simple API is [`get_slice`](Self::get_slice) — fetch a half-open
/// byte range, or error. Almost every caller wants this.
/// [`get`](Self::get) — whole blob, missing-as-None — and
/// [`get_range`](Self::get_range) — HTTP `Range:`-shaped with
/// [`ResolvedRange`] metadata — both derive from it.
///
/// Default-impl chain:
/// * [`get`](Self::get) ⇄ [`get_slice`](Self::get_slice) are mutually
///   derivable. Each defaults via the other — backends **MUST implement
///   at least one** (implementing neither recurses infinitely; the docs
///   are the only warning).
/// * [`head`](Self::head) defaults via `get_slice` (sized via the
///   returned vec).
/// * [`get_range`](Self::get_range) defaults via `head` + `get_slice`.
/// * [`contains`](Self::contains) defaults via `head`.
///
/// **Override [`get_slice`](Self::get_slice) for native partial reads**
/// — sqlite incremental I/O, FS `pread`, HTTP `Range:`. The HTTP-shaped
/// [`get_range`](Self::get_range) is "`get_slice` plus metadata";
/// returning a bigger range than asked, or bundling body + size in one
/// round trip, are the kinds of optimizations that override there.
/// Simplest backend: just implement `get`.
///
/// Multi-range requests live above the trait — see [`fetch_ranges`] for
/// the batch helper and [`ByteRange::parse_http_header_multi`] for the
/// parser.
pub trait ContentStore<K>: Send + Sync {
    /// Store data under the given key.
    fn put(&self, key: K, data: &[u8]) -> Result<(), StoreError>;

    /// Hash and store data, returning the content key.
    fn insert(&self, data: &[u8]) -> Result<K, StoreError>;

    /// Retrieve the full blob by key. Default delegates to
    /// `get_slice(0..u64::MAX)`.
    fn get(&self, key: &K) -> Option<Vec<u8>> {
        self.get_slice(key, 0..u64::MAX).ok()
    }

    /// Fetch a half-open byte range — the simple API.
    ///
    /// Errors: [`StoreError::NotFound`] (unknown key),
    /// [`StoreError::RangeNotSatisfiable`] (`start` past the blob's
    /// end). `start >= end` returns `Ok(vec![])` after an existence
    /// check; `end > total` clamps silently (POSIX read semantics).
    ///
    /// Default impl pulls the whole blob via `get` and slices it.
    fn get_slice(&self, key: &K, range: std::ops::Range<u64>) -> Result<Vec<u8>, StoreError> {
        let Some(full) = self.get(key) else {
            return Err(StoreError::NotFound);
        };
        slice_range(&full, range)
    }

    /// Check whether a key exists. Default uses `head`.
    fn contains(&self, key: &K) -> bool {
        self.head(key).is_some()
    }

    /// Number of entries in the store, if cheaply available.
    fn len(&self) -> Option<usize> {
        None
    }

    /// Blob metadata without (necessarily) fetching the body — HTTP `HEAD`.
    ///
    /// Default impl probes via `get_slice` (which a range-native backend
    /// can serve cheaply). Override on backends that can answer in one
    /// round trip (sqlite `SELECT length(...)`).
    fn head(&self, key: &K) -> Option<BlobInfo> {
        match self.get_slice(key, 0..u64::MAX) {
            Ok(v) => Some(BlobInfo {
                size: v.len() as u64,
            }),
            Err(_) => None,
        }
    }

    /// Fetch a byte range — HTTP `GET` with a `Range:` header.
    ///
    /// `Ok(None)` is unknown key, `Ok(Some((bytes, resolved)))` is a hit
    /// (where `resolved` populates `Content-Range`), and
    /// [`StoreError::RangeNotSatisfiable`] is an unsatisfiable range.
    ///
    /// Default: `head` to learn total size, resolve [`ByteRange`] to
    /// concrete bounds, then delegate to `get_slice`. Override on
    /// backends that can return body + metadata in one round trip
    /// (HTTP `Range:` upstream), or that find it useful to return more
    /// bytes than asked.
    fn get_range(
        &self,
        key: &K,
        range: ByteRange,
    ) -> Result<Option<(Vec<u8>, ResolvedRange)>, StoreError> {
        let Some(info) = self.head(key) else {
            return Ok(None);
        };
        let resolved = range.resolve(info.size)?;
        let bytes = self.get_slice(key, resolved.start..resolved.end + 1)?;
        Ok(Some((bytes, resolved)))
    }
}

/// Batch-fetch a list of byte ranges from one blob.
///
/// One [`ContentStore::head`] call to learn total size + one
/// [`ContentStore::get_slice`] call per range. Returns `Ok(None)` if the
/// key is missing; the per-range vector matches `ranges` 1:1.
///
/// Multi-range batching deliberately doesn't live on the trait — most
/// backends serve ranges one at a time, and
/// `multipart/byteranges` serialization is an HTTP concern. Backends
/// with native multi-range support (sqlite single transaction, HTTP
/// `Range:` upstream returning `multipart/byteranges`) should expose an
/// optimized helper on the concrete type and have callers use it
/// directly.
///
/// For the HTTP parser, see [`ByteRange::parse_http_header_multi`].
pub fn fetch_ranges<K, S>(
    store: &S,
    key: &K,
    ranges: &[ByteRange],
) -> Result<Option<Vec<(Vec<u8>, ResolvedRange)>>, StoreError>
where
    S: ContentStore<K> + ?Sized,
{
    let Some(info) = store.head(key) else {
        return Ok(None);
    };
    let mut out = Vec::with_capacity(ranges.len());
    for &range in ranges {
        let resolved = range.resolve(info.size)?;
        let bytes = store.get_slice(key, resolved.start..resolved.end + 1)?;
        out.push((bytes, resolved));
    }
    Ok(Some(out))
}

// ---------------------------------------------------------------------------
// BlobStore<K> — Arc<dyn ContentStore<K>> wrapper
// ---------------------------------------------------------------------------

/// Content-addressed blob store.
///
/// Wraps any [`ContentStore<K>`] implementation behind an `Arc`,
/// making clone cheap and dispatch dynamic.
#[derive(Clone)]
pub struct BlobStore<K>(Arc<dyn ContentStore<K>>);

impl<K> BlobStore<K> {
    /// Wrap any `ContentStore<K>` implementation.
    pub fn new(store: impl ContentStore<K> + 'static) -> Self {
        Self(Arc::new(store))
    }
}

impl<K: Send + Sync> ContentStore<K> for BlobStore<K> {
    fn get(&self, key: &K) -> Option<Vec<u8>> {
        self.0.get(key)
    }

    fn put(&self, key: K, data: &[u8]) -> Result<(), StoreError> {
        self.0.put(key, data)
    }

    fn insert(&self, data: &[u8]) -> Result<K, StoreError> {
        self.0.insert(data)
    }

    fn contains(&self, key: &K) -> bool {
        self.0.contains(key)
    }

    fn len(&self) -> Option<usize> {
        self.0.len()
    }

    fn head(&self, key: &K) -> Option<BlobInfo> {
        self.0.head(key)
    }

    fn get_slice(&self, key: &K, range: std::ops::Range<u64>) -> Result<Vec<u8>, StoreError> {
        self.0.get_slice(key, range)
    }

    fn get_range(
        &self,
        key: &K,
        range: ByteRange,
    ) -> Result<Option<(Vec<u8>, ResolvedRange)>, StoreError> {
        self.0.get_range(key, range)
    }
}

// ---------------------------------------------------------------------------
// TaggedStore — content-addressed storage with keyed-hash tags
// ---------------------------------------------------------------------------

/// Tagged content store — extends content-addressed storage with keyed-hash tags.
///
/// Generic over key type `K` and tag type `T` (defaults to `K`).
/// Given `insert_tagged(tag, blob)`, the implementation computes a key from the
/// tag and blob data. The blob is stored once; a tag index maps computed keys
/// to `(tag, blob)` pairs.
///
/// The plain [`ContentStore::get`] returns data only for content-addressed keys
/// (inserted via [`ContentStore::insert`] / [`ContentStore::put`]), **not** for
/// tagged keys. Use [`get_repr`](TaggedStore::get_repr) to retrieve data
/// by either kind of key.
pub trait TaggedStore<K, T = K>: ContentStore<K> {
    /// Get blob data by any key (content hash or tagged key).
    fn get_repr(&self, key: &K) -> Option<Vec<u8>>;

    /// Get the tag for a tagged entry. Returns `None` for plain blobs.
    fn get_tag(&self, key: &K) -> Option<T>;

    /// Store a blob with a tag, returning the derived key.
    fn insert_tagged(&self, tag: T, data: &[u8]) -> Result<K, StoreError>;

    /// Get blob data given both tag and key (potentially more efficient).
    fn get_repr_with(&self, tag: &T, key: &K) -> Option<Vec<u8>> {
        let _ = tag;
        self.get_repr(key)
    }

    /// Get the tag given both tag and key (validates the tag matches).
    fn get_tag_with(&self, tag: &T, key: &K) -> Option<T> {
        let _ = tag;
        self.get_tag(key)
    }
}

// ---------------------------------------------------------------------------
// TaggedBlobStore — Arc<dyn TaggedStore> wrapper
// ---------------------------------------------------------------------------

/// Tagged blob store — wraps a [`TaggedStore`] behind an `Arc`.
///
/// Like [`BlobStore`], but also exposes tagged operations.
/// Converts to `BlobStore<K>` via [`From`].
#[derive(Clone)]
pub struct TaggedBlobStore<K, T = K>(Arc<dyn TaggedStore<K, T>>);

impl<K, T> TaggedBlobStore<K, T> {
    /// Wrap any `TaggedStore` implementation.
    pub fn new(store: impl TaggedStore<K, T> + 'static) -> Self {
        Self(Arc::new(store))
    }

    pub fn get_repr(&self, key: &K) -> Option<Vec<u8>> {
        self.0.get_repr(key)
    }

    pub fn get_tag(&self, key: &K) -> Option<T> {
        self.0.get_tag(key)
    }

    pub fn insert_tagged(&self, tag: T, data: &[u8]) -> Result<K, StoreError> {
        self.0.insert_tagged(tag, data)
    }

    pub fn get_repr_with(&self, tag: &T, key: &K) -> Option<Vec<u8>> {
        self.0.get_repr_with(tag, key)
    }

    pub fn get_tag_with(&self, tag: &T, key: &K) -> Option<T> {
        self.0.get_tag_with(tag, key)
    }
}

impl<K: Send + Sync, T: Send + Sync> ContentStore<K> for TaggedBlobStore<K, T> {
    fn get(&self, key: &K) -> Option<Vec<u8>> {
        self.0.get(key)
    }

    fn put(&self, key: K, data: &[u8]) -> Result<(), StoreError> {
        self.0.put(key, data)
    }

    fn insert(&self, data: &[u8]) -> Result<K, StoreError> {
        self.0.insert(data)
    }

    fn contains(&self, key: &K) -> bool {
        self.0.contains(key)
    }

    fn len(&self) -> Option<usize> {
        self.0.len()
    }

    fn head(&self, key: &K) -> Option<BlobInfo> {
        self.0.head(key)
    }

    fn get_slice(&self, key: &K, range: std::ops::Range<u64>) -> Result<Vec<u8>, StoreError> {
        self.0.get_slice(key, range)
    }

    fn get_range(
        &self,
        key: &K,
        range: ByteRange,
    ) -> Result<Option<(Vec<u8>, ResolvedRange)>, StoreError> {
        self.0.get_range(key, range)
    }
}

impl<K: Send + Sync, T: Send + Sync> TaggedStore<K, T> for TaggedBlobStore<K, T> {
    fn get_repr(&self, key: &K) -> Option<Vec<u8>> {
        self.0.get_repr(key)
    }

    fn get_tag(&self, key: &K) -> Option<T> {
        self.0.get_tag(key)
    }

    fn insert_tagged(&self, tag: T, data: &[u8]) -> Result<K, StoreError> {
        self.0.insert_tagged(tag, data)
    }

    fn get_repr_with(&self, tag: &T, key: &K) -> Option<Vec<u8>> {
        self.0.get_repr_with(tag, key)
    }

    fn get_tag_with(&self, tag: &T, key: &K) -> Option<T> {
        self.0.get_tag_with(tag, key)
    }
}

impl<K: Send + Sync + 'static, T: Send + Sync + 'static> From<TaggedBlobStore<K, T>>
    for BlobStore<K>
{
    fn from(tagged: TaggedBlobStore<K, T>) -> Self {
        BlobStore::new(tagged)
    }
}

mod git;
pub use git::{GitObjectType, GitPrefixStore, GitTaggedObjectStore};

#[cfg(feature = "memory")]
mod memory;
#[cfg(feature = "memory")]
pub use memory::{MemoryStore, SharedMemoryStore};

#[cfg(feature = "memory")]
mod tree;
#[cfg(feature = "memory")]
pub use tree::MemoryTreeStore;

#[cfg(feature = "sqlite")]
mod sqlite;
#[cfg(feature = "sqlite")]
pub use sqlite::SqliteStore;

#[cfg(feature = "async")]
mod async_store;
#[cfg(feature = "async")]
pub use async_store::{AsyncBlobStore, AsyncContentStore, AsyncOverSync};

#[cfg(feature = "blocking")]
mod blocking;
#[cfg(feature = "blocking")]
pub use blocking::BlockingBlobStore;

#[cfg(feature = "metadata")]
pub mod metadata;
#[cfg(feature = "metadata")]
pub use metadata::{StoreManifest, StoreRef};

#[cfg(test)]
#[cfg(feature = "memory")]
mod trait_tests {
    //! Integration tests for the `ContentStore` trait's default-impl
    //! chains. Backend-specific tests live with their backends.
    use super::*;

    /// Backend that implements only `get_slice` — exercises the
    /// reverse default chain (`get` and `head` falling back to it).
    struct SliceOnly {
        blobs: std::sync::RwLock<std::collections::HashMap<u64, Vec<u8>>>,
    }
    impl SliceOnly {
        fn new() -> Self {
            Self {
                blobs: std::sync::RwLock::new(std::collections::HashMap::new()),
            }
        }
    }
    impl ContentStore<u64> for SliceOnly {
        fn put(&self, key: u64, data: &[u8]) -> Result<(), StoreError> {
            self.blobs.write().unwrap().insert(key, data.to_vec());
            Ok(())
        }
        fn insert(&self, _data: &[u8]) -> Result<u64, StoreError> {
            unimplemented!("test backend uses explicit keys")
        }
        fn get_slice(&self, key: &u64, range: std::ops::Range<u64>) -> Result<Vec<u8>, StoreError> {
            let blobs = self.blobs.read().unwrap();
            let Some(data) = blobs.get(key) else {
                return Err(StoreError::NotFound);
            };
            let total = data.len() as u64;
            if range.start >= range.end {
                return Ok(Vec::new());
            }
            if total == 0 {
                return if range.start == 0 {
                    Ok(Vec::new())
                } else {
                    Err(StoreError::RangeNotSatisfiable { total })
                };
            }
            if range.start >= total {
                return Err(StoreError::RangeNotSatisfiable { total });
            }
            let end = range.end.min(total) as usize;
            Ok(data[range.start as usize..end].to_vec())
        }
    }

    #[test]
    fn slice_only_backend_derives_get() {
        let s = SliceOnly::new();
        s.put(1, b"hello").unwrap();
        assert_eq!(s.get(&1), Some(b"hello".to_vec()));
        assert_eq!(s.get(&999), None);
    }

    #[test]
    fn slice_only_backend_derives_head() {
        let s = SliceOnly::new();
        s.put(1, b"hello").unwrap();
        assert_eq!(s.head(&1), Some(BlobInfo { size: 5 }));
        assert_eq!(s.head(&999), None);
    }

    #[test]
    fn slice_only_backend_derives_get_range() {
        let s = SliceOnly::new();
        s.put(1, b"0123456789").unwrap();
        let (bytes, resolved) = s
            .get_range(&1, ByteRange::Suffix { length: 3 })
            .unwrap()
            .unwrap();
        assert_eq!(bytes, b"789");
        assert_eq!((resolved.start, resolved.end, resolved.total), (7, 9, 10));
    }

    #[test]
    fn slice_only_backend_derives_contains() {
        let s = SliceOnly::new();
        s.put(1, b"x").unwrap();
        assert!(s.contains(&1));
        assert!(!s.contains(&999));
    }

    #[test]
    fn empty_blob_get_returns_some_empty() {
        let s = SliceOnly::new();
        s.put(1, b"").unwrap();
        assert_eq!(s.get(&1), Some(Vec::new()));
        assert_eq!(s.head(&1), Some(BlobInfo { size: 0 }));
        assert!(s.contains(&1));
    }

    #[test]
    fn fetch_ranges_batches_three() {
        let s = SharedMemoryStore::new();
        let hash = s.insert(b"0123456789").unwrap();
        let result = fetch_ranges(
            &s,
            &hash,
            &[
                ByteRange::Closed { start: 0, end: 2 },
                ByteRange::Closed { start: 5, end: 7 },
                ByteRange::Suffix { length: 2 },
            ],
        )
        .unwrap()
        .unwrap();
        assert_eq!(result.len(), 3);
        assert_eq!(result[0].0, b"012");
        assert_eq!(result[1].0, b"567");
        assert_eq!(result[2].0, b"89");
        assert_eq!(result[2].1.to_content_range(), "bytes 8-9/10");
    }

    #[test]
    fn fetch_ranges_missing_returns_none() {
        let s = SharedMemoryStore::new();
        let result = fetch_ranges(
            &s,
            &O256::blob(b"absent"),
            &[ByteRange::Closed { start: 0, end: 1 }],
        )
        .unwrap();
        assert!(result.is_none());
    }

    #[test]
    fn fetch_ranges_one_bad_range_errors_whole_batch() {
        let s = SharedMemoryStore::new();
        let hash = s.insert(b"short").unwrap();
        // First range fine, second past end — whole batch is `RangeNotSatisfiable`.
        match fetch_ranges(
            &s,
            &hash,
            &[
                ByteRange::Closed { start: 0, end: 2 },
                ByteRange::From { start: 100 },
            ],
        ) {
            Err(StoreError::RangeNotSatisfiable { total }) => assert_eq!(total, 5),
            other => panic!("expected RangeNotSatisfiable, got {other:?}"),
        }
    }
}
