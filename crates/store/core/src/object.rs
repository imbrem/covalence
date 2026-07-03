//! Typed object storage: [`ObjectKind`], [`Object`] trait, concrete types, and [`ObjectStore`].

use covalence_hash::O256;

use crate::{ContentStore, StoreError, TaggedStore};

/// The kind of a stored object.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ObjectKind {
    Blob,
    Tree,
    Commit,
    Tag,
}

/// A typed store object with a statically-known kind.
pub trait Object: Send + Sync + Sized {
    /// The kind of this object type.
    const KIND: ObjectKind;

    /// Access raw data bytes.
    fn data(&self) -> &[u8];

    /// Wrap raw bytes into this type.
    fn from_data(data: Vec<u8>) -> Self;

    /// Consume into raw bytes.
    fn into_data(self) -> Vec<u8>;
}

/// Raw binary blob.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Blob(pub Vec<u8>);

/// Raw tree data (serialized directory listing).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tree(pub Vec<u8>);

/// Raw commit object (header + message).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Commit(pub Vec<u8>);

/// Raw annotated tag object.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tag(pub Vec<u8>);

macro_rules! impl_object {
    ($ty:ident, $kind:expr) => {
        impl Object for $ty {
            const KIND: ObjectKind = $kind;
            fn data(&self) -> &[u8] {
                &self.0
            }
            fn from_data(data: Vec<u8>) -> Self {
                Self(data)
            }
            fn into_data(self) -> Vec<u8> {
                self.0
            }
        }
    };
}

impl_object!(Blob, ObjectKind::Blob);
impl_object!(Tree, ObjectKind::Tree);
impl_object!(Commit, ObjectKind::Commit);
impl_object!(Tag, ObjectKind::Tag);

/// Dynamically-typed object (any kind).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AnyObject {
    pub kind: ObjectKind,
    pub data: Vec<u8>,
}

/// A content-addressed store that preserves object type information.
///
/// Generic over key type `K` and typed object `T`.
/// Type checking happens on read: if the stored kind doesn't match `T::KIND`,
/// returns `Err(StoreError::KindMismatch)`.
pub trait ObjectStore<K, T: Object>: Send + Sync {
    /// Retrieve a typed object by key.
    /// Returns `Ok(None)` if not found, `Err(KindMismatch)` if wrong type.
    fn get(&self, key: &K) -> Result<Option<T>, StoreError>;

    /// Hash and store a typed object, returning its content key.
    fn insert(&self, obj: &T) -> Result<K, StoreError>;

    /// Store at a specific key (verifies hash match).
    fn put(&self, key: K, obj: &T) -> Result<(), StoreError>;

    /// Check if a key exists (any type).
    fn contains(&self, key: &K) -> bool;
}

// ---------------------------------------------------------------------------
// KeyedObjectStore<S> — Blob + Tree over TaggedStore<O256>
// ---------------------------------------------------------------------------

/// Adapter for covalence-native object storage using BLAKE3 keyed hashing.
///
/// - **Blobs** are stored untagged via [`ContentStore::insert`], keyed by
///   `O256::blob(data)`.
/// - **Trees** are stored tagged via [`TaggedStore::insert_tagged`] with tag
///   `O256::blob("tree")`, keyed by the BLAKE3 keyed hash — the same
///   domain-separated scheme used by [`dir_hash`](covalence_object::dir_hash).
///
/// Only `Blob` and `Tree` types are supported.
pub struct KeyedObjectStore<S> {
    inner: S,
}

impl<S> KeyedObjectStore<S> {
    pub fn new(inner: S) -> Self {
        Self { inner }
    }

    pub fn inner(&self) -> &S {
        &self.inner
    }

    pub fn into_inner(self) -> S {
        self.inner
    }

    /// The tag key used for tree objects: `O256::blob("tree")`.
    fn tree_tag() -> O256 {
        O256::blob("tree")
    }
}

impl<S: TaggedStore<O256>> ObjectStore<O256, Blob> for KeyedObjectStore<S> {
    fn get(&self, key: &O256) -> Result<Option<Blob>, StoreError> {
        // If the key is in the tag index, it's a tagged entry (not a blob).
        if self.inner.get_tag(key).is_some() {
            let got = ObjectKind::Tree; // Only trees have tags in this store
            return Err(StoreError::KindMismatch {
                expected: ObjectKind::Blob,
                got,
            });
        }
        Ok(ContentStore::get(&self.inner, key).map(Blob::from_data))
    }

    fn insert(&self, obj: &Blob) -> Result<O256, StoreError> {
        ContentStore::insert(&self.inner, obj.data())
    }

    fn put(&self, key: O256, obj: &Blob) -> Result<(), StoreError> {
        ContentStore::put(&self.inner, key, obj.data())
    }

    fn contains(&self, key: &O256) -> bool {
        self.inner.get_tag(key).is_some() || ContentStore::contains(&self.inner, key)
    }
}

impl<S: TaggedStore<O256>> ObjectStore<O256, Tree> for KeyedObjectStore<S> {
    fn get(&self, key: &O256) -> Result<Option<Tree>, StoreError> {
        let tree_tag = Self::tree_tag();
        match self.inner.get_tag(key) {
            Some(tag) if tag == tree_tag => match self.inner.get_repr(key) {
                Some(data) => Ok(Some(Tree::from_data(data))),
                None => Err(StoreError::Io("tag exists but data missing".into())),
            },
            Some(_) => Err(StoreError::KindMismatch {
                expected: ObjectKind::Tree,
                got: ObjectKind::Blob,
            }),
            None => {
                if ContentStore::contains(&self.inner, key) {
                    Err(StoreError::KindMismatch {
                        expected: ObjectKind::Tree,
                        got: ObjectKind::Blob,
                    })
                } else {
                    Ok(None)
                }
            }
        }
    }

    fn insert(&self, obj: &Tree) -> Result<O256, StoreError> {
        self.inner.insert_tagged(Self::tree_tag(), obj.data())
    }

    fn put(&self, key: O256, obj: &Tree) -> Result<(), StoreError> {
        let computed = ObjectStore::insert(self, obj)?;
        if computed != key {
            return Err(StoreError::Io(format!(
                "hash mismatch: expected {key}, computed {computed}"
            )));
        }
        Ok(())
    }

    fn contains(&self, key: &O256) -> bool {
        self.inner.get_tag(key).is_some() || ContentStore::contains(&self.inner, key)
    }
}

impl<S: TaggedStore<O256>> KeyedObjectStore<S> {
    /// Retrieve an object without static type checking.
    pub fn get_any(&self, key: &O256) -> Result<Option<AnyObject>, StoreError> {
        if let Some(tag) = self.inner.get_tag(key) {
            let data = self
                .inner
                .get_repr(key)
                .ok_or_else(|| StoreError::Io("tag exists but data missing".into()))?;
            let kind = if tag == Self::tree_tag() {
                ObjectKind::Tree
            } else {
                return Err(StoreError::Io(format!("unknown tag: {tag}")));
            };
            return Ok(Some(AnyObject { kind, data }));
        }
        match ContentStore::get(&self.inner, key) {
            Some(data) => Ok(Some(AnyObject {
                kind: ObjectKind::Blob,
                data,
            })),
            None => Ok(None),
        }
    }

    /// Store a dynamically-typed object.
    pub fn insert_any(&self, obj: &AnyObject) -> Result<O256, StoreError> {
        match obj.kind {
            ObjectKind::Blob => ContentStore::insert(&self.inner, &obj.data),
            ObjectKind::Tree => self.inner.insert_tagged(Self::tree_tag(), &obj.data),
            other => Err(StoreError::Io(format!(
                "unsupported kind for keyed store: {other:?}"
            ))),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn blob_object_impl() {
        let data = b"hello world".to_vec();
        let blob = Blob::from_data(data.clone());
        assert_eq!(Blob::KIND, ObjectKind::Blob);
        assert_eq!(blob.data(), b"hello world");
        assert_eq!(blob.into_data(), data);
    }

    #[test]
    fn tree_object_impl() {
        let data = vec![1, 2, 3];
        let tree = Tree::from_data(data.clone());
        assert_eq!(Tree::KIND, ObjectKind::Tree);
        assert_eq!(tree.data(), &[1, 2, 3]);
        assert_eq!(tree.into_data(), data);
    }

    #[test]
    fn commit_object_impl() {
        let data = b"commit data".to_vec();
        let commit = Commit::from_data(data.clone());
        assert_eq!(Commit::KIND, ObjectKind::Commit);
        assert_eq!(commit.data(), b"commit data");
        assert_eq!(commit.into_data(), data);
    }

    #[test]
    fn tag_object_impl() {
        let data = b"tag data".to_vec();
        let tag = Tag::from_data(data.clone());
        assert_eq!(Tag::KIND, ObjectKind::Tag);
        assert_eq!(tag.data(), b"tag data");
        assert_eq!(tag.into_data(), data);
    }

    #[test]
    fn any_object_construction() {
        let obj = AnyObject {
            kind: ObjectKind::Tree,
            data: vec![10, 20, 30],
        };
        assert_eq!(obj.kind, ObjectKind::Tree);
        assert_eq!(obj.data, vec![10, 20, 30]);
    }

    // -- KeyedObjectStore tests --

    #[cfg(feature = "memory")]
    mod keyed {
        use super::*;
        use crate::SharedMemoryStore;

        fn keyed_store() -> KeyedObjectStore<SharedMemoryStore> {
            KeyedObjectStore::new(SharedMemoryStore::new())
        }

        #[test]
        fn blob_round_trip() {
            let os = keyed_store();
            let blob = Blob(b"hello".to_vec());
            let key = ObjectStore::<_, Blob>::insert(&os, &blob).unwrap();
            let got: Blob = ObjectStore::get(&os, &key).unwrap().unwrap();
            assert_eq!(got.0, b"hello");
        }

        #[test]
        fn tree_round_trip() {
            let os = keyed_store();
            let tree = Tree(b"tree bytes".to_vec());
            let key = ObjectStore::<_, Tree>::insert(&os, &tree).unwrap();
            let got: Tree = ObjectStore::get(&os, &key).unwrap().unwrap();
            assert_eq!(got.0, b"tree bytes");
        }

        #[test]
        fn blob_and_tree_different_keys() {
            let os = keyed_store();
            let data = b"same data";
            let blob_key = ObjectStore::insert(&os, &Blob(data.to_vec())).unwrap();
            let tree_key = ObjectStore::insert(&os, &Tree(data.to_vec())).unwrap();
            // Blob uses O256::blob(data), tree uses O256::blob("tree").tag(data)
            assert_ne!(blob_key, tree_key);
        }

        #[test]
        fn blob_key_as_tree_returns_mismatch() {
            let os = keyed_store();
            let blob = Blob(b"data".to_vec());
            let key = ObjectStore::<_, Blob>::insert(&os, &blob).unwrap();

            let result: Result<Option<Tree>, _> = ObjectStore::get(&os, &key);
            match result {
                Err(StoreError::KindMismatch { expected, got }) => {
                    assert_eq!(expected, ObjectKind::Tree);
                    assert_eq!(got, ObjectKind::Blob);
                }
                other => panic!("expected KindMismatch, got {other:?}"),
            }
        }

        #[test]
        fn tree_key_as_blob_returns_mismatch() {
            let os = keyed_store();
            let tree = Tree(b"data".to_vec());
            let key = ObjectStore::<_, Tree>::insert(&os, &tree).unwrap();

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
        fn get_missing_returns_none() {
            let os = keyed_store();
            let missing = O256::blob(b"not stored");

            let blob_result: Result<Option<Blob>, _> = ObjectStore::get(&os, &missing);
            assert!(matches!(blob_result, Ok(None)));

            let tree_result: Result<Option<Tree>, _> = ObjectStore::get(&os, &missing);
            assert!(matches!(tree_result, Ok(None)));
        }

        #[test]
        fn contains_sees_both_types() {
            let os = keyed_store();
            let blob = Blob(b"b".to_vec());
            let tree = Tree(b"t".to_vec());
            let blob_key = ObjectStore::<_, Blob>::insert(&os, &blob).unwrap();
            let tree_key = ObjectStore::<_, Tree>::insert(&os, &tree).unwrap();

            assert!(ObjectStore::<_, Blob>::contains(&os, &blob_key));
            assert!(ObjectStore::<_, Blob>::contains(&os, &tree_key));
            assert!(ObjectStore::<_, Tree>::contains(&os, &blob_key));
            assert!(ObjectStore::<_, Tree>::contains(&os, &tree_key));
        }

        #[test]
        fn get_any_blob() {
            let os = keyed_store();
            let blob = Blob(b"hello".to_vec());
            let key = ObjectStore::<_, Blob>::insert(&os, &blob).unwrap();

            let any = os.get_any(&key).unwrap().unwrap();
            assert_eq!(any.kind, ObjectKind::Blob);
            assert_eq!(any.data, b"hello");
        }

        #[test]
        fn get_any_tree() {
            let os = keyed_store();
            let tree = Tree(b"tree data".to_vec());
            let key = ObjectStore::<_, Tree>::insert(&os, &tree).unwrap();

            let any = os.get_any(&key).unwrap().unwrap();
            assert_eq!(any.kind, ObjectKind::Tree);
            assert_eq!(any.data, b"tree data");
        }

        #[test]
        fn get_any_missing() {
            let os = keyed_store();
            let missing = O256::blob(b"nope");
            assert!(matches!(os.get_any(&missing), Ok(None)));
        }

        #[test]
        fn insert_any_blob() {
            let os = keyed_store();
            let any = AnyObject {
                kind: ObjectKind::Blob,
                data: b"any blob".to_vec(),
            };
            let key = os.insert_any(&any).unwrap();
            let blob: Blob = ObjectStore::get(&os, &key).unwrap().unwrap();
            assert_eq!(blob.0, b"any blob");
        }

        #[test]
        fn insert_any_tree() {
            let os = keyed_store();
            let any = AnyObject {
                kind: ObjectKind::Tree,
                data: b"any tree".to_vec(),
            };
            let key = os.insert_any(&any).unwrap();
            let tree: Tree = ObjectStore::get(&os, &key).unwrap().unwrap();
            assert_eq!(tree.0, b"any tree");
        }

        #[test]
        fn insert_any_unsupported_kind() {
            let os = keyed_store();
            let any = AnyObject {
                kind: ObjectKind::Commit,
                data: b"commit".to_vec(),
            };
            assert!(os.insert_any(&any).is_err());
        }

        #[test]
        fn put_blob_matching_hash() {
            let os = keyed_store();
            let blob = Blob(b"put test".to_vec());
            let key = ObjectStore::<_, Blob>::insert(&os, &blob).unwrap();
            ObjectStore::put(&os, key, &blob).unwrap();
        }

        #[test]
        fn put_tree_matching_hash() {
            let os = keyed_store();
            let tree = Tree(b"put tree".to_vec());
            let key = ObjectStore::<_, Tree>::insert(&os, &tree).unwrap();
            ObjectStore::put(&os, key, &tree).unwrap();
        }

        #[test]
        fn put_tree_wrong_hash() {
            let os = keyed_store();
            let tree = Tree(b"data".to_vec());
            let wrong = O256::blob(b"wrong");
            assert!(ObjectStore::put(&os, wrong, &tree).is_err());
        }

        #[test]
        fn over_tagged_blobstore() {
            let tagged = crate::TaggedBlobStore::new(SharedMemoryStore::new());
            let os = KeyedObjectStore::new(tagged);

            let blob = Blob(b"blob".to_vec());
            let blob_key = ObjectStore::<_, Blob>::insert(&os, &blob).unwrap();
            let got: Blob = ObjectStore::get(&os, &blob_key).unwrap().unwrap();
            assert_eq!(got.0, b"blob");

            let tree = Tree(b"tree".to_vec());
            let tree_key = ObjectStore::<_, Tree>::insert(&os, &tree).unwrap();
            let got: Tree = ObjectStore::get(&os, &tree_key).unwrap().unwrap();
            assert_eq!(got.0, b"tree");
        }
    }
}
