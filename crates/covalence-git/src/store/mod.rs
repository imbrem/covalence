//! Git object store — content-addressed storage backed by a `.git/objects` directory.
//!
//! This module provides:
//!
//! - [`GitBackend`]: trait abstracting the git object database (loose files,
//!   pack files, CLI, etc.).
//! - [`LooseBackend`]: implementation that reads and writes loose objects.
//! - [`GitObjectStore`]: adapter wrapping any `GitBackend` as a
//!   [`ContentStore<ObjectId>`](covalence_store::ContentStore).
//!
//! Through the [`ContentStore`] interface, `insert` and `put` operate on
//! **blob** objects.  Use the [`GitBackend`] trait directly for type-aware
//! operations on trees, commits, and tags.

mod backend;
mod loose;
#[cfg(feature = "odb")]
mod odb;

pub use backend::{GitBackend, GitObject, GitObjectKind};
pub use loose::LooseBackend;
#[cfg(feature = "odb")]
pub use odb::OdbBackend;

use covalence_hash::gix_hash;
use covalence_store::{AnyObject, ContentStore, Object, ObjectKind, ObjectStore, StoreError};

/// Adapter exposing any [`GitBackend`] as a [`ContentStore`] keyed by
/// [`ObjectId`](gix_hash::ObjectId).
///
/// All objects written through the `ContentStore` interface are stored as
/// blobs.  Reading (`get`) works for any object type and returns the raw
/// object data (without the git header).
pub struct GitObjectStore<B> {
    backend: B,
}

impl<B> GitObjectStore<B> {
    /// Wrap a [`GitBackend`] in a `ContentStore` adapter.
    pub fn new(backend: B) -> Self {
        Self { backend }
    }

    /// Borrow the inner backend.
    pub fn backend(&self) -> &B {
        &self.backend
    }

    /// Unwrap, returning the inner backend.
    pub fn into_inner(self) -> B {
        self.backend
    }
}

impl<B: GitBackend> ContentStore<gix_hash::ObjectId> for GitObjectStore<B> {
    fn get(&self, key: &gix_hash::ObjectId) -> Option<Vec<u8>> {
        self.backend.read_object(key).ok().map(|obj| obj.data)
    }

    fn put(&self, key: gix_hash::ObjectId, data: &[u8]) -> Result<(), StoreError> {
        let computed = self.backend.write_object(GitObjectKind::Blob, data)?;
        if computed != key {
            return Err(StoreError::Io(format!(
                "hash mismatch: expected {key}, computed {computed}",
            )));
        }
        Ok(())
    }

    fn insert(&self, data: &[u8]) -> Result<gix_hash::ObjectId, StoreError> {
        self.backend.write_object(GitObjectKind::Blob, data)
    }

    fn contains(&self, key: &gix_hash::ObjectId) -> bool {
        self.backend.contains_object(key)
    }
}

impl<B: GitBackend, T: Object> ObjectStore<gix_hash::ObjectId, T> for GitObjectStore<B> {
    fn get(&self, key: &gix_hash::ObjectId) -> Result<Option<T>, StoreError> {
        match self.backend.read_object(key) {
            Ok(obj) => {
                let kind: ObjectKind = obj.kind.into();
                if kind != T::KIND {
                    return Err(StoreError::KindMismatch {
                        expected: T::KIND,
                        got: kind,
                    });
                }
                Ok(Some(T::from_data(obj.data)))
            }
            Err(_) => Ok(None),
        }
    }

    fn insert(&self, obj: &T) -> Result<gix_hash::ObjectId, StoreError> {
        let git_kind: GitObjectKind = T::KIND.into();
        self.backend.write_object(git_kind, obj.data())
    }

    fn put(&self, key: gix_hash::ObjectId, obj: &T) -> Result<(), StoreError> {
        let git_kind: GitObjectKind = T::KIND.into();
        let computed = self.backend.write_object(git_kind, obj.data())?;
        if computed != key {
            return Err(StoreError::Io(format!(
                "hash mismatch: expected {key}, computed {computed}",
            )));
        }
        Ok(())
    }

    fn contains(&self, key: &gix_hash::ObjectId) -> bool {
        self.backend.contains_object(key)
    }
}

impl<B: GitBackend> GitObjectStore<B> {
    /// Retrieve an object without static type checking.
    pub fn get_any(&self, key: &gix_hash::ObjectId) -> Result<Option<AnyObject>, StoreError> {
        match self.backend.read_object(key) {
            Ok(obj) => Ok(Some(AnyObject {
                kind: obj.kind.into(),
                data: obj.data,
            })),
            Err(_) => Ok(None),
        }
    }

    /// Store a dynamically-typed object.
    pub fn insert_any(&self, obj: &AnyObject) -> Result<gix_hash::ObjectId, StoreError> {
        let git_kind: GitObjectKind = obj.kind.into();
        self.backend.write_object(git_kind, &obj.data)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_store::{Blob, Tree};
    use std::fs;

    fn temp_store() -> (GitObjectStore<LooseBackend>, std::path::PathBuf) {
        let dir = std::env::temp_dir().join(format!(
            "cov_gitstore_{}_{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).unwrap();
        let backend = LooseBackend::new(&dir, gix_hash::Kind::Sha1);
        (GitObjectStore::new(backend), dir)
    }

    #[test]
    fn content_store_round_trip() {
        let (store, dir) = temp_store();

        let data = b"content store test";
        let id = ContentStore::insert(&store, data.as_slice()).unwrap();
        assert!(ContentStore::contains(&store, &id));
        assert_eq!(ContentStore::get(&store, &id).unwrap(), data);

        // put with matching hash succeeds
        let data2 = b"another blob";
        let expected = covalence_hash::git::blob_sha1("another blob");
        ContentStore::put(&store, expected, data2).unwrap();
        assert_eq!(ContentStore::get(&store, &expected).unwrap(), data2);

        // put with wrong hash fails
        let wrong_key = covalence_hash::git::blob_sha1("wrong");
        assert!(ContentStore::put(&store, wrong_key, b"right").is_err());

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn object_store_blob_round_trip() {
        let (store, dir) = temp_store();

        let blob = Blob(b"typed blob test".to_vec());
        let id = ObjectStore::insert(&store, &blob).unwrap();
        assert!(ObjectStore::<_, Blob>::contains(&store, &id));

        let got: Blob = ObjectStore::get(&store, &id).unwrap().unwrap();
        assert_eq!(got.0, b"typed blob test");

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn object_store_kind_mismatch() {
        let (store, dir) = temp_store();

        // Write a tree
        let tree = Tree(b"fake tree data".to_vec());
        let id = ObjectStore::insert(&store, &tree).unwrap();

        // Try reading as a Blob → KindMismatch
        let result: Result<Option<Blob>, StoreError> = ObjectStore::get(&store, &id);
        match result {
            Err(StoreError::KindMismatch { expected, got }) => {
                assert_eq!(expected, ObjectKind::Blob);
                assert_eq!(got, ObjectKind::Tree);
            }
            other => panic!("expected KindMismatch, got {other:?}"),
        }

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn object_store_get_any() {
        let (store, dir) = temp_store();

        let tree = Tree(b"tree bytes".to_vec());
        let id = ObjectStore::insert(&store, &tree).unwrap();

        let any = store.get_any(&id).unwrap().unwrap();
        assert_eq!(any.kind, ObjectKind::Tree);
        assert_eq!(any.data, b"tree bytes");

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn object_store_insert_any_and_read_typed() {
        let (store, dir) = temp_store();

        let any = AnyObject {
            kind: ObjectKind::Blob,
            data: b"any blob".to_vec(),
        };
        let id = store.insert_any(&any).unwrap();

        let blob: Blob = ObjectStore::get(&store, &id).unwrap().unwrap();
        assert_eq!(blob.0, b"any blob");

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn object_store_contains_after_insert() {
        let (store, dir) = temp_store();

        let blob = Blob(b"exists".to_vec());
        let id = ObjectStore::insert(&store, &blob).unwrap();
        assert!(ObjectStore::<_, Blob>::contains(&store, &id));

        // Non-existent key
        let fake =
            gix_hash::ObjectId::from_hex(b"0000000000000000000000000000000000000000").unwrap();
        assert!(!ObjectStore::<_, Blob>::contains(&store, &fake));

        let _ = fs::remove_dir_all(&dir);
    }
}
