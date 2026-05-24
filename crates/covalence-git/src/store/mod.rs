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

pub use backend::{GitBackend, GitObject, GitObjectKind};
pub use loose::LooseBackend;

use covalence_hash::gix_hash;
use covalence_store::{ContentStore, StoreError};

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

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    #[test]
    fn content_store_round_trip() {
        let dir = std::env::temp_dir().join(format!("cov_gitstore_{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).unwrap();

        let backend = LooseBackend::new(&dir, gix_hash::Kind::Sha1);
        let store = GitObjectStore::new(backend);

        let data = b"content store test";
        let id = store.insert(data).unwrap();
        assert!(store.contains(&id));
        assert_eq!(store.get(&id).unwrap(), data);

        // put with matching hash succeeds
        let data2 = b"another blob";
        let expected = covalence_hash::git::blob_sha1("another blob");
        store.put(expected, data2).unwrap();
        assert_eq!(store.get(&expected).unwrap(), data2);

        // put with wrong hash fails
        let wrong_key = covalence_hash::git::blob_sha1("wrong");
        assert!(store.put(wrong_key, b"right").is_err());

        let _ = fs::remove_dir_all(&dir);
    }
}
