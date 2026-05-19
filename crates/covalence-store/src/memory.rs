use std::collections::HashMap;
use std::sync::RwLock;

use covalence_hash::{IdentityBuildHasher, O256};

use crate::ContentStore;

// ---------------------------------------------------------------------------
// MemoryStore — single-threaded, &mut self, no locking overhead
// ---------------------------------------------------------------------------

/// In-memory content-addressed blob store backed by a [`HashMap`].
///
/// Uses an identity hasher since [`O256`] keys are already BLAKE3 hashes —
/// their first 8 bytes are used directly as the bucket hash.
///
/// For concurrent use, wrap in [`SharedMemoryStore`].
#[derive(Debug, Clone)]
pub struct MemoryStore {
    blobs: HashMap<O256, Vec<u8>, IdentityBuildHasher>,
}

impl MemoryStore {
    pub fn new() -> Self {
        Self {
            blobs: HashMap::with_hasher(IdentityBuildHasher::default()),
        }
    }

    pub fn get(&self, key: &O256) -> Option<&[u8]> {
        self.blobs.get(key).map(|v| v.as_slice())
    }

    pub fn contains(&self, key: &O256) -> bool {
        self.blobs.contains_key(key)
    }

    pub fn insert(&mut self, data: &[u8]) -> O256 {
        let hash = O256::blob(data);
        self.blobs.entry(hash).or_insert_with(|| data.to_vec());
        hash
    }

    pub fn put(&mut self, key: O256, data: &[u8]) {
        self.blobs.entry(key).or_insert_with(|| data.to_vec());
    }

    pub fn len(&self) -> usize {
        self.blobs.len()
    }

    pub fn is_empty(&self) -> bool {
        self.blobs.is_empty()
    }
}

impl Default for MemoryStore {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// SharedMemoryStore — concurrent via RwLock (no internal Arc)
// ---------------------------------------------------------------------------

/// Thread-safe wrapper around [`MemoryStore`].
///
/// Adds a [`RwLock`] for interior mutability so it can implement [`ContentStore`].
/// Wrap in [`BlobStore`](crate::BlobStore) for cheap cloning via Arc.
pub struct SharedMemoryStore(RwLock<MemoryStore>);

impl SharedMemoryStore {
    pub fn new() -> Self {
        Self(RwLock::new(MemoryStore::new()))
    }
}

impl Default for SharedMemoryStore {
    fn default() -> Self {
        Self::new()
    }
}

impl ContentStore<O256> for SharedMemoryStore {
    fn get(&self, key: &O256) -> Option<Vec<u8>> {
        self.0.read().unwrap().get(key).map(|s| s.to_vec())
    }

    fn put(&self, key: O256, data: &[u8]) -> Result<(), crate::StoreError> {
        self.0.write().unwrap().put(key, data);
        Ok(())
    }

    fn insert(&self, data: &[u8]) -> Result<O256, crate::StoreError> {
        Ok(self.0.write().unwrap().insert(data))
    }

    fn contains(&self, key: &O256) -> bool {
        self.0.read().unwrap().contains(key)
    }

    fn len(&self) -> Option<usize> {
        Some(self.0.read().unwrap().len())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::BlobStore;

    #[test]
    fn memory_store_basics() {
        let mut store = MemoryStore::new();
        let hash = store.insert(b"hello");
        assert_eq!(store.get(&hash), Some(b"hello".as_slice()));
        assert!(store.contains(&hash));
        assert_eq!(store.len(), 1);
    }

    #[test]
    fn content_addressed() {
        let mut store = MemoryStore::new();
        let h1 = store.insert(b"data");
        let h2 = store.insert(b"data");
        assert_eq!(h1, h2);
        assert_eq!(store.len(), 1);
    }

    #[test]
    fn shared_store() {
        let store = SharedMemoryStore::new();
        let hash = store.insert(b"hello").unwrap();
        assert_eq!(ContentStore::get(&store, &hash), Some(b"hello".to_vec()));
        assert!(store.contains(&hash));
        assert_eq!(store.len(), Some(1));
    }

    #[test]
    fn blobstore_clone_shares() {
        let store = BlobStore::new(SharedMemoryStore::new());
        let hash = store.insert(b"shared").unwrap();
        let clone = store.clone();
        assert_eq!(clone.get(&hash), Some(b"shared".to_vec()));
    }
}
