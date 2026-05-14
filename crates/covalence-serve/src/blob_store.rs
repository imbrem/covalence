use std::collections::HashMap;

use covalence_object::O256;
use covalence_wasm::BlobLookup;

/// Entry in the blob store — either loaded data or just a known hash.
#[derive(Debug, Clone)]
enum BlobEntry {
    /// Full blob data in memory.
    Loaded(Vec<u8>),
    /// Hash is known but data is not available.
    /// Operations that need the data will fail.
    HashOnly,
}

/// In-memory BLAKE3 content-addressed blob store.
///
/// Supports lazy blobs (hash known but data not loaded) for the import
/// semantics described in MVP_DESIGN.md: unknown blob imports should
/// fail only when the blob data is actually accessed.
#[derive(Debug, Clone)]
pub struct BlobStore {
    blobs: HashMap<O256, BlobEntry>,
}

impl BlobStore {
    pub fn new() -> Self {
        BlobStore {
            blobs: HashMap::new(),
        }
    }

    /// Insert blob data, returning its BLAKE3 hash.
    pub fn insert(&mut self, data: Vec<u8>) -> O256 {
        let hash = O256::blob(&data);
        self.blobs.insert(hash, BlobEntry::Loaded(data));
        hash
    }

    /// Register a hash without data (for lazy/deferred loading).
    pub fn insert_hash_only(&mut self, hash: O256) {
        self.blobs.entry(hash).or_insert(BlobEntry::HashOnly);
    }

    /// Get blob data by hash. Returns `None` if the hash is unknown
    /// or if only the hash is known (HashOnly).
    pub fn get(&self, hash: &O256) -> Option<&[u8]> {
        match self.blobs.get(hash)? {
            BlobEntry::Loaded(data) => Some(data),
            BlobEntry::HashOnly => None,
        }
    }

    /// Check if a hash is registered (either Loaded or HashOnly).
    pub fn contains(&self, hash: &O256) -> bool {
        self.blobs.contains_key(hash)
    }

    /// List all hashes in the store.
    pub fn hashes(&self) -> Vec<O256> {
        self.blobs.keys().copied().collect()
    }

    /// Return the number of entries.
    pub fn len(&self) -> usize {
        self.blobs.len()
    }

    pub fn is_empty(&self) -> bool {
        self.blobs.is_empty()
    }
}

impl Default for BlobStore {
    fn default() -> Self {
        Self::new()
    }
}

impl BlobLookup for BlobStore {
    fn get_blob(&self, hash: &O256) -> Option<&[u8]> {
        self.get(hash)
    }

    fn contains_blob(&self, hash: &O256) -> bool {
        self.contains(hash)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn insert_and_retrieve() {
        let mut store = BlobStore::new();
        let hash = store.insert(b"hello world".to_vec());
        assert_eq!(store.get(&hash).unwrap(), b"hello world");
    }

    #[test]
    fn insert_returns_blake3_hash() {
        let mut store = BlobStore::new();
        let data = b"hello world";
        let hash = store.insert(data.to_vec());
        let expected = O256::blob(data);
        assert_eq!(hash, expected);
    }

    #[test]
    fn hash_only_contains_but_no_data() {
        let mut store = BlobStore::new();
        let hash = O256::blob(b"some data");
        store.insert_hash_only(hash);
        assert!(store.contains(&hash));
        assert!(store.get(&hash).is_none());
    }

    #[test]
    fn unknown_hash_not_contained() {
        let store = BlobStore::new();
        let hash = O256::blob(b"anything");
        assert!(!store.contains(&hash));
        assert!(store.get(&hash).is_none());
    }

    #[test]
    fn duplicate_insert_is_idempotent() {
        let mut store = BlobStore::new();
        let h1 = store.insert(b"data".to_vec());
        let h2 = store.insert(b"data".to_vec());
        assert_eq!(h1, h2);
        assert_eq!(store.len(), 1);
    }

    #[test]
    fn hash_only_not_overwritten_by_another_hash_only() {
        let mut store = BlobStore::new();
        let hash = O256::blob(b"test");
        store.insert(b"test".to_vec());
        // insert_hash_only should not overwrite existing Loaded entry
        store.insert_hash_only(hash);
        assert_eq!(store.get(&hash).unwrap(), b"test");
    }

    #[test]
    fn blob_equality_by_hash() {
        let h1 = O256::blob(b"same content");
        let h2 = O256::blob(b"same content");
        assert_eq!(h1, h2);

        let h3 = O256::blob(b"different content");
        assert_ne!(h1, h3);
    }

    #[test]
    fn list_hashes() {
        let mut store = BlobStore::new();
        let h1 = store.insert(b"alpha".to_vec());
        let h2 = store.insert(b"beta".to_vec());
        let hashes = store.hashes();
        assert_eq!(hashes.len(), 2);
        assert!(hashes.contains(&h1));
        assert!(hashes.contains(&h2));
    }
}
