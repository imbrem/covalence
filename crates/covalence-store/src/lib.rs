use std::sync::Arc;

pub use covalence_hash::O256;

/// Errors from store operations.
#[derive(Debug, thiserror::Error)]
pub enum StoreError {
    #[error("store I/O error: {0}")]
    Io(String),
}

/// Content-addressed store trait.
///
/// Self-contained interface for content-addressed storage. Designed to be
/// object-safe for use behind `Arc<dyn ContentStore<K>>`.
pub trait ContentStore<K>: Send + Sync {
    /// Retrieve data by key.
    fn get(&self, key: &K) -> Option<Vec<u8>>;

    /// Store data under the given key.
    fn put(&self, key: K, data: &[u8]) -> Result<(), StoreError>;

    /// Hash and store data, returning the content key.
    fn insert(&self, data: &[u8]) -> Result<K, StoreError>;

    /// Check whether a key exists. Default checks via `get`.
    fn contains(&self, key: &K) -> bool {
        self.get(key).is_some()
    }

    /// Number of entries in the store, if cheaply available.
    fn len(&self) -> Option<usize> {
        None
    }
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
}

#[cfg(feature = "memory")]
mod memory;
#[cfg(feature = "memory")]
pub use memory::{MemoryStore, SharedMemoryStore};

#[cfg(feature = "sqlite")]
mod sqlite;
#[cfg(feature = "sqlite")]
pub use sqlite::SqliteStore;
