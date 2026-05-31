use std::collections::HashSet;
use std::sync::{Arc, RwLock};

use covalence_hash::O256;
use covalence_store::{BlobStore, ContentStore, SharedMemoryStore};

use crate::{AsyncBackend, BackendInfo, KernelError, SyncBackend};

/// The execution kernel: a content-addressed store with tree-hash tracking.
///
/// In the new design the "kernel" is just a thin wrapper around a blob store.
/// Proposition deciding, observation tracking, and concept management land in
/// the new HOL kernel and the covalence-shell crate during phase 1+.
pub struct Kernel<S = BlobStore<O256>> {
    store: S,
    /// Hashes stored as trees (domain-separated from blobs).
    tree_hashes: Arc<RwLock<HashSet<O256>>>,
}

impl<S: Clone> Clone for Kernel<S> {
    fn clone(&self) -> Self {
        Self {
            store: self.store.clone(),
            tree_hashes: Arc::clone(&self.tree_hashes),
        }
    }
}

impl Kernel {
    /// Create a new kernel with a fresh in-memory store.
    pub fn new() -> Self {
        Self::with_store(BlobStore::new(SharedMemoryStore::new()))
    }

    /// Create a new kernel with the given store.
    pub fn with_store(store: BlobStore<O256>) -> Self {
        Self {
            store,
            tree_hashes: Arc::new(RwLock::new(HashSet::new())),
        }
    }
}

impl Default for Kernel {
    fn default() -> Self {
        Self::new()
    }
}

impl<S> Kernel<S> {
    /// Create a kernel with an explicit store.
    pub fn with_components(store: S) -> Self {
        Self {
            store,
            tree_hashes: Arc::new(RwLock::new(HashSet::new())),
        }
    }

    /// Direct access to the underlying store.
    pub fn store(&self) -> &S {
        &self.store
    }

    /// Register a hash as a known tree.
    ///
    /// Use this to pre-populate the tree set (e.g. from persisted `cov_trees`
    /// metadata after reopening a store that was used with `cov cog clone`).
    pub fn register_tree(&self, hash: O256) {
        self.tree_hashes.write().unwrap().insert(hash);
    }
}

impl<S> SyncBackend for Kernel<S>
where
    S: ContentStore<O256> + Clone + Send + Sync + 'static,
{
    fn info(&self) -> BackendInfo {
        let count = self.store.len().unwrap_or(0);
        BackendInfo {
            kind: "local".to_string(),
            target: format!("{count} blobs"),
        }
    }

    fn store_blob(&self, data: &[u8]) -> Result<O256, KernelError> {
        self.store
            .insert(data)
            .map_err(|e| KernelError::Store(e.to_string()))
    }

    fn get_blob(&self, hash: &O256) -> Result<Option<Vec<u8>>, KernelError> {
        Ok(self.store.get(hash))
    }

    fn has_blob(&self, hash: &O256) -> Result<bool, KernelError> {
        Ok(self.store.contains(hash))
    }

    fn blob_count(&self) -> Result<Option<usize>, KernelError> {
        Ok(self.store.len())
    }

    fn store_tree(&self, data: &[u8]) -> Result<O256, KernelError> {
        let table = covalence_object::Table::parse(data.to_vec(), covalence_object::Dir)
            .map_err(|e| KernelError::Store(format!("invalid tree: {e}")))?;
        let tree_hash = table.dir_hash();
        self.store
            .put(tree_hash, data)
            .map_err(|e| KernelError::Store(e.to_string()))?;
        self.tree_hashes.write().unwrap().insert(tree_hash);
        Ok(tree_hash)
    }

    fn is_tree(&self, hash: &O256) -> Result<bool, KernelError> {
        Ok(self.tree_hashes.read().unwrap().contains(hash))
    }
}

impl<S> AsyncBackend for Kernel<S>
where
    S: ContentStore<O256> + Clone + Send + Sync + 'static,
{
    fn info(&self) -> BackendInfo {
        SyncBackend::info(self)
    }

    async fn store_blob(&self, data: &[u8]) -> Result<O256, KernelError> {
        SyncBackend::store_blob(self, data)
    }

    async fn get_blob(&self, hash: &O256) -> Result<Option<Vec<u8>>, KernelError> {
        SyncBackend::get_blob(self, hash)
    }

    async fn has_blob(&self, hash: &O256) -> Result<bool, KernelError> {
        SyncBackend::has_blob(self, hash)
    }

    async fn blob_count(&self) -> Result<Option<usize>, KernelError> {
        SyncBackend::blob_count(self)
    }

    async fn store_tree(&self, data: &[u8]) -> Result<O256, KernelError> {
        SyncBackend::store_tree(self, data)
    }

    async fn is_tree(&self, hash: &O256) -> Result<bool, KernelError> {
        SyncBackend::is_tree(self, hash)
    }
}
