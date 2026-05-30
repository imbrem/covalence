use std::collections::HashSet;
use std::sync::{Arc, RwLock};

use covalence_hash::O256;
use covalence_store::{BlobStore, ContentStore, SharedMemoryStore};

use crate::{
    AsyncBackend, BackendInfo, DecideOutput, Decision, Evaluator, KernelError, SyncBackend,
    WasmEngine,
};

/// The execution kernel: owns a content-addressed store and a proposition evaluator.
/// Clone is cheap (Arc internals for caches, evaluator should be cheap to clone).
pub struct Kernel<S = BlobStore<O256>, E = WasmEngine> {
    store: S,
    evaluator: E,
    /// Hashes previously decided as Sat.
    sat_set: Arc<RwLock<HashSet<O256>>>,
    /// Hashes previously decided as Unsat.
    unsat_set: Arc<RwLock<HashSet<O256>>>,
    /// Hashes stored as trees (domain-separated from blobs).
    tree_hashes: Arc<RwLock<HashSet<O256>>>,
}

impl<S: Clone, E: Clone> Clone for Kernel<S, E> {
    fn clone(&self) -> Self {
        Self {
            store: self.store.clone(),
            evaluator: self.evaluator.clone(),
            sat_set: Arc::clone(&self.sat_set),
            unsat_set: Arc::clone(&self.unsat_set),
            tree_hashes: Arc::clone(&self.tree_hashes),
        }
    }
}

impl Kernel {
    /// Create a new kernel with a fresh in-memory store and engine.
    pub fn new() -> Result<Self, KernelError> {
        Self::with_store(BlobStore::new(SharedMemoryStore::new()))
    }

    /// Create a new kernel with the given store.
    pub fn with_store(store: BlobStore<O256>) -> Result<Self, KernelError> {
        let engine =
            WasmEngine::new().map_err(|e| KernelError::Engine(format!("create engine: {e}")))?;
        Ok(Self {
            store,
            evaluator: engine,
            sat_set: Arc::new(RwLock::new(HashSet::new())),
            unsat_set: Arc::new(RwLock::new(HashSet::new())),
            tree_hashes: Arc::new(RwLock::new(HashSet::new())),
        })
    }
}

impl<S, E> Kernel<S, E> {
    /// Create a kernel with explicit store and evaluator.
    pub fn with_components(store: S, evaluator: E) -> Self {
        Self {
            store,
            evaluator,
            sat_set: Arc::new(RwLock::new(HashSet::new())),
            unsat_set: Arc::new(RwLock::new(HashSet::new())),
            tree_hashes: Arc::new(RwLock::new(HashSet::new())),
        }
    }

    /// Direct access to the underlying store.
    pub fn store(&self) -> &S {
        &self.store
    }

    /// Direct access to the underlying evaluator.
    pub fn evaluator(&self) -> &E {
        &self.evaluator
    }

    /// Register a hash as a known tree.
    ///
    /// Use this to pre-populate the tree set (e.g. from persisted `cov_trees`
    /// metadata after reopening a store that was used with `cov cog clone`).
    pub fn register_tree(&self, hash: O256) {
        self.tree_hashes.write().unwrap().insert(hash);
    }
}

impl<S, E> Kernel<S, E>
where
    S: ContentStore<O256> + Clone + Send + Sync + 'static,
    E: Evaluator<S> + 'static,
{
    /// Prove a container: decide it and, if Sat, add the container's own hash
    /// to the proved set (as if it were a prove-dep of itself).
    pub fn prove_container(&self, hash: &O256) -> Result<DecideOutput, KernelError> {
        let mut output = SyncBackend::decide(self, hash)?;
        if output.decision == Decision::Sat && !output.proved.contains(hash) {
            output.proved.push(*hash);
        }
        Ok(output)
    }
}

impl<S, E> SyncBackend for Kernel<S, E>
where
    S: ContentStore<O256> + Clone + Send + Sync + 'static,
    E: Evaluator<S> + 'static,
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

    fn decide(&self, hash: &O256) -> Result<DecideOutput, KernelError> {
        // Check cache
        if self.sat_set.read().unwrap().contains(hash) {
            return Ok(DecideOutput {
                decision: Decision::Sat,
                proved: vec![],
            });
        }
        if self.unsat_set.read().unwrap().contains(hash) {
            return Ok(DecideOutput {
                decision: Decision::Unsat,
                proved: vec![],
            });
        }

        let data = self
            .store
            .get(hash)
            .ok_or_else(|| KernelError::NotFound(format!("blob not found: {hash}")))?;
        let output = self.evaluator.decide(&data, &self.store)?;

        // Cache all proved hashes + the queried hash
        {
            let mut sat_set = self.sat_set.write().unwrap();
            for proved_hash in &output.proved {
                sat_set.insert(*proved_hash);
            }
            if output.decision == Decision::Sat {
                sat_set.insert(*hash);
            }
        }
        if output.decision == Decision::Unsat {
            self.unsat_set.write().unwrap().insert(*hash);
        }

        Ok(output)
    }
}

impl<S, E> AsyncBackend for Kernel<S, E>
where
    S: ContentStore<O256> + Clone + Send + Sync + 'static,
    E: Evaluator<S> + 'static,
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

    async fn decide(&self, hash: &O256) -> Result<DecideOutput, KernelError> {
        SyncBackend::decide(self, hash)
    }
}
