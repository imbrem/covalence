use std::collections::HashSet;
use std::sync::{Arc, RwLock};

use covalence_hash::O256;
use covalence_store::{BlobStore, ContentStore, SharedMemoryStore};

use crate::{
    AsyncBackend, BackendInfo, DecideOutput, Decision, KernelError, SyncBackend, WasmEngine,
};

/// The execution kernel: owns a content-addressed store and a WASM engine.
/// Clone is cheap (Arc internals).
#[derive(Clone)]
pub struct Kernel {
    store: BlobStore<O256>,
    engine: Arc<WasmEngine>,
    /// Hashes previously decided as Sat.
    sat_set: Arc<RwLock<HashSet<O256>>>,
    /// Hashes previously decided as Unsat.
    unsat_set: Arc<RwLock<HashSet<O256>>>,
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
            engine: Arc::new(engine),
            sat_set: Arc::new(RwLock::new(HashSet::new())),
            unsat_set: Arc::new(RwLock::new(HashSet::new())),
        })
    }

    /// Direct access to the underlying store.
    pub fn store(&self) -> &BlobStore<O256> {
        &self.store
    }

    /// Direct access to the underlying engine.
    pub fn engine(&self) -> &Arc<WasmEngine> {
        &self.engine
    }
}

impl SyncBackend for Kernel {
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
        let output = self
            .engine
            .decide(&data, &self.store)
            .map_err(|e| KernelError::Engine(format!("{e}")))?;

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

impl AsyncBackend for Kernel {
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

    async fn decide(&self, hash: &O256) -> Result<DecideOutput, KernelError> {
        SyncBackend::decide(self, hash)
    }
}
