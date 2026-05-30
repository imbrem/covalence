use covalence_hash::O256;

pub use covalence_types::{Decision, ParseDecisionError};

/// Errors from kernel operations.
#[derive(Debug, thiserror::Error)]
pub enum KernelError {
    #[error("engine error: {0}")]
    Engine(String),
    #[error("store error: {0}")]
    Store(String),
    #[error("not found: {0}")]
    NotFound(String),
}

/// Output from deciding a proposition, including transitively proved hashes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DecideOutput {
    /// The decision for the queried hash.
    pub decision: Decision,
    /// Hashes proved Sat during this decide (on the prove stack when attest was called).
    pub proved: Vec<O256>,
}

/// Evaluates propositions and produces decisions.
pub trait Evaluator<S>: Send + Sync {
    fn decide(&self, bytes: &[u8], store: &S) -> Result<DecideOutput, KernelError>;
}

/// Information about a backend.
pub struct BackendInfo {
    /// "local" or "http"
    pub kind: String,
    /// Human-readable connection target (e.g. "in-memory" or URL)
    pub target: String,
}

/// Synchronous backend trait — dyn-compatible for use with `Box<dyn SyncBackend>`.
pub trait SyncBackend: Send {
    fn info(&self) -> BackendInfo;
    fn store_blob(&self, data: &[u8]) -> Result<O256, KernelError>;
    fn get_blob(&self, hash: &O256) -> Result<Option<Vec<u8>>, KernelError>;
    fn has_blob(&self, hash: &O256) -> Result<bool, KernelError>;
    fn blob_count(&self) -> Result<Option<usize>, KernelError>;
    fn decide(&self, hash: &O256) -> Result<DecideOutput, KernelError>;

    /// Store tree data, returning a tree-tagged hash.
    fn store_tree(&self, data: &[u8]) -> Result<O256, KernelError> {
        self.store_blob(data)
    }

    /// Check whether a hash refers to a tree.
    fn is_tree(&self, hash: &O256) -> Result<bool, KernelError> {
        let _ = hash;
        Ok(false)
    }
}

/// Asynchronous backend trait — NOT dyn-compatible (uses native async fn).
/// Used with concrete types in the server.
#[allow(async_fn_in_trait)]
pub trait AsyncBackend: Send + Sync {
    fn info(&self) -> BackendInfo;
    async fn store_blob(&self, data: &[u8]) -> Result<O256, KernelError>;
    async fn get_blob(&self, hash: &O256) -> Result<Option<Vec<u8>>, KernelError>;
    async fn has_blob(&self, hash: &O256) -> Result<bool, KernelError>;
    async fn blob_count(&self) -> Result<Option<usize>, KernelError>;
    async fn decide(&self, hash: &O256) -> Result<DecideOutput, KernelError>;

    /// Store tree data, returning a tree-tagged hash.
    async fn store_tree(&self, data: &[u8]) -> Result<O256, KernelError> {
        self.store_blob(data).await
    }

    /// Check whether a hash refers to a tree.
    async fn is_tree(&self, hash: &O256) -> Result<bool, KernelError> {
        let _ = hash;
        Ok(false)
    }
}
