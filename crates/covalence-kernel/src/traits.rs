use std::fmt;
use std::str::FromStr;

use covalence_hash::O256;

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

/// Result of deciding a proposition.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Decision {
    /// The proposition called `attest()` during startup — decidably true.
    True,
    /// The proposition imports `attest()` but did not call it during startup.
    Unknown,
    /// The proposition does not import `attest()` at all — statically false.
    False,
}

impl fmt::Display for Decision {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Decision::True => write!(f, "true"),
            Decision::Unknown => write!(f, "unknown"),
            Decision::False => write!(f, "false"),
        }
    }
}

impl FromStr for Decision {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "true" => Ok(Decision::True),
            "unknown" => Ok(Decision::Unknown),
            "false" => Ok(Decision::False),
            _ => Err(format!("invalid decision: {s:?}")),
        }
    }
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
    fn decide(&self, hash: &O256) -> Result<Decision, KernelError>;
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
    async fn decide(&self, hash: &O256) -> Result<Decision, KernelError>;
}
