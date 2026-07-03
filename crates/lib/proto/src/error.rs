#[derive(Debug, thiserror::Error)]
pub enum DiscoveryError {
    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),
    #[error("serialization error: {0}")]
    Serde(#[from] serde_json::Error),
    #[error("no server found")]
    NoServerFound,
}
