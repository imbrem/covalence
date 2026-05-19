#[derive(Debug, thiserror::Error)]
pub enum DiscoveryError {
    #[error("I/O error: {0}")]
    Io(String),
    #[error("no server found")]
    NoServerFound,
}
