use serde::{Deserialize, Serialize};

/// Service descriptor written to the XDG registry directory.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ServiceDescriptor {
    /// Unique instance ID.
    pub id: String,
    /// Process ID of the server.
    pub pid: u32,
    /// Server version string.
    pub version: String,
    /// ISO 8601 timestamp of when the server started.
    pub started_at: String,
    /// Path to Unix domain socket serving HTTP (None if TCP-only).
    pub socket: Option<String>,
    /// HTTP base URL (None if socket-only).
    pub url: Option<String>,
    /// Capabilities this server supports.
    pub capabilities: Vec<String>,
    /// Working directory of the server process.
    pub cwd: String,
}
