pub mod descriptor;
#[cfg(unix)]
pub mod liveness;

use std::path::PathBuf;

pub use descriptor::ServiceDescriptor;

/// A live server registration.
pub struct Registration {
    pub id: String,
    pub descriptor_path: PathBuf,
    pub socket_path: PathBuf,
    pub descriptor: ServiceDescriptor,
}

#[cfg(unix)]
mod imp {
    use std::fs;
    use std::path::{Path, PathBuf};

    use super::{Registration, ServiceDescriptor};
    use crate::error::DiscoveryError;

    /// Get the runtime directory for covalence service discovery.
    /// Uses `$XDG_RUNTIME_DIR/covalence/` via the `dirs` crate.
    pub fn runtime_dir() -> PathBuf {
        dirs::runtime_dir()
            .unwrap_or_else(|| PathBuf::from("/tmp"))
            .join("covalence")
    }

    /// Get the registry directory path.
    pub fn registry_dir() -> PathBuf {
        runtime_dir().join("registry")
    }

    /// Get the sockets directory path.
    pub fn sockets_dir() -> PathBuf {
        runtime_dir().join("sockets")
    }

    /// Discover available servers, preferring those matching the given cwd.
    /// Returns descriptors sorted by preference (cwd match first, then newest).
    pub fn discover_servers(prefer_cwd: Option<&Path>) -> Vec<(PathBuf, ServiceDescriptor)> {
        let registry = registry_dir();
        let entries = match fs::read_dir(&registry) {
            Ok(e) => e,
            Err(_) => return Vec::new(),
        };

        let mut servers: Vec<(PathBuf, ServiceDescriptor)> = Vec::new();

        for entry in entries.flatten() {
            let path = entry.path();
            if path.extension().and_then(|e| e.to_str()) != Some("json") {
                continue;
            }
            let content = match fs::read_to_string(&path) {
                Ok(c) => c,
                Err(_) => continue,
            };
            let desc: ServiceDescriptor = match serde_json::from_str(&content) {
                Ok(d) => d,
                Err(_) => {
                    let _ = fs::remove_file(&path);
                    continue;
                }
            };

            if !super::liveness::pid_alive(desc.pid) {
                super::liveness::cleanup_stale(&path, &desc);
                continue;
            }

            servers.push((path, desc));
        }

        // Sort: cwd match first, then by started_at descending (newest first)
        servers.sort_by(|(_, a), (_, b)| {
            let a_match = prefer_cwd.is_some_and(|cwd| Path::new(&a.cwd) == cwd);
            let b_match = prefer_cwd.is_some_and(|cwd| Path::new(&b.cwd) == cwd);
            match (a_match, b_match) {
                (true, false) => std::cmp::Ordering::Less,
                (false, true) => std::cmp::Ordering::Greater,
                _ => b.started_at.cmp(&a.started_at),
            }
        });

        servers
    }

    /// Register a new server instance. Returns the registration handle.
    pub fn register(
        version: &str,
        port: Option<u16>,
        socket_only: bool,
    ) -> Result<Registration, DiscoveryError> {
        let id = uuid::Uuid::new_v4().to_string();
        let registry = registry_dir();
        let sockets = sockets_dir();

        fs::create_dir_all(&registry).map_err(|e| DiscoveryError::Io(e.to_string()))?;
        fs::create_dir_all(&sockets).map_err(|e| DiscoveryError::Io(e.to_string()))?;

        let socket_path = sockets.join(format!("{id}.sock"));
        let descriptor_path = registry.join(format!("{id}.json"));

        let url = if socket_only {
            None
        } else {
            port.map(|p| format!("http://127.0.0.1:{p}"))
        };

        let cwd = std::env::current_dir()
            .map(|p| p.display().to_string())
            .unwrap_or_else(|_| "unknown".into());

        let descriptor = ServiceDescriptor {
            id: id.clone(),
            pid: std::process::id(),
            version: version.to_string(),
            started_at: unix_timestamp(),
            socket: Some(socket_path.display().to_string()),
            url,
            capabilities: vec!["blobs".to_string(), "eval".to_string(), "wasm".to_string()],
            cwd,
        };

        // Write atomically: temp file + rename
        let tmp_path = registry.join(format!("{id}.json.tmp"));
        let content = serde_json::to_string_pretty(&descriptor)
            .map_err(|e| DiscoveryError::Io(e.to_string()))?;
        fs::write(&tmp_path, &content).map_err(|e| DiscoveryError::Io(e.to_string()))?;
        fs::rename(&tmp_path, &descriptor_path).map_err(|e| DiscoveryError::Io(e.to_string()))?;

        Ok(Registration {
            id,
            descriptor_path,
            socket_path,
            descriptor,
        })
    }

    /// Unregister a server instance. Removes the descriptor and socket files.
    pub fn unregister(registration: &Registration) {
        let _ = fs::remove_file(&registration.descriptor_path);
        let _ = fs::remove_file(&registration.socket_path);
    }

    /// Unix timestamp as a string (for ordering descriptors by age).
    fn unix_timestamp() -> String {
        use std::time::SystemTime;
        let secs = SystemTime::now()
            .duration_since(SystemTime::UNIX_EPOCH)
            .unwrap_or_default()
            .as_secs();
        format!("{secs}")
    }
}

#[cfg(not(unix))]
mod imp {
    use std::path::{Path, PathBuf};

    use super::{Registration, ServiceDescriptor};
    use crate::error::DiscoveryError;

    /// Discover available servers. Not supported on this platform.
    pub fn discover_servers(_prefer_cwd: Option<&Path>) -> Vec<(PathBuf, ServiceDescriptor)> {
        Vec::new()
    }

    /// Register a new server instance. Not supported on this platform.
    pub fn register(
        _version: &str,
        _port: Option<u16>,
        _socket_only: bool,
    ) -> Result<Registration, DiscoveryError> {
        Err(DiscoveryError::Io(
            "not supported on this platform".to_string(),
        ))
    }

    /// Unregister a server instance. No-op on this platform.
    pub fn unregister(_registration: &Registration) {}
}

pub use imp::*;
