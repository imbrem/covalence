use std::path::PathBuf;

use serde::Deserialize;

/// User configuration loaded from `$XDG_CONFIG_HOME/covalence/config.json`.
/// Unknown fields are silently ignored.
#[derive(Debug, Clone, Default, Deserialize)]
#[serde(default)]
pub struct UserConfig {}

/// Returns the path to the user config file, if determinable.
pub fn config_path() -> Option<PathBuf> {
    dirs::config_dir().map(|d| d.join("covalence/config.json"))
}

/// Load user configuration. Returns defaults on any error (missing file, parse error, etc.).
#[cfg(unix)]
pub fn load_config() -> UserConfig {
    let Some(path) = config_path() else {
        return UserConfig::default();
    };
    let Ok(content) = std::fs::read_to_string(&path) else {
        return UserConfig::default();
    };
    serde_json::from_str(&content).unwrap_or_default()
}

/// Load user configuration. Not supported on non-unix; returns defaults.
#[cfg(not(unix))]
pub fn load_config() -> UserConfig {
    UserConfig::default()
}

/// Returns the default path for the SQLite blob store:
/// `$XDG_DATA_HOME/covalence/blobs.db` (typically `~/.local/share/covalence/blobs.db`).
pub fn default_store_path() -> Option<PathBuf> {
    dirs::data_dir().map(|d| d.join("covalence/blobs.db"))
}
