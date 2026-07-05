//! Resolve secrets (API keys, tokens) and other env-based configuration with
//! a `COV_<VAR>` → `<VAR>` override pattern.
//!
//! The same resolution chain is used for both secret and non-secret values:
//!
//! 1. `COV_<VAR>` — covalence-specific override (so users can pin a value for
//!    cov without disturbing the SDK env var that other tools rely on).
//! 2. `COV_<VAR>_CMD` — same override, command form (secrets only).
//! 3. `<VAR>` — the standard SDK env var (`OPENAI_API_KEY`, `OPENAI_BASE_URL`,
//!    …).
//! 4. `<VAR>_CMD` — command form (secrets only). Mirrors git's
//!    `*_PROGRAM`/`*_COMMAND` env vars and sops/GitHub CLI's `_CMD` fallback;
//!    lets users defer to their password manager (`pass`, `op`, `bw`, …)
//!    without us taking on a keychain dep.
//!
//! If *either* `COV_<VAR>` or `COV_<VAR>_CMD` is set, we use that pair
//! exclusively — no fall-through to the unprefixed standard form. This keeps
//! "override" semantics predictable.
//!
//! Secrets are wrapped in [`SecretString`] so they don't accidentally land in
//! `Debug` output, log lines, or panics. Non-secret values (base URLs) come
//! back as plain `String`.

use std::process::Command;

pub use secrecy::{ExposeSecret, SecretString};

#[derive(Debug, thiserror::Error)]
pub enum SecretError {
    #[error("none of COV_{var}, COV_{var}_CMD, {var}, {var}_CMD is set")]
    Missing { var: String },
    #[error("env var {var} contains invalid UTF-8")]
    NotUtf8 { var: String },
    #[error("{var}_CMD failed to spawn: {message}")]
    SpawnFailed { var: String, message: String },
    #[error("{var}_CMD exited with status {status}: {stderr}")]
    CommandFailed {
        var: String,
        status: i32,
        stderr: String,
    },
    #[error("{var}_CMD produced empty output")]
    EmptyOutput { var: String },
}

/// Resolve a secret env var (`var`) with the standard fallback chain.
///
/// Order: `COV_<var>` → `COV_<var>_CMD` → `<var>` → `<var>_CMD`. Returns
/// [`SecretError::Missing`] if none of the four are set.
pub fn from_env(var: &str) -> Result<SecretString, SecretError> {
    match from_env_optional(var)? {
        Some(s) => Ok(s),
        None => Err(SecretError::Missing {
            var: var.to_string(),
        }),
    }
}

/// Like [`from_env`], but returns `Ok(None)` when no env var in the chain is
/// set. Other errors (UTF-8, command failure) still surface.
pub fn from_env_optional(var: &str) -> Result<Option<SecretString>, SecretError> {
    let cov_var = format!("COV_{var}");
    if env_present(&cov_var) || env_present(&format!("{cov_var}_CMD")) {
        return resolve_pair(&cov_var);
    }
    resolve_pair(var)
}

/// Resolve a non-secret env var (e.g. a base URL) with the same `COV_<var>`
/// override pattern. The `_CMD` fallback is **not** consulted — base URLs
/// are static configuration, not secrets.
///
/// Returns `Some(value)` for the first non-empty hit, otherwise `None`.
pub fn endpoint_from_env(var: &str) -> Option<String> {
    let cov_var = format!("COV_{var}");
    if let Ok(v) = std::env::var(&cov_var)
        && !v.trim().is_empty()
    {
        return Some(v);
    }
    if let Ok(v) = std::env::var(var)
        && !v.trim().is_empty()
    {
        return Some(v);
    }
    None
}

fn env_present(var: &str) -> bool {
    matches!(std::env::var(var), Ok(s) if !s.trim().is_empty())
}

fn resolve_pair(var: &str) -> Result<Option<SecretString>, SecretError> {
    match std::env::var(var) {
        Ok(value) if !value.is_empty() => return Ok(Some(SecretString::from(value))),
        Ok(_) => {}
        Err(std::env::VarError::NotUnicode(_)) => {
            return Err(SecretError::NotUtf8 {
                var: var.to_string(),
            });
        }
        Err(std::env::VarError::NotPresent) => {}
    }
    from_env_cmd(var)
}

fn from_env_cmd(var: &str) -> Result<Option<SecretString>, SecretError> {
    let cmd_var = format!("{var}_CMD");
    let cmd = match std::env::var(&cmd_var) {
        Ok(s) if s.trim().is_empty() => return Ok(None),
        Ok(s) => s,
        Err(std::env::VarError::NotUnicode(_)) => {
            return Err(SecretError::NotUtf8 { var: cmd_var });
        }
        Err(std::env::VarError::NotPresent) => return Ok(None),
    };

    let output = Command::new("sh")
        .arg("-c")
        .arg(&cmd)
        .output()
        .map_err(|e| SecretError::SpawnFailed {
            var: var.to_string(),
            message: e.to_string(),
        })?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr).trim().to_string();
        return Err(SecretError::CommandFailed {
            var: var.to_string(),
            status: output.status.code().unwrap_or(-1),
            stderr,
        });
    }

    let stdout = String::from_utf8(output.stdout).map_err(|_| SecretError::NotUtf8 {
        var: cmd_var.clone(),
    })?;
    let trimmed = stdout.trim_end_matches(['\n', '\r']).to_string();
    if trimmed.is_empty() {
        return Err(SecretError::EmptyOutput {
            var: var.to_string(),
        });
    }
    Ok(Some(SecretString::from(trimmed)))
}
