//! Carry a [`StoreManifest`] inside the component binary as a WASM
//! custom section.
//!
//! Embedding makes the component's content hash also pin its
//! self-description: a store is identified by
//! `O256::blob(component_bytes)`, and any change to the manifest
//! (kind, wraps, depends_on, config) yields a different hash.
//!
//! Section name is [`STORE_MANIFEST_SECTION`]. Payload is a UTF-8
//! JSON serialisation of [`StoreManifest`] (pretty-printed for
//! diff-ability — overhead is negligible next to the wasm body).
//!
//! Reading is single-section, first-match: deployments embed at most
//! one manifest per component. Re-embedding a manifest into a
//! component that already carries one produces a binary with two
//! manifest sections; [`extract_manifest`] returns the first.
//! Callers needing a clean swap should strip and rewrite explicitly
//! (we'll add a helper if that becomes a real use case).

use covalence_store::StoreManifest;
use covalence_wasm::{WasmError, append_custom_section, find_custom_section};

/// Name of the WASM custom section that carries the JSON-encoded
/// [`StoreManifest`].
pub const STORE_MANIFEST_SECTION: &str = "cov:store/manifest";

/// Errors from [`embed_manifest`] / [`extract_manifest`].
#[derive(Debug, thiserror::Error)]
pub enum ManifestError {
    #[error("wasm: {0}")]
    Wasm(#[from] WasmError),
    #[error("json: {0}")]
    Json(#[from] covalence_json::Error),
    #[error("manifest section is not valid UTF-8")]
    InvalidUtf8,
}

/// Serialise `manifest` to JSON and append it as a custom section to
/// `component_bytes`. The returned vec is the input bytes followed by
/// the manifest section — re-validation by the wasm runtime is
/// unaffected.
pub fn embed_manifest(
    component_bytes: &[u8],
    manifest: &StoreManifest,
) -> Result<Vec<u8>, ManifestError> {
    let json = covalence_json::to_string_pretty(manifest)?;
    Ok(append_custom_section(
        component_bytes,
        STORE_MANIFEST_SECTION,
        json.as_bytes(),
    ))
}

/// Read the first `cov:store/manifest` custom section from a
/// component binary and parse it as a [`StoreManifest`]. Returns
/// `Ok(None)` if no such section exists.
pub fn extract_manifest(component_bytes: &[u8]) -> Result<Option<StoreManifest>, ManifestError> {
    let Some(data) = find_custom_section(component_bytes, STORE_MANIFEST_SECTION)? else {
        return Ok(None);
    };
    let text = std::str::from_utf8(&data).map_err(|_| ManifestError::InvalidUtf8)?;
    Ok(Some(covalence_json::from_str(text)?))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Eight-byte empty-component preamble (`\0asm`, version, layer).
    fn empty_component() -> Vec<u8> {
        vec![0x00, 0x61, 0x73, 0x6d, 0x0d, 0x00, 0x01, 0x00]
    }

    #[test]
    fn roundtrip_minimal_manifest() {
        let m = StoreManifest::new("root", "memory");
        let bytes = embed_manifest(&empty_component(), &m).unwrap();
        let back = extract_manifest(&bytes).unwrap().unwrap();
        assert_eq!(back, m);
    }

    #[test]
    fn absent_section_returns_none() {
        let bytes = empty_component();
        assert!(extract_manifest(&bytes).unwrap().is_none());
    }

    #[test]
    fn manifest_change_alters_bytes() {
        // Different manifests produce different component bytes —
        // the contract that lets us identify a store by its
        // component-binary hash.
        let base = empty_component();
        let a = embed_manifest(&base, &StoreManifest::new("a", "memory")).unwrap();
        let b = embed_manifest(&base, &StoreManifest::new("b", "memory")).unwrap();
        assert_ne!(a, b);
    }
}
