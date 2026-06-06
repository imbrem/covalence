//! JSON-shaped, self-describing store manifest.
//!
//! A `StoreManifest` carries enough metadata for a store to introspect
//! itself and the stores it wraps or depends on — the same way an OCI
//! image manifest links to layers, or a Linux mount point names its
//! backing device. The shape is deliberately extensible: `config` is an
//! opaque `Value` so each store kind can define its own configuration
//! schema without churning this type.
//!
//! Naming follows the kernel/filesystem analogy:
//! - `wraps`       — stores this one transforms / overlays (cache → backing).
//! - `depends_on`  — stores this one can read from but does not own.
//!
//! Distinguishing the two matters: a cache layer is unsound without its
//! backing store (wraps), whereas a federated fetcher can ride out a
//! missing upstream (depends_on).

use std::collections::BTreeMap;

use covalence_json::Value;
use serde::{Deserialize, Serialize};

/// Self-description of a store.
///
/// Round-trips through `serde_json`. Forward-compatible: unknown fields
/// are accepted and re-emitted via `extra`, so newer manifests survive
/// older readers.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct StoreManifest {
    /// Stable identifier for this store instance (e.g.,
    /// `"local-cache"`, `"upstream-s3"`). Unique within a deployment.
    pub name: String,

    /// Family of store. Convention: short kebab-case, e.g.
    /// `"memory"`, `"sqlite"`, `"git-prefix"`, `"wasm-component"`,
    /// `"http"`. Kernel matches on this to route through the right
    /// adapter.
    pub kind: String,

    /// Semver-ish version of the store implementation. Optional —
    /// purely informational. The on-wire compatibility contract lives
    /// in `kind` + the WIT package version.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub version: Option<String>,

    /// Human-readable description.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub description: Option<String>,

    /// Stores this one *wraps* — i.e., layers on top of and depends
    /// on for correctness. A cache wraps its backing store; a
    /// signature-checking overlay wraps the raw bytes.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub wraps: Vec<StoreRef>,

    /// Stores this one *depends on* but does not transform. Upstream
    /// sources a federated fetcher can pull from, hints to a fallback
    /// store, etc.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub depends_on: Vec<StoreRef>,

    /// Per-kind configuration. Opaque to the manifest layer — each
    /// adapter parses this into its own typed config.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub config: Option<Value>,

    /// Forward-compatibility bucket. Unknown fields on the wire land
    /// here and are re-emitted on serialise, so future fields don't
    /// break older readers.
    #[serde(flatten)]
    pub extra: BTreeMap<String, Value>,
}

/// Reference to another store from inside a manifest.
///
/// A reference either *names* another store known to the same registry
/// (`name`) or *inlines* its full manifest (`manifest`). Both are
/// allowed simultaneously — `name` is the stable identifier, `manifest`
/// is the live description.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct StoreRef {
    /// Stable name of the referenced store (matches another manifest's
    /// `name`). Required: every reference has a name even if its
    /// definition is inlined.
    pub name: String,

    /// Optional inline manifest. Lets a deployment ship a single JSON
    /// document with the whole store graph embedded.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub manifest: Option<Box<StoreManifest>>,

    /// Forward-compat bucket.
    #[serde(flatten)]
    pub extra: BTreeMap<String, Value>,
}

impl StoreManifest {
    /// Minimal constructor — leaves every optional field empty.
    pub fn new(name: impl Into<String>, kind: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            kind: kind.into(),
            version: None,
            description: None,
            wraps: Vec::new(),
            depends_on: Vec::new(),
            config: None,
            extra: BTreeMap::new(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_json::{from_str, json, to_string};

    #[test]
    fn minimal_roundtrip() {
        let m = StoreManifest::new("root", "memory");
        let s = to_string(&m).unwrap();
        let back: StoreManifest = from_str(&s).unwrap();
        assert_eq!(back, m);
    }

    #[test]
    fn omits_empty_collections() {
        let s = to_string(&StoreManifest::new("root", "memory")).unwrap();
        assert!(!s.contains("wraps"));
        assert!(!s.contains("depends_on"));
        assert!(!s.contains("config"));
        assert!(!s.contains("version"));
        assert!(!s.contains("description"));
    }

    #[test]
    fn wraps_and_depends_on_distinct() {
        let mut m = StoreManifest::new("cache", "lru-overlay");
        m.wraps.push(StoreRef {
            name: "disk".into(),
            manifest: Some(Box::new(StoreManifest::new("disk", "sqlite"))),
            extra: BTreeMap::new(),
        });
        m.depends_on.push(StoreRef {
            name: "upstream".into(),
            manifest: None,
            extra: BTreeMap::new(),
        });
        let s = to_string(&m).unwrap();
        let back: StoreManifest = from_str(&s).unwrap();
        assert_eq!(back.wraps.len(), 1);
        assert_eq!(back.wraps[0].name, "disk");
        assert!(back.wraps[0].manifest.is_some());
        assert_eq!(back.depends_on.len(), 1);
        assert!(back.depends_on[0].manifest.is_none());
    }

    #[test]
    fn opaque_config_passes_through() {
        let mut m = StoreManifest::new("http", "http-cas");
        m.config = Some(json!({
            "endpoint": "https://blobs.example.com/v1",
            "timeout_ms": 5000,
        }));
        let s = to_string(&m).unwrap();
        let back: StoreManifest = from_str(&s).unwrap();
        assert_eq!(
            back.config.as_ref().unwrap()["endpoint"],
            json!("https://blobs.example.com/v1")
        );
    }

    #[test]
    fn unknown_fields_round_trip() {
        let raw = r#"{
            "name": "future",
            "kind": "memory",
            "newfangled_field": {"foo": 42}
        }"#;
        let m: StoreManifest = from_str(raw).unwrap();
        assert_eq!(m.extra.get("newfangled_field"), Some(&json!({"foo": 42})));
        let back = to_string(&m).unwrap();
        let m2: StoreManifest = from_str(&back).unwrap();
        assert_eq!(m, m2);
    }
}
