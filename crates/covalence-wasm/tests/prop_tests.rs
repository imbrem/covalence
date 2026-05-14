use std::collections::HashMap;

use covalence_object::O256;
use covalence_wasm::{BlobLookup, PropResult, WasmEngine};

/// Simple test blob store implementing BlobLookup.
struct TestStore {
    blobs: HashMap<O256, Option<Vec<u8>>>,
}

impl TestStore {
    fn new() -> Self {
        TestStore {
            blobs: HashMap::new(),
        }
    }

    fn insert(&mut self, data: &[u8]) -> O256 {
        let hash = O256::blob(data);
        self.blobs.insert(hash, Some(data.to_vec()));
        hash
    }

    /// Register a hash as known but without data.
    #[allow(dead_code)]
    fn insert_hash_only(&mut self, hash: O256) {
        self.blobs.entry(hash).or_insert(None);
    }
}

impl BlobLookup for TestStore {
    fn get_blob(&self, hash: &O256) -> Option<&[u8]> {
        self.blobs.get(hash)?.as_deref()
    }

    fn contains_blob(&self, hash: &O256) -> bool {
        self.blobs.contains_key(hash)
    }
}

fn engine() -> WasmEngine {
    WasmEngine::new().expect("failed to create engine")
}

/// Compile WAT text (component model syntax) to binary.
fn wat(source: &str) -> Vec<u8> {
    wat::parse_str(source).expect("failed to parse WAT")
}

// ============================================================
// Basic proposition checking: True / Unknown / False
// ============================================================

#[test]
fn trivial_true_prop() {
    // Component that imports attest and calls it in its start function.
    let bytes = wat(r#"
        (component
            (import "attest" (func $attest))
            (core module $m
                (import "env" "attest" (func $attest))
                (func $start (call $attest))
                (start $start)
            )
            (core func $attest_lowered (canon lower (func $attest)))
            (core instance $i (instantiate $m
                (with "env" (instance
                    (export "attest" (func $attest_lowered))
                ))
            ))
        )
        "#);

    let engine = engine();
    let store = TestStore::new();
    let result = engine
        .check_prop(&bytes, &store)
        .expect("check_prop failed");
    assert_eq!(result, PropResult::True);
}

#[test]
fn trivial_unknown_prop() {
    // Component that imports attest but does NOT call it during startup.
    let bytes = wat(r#"
        (component
            (import "attest" (func $attest))
            (core module $m
                (import "env" "attest" (func $attest))
                (func $start)
                (start $start)
            )
            (core func $attest_lowered (canon lower (func $attest)))
            (core instance $i (instantiate $m
                (with "env" (instance
                    (export "attest" (func $attest_lowered))
                ))
            ))
        )
        "#);

    let engine = engine();
    let store = TestStore::new();
    let result = engine
        .check_prop(&bytes, &store)
        .expect("check_prop failed");
    assert_eq!(result, PropResult::Unknown);
}

#[test]
fn statically_false_prop() {
    // Component that does NOT import attest at all.
    let bytes = wat(r#"
        (component
            (core module $m
                (func $start)
                (start $start)
            )
            (core instance $i (instantiate $m))
        )
        "#);

    let engine = engine();
    let store = TestStore::new();
    let result = engine
        .check_prop(&bytes, &store)
        .expect("check_prop failed");
    assert_eq!(result, PropResult::False);
}

#[test]
fn empty_component_is_false() {
    // Minimal empty component — no imports, no start.
    let bytes = wat("(component)");

    let engine = engine();
    let store = TestStore::new();
    let result = engine
        .check_prop(&bytes, &store)
        .expect("check_prop failed");
    assert_eq!(result, PropResult::False);
}

// ============================================================
// Import resolution: lazy vs eager
// ============================================================

#[test]
fn unknown_component_import_fails_eager() {
    // In eager mode, unknown component imports must fail.
    let fake_hash = "0000000000000000000000000000000000000000000000000000000000000000";
    let source = format!(
        r#"
        (component
            (import "attest" (func $attest))
            (import "component/{fake_hash}" (func $dep))
            (core module $m
                (import "env" "attest" (func $attest))
                (func $start (call $attest))
                (start $start)
            )
            (core func $attest_lowered (canon lower (func $attest)))
            (core instance $i (instantiate $m
                (with "env" (instance
                    (export "attest" (func $attest_lowered))
                ))
            ))
        )
        "#
    );
    let bytes = wat(&source);

    let engine = engine();
    let store = TestStore::new();
    let result = engine.check_prop_eager(&bytes, &store);
    // Must fail — either at our pre-check (UnknownImport) or at component
    // validation/linking.
    assert!(
        result.is_err(),
        "unknown component import should fail in eager mode"
    );
}

#[test]
fn unknown_component_import_accepted_lazy() {
    // In lazy mode (default), unknown component imports become traps.
    let fake_hash = "0000000000000000000000000000000000000000000000000000000000000000";
    let source = format!(
        r#"
        (component
            (import "attest" (func $attest))
            (import "component/{fake_hash}" (func $dep))
            (core module $m
                (import "env" "attest" (func $attest))
                (func $start (call $attest))
                (start $start)
            )
            (core func $attest_lowered (canon lower (func $attest)))
            (core instance $i (instantiate $m
                (with "env" (instance
                    (export "attest" (func $attest_lowered))
                ))
            ))
        )
        "#
    );
    let bytes = wat(&source);

    let engine = engine();
    let store = TestStore::new();
    let result = engine.check_prop(&bytes, &store);
    // Should NOT produce UnknownImport — lazy mode replaces with traps.
    match &result {
        Err(e) => {
            assert!(
                !e.to_string().contains("unknown import"),
                "lazy component import should not produce UnknownImport: {e}"
            );
        }
        Ok(r) => {
            // The component import is never called, attest IS called → True
            assert_eq!(*r, PropResult::True, "expected True, got {r}");
        }
    }
}

#[test]
fn unknown_prop_import_accepted() {
    // Prop imports are always permissive (lazy only) — they become traps.
    // Since the prop function is never called, this should succeed.
    let fake_hash = "0000000000000000000000000000000000000000000000000000000000000000";
    let source = format!(
        r#"
        (component
            (import "attest" (func $attest))
            (import "prop/{fake_hash}" (func $dep))
            (core module $m
                (import "env" "attest" (func $attest))
                (func $start (call $attest))
                (start $start)
            )
            (core func $attest_lowered (canon lower (func $attest)))
            (core instance $i (instantiate $m
                (with "env" (instance
                    (export "attest" (func $attest_lowered))
                ))
            ))
        )
        "#
    );
    let bytes = wat(&source);

    let engine = engine();
    let store = TestStore::new();
    let result = engine.check_prop(&bytes, &store);
    match &result {
        Err(e) => {
            assert!(
                !e.to_string().contains("unknown import"),
                "prop import should not produce UnknownImport: {e}"
            );
        }
        Ok(r) => {
            assert_eq!(*r, PropResult::True, "expected True, got {r}");
        }
    }
}

#[test]
fn unknown_prop_import_fails_even_in_eager_mode() {
    // Props are ALWAYS lazy — check_prop_eager should still accept them.
    let fake_hash = "0000000000000000000000000000000000000000000000000000000000000000";
    let source = format!(
        r#"
        (component
            (import "attest" (func $attest))
            (import "prop/{fake_hash}" (func $dep))
            (core module $m
                (import "env" "attest" (func $attest))
                (func $start (call $attest))
                (start $start)
            )
            (core func $attest_lowered (canon lower (func $attest)))
            (core instance $i (instantiate $m
                (with "env" (instance
                    (export "attest" (func $attest_lowered))
                ))
            ))
        )
        "#
    );
    let bytes = wat(&source);

    let engine = engine();
    let store = TestStore::new();
    let result = engine.check_prop_eager(&bytes, &store);
    // Props are always lazy — should NOT produce UnknownImport even in eager mode.
    match &result {
        Err(e) => {
            assert!(
                !e.to_string().contains("unknown import"),
                "prop import should be lazy even in eager mode: {e}"
            );
        }
        Ok(r) => {
            assert_eq!(*r, PropResult::True, "expected True, got {r}");
        }
    }
}

#[test]
fn known_component_import_accepted() {
    // Register a hash in the store, then import it.
    let mut store = TestStore::new();
    let component_data = wat("(component)");
    let hash = store.insert(&component_data);
    let hash_hex = hash.to_string();

    let source = format!(
        r#"
        (component
            (import "attest" (func $attest))
            (import "component/{hash_hex}" (func $dep))
            (core module $m
                (import "env" "attest" (func $attest))
                (func $start (call $attest))
                (start $start)
            )
            (core func $attest_lowered (canon lower (func $attest)))
            (core instance $i (instantiate $m
                (with "env" (instance
                    (export "attest" (func $attest_lowered))
                ))
            ))
        )
        "#
    );
    let bytes = wat(&source);

    let engine = engine();
    // Both lazy and eager should pass — component hash is known.
    let result = engine.check_prop_eager(&bytes, &store);
    match &result {
        Err(e) => {
            assert!(
                !e.to_string().contains("unknown import"),
                "known component import should not produce UnknownImport: {e}"
            );
        }
        Ok(_) => {}
    }
}

#[test]
fn known_prop_import_accepted() {
    let mut store = TestStore::new();
    let prop_data = wat("(component)");
    let hash = store.insert(&prop_data);
    let hash_hex = hash.to_string();

    let source = format!(
        r#"
        (component
            (import "attest" (func $attest))
            (import "prop/{hash_hex}" (func $dep))
            (core module $m
                (import "env" "attest" (func $attest))
                (func $start (call $attest))
                (start $start)
            )
            (core func $attest_lowered (canon lower (func $attest)))
            (core instance $i (instantiate $m
                (with "env" (instance
                    (export "attest" (func $attest_lowered))
                ))
            ))
        )
        "#
    );
    let bytes = wat(&source);

    let engine = engine();
    let result = engine.check_prop(&bytes, &store);
    match &result {
        Err(e) => {
            assert!(
                !e.to_string().contains("unknown import"),
                "known prop import should not produce UnknownImport: {e}"
            );
        }
        Ok(r) => {
            assert_eq!(*r, PropResult::True, "expected True, got {r}");
        }
    }
}

// ============================================================
// Module parsing
// ============================================================

#[test]
fn parse_valid_module() {
    let bytes = wat(r#"
        (module
            (func $add (param i32 i32) (result i32)
                local.get 0
                local.get 1
                i32.add
            )
            (export "add" (func $add))
        )
        "#);

    let engine = engine();
    let info = engine.parse_module(&bytes).expect("parse_module failed");
    assert_eq!(info.exports, vec!["add"]);
    assert!(info.imports.is_empty());
}

#[test]
fn parse_invalid_module_fails() {
    let engine = engine();
    let result = engine.parse_module(b"not wasm");
    assert!(result.is_err());
}

// ============================================================
// Component parsing
// ============================================================

#[test]
fn parse_valid_component() {
    let bytes = wat("(component)");

    let engine = engine();
    let info = engine
        .parse_component(&bytes)
        .expect("parse_component failed");
    assert!(info.imports.is_empty());
    assert!(info.exports.is_empty());
}

#[test]
fn parse_component_with_imports() {
    let bytes = wat(r#"
        (component
            (import "attest" (func $attest))
        )
        "#);

    let engine = engine();
    let info = engine
        .parse_component(&bytes)
        .expect("parse_component failed");
    assert_eq!(info.imports, vec!["attest"]);
}

#[test]
fn parse_invalid_component_fails() {
    let engine = engine();
    let result = engine.parse_component(b"not a component");
    assert!(result.is_err());
}

// ============================================================
// Blob import laziness
// ============================================================

#[test]
fn unknown_blob_import_does_not_fail_precheck() {
    // A component that imports a blob by hash that is NOT in the store.
    // The pre-check should NOT reject this (blobs are lazy).
    let fake_hash = "0000000000000000000000000000000000000000000000000000000000000000";
    let source = format!(
        r#"
        (component
            (import "attest" (func $attest))
            (import "blob/{fake_hash}" (func $blob (result (list u8))))
            (core module $m
                (import "env" "attest" (func $attest))
                (func $start (call $attest))
                (start $start)
            )
            (core func $attest_lowered (canon lower (func $attest)))
            (core instance $i (instantiate $m
                (with "env" (instance
                    (export "attest" (func $attest_lowered))
                ))
            ))
        )
        "#
    );
    let bytes = wat(&source);

    let engine = engine();
    let store = TestStore::new();
    let result = engine.check_prop(&bytes, &store);
    // Should NOT fail with UnknownImport — blobs are lazy.
    // May fail at linking/instantiation for other reasons, but not "unknown import".
    match &result {
        Err(e) => {
            assert!(
                !e.to_string().contains("unknown import"),
                "blob import should be lazy (not rejected in pre-check): {e}"
            );
        }
        Ok(_) => {} // Even better — succeeded
    }
}

#[test]
fn known_blob_import_succeeds_if_unused() {
    // A component that imports a known blob but never calls the function.
    let mut store = TestStore::new();
    let blob_data = b"hello blob";
    let hash = store.insert(blob_data);
    let hash_hex = hash.to_string();

    let source = format!(
        r#"
        (component
            (import "attest" (func $attest))
            (import "blob/{hash_hex}" (func $blob (result (list u8))))
            (core module $m
                (import "env" "attest" (func $attest))
                (func $start (call $attest))
                (start $start)
            )
            (core func $attest_lowered (canon lower (func $attest)))
            (core instance $i (instantiate $m
                (with "env" (instance
                    (export "attest" (func $attest_lowered))
                ))
            ))
        )
        "#
    );
    let bytes = wat(&source);

    let engine = engine();
    let result = engine.check_prop(&bytes, &store);
    // The blob function is never used, and attest IS called.
    // Whether this succeeds depends on whether the linker can satisfy the
    // blob import type. If it fails, it should be a link error, not unknown import.
    match &result {
        Err(e) => {
            assert!(
                !e.to_string().contains("unknown import"),
                "known blob should not produce UnknownImport: {e}"
            );
        }
        Ok(r) => {
            // Ideally True — attest is called and blob is unused
            assert_eq!(*r, PropResult::True, "expected True, got {r}");
        }
    }
}

// ============================================================
// Module import tests
// ============================================================

#[test]
fn unknown_module_import_does_not_fail_precheck() {
    // Module imports, like blob imports, should not cause immediate failure.
    let fake_hash = "0000000000000000000000000000000000000000000000000000000000000000";
    let source = format!(
        r#"
        (component
            (import "attest" (func $attest))
            (import "module/{fake_hash}" (func $mod_fn))
            (core module $m
                (import "env" "attest" (func $attest))
                (func $start (call $attest))
                (start $start)
            )
            (core func $attest_lowered (canon lower (func $attest)))
            (core instance $i (instantiate $m
                (with "env" (instance
                    (export "attest" (func $attest_lowered))
                ))
            ))
        )
        "#
    );
    let bytes = wat(&source);

    let engine = engine();
    let store = TestStore::new();
    let result = engine.check_prop(&bytes, &store);
    match &result {
        Err(e) => {
            assert!(
                !e.to_string().contains("unknown import"),
                "module import should not cause UnknownImport: {e}"
            );
        }
        Ok(_) => {}
    }
}

// ============================================================
// Calling unresolved imports traps
// ============================================================

#[test]
fn calling_unresolved_prop_import_traps() {
    // A component that imports an unknown prop AND calls it during start.
    // The call should trap (instantiation error), not silently succeed.
    let fake_hash = "0000000000000000000000000000000000000000000000000000000000000000";
    let source = format!(
        r#"
        (component
            (import "attest" (func $attest))
            (import "prop/{fake_hash}" (func $dep))
            (core module $m
                (import "env" "attest" (func $attest))
                (import "env" "dep" (func $dep))
                (func $start
                    (call $dep)
                    (call $attest)
                )
                (start $start)
            )
            (core func $attest_lowered (canon lower (func $attest)))
            (core func $dep_lowered (canon lower (func $dep)))
            (core instance $i (instantiate $m
                (with "env" (instance
                    (export "attest" (func $attest_lowered))
                    (export "dep" (func $dep_lowered))
                ))
            ))
        )
        "#
    );
    let bytes = wat(&source);

    let engine = engine();
    let store = TestStore::new();
    let result = engine.check_prop(&bytes, &store);
    // The prop import is a trap function — calling it should cause an
    // instantiation error (trap during start).
    assert!(
        result.is_err(),
        "calling unresolved prop import should trap"
    );
}

#[test]
fn calling_unresolved_lazy_component_import_traps() {
    // A component that lazily imports an unknown component AND calls it.
    // Default check_prop is lazy, so the import is accepted but calling traps.
    let fake_hash = "0000000000000000000000000000000000000000000000000000000000000000";
    let source = format!(
        r#"
        (component
            (import "attest" (func $attest))
            (import "component/{fake_hash}" (func $dep))
            (core module $m
                (import "env" "attest" (func $attest))
                (import "env" "dep" (func $dep))
                (func $start
                    (call $dep)
                    (call $attest)
                )
                (start $start)
            )
            (core func $attest_lowered (canon lower (func $attest)))
            (core func $dep_lowered (canon lower (func $dep)))
            (core instance $i (instantiate $m
                (with "env" (instance
                    (export "attest" (func $attest_lowered))
                    (export "dep" (func $dep_lowered))
                ))
            ))
        )
        "#
    );
    let bytes = wat(&source);

    let engine = engine();
    let store = TestStore::new();
    let result = engine.check_prop(&bytes, &store);
    // Lazy mode accepts the import, but calling the trap function should
    // cause an instantiation error.
    match &result {
        Err(e) => {
            assert!(
                !e.to_string().contains("unknown import"),
                "lazy mode should not produce UnknownImport: {e}"
            );
            // Should be an instantiation error (trap)
        }
        Ok(_) => panic!("calling unresolved lazy component import should trap"),
    }
}

// ============================================================
// Invalid component for check_prop
// ============================================================

#[test]
fn check_prop_rejects_invalid_bytes() {
    let engine = engine();
    let store = TestStore::new();
    let result = engine.check_prop(b"garbage bytes", &store);
    assert!(result.is_err());
    assert!(
        result
            .unwrap_err()
            .to_string()
            .contains("invalid component")
    );
}

#[test]
fn check_prop_rejects_core_module() {
    // A core WASM module is NOT a component.
    let bytes = wat("(module)");
    let engine = engine();
    let store = TestStore::new();
    let result = engine.check_prop(&bytes, &store);
    assert!(
        result.is_err(),
        "core module should not be accepted as a prop"
    );
}
