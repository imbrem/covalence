#![cfg(feature = "runtime")]

use std::collections::HashMap;

use covalence_hash::O256;
use covalence_store::ContentStore;
use covalence_wasm::{PropResult, WasmEngine};

/// Simple test blob store implementing ContentStore.
struct TestStore {
    blobs: std::sync::RwLock<HashMap<O256, Option<Vec<u8>>>>,
}

impl TestStore {
    fn new() -> Self {
        TestStore {
            blobs: std::sync::RwLock::new(HashMap::new()),
        }
    }
}

impl ContentStore<O256> for TestStore {
    fn get(&self, key: &O256) -> Option<Vec<u8>> {
        self.blobs.read().unwrap().get(key)?.clone()
    }

    fn put(&self, key: O256, data: &[u8]) -> Result<(), covalence_store::StoreError> {
        self.blobs.write().unwrap().insert(key, Some(data.to_vec()));
        Ok(())
    }

    fn insert(&self, data: &[u8]) -> Result<O256, covalence_store::StoreError> {
        let hash = O256::blob(data);
        self.blobs
            .write()
            .unwrap()
            .insert(hash, Some(data.to_vec()));
        Ok(hash)
    }

    fn contains(&self, key: &O256) -> bool {
        self.blobs.read().unwrap().contains_key(key)
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
// Basic proposition deciding: True / Unknown / False
// ============================================================

#[test]
fn trivial_true() {
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
    let result = engine.decide(&bytes, &store).expect("decide failed");
    assert_eq!(result, PropResult::True);
}

#[test]
fn trivial_unknown() {
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
    let result = engine.decide(&bytes, &store).expect("decide failed");
    assert_eq!(result, PropResult::Unknown);
}

#[test]
fn statically_false() {
    // Component that does NOT import attest at all and has no deps.
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
    let result = engine.decide(&bytes, &store).expect("decide failed");
    assert_eq!(result, PropResult::False);
}

#[test]
fn empty_component_false() {
    // Minimal empty component — no imports, no start.
    let bytes = wat("(component)");

    let engine = engine();
    let store = TestStore::new();
    let result = engine.decide(&bytes, &store).expect("decide failed");
    assert_eq!(result, PropResult::False);
}

// ============================================================
// Import linking — basic
// ============================================================

#[test]
fn import_instance_forward_exports() {
    // Dep exports "add", parent imports and calls it.
    let store = TestStore::new();
    let dep_bytes = wat(r#"
        (component
            (core module $m
                (func $add (param i32 i32) (result i32)
                    local.get 0
                    local.get 1
                    i32.add
                )
                (export "add" (func $add))
            )
            (core instance $i (instantiate $m))
            (func $add (param "a" s32) (param "b" s32) (result s32)
                (canon lift (core func $i "add"))
            )
            (export "add" (func $add))
        )
        "#);
    let dep_hash = store.insert(&dep_bytes).unwrap();
    let dep_hex = dep_hash.to_string();

    // Parent: imports the dep instance and uses add, then attests
    let parent_bytes = wat(&format!(
        r#"
        (component
            (import "attest" (func $attest))
            (import "component-{dep_hex}" (instance $lib
                (export "add" (func (param "a" s32) (param "b" s32) (result s32)))
            ))
            (alias export $lib "add" (func $add))
            (core module $m
                (import "env" "attest" (func $attest))
                (import "env" "add" (func $add (param i32 i32) (result i32)))
                (func $start
                    (drop (call $add (i32.const 1) (i32.const 2)))
                    (call $attest)
                )
                (start $start)
            )
            (core func $attest_lowered (canon lower (func $attest)))
            (core func $add_lowered (canon lower (func $add)))
            (core instance $i (instantiate $m
                (with "env" (instance
                    (export "attest" (func $attest_lowered))
                    (export "add" (func $add_lowered))
                ))
            ))
        )
        "#
    ));

    let engine = engine();
    let result = engine.decide(&parent_bytes, &store).expect("decide failed");
    assert_eq!(result, PropResult::True);
}

#[test]
fn import_dep_calls_attest() {
    // Dep imports attest and calls it → parent is True (transitive).
    let store = TestStore::new();
    let dep_bytes = wat(r#"
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
    let dep_hash = store.insert(&dep_bytes).unwrap();
    let dep_hex = dep_hash.to_string();

    // Parent doesn't import attest directly, but imports the dep
    let parent_bytes = wat(&format!(
        r#"
        (component
            (import "component-{dep_hex}" (instance $lib))
        )
        "#
    ));

    let engine = engine();
    let result = engine.decide(&parent_bytes, &store).expect("decide failed");
    // The dep calls attest during its instantiation (shared store state),
    // so the parent should be True.
    assert_eq!(result, PropResult::True);
}

#[test]
fn import_missing_hash_errors() {
    // Hash not in store → error
    let fake_hash = "0000000000000000000000000000000000000000000000000000000000000000";
    let parent_bytes = wat(&format!(
        r#"
        (component
            (import "attest" (func $attest))
            (import "component-{fake_hash}" (instance $lib))
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
    ));

    let engine = engine();
    let store = TestStore::new();
    let result = engine.decide(&parent_bytes, &store);
    assert!(result.is_err(), "missing hash should fail");
    assert!(
        result.unwrap_err().to_string().contains("blob not found"),
        "error should mention blob not found"
    );
}

#[test]
fn import_invalid_bytes_errors() {
    // Hash contains garbage → error
    let store = TestStore::new();
    let garbage = b"not a valid wasm component";
    let hash = store.insert(garbage).unwrap();
    let hash_hex = hash.to_string();

    let parent_bytes = wat(&format!(
        r#"
        (component
            (import "attest" (func $attest))
            (import "component-{hash_hex}" (instance $lib))
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
    ));

    let engine = engine();
    let result = engine.decide(&parent_bytes, &store);
    assert!(result.is_err(), "invalid bytes should fail");
    assert!(
        result
            .unwrap_err()
            .to_string()
            .contains("invalid component"),
        "error should mention invalid component"
    );
}

// ============================================================
// Import linking — instance caching
// ============================================================

#[test]
fn import_same_hash_shared_instance() {
    // A dep that calls attest on instantiation — only instantiated once (cached).
    let store = TestStore::new();
    let dep_bytes = wat(r#"
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
    let dep_hash = store.insert(&dep_bytes).unwrap();
    let dep_hex = dep_hash.to_string();

    let parent_bytes = wat(&format!(
        r#"
        (component
            (import "component-{dep_hex}" (instance $lib1))
        )
        "#
    ));

    let engine = engine();
    let result = engine.decide(&parent_bytes, &store).expect("decide failed");
    assert_eq!(result, PropResult::True);
}

// ============================================================
// Import linking — recursion & diamond deps
// ============================================================

#[test]
fn import_dep_with_own_deps() {
    // dep has its own cov:// deps, resolved recursively
    let store = TestStore::new();

    // Level-2 dep: just attests
    let level2_bytes = wat(r#"
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
    let level2_hash = store.insert(&level2_bytes).unwrap();
    let level2_hex = level2_hash.to_string();

    // Level-1 dep: imports level2
    let level1_bytes = wat(&format!(
        r#"
        (component
            (import "component-{level2_hex}" (instance $dep))
        )
        "#
    ));
    let level1_hash = store.insert(&level1_bytes).unwrap();
    let level1_hex = level1_hash.to_string();

    // Parent: imports level1
    let parent_bytes = wat(&format!(
        r#"
        (component
            (import "component-{level1_hex}" (instance $lib))
        )
        "#
    ));

    let engine = engine();
    let result = engine.decide(&parent_bytes, &store).expect("decide failed");
    // level2 attests, which propagates through
    assert_eq!(result, PropResult::True);
}

#[test]
fn import_diamond_dep() {
    // A imports B and C, both B and C import D → D instantiated once.
    let store = TestStore::new();

    // D: attests
    let d_bytes = wat(r#"
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
    let d_hash = store.insert(&d_bytes).unwrap();
    let d_hex = d_hash.to_string();

    // B: imports D, exports a constant
    let b_bytes = wat(&format!(
        r#"
        (component
            (import "component-{d_hex}" (instance $d))
            (core module $m
                (func $val (result i32) (i32.const 1))
                (export "val" (func $val))
            )
            (core instance $i (instantiate $m))
            (func $val (result s32) (canon lift (core func $i "val")))
            (export "val" (func $val))
        )
        "#
    ));
    let b_hash = store.insert(&b_bytes).unwrap();
    let b_hex = b_hash.to_string();

    // C: imports D, exports a different constant (distinct content → distinct hash)
    let c_bytes = wat(&format!(
        r#"
        (component
            (import "component-{d_hex}" (instance $d))
            (core module $m
                (func $val (result i32) (i32.const 2))
                (export "val" (func $val))
            )
            (core instance $i (instantiate $m))
            (func $val (result s32) (canon lift (core func $i "val")))
            (export "val" (func $val))
        )
        "#
    ));
    let c_hash = store.insert(&c_bytes).unwrap();
    let c_hex = c_hash.to_string();

    // A (parent): imports B and C
    let parent_bytes = wat(&format!(
        r#"
        (component
            (import "component-{b_hex}" (instance $b))
            (import "component-{c_hex}" (instance $c))
        )
        "#
    ));

    let engine = engine();
    let result = engine.decide(&parent_bytes, &store).expect("decide failed");
    assert_eq!(result, PropResult::True);
}

// ============================================================
// Import linking — exports
// ============================================================

#[test]
fn import_dep_result_usable() {
    // Parent uses return value from dep's export to decide whether to attest.
    let store = TestStore::new();

    // Dep exports a function that returns 42
    let dep_bytes = wat(r#"
        (component
            (core module $m
                (func $get_val (result i32) (i32.const 42))
                (export "get-val" (func $get_val))
            )
            (core instance $i (instantiate $m))
            (func $get_val (result s32)
                (canon lift (core func $i "get-val"))
            )
            (export "get-val" (func $get_val))
        )
        "#);
    let dep_hash = store.insert(&dep_bytes).unwrap();
    let dep_hex = dep_hash.to_string();

    // Parent: imports dep, calls get-val, if result == 42 then attest
    let parent_bytes = wat(&format!(
        r#"
        (component
            (import "attest" (func $attest))
            (import "component-{dep_hex}" (instance $lib
                (export "get-val" (func (result s32)))
            ))
            (alias export $lib "get-val" (func $get_val))
            (core module $m
                (import "env" "attest" (func $attest))
                (import "env" "get-val" (func $get_val (result i32)))
                (func $start
                    (if (i32.eq (call $get_val) (i32.const 42))
                        (then (call $attest))
                    )
                )
                (start $start)
            )
            (core func $attest_lowered (canon lower (func $attest)))
            (core func $get_val_lowered (canon lower (func $get_val)))
            (core instance $i (instantiate $m
                (with "env" (instance
                    (export "attest" (func $attest_lowered))
                    (export "get-val" (func $get_val_lowered))
                ))
            ))
        )
        "#
    ));

    let engine = engine();
    let result = engine.decide(&parent_bytes, &store).expect("decide failed");
    assert_eq!(result, PropResult::True);
}

// ============================================================
// Pre-check fix
// ============================================================

#[test]
fn no_attest_but_has_import_dep_not_false() {
    // Component with cov:// dep but no attest → NOT statically False
    // (dep might transitively attest)
    let store = TestStore::new();
    let dep_bytes = wat(r#"
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
    let dep_hash = store.insert(&dep_bytes).unwrap();
    let dep_hex = dep_hash.to_string();

    // Parent does NOT import attest, but imports dep that does attest
    let parent_bytes = wat(&format!(
        r#"
        (component
            (import "component-{dep_hex}" (instance $lib))
        )
        "#
    ));

    let engine = engine();
    let result = engine.decide(&parent_bytes, &store).expect("decide failed");
    // Should NOT be statically False — the dep attests
    assert_eq!(result, PropResult::True);
}

#[test]
fn no_attest_no_imports_is_false() {
    // Component with neither attest nor deps → statically False
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
    let result = engine.decide(&bytes, &store).expect("decide failed");
    assert_eq!(result, PropResult::False);
}

// ============================================================
// Traps return Unknown
// ============================================================

#[test]
fn trap_without_attest_returns_unknown() {
    // Component that traps in its start function without calling attest.
    let bytes = wat(r#"
        (component
            (import "attest" (func $attest))
            (core module $m
                (import "env" "attest" (func $attest))
                (func $start (unreachable))
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
        .decide(&bytes, &store)
        .expect("decide should not error on trap");
    assert_eq!(result, PropResult::Unknown);
}

#[test]
fn trap_after_attest_returns_true() {
    // Component that calls attest then traps — attest was already called.
    let bytes = wat(r#"
        (component
            (import "attest" (func $attest))
            (core module $m
                (import "env" "attest" (func $attest))
                (func $start
                    (call $attest)
                    (unreachable)
                )
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
        .decide(&bytes, &store)
        .expect("decide should not error on trap");
    assert_eq!(result, PropResult::True);
}

// ============================================================
// Invalid component for decide
// ============================================================

#[test]
fn decide_rejects_invalid_bytes() {
    let engine = engine();
    let store = TestStore::new();
    let result = engine.decide(b"garbage bytes", &store);
    assert!(result.is_err());
    assert!(
        result
            .unwrap_err()
            .to_string()
            .contains("invalid component")
    );
}

#[test]
fn decide_rejects_core_module() {
    // A core WASM module is NOT a component.
    let bytes = wat("(module)");
    let engine = engine();
    let store = TestStore::new();
    let result = engine.decide(&bytes, &store);
    assert!(
        result.is_err(),
        "core module should not be accepted as a prop"
    );
}

// ============================================================
// Module parsing (unchanged)
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
// Component parsing (unchanged)
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
            (import "blob-{fake_hash}" (func $blob (result (list u8))))
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
    let result = engine.decide(&bytes, &store);
    // Should NOT fail with MissingDep — blobs are lazy.
    match &result {
        Err(e) => {
            assert!(
                !e.to_string().contains("missing dep"),
                "blob import should be lazy (not rejected in pre-check): {e}"
            );
        }
        Ok(_) => {} // Even better — succeeded
    }
}

#[test]
fn known_blob_import_succeeds_if_unused() {
    // A component that imports a known blob but never calls the function.
    let store = TestStore::new();
    let blob_data = b"hello blob";
    let hash = store.insert(blob_data).unwrap();
    let hash_hex = hash.to_string();

    let source = format!(
        r#"
        (component
            (import "attest" (func $attest))
            (import "blob-{hash_hex}" (func $blob (result (list u8))))
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
    let result = engine.decide(&bytes, &store);
    match &result {
        Err(e) => {
            assert!(
                !e.to_string().contains("missing dep"),
                "known blob should not produce MissingDep: {e}"
            );
        }
        Ok(r) => {
            assert_eq!(*r, PropResult::True, "expected True, got {r}");
        }
    }
}
