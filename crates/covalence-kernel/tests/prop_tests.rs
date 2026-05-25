#![cfg(feature = "engine")]

use std::collections::HashMap;

use covalence_hash::O256;
use covalence_kernel::{Decision, WasmEngine};
use covalence_store::{BlobStore, ContentStore};

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

/// Create a BlobStore backed by a TestStore.
fn test_store() -> BlobStore<O256> {
    BlobStore::new(TestStore::new())
}

/// Compile WAT text (component model syntax) to binary.
fn wat(source: &str) -> Vec<u8> {
    wat::parse_str(source).expect("failed to parse WAT")
}

/// Helper: decide and return just the result (ignoring proved list).
fn decide_result(engine: &WasmEngine, bytes: &[u8], store: &BlobStore<O256>) -> Decision {
    engine.decide(bytes, store).expect("decide failed").decision
}

// ============================================================
// Basic proposition deciding: Sat / Unknown / Unsat
// ============================================================

#[test]
fn trivial_true() {
    let bytes = wat(include_str!("wat/trivial_true.wat"));

    let engine = engine();
    let store = test_store();
    let result = decide_result(&engine, &bytes, &store);
    assert_eq!(result, Decision::Sat);
}

#[test]
fn trivial_unknown() {
    let bytes = wat(include_str!("wat/trivial_unknown.wat"));

    let engine = engine();
    let store = test_store();
    let result = decide_result(&engine, &bytes, &store);
    assert_eq!(result, Decision::Unknown);
}

#[test]
fn statically_false() {
    let bytes = wat(include_str!("wat/statically_false.wat"));

    let engine = engine();
    let store = test_store();
    let result = decide_result(&engine, &bytes, &store);
    assert_eq!(result, Decision::Unsat);
}

#[test]
fn empty_component_false() {
    let bytes = wat("(component)");

    let engine = engine();
    let store = test_store();
    let result = decide_result(&engine, &bytes, &store);
    assert_eq!(result, Decision::Unsat);
}

// ============================================================
// Import linking — basic
// ============================================================

#[test]
fn import_instance_forward_exports() {
    let store = test_store();
    let dep_bytes = wat(include_str!("wat/import_instance_forward_exports/dep.wat"));
    let dep_hash = store.insert(&dep_bytes).unwrap();
    let dep_hex = dep_hash.to_string();

    let parent_bytes = wat(
        &include_str!("wat/import_instance_forward_exports/parent.wat")
            .replace("{dep_hex}", &dep_hex),
    );

    let engine = engine();
    let result = decide_result(&engine, &parent_bytes, &store);
    assert_eq!(result, Decision::Sat);
}

#[test]
fn import_dep_calls_attest() {
    let store = test_store();
    let dep_bytes = wat(include_str!("wat/import_dep_calls_attest/dep.wat"));
    let dep_hash = store.insert(&dep_bytes).unwrap();
    let dep_hex = dep_hash.to_string();

    let parent_bytes =
        wat(&include_str!("wat/import_dep_calls_attest/parent.wat").replace("{dep_hex}", &dep_hex));

    let engine = engine();
    let result = decide_result(&engine, &parent_bytes, &store);
    assert_eq!(result, Decision::Sat);
}

#[test]
fn import_missing_hash_errors() {
    let fake_hash = "0000000000000000000000000000000000000000000000000000000000000000";
    let parent_bytes = wat(&include_str!("wat/import_missing_hash_errors/parent.wat")
        .replace("{fake_hash}", fake_hash));

    let engine = engine();
    let store = test_store();
    let result = engine.decide(&parent_bytes, &store);
    assert!(result.is_err(), "missing hash should fail");
    assert!(
        result.unwrap_err().to_string().contains("blob not found"),
        "error should mention blob not found"
    );
}

#[test]
fn import_invalid_bytes_errors() {
    let store = test_store();
    let garbage = b"not a valid wasm component";
    let hash = store.insert(garbage).unwrap();
    let hash_hex = hash.to_string();

    let parent_bytes = wat(&include_str!("wat/import_invalid_bytes_errors/parent.wat")
        .replace("{hash_hex}", &hash_hex));

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
    let store = test_store();
    let dep_bytes = wat(include_str!("wat/import_same_hash_shared_instance/dep.wat"));
    let dep_hash = store.insert(&dep_bytes).unwrap();
    let dep_hex = dep_hash.to_string();

    let parent_bytes = wat(
        &include_str!("wat/import_same_hash_shared_instance/parent.wat")
            .replace("{dep_hex}", &dep_hex),
    );

    let engine = engine();
    let result = decide_result(&engine, &parent_bytes, &store);
    assert_eq!(result, Decision::Sat);
}

// ============================================================
// Import linking — recursion & diamond deps
// ============================================================

#[test]
fn import_dep_with_own_deps() {
    let store = test_store();

    let level2_bytes = wat(include_str!("wat/import_dep_with_own_deps/level2.wat"));
    let level2_hash = store.insert(&level2_bytes).unwrap();
    let level2_hex = level2_hash.to_string();

    let level1_bytes = wat(&include_str!("wat/import_dep_with_own_deps/level1.wat")
        .replace("{level2_hex}", &level2_hex));
    let level1_hash = store.insert(&level1_bytes).unwrap();
    let level1_hex = level1_hash.to_string();

    let parent_bytes = wat(&include_str!("wat/import_dep_with_own_deps/parent.wat")
        .replace("{level1_hex}", &level1_hex));

    let engine = engine();
    let result = decide_result(&engine, &parent_bytes, &store);
    assert_eq!(result, Decision::Sat);
}

#[test]
fn import_diamond_dep() {
    let store = test_store();

    let d_bytes = wat(include_str!("wat/import_diamond_dep/d.wat"));
    let d_hash = store.insert(&d_bytes).unwrap();
    let d_hex = d_hash.to_string();

    let b_bytes = wat(&include_str!("wat/import_diamond_dep/b.wat").replace("{d_hex}", &d_hex));
    let b_hash = store.insert(&b_bytes).unwrap();
    let b_hex = b_hash.to_string();

    let c_bytes = wat(&include_str!("wat/import_diamond_dep/c.wat").replace("{d_hex}", &d_hex));
    let c_hash = store.insert(&c_bytes).unwrap();
    let c_hex = c_hash.to_string();

    let parent_bytes = wat(&include_str!("wat/import_diamond_dep/parent.wat")
        .replace("{b_hex}", &b_hex)
        .replace("{c_hex}", &c_hex));

    let engine = engine();
    let result = decide_result(&engine, &parent_bytes, &store);
    assert_eq!(result, Decision::Sat);
}

// ============================================================
// Import linking — exports
// ============================================================

#[test]
fn import_dep_result_usable() {
    let store = test_store();

    let dep_bytes = wat(include_str!("wat/import_dep_result_usable/dep.wat"));
    let dep_hash = store.insert(&dep_bytes).unwrap();
    let dep_hex = dep_hash.to_string();

    let parent_bytes = wat(
        &include_str!("wat/import_dep_result_usable/parent.wat").replace("{dep_hex}", &dep_hex)
    );

    let engine = engine();
    let result = decide_result(&engine, &parent_bytes, &store);
    assert_eq!(result, Decision::Sat);
}

// ============================================================
// Pre-check fix
// ============================================================

#[test]
fn no_attest_but_has_import_dep_not_false() {
    let store = test_store();
    let dep_bytes = wat(include_str!(
        "wat/no_attest_but_has_import_dep_not_false/dep.wat"
    ));
    let dep_hash = store.insert(&dep_bytes).unwrap();
    let dep_hex = dep_hash.to_string();

    let parent_bytes = wat(
        &include_str!("wat/no_attest_but_has_import_dep_not_false/parent.wat")
            .replace("{dep_hex}", &dep_hex),
    );

    let engine = engine();
    let result = decide_result(&engine, &parent_bytes, &store);
    assert_eq!(result, Decision::Sat);
}

// ============================================================
// Traps return Unknown
// ============================================================

#[test]
fn trap_without_attest_returns_unknown() {
    let bytes = wat(include_str!("wat/trap_without_attest_returns_unknown.wat"));

    let engine = engine();
    let store = test_store();
    let result = engine
        .decide(&bytes, &store)
        .expect("decide should not error on trap")
        .decision;
    assert_eq!(result, Decision::Unknown);
}

#[test]
fn trap_after_attest_returns_true() {
    let bytes = wat(include_str!("wat/trap_after_attest_returns_true.wat"));

    let engine = engine();
    let store = test_store();
    let result = engine
        .decide(&bytes, &store)
        .expect("decide should not error on trap")
        .decision;
    assert_eq!(result, Decision::Sat);
}

// ============================================================
// Invalid component for decide
// ============================================================

#[test]
fn decide_rejects_invalid_bytes() {
    let engine = engine();
    let store = test_store();
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
    let bytes = wat("(module)");
    let engine = engine();
    let store = test_store();
    let result = engine.decide(&bytes, &store);
    assert!(
        result.is_err(),
        "core module should not be accepted as a prop"
    );
}

// ============================================================
// Blob import laziness
// ============================================================

#[test]
fn unknown_blob_import_does_not_fail_precheck() {
    let fake_hash = "0000000000000000000000000000000000000000000000000000000000000000";
    let bytes =
        wat(&include_str!("wat/unknown_blob_import/component.wat")
            .replace("{fake_hash}", fake_hash));

    let engine = engine();
    let store = test_store();
    let result = engine.decide(&bytes, &store);
    match &result {
        Err(e) => {
            assert!(
                !e.to_string().contains("missing dep"),
                "blob import should be lazy (not rejected in pre-check): {e}"
            );
        }
        Ok(_) => {}
    }
}

#[test]
fn known_blob_import_succeeds_if_unused() {
    let store = test_store();
    let blob_data = b"hello blob";
    let hash = store.insert(blob_data).unwrap();
    let hash_hex = hash.to_string();

    let bytes =
        wat(&include_str!("wat/known_blob_import/component.wat").replace("{hash_hex}", &hash_hex));

    let engine = engine();
    let result = engine.decide(&bytes, &store);
    match &result {
        Err(e) => {
            assert!(
                !e.to_string().contains("missing dep"),
                "known blob should not produce MissingDep: {e}"
            );
        }
        Ok(output) => {
            assert_eq!(
                output.decision,
                Decision::Sat,
                "expected True, got {:?}",
                output.decision
            );
        }
    }
}

// ============================================================
// Blob resource: read, eq, drop
// ============================================================

#[test]
fn blob_read_returns_data() {
    let store = test_store();
    let blob_data = b"hello blob";
    let hash = store.insert(blob_data).unwrap();
    let hash_hex = hash.to_string();

    let bytes = wat(&include_str!("wat/blob_read/component.wat").replace("{hash_hex}", &hash_hex));

    let engine = engine();
    let result = engine.decide(&bytes, &store).expect("decide failed");
    assert_eq!(result.decision, Decision::Sat);
}

#[test]
fn blob_eq_same_hash() {
    let store = test_store();
    let blob_data = b"same blob";
    let hash = store.insert(blob_data).unwrap();
    let hash_hex = hash.to_string();

    let bytes =
        wat(&include_str!("wat/blob_eq_same_hash/component.wat").replace("{hash_hex}", &hash_hex));

    let engine = engine();
    let result = engine.decide(&bytes, &store).expect("decide failed");
    assert_eq!(result.decision, Decision::Sat);
}

#[test]
fn blob_eq_different_hash() {
    let store = test_store();
    let hash_a = store.insert(b"blob a").unwrap();
    let hash_b = store.insert(b"blob b").unwrap();
    let hex_a = hash_a.to_string();
    let hex_b = hash_b.to_string();

    let bytes = wat(&include_str!("wat/blob_eq_different_hash/component.wat")
        .replace("{hex_a}", &hex_a)
        .replace("{hex_b}", &hex_b));

    let engine = engine();
    let result = engine.decide(&bytes, &store).expect("decide failed");
    assert_eq!(result.decision, Decision::Sat);
}

#[test]
fn blob_eq_without_data() {
    let fake_hash_a = "0000000000000000000000000000000000000000000000000000000000000001";
    let fake_hash_b = "0000000000000000000000000000000000000000000000000000000000000002";

    let bytes = wat(&include_str!("wat/blob_eq_without_data/component.wat")
        .replace("{fake_hash_a}", fake_hash_a)
        .replace("{fake_hash_b}", fake_hash_b));

    let engine = engine();
    let store = test_store();
    let result = engine.decide(&bytes, &store).expect("decide failed");
    assert_eq!(result.decision, Decision::Sat);
}

// ============================================================
// Prove imports — stack-based proving
// ============================================================

#[test]
fn prove_import_attests_through_dep() {
    let store = test_store();
    let dep_bytes = wat(include_str!("wat/prove_import_attests_through_dep/dep.wat"));
    let dep_hash = store.insert(&dep_bytes).unwrap();
    let dep_hex = dep_hash.to_string();

    let parent_bytes = wat(
        &include_str!("wat/prove_import_attests_through_dep/parent.wat")
            .replace("{dep_hex}", &dep_hex),
    );

    let engine = engine();
    let output = engine.decide(&parent_bytes, &store).expect("decide failed");
    assert_eq!(output.decision, Decision::Sat);
    assert!(
        output.proved.contains(&dep_hash),
        "dep should be proved: proved={:?}",
        output.proved
    );
}

#[test]
fn prove_import_dep_start_attests() {
    let store = test_store();
    let dep_bytes = wat(include_str!("wat/prove_import_dep_start_attests/dep.wat"));
    let dep_hash = store.insert(&dep_bytes).unwrap();
    let dep_hex = dep_hash.to_string();

    let parent_bytes = wat(
        &include_str!("wat/prove_import_dep_start_attests/parent.wat")
            .replace("{dep_hex}", &dep_hex),
    );

    let engine = engine();
    let output = engine.decide(&parent_bytes, &store).expect("decide failed");
    assert!(
        output.proved.contains(&dep_hash),
        "dep should be proved via start function: proved={:?}",
        output.proved
    );
}

#[test]
fn prove_import_not_called_not_proved() {
    let store = test_store();
    let dep_bytes = wat(include_str!(
        "wat/prove_import_not_called_not_proved/dep.wat"
    ));
    let dep_hash = store.insert(&dep_bytes).unwrap();
    let dep_hex = dep_hash.to_string();

    let parent_bytes = wat(
        &include_str!("wat/prove_import_not_called_not_proved/parent.wat")
            .replace("{dep_hex}", &dep_hex),
    );

    let engine = engine();
    let output = engine.decide(&parent_bytes, &store).expect("decide failed");
    assert_eq!(output.decision, Decision::Sat, "parent should be True");
    assert!(
        !output.proved.contains(&dep_hash),
        "dep should NOT be proved (never called): proved={:?}",
        output.proved
    );
}

#[test]
fn prove_import_transitive() {
    let store = test_store();

    let c_bytes = wat(include_str!("wat/prove_import_transitive/c.wat"));
    let c_hash = store.insert(&c_bytes).unwrap();
    let c_hex = c_hash.to_string();

    let b_bytes =
        wat(&include_str!("wat/prove_import_transitive/b.wat").replace("{c_hex}", &c_hex));
    let b_hash = store.insert(&b_bytes).unwrap();
    let b_hex = b_hash.to_string();

    let a_bytes =
        wat(&include_str!("wat/prove_import_transitive/a.wat").replace("{b_hex}", &b_hex));

    let engine = engine();
    let output = engine.decide(&a_bytes, &store).expect("decide failed");
    assert!(
        output.proved.contains(&b_hash),
        "B should be proved: proved={:?}",
        output.proved
    );
    assert!(
        output.proved.contains(&c_hash),
        "C should be proved: proved={:?}",
        output.proved
    );
}

#[test]
fn prove_import_shared_component_only_proves_through_call() {
    let store = test_store();

    let shared_bytes = wat(include_str!("wat/prove_import_shared_component/shared.wat"));
    let shared_hash = store.insert(&shared_bytes).unwrap();
    let shared_hex = shared_hash.to_string();

    let dep_bytes = wat(&include_str!("wat/prove_import_shared_component/dep.wat")
        .replace("{shared_hex}", &shared_hex));
    let dep_hash = store.insert(&dep_bytes).unwrap();
    let dep_hex = dep_hash.to_string();

    let parent_bytes = wat(
        &include_str!("wat/prove_import_shared_component/parent.wat")
            .replace("{shared_hex}", &shared_hex)
            .replace("{dep_hex}", &dep_hex),
    );

    let engine = engine();
    let output = engine.decide(&parent_bytes, &store).expect("decide failed");
    assert_eq!(output.decision, Decision::Sat);
    assert!(
        !output.proved.contains(&dep_hash),
        "dep should NOT be proved (shared attested during eager init, not through prove): proved={:?}",
        output.proved
    );
}

#[test]
fn prove_import_deep_resolve_no_crash() {
    let store = test_store();

    let a_bytes_placeholder = wat(include_str!(
        "wat/prove_import_deep_resolve/a_placeholder.wat"
    ));
    let a_hash = store.insert(&a_bytes_placeholder).unwrap();
    let a_hex = a_hash.to_string();

    let b_bytes =
        wat(&include_str!("wat/prove_import_deep_resolve/b.wat").replace("{a_hex}", &a_hex));
    let b_hash = store.insert(&b_bytes).unwrap();
    let b_hex = b_hash.to_string();

    let a_bytes =
        wat(&include_str!("wat/prove_import_deep_resolve/a.wat").replace("{b_hex}", &b_hex));

    let engine = engine();
    let result = engine.decide(&a_bytes, &store);
    assert!(
        result.is_ok(),
        "should resolve without cycle: {:?}",
        result.err()
    );
}

// ============================================================
// Equational reasoning: (x + y) + z = x + (y + z)
// ============================================================

#[test]
fn prove_equational_reasoning_assoc() {
    let store = test_store();

    // Layer 1: Union-Find (multi-memory)
    let uf_bytes = wat(include_str!("wat/prove_equational_reasoning_assoc/uf.wat"));
    let uf_hash = store.insert(&uf_bytes).unwrap();
    let uf_hex = uf_hash.to_string();

    // Layer 2: Pair Map (GC struct + array)
    let map_bytes = wat(include_str!("wat/prove_equational_reasoning_assoc/map.wat"));
    let map_hash = store.insert(&map_bytes).unwrap();
    let map_hex = map_hash.to_string();

    // Layer 3: Theory (prove-dep)
    let theory_bytes = wat(
        &include_str!("wat/prove_equational_reasoning_assoc/theory.wat")
            .replace("{uf_hex}", &uf_hex)
            .replace("{map_hex}", &map_hex),
    );
    let theory_hash = store.insert(&theory_bytes).unwrap();
    let theory_hex = theory_hash.to_string();

    // Layer 4: Proposition (prove-dep)
    let prop_bytes = wat(
        &include_str!("wat/prove_equational_reasoning_assoc/prop.wat")
            .replace("{theory_hex}", &theory_hex),
    );
    let prop_hash = store.insert(&prop_bytes).unwrap();
    let prop_hex = prop_hash.to_string();

    // Layer 5: Proof (top-level, decided)
    let proof_bytes = wat(
        &include_str!("wat/prove_equational_reasoning_assoc/proof.wat")
            .replace("{prop_hex}", &prop_hex),
    );

    let engine = engine();
    let output = engine.decide(&proof_bytes, &store).expect("decide failed");

    assert_eq!(
        output.decision,
        Decision::Sat,
        "proof of associativity should be True"
    );
    assert!(
        output.proved.contains(&prop_hash),
        "proposition should be proved: proved={:?}",
        output.proved
    );
    assert!(
        output.proved.contains(&theory_hash),
        "theory should be proved: proved={:?}",
        output.proved
    );
    assert!(
        !output.proved.contains(&uf_hash),
        "uf is a component dep, should NOT be proved"
    );
    assert!(
        !output.proved.contains(&map_hash),
        "map is a component dep, should NOT be proved"
    );
}

// ============================================================
// Copy imports — fresh (unshared) instances
// ============================================================

#[test]
fn copy_import_fresh_instance() {
    let store = test_store();

    // D: counter component (inc returns old value, then increments)
    let d_bytes = wat(include_str!("wat/copy_import_fresh_instance/d.wat"));
    let d_hash = store.insert(&d_bytes).unwrap();
    let d_hex = d_hash.to_string();

    // B: imports D as copy, exports go = D.inc
    let b_bytes =
        wat(&include_str!("wat/copy_import_fresh_instance/b.wat").replace("{d_hex}", &d_hex));
    let b_hash = store.insert(&b_bytes).unwrap();
    let b_hex = b_hash.to_string();

    // C: imports D as copy, exports run = D.inc
    let c_bytes =
        wat(&include_str!("wat/copy_import_fresh_instance/c.wat").replace("{d_hex}", &d_hex));
    let c_hash = store.insert(&c_bytes).unwrap();
    let c_hex = c_hash.to_string();

    // Parent: links D, B, C; verifies 3 separate D instances
    let parent_bytes = wat(&include_str!("wat/copy_import_fresh_instance/parent.wat")
        .replace("{d_hex}", &d_hex)
        .replace("{b_hex}", &b_hex)
        .replace("{c_hex}", &c_hex));

    let engine = engine();
    let result = decide_result(&engine, &parent_bytes, &store);
    assert_eq!(
        result,
        Decision::Sat,
        "copy imports should produce fresh (unshared) instances"
    );
}

#[test]
fn prove_import_gets_isolated_component_instance() {
    let store = test_store();

    let c_bytes = wat(include_str!("wat/prove_import_isolated_instance/c.wat"));
    let c_hash = store.insert(&c_bytes).unwrap();
    let c_hex = c_hash.to_string();

    let b_bytes =
        wat(&include_str!("wat/prove_import_isolated_instance/b.wat").replace("{c_hex}", &c_hex));
    let b_hash = store.insert(&b_bytes).unwrap();
    let b_hex = b_hash.to_string();

    let parent_bytes = wat(
        &include_str!("wat/prove_import_isolated_instance/parent.wat")
            .replace("{c_hex}", &c_hex)
            .replace("{b_hex}", &b_hex),
    );

    let engine = engine();
    let output = engine.decide(&parent_bytes, &store).expect("decide failed");
    assert_eq!(
        output.decision,
        Decision::Sat,
        "parent should be True (prove-dep got isolated component instance)"
    );
}

// Name resource: cons, uncons, eq, static cons, repr, tag
// ============================================================

#[test]
fn name_cons_uncons_roundtrip() {
    let store = test_store();
    let blob_data = b"hello name";
    let hash = store.insert(blob_data).unwrap();
    let hash_hex = hash.to_string();

    let bytes =
        wat(&include_str!("wat/name_cons_uncons/component.wat").replace("{hash_hex}", &hash_hex));

    let engine = engine();
    let result = engine.decide(&bytes, &store).expect("decide failed");
    assert_eq!(result.decision, Decision::Sat);
}

#[test]
fn name_eq_same_and_different() {
    let store = test_store();
    let hash_a = store.insert(b"blob a").unwrap();
    let hash_b = store.insert(b"blob b").unwrap();
    let hex_a = hash_a.to_string();
    let hex_b = hash_b.to_string();

    let bytes = wat(&include_str!("wat/name_eq/component.wat")
        .replace("{hex_a}", &hex_a)
        .replace("{hex_b}", &hex_b));

    let engine = engine();
    let result = engine.decide(&bytes, &store).expect("decide failed");
    assert_eq!(result.decision, Decision::Sat);
}

#[test]
fn name_cons_tagged_differs_from_plain() {
    let store = test_store();
    let hash_a = store.insert(b"tag blob").unwrap();
    let hash_b = store.insert(b"data blob").unwrap();
    let hex_a = hash_a.to_string();
    let hex_b = hash_b.to_string();

    let bytes = wat(&include_str!("wat/name_cons_tagged/component.wat")
        .replace("{hex_a}", &hex_a)
        .replace("{hex_b}", &hex_b));

    let engine = engine();
    let result = engine.decide(&bytes, &store).expect("decide failed");
    assert_eq!(result.decision, Decision::Sat);
}

#[test]
fn name_tag_traps() {
    let store = test_store();
    let blob_data = b"some blob";
    let hash = store.insert(blob_data).unwrap();
    let hash_hex = hash.to_string();

    let bytes =
        wat(&include_str!("wat/name_tag_traps/component.wat").replace("{hash_hex}", &hash_hex));

    let engine = engine();
    let result = engine.decide(&bytes, &store).expect("decide failed");
    // Attest is called before tag() traps, so result should be Sat.
    assert_eq!(result.decision, Decision::Sat);
}

// ============================================================
// Store resource imports
// ============================================================

#[test]
fn store_basic_set_get() {
    let bytes = wat(include_str!("wat/store_basic/component.wat"));

    let engine = engine();
    let store = test_store();
    let result = decide_result(&engine, &bytes, &store);
    assert_eq!(result, Decision::Sat, "set then get should succeed");
}

#[test]
fn store_get_missing_traps() {
    let bytes = wat(include_str!("wat/store_get_missing_traps/component.wat"));

    let engine = engine();
    let store = test_store();
    let result = decide_result(&engine, &bytes, &store);
    assert_eq!(
        result,
        Decision::Unknown,
        "get without set should trap → Unknown"
    );
}

#[test]
fn store_open_sub_store() {
    let bytes = wat(include_str!("wat/store_open_sub_store/component.wat"));

    let engine = engine();
    let store = test_store();
    let result = decide_result(&engine, &bytes, &store);
    assert_eq!(result, Decision::Sat, "sub-store set/get should work");
}

#[test]
fn store_overwrite() {
    let bytes = wat(include_str!("wat/store_overwrite/component.wat"));

    let engine = engine();
    let store = test_store();
    let result = decide_result(&engine, &bytes, &store);
    assert_eq!(
        result,
        Decision::Sat,
        "second set should overwrite the first"
    );
}

#[test]
fn store_shared_across_link_deps() {
    let store = test_store();

    let writer_bytes = wat(include_str!("wat/store_shared_across_link_deps/writer.wat"));
    let writer_hash = store.insert(&writer_bytes).unwrap();
    let writer_hex = writer_hash.to_string();

    let reader_bytes = wat(include_str!("wat/store_shared_across_link_deps/reader.wat"));
    let reader_hash = store.insert(&reader_bytes).unwrap();
    let reader_hex = reader_hash.to_string();

    let parent_bytes = wat(
        &include_str!("wat/store_shared_across_link_deps/parent.wat")
            .replace("{writer_hex}", &writer_hex)
            .replace("{reader_hex}", &reader_hex),
    );

    let engine = engine();
    let result = decide_result(&engine, &parent_bytes, &store);
    assert_eq!(
        result,
        Decision::Sat,
        "link-deps should share the same store root"
    );
}

#[test]
fn store_isolated_prove_dep() {
    let store = test_store();

    let dep_bytes = wat(include_str!("wat/store_isolated_prove_dep/dep.wat"));
    let dep_hash = store.insert(&dep_bytes).unwrap();
    let dep_hex = dep_hash.to_string();

    let parent_bytes = wat(
        &include_str!("wat/store_isolated_prove_dep/parent.wat").replace("{dep_hex}", &dep_hex)
    );

    let engine = engine();
    let output = engine.decide(&parent_bytes, &store).expect("decide failed");
    assert_eq!(
        output.decision,
        Decision::Sat,
        "parent attested before prove-dep trapped"
    );
}

#[test]
fn store_only_not_decidable() {
    let bytes = wat(include_str!("wat/store_only_not_decidable/component.wat"));

    let engine = engine();
    let store = test_store();
    let result = decide_result(&engine, &bytes, &store);
    assert_eq!(
        result,
        Decision::Unsat,
        "store alone (no attest) should be Unsat"
    );
}

#[test]
fn store_parent_child_independent() {
    let store = test_store();

    let dep_bytes = wat(include_str!("wat/store_parent_child_independent/dep.wat"));
    let dep_hash = store.insert(&dep_bytes).unwrap();
    let dep_hex = dep_hash.to_string();

    let parent_bytes = wat(
        &include_str!("wat/store_parent_child_independent/parent.wat")
            .replace("{dep_hex}", &dep_hex),
    );

    let engine = engine();
    let output = engine.decide(&parent_bytes, &store).expect("decide failed");
    assert_eq!(
        output.decision,
        Decision::Sat,
        "parent and child should independently set+get from isolated stores"
    );
    assert!(
        output.proved.contains(&dep_hash),
        "prove-dep should be proved: proved={:?}",
        output.proved
    );
}

#[test]
fn store_nested_hierarchy() {
    let bytes = wat(include_str!("wat/store_nested_hierarchy/component.wat"));

    let engine = engine();
    let store = test_store();
    let result = decide_result(&engine, &bytes, &store);
    assert_eq!(
        result,
        Decision::Sat,
        "multi-level dir navigation should persist data"
    );
}

#[test]
fn store_child_returns_nested() {
    let store = test_store();

    let child_bytes = wat(include_str!("wat/store_child_returns_nested/child.wat"));
    let child_hash = store.insert(&child_bytes).unwrap();
    let child_hex = child_hash.to_string();

    let parent_bytes = wat(&include_str!("wat/store_child_returns_nested/parent.wat")
        .replace("{child_hex}", &child_hex));

    let engine = engine();
    let result = decide_result(&engine, &parent_bytes, &store);
    assert_eq!(
        result,
        Decision::Sat,
        "parent should read nested store data returned by child"
    );
}

#[test]
fn store_nested_no_parent_access() {
    let store = test_store();

    let child_bytes = wat(include_str!("wat/store_nested_no_parent_access/child.wat"));
    let child_hash = store.insert(&child_bytes).unwrap();
    let child_hex = child_hash.to_string();

    let parent_bytes = wat(
        &include_str!("wat/store_nested_no_parent_access/parent.wat")
            .replace("{child_hex}", &child_hex),
    );

    let engine = engine();
    let output = engine.decide(&parent_bytes, &store).expect("decide failed");
    assert_eq!(
        output.decision,
        Decision::Sat,
        "parent attested before trap; nested store can't see root keys"
    );
}

// ============================================================
// Store: try-get, assert-exists, try-exists
// ============================================================

#[test]
fn store_try_get_existing() {
    let bytes = wat(include_str!("wat/store_try_get_existing/component.wat"));

    let engine = engine();
    let store = test_store();
    let result = decide_result(&engine, &bytes, &store);
    assert_eq!(
        result,
        Decision::Sat,
        "try-get existing key should return Some with correct value"
    );
}

#[test]
fn store_try_get_missing() {
    let bytes = wat(include_str!("wat/store_try_get_missing/component.wat"));

    let engine = engine();
    let store = test_store();
    let result = decide_result(&engine, &bytes, &store);
    assert_eq!(
        result,
        Decision::Sat,
        "try-get missing key should return None"
    );
}

#[test]
fn store_assert_exists_after_set() {
    let bytes = wat(include_str!(
        "wat/store_assert_exists_after_set/component.wat"
    ));

    let engine = engine();
    let store = test_store();
    let result = decide_result(&engine, &bytes, &store);
    assert_eq!(
        result,
        Decision::Sat,
        "assert-exists after set should not trap"
    );
}

#[test]
fn store_assert_exists_ns_alone_traps() {
    let bytes = wat(include_str!(
        "wat/store_assert_exists_ns_alone_traps/component.wat"
    ));

    let engine = engine();
    let store = test_store();
    let result = decide_result(&engine, &bytes, &store);
    assert_eq!(
        result,
        Decision::Unknown,
        "ns alone does not create presence; assert-exists should trap"
    );
}

#[test]
fn store_assert_exists_missing_traps() {
    let bytes = wat(include_str!(
        "wat/store_assert_exists_missing_traps/component.wat"
    ));

    let engine = engine();
    let store = test_store();
    let result = decide_result(&engine, &bytes, &store);
    assert_eq!(
        result,
        Decision::Unknown,
        "assert-exists on empty store should trap"
    );
}

#[test]
fn store_try_exists_after_set() {
    let bytes = wat(include_str!("wat/store_try_exists_after_set/component.wat"));

    let engine = engine();
    let store = test_store();
    let result = decide_result(&engine, &bytes, &store);
    assert_eq!(
        result,
        Decision::Sat,
        "try-exists after set should return Some"
    );
}

#[test]
fn store_try_exists_missing() {
    let bytes = wat(include_str!("wat/store_try_exists_missing/component.wat"));

    let engine = engine();
    let store = test_store();
    let result = decide_result(&engine, &bytes, &store);
    assert_eq!(
        result,
        Decision::Sat,
        "try-exists on empty store should return None"
    );
}
