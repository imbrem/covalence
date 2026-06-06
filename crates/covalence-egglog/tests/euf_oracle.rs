//! End-to-end tests for the external-egglog driver path
//! (`cfg(feature = "external-egglog")`).
//!
//! These spin up a real upstream `egglog::EGraph`, run a small program,
//! extract the proof DAG via the patched `egglog::proof` module, convert
//! it through [`covalence_egglog::external::run_program`], and ingest it
//! into a `KernelEgglogBridge`. They exercise the only path in the crate
//! that bridges real solver output into our kernel — so a regression
//! here is the loudest possible early-warning signal.

#![cfg(feature = "external-egglog")]

use covalence_egglog::external::{ingest_via_oracle, run_program};
use covalence_egglog::{BridgeError, KernelEgglogBridge};
use covalence_kernel::Kernel;

// =====================================================================
// run_program — produces a non-empty proof DAG for a (prove …) target
// =====================================================================

#[test]
fn run_program_emits_non_empty_proof_for_euf_union() {
    // `(union (A) (B))` then `(prove (= (A) (B)))` — the smallest
    // upstream-roundtrip that exercises proof extraction.
    let src = r#"
        (datatype U (A) (B))
        (union (A) (B))
        (prove (= (A) (B)))
    "#;
    let (dag, store, _root) = run_program(src).expect("upstream run_program should succeed");
    assert!(!dag.is_empty(), "term arena should be populated");
    assert!(!store.is_empty(), "proof store should be populated");
}

// =====================================================================
// ingest_via_oracle — full kernel ingestion of an upstream proof DAG
// =====================================================================

#[test]
fn ingest_via_oracle_closes_euf_union() {
    // Same EUF program as above, but now we also auto-declare every
    // constructor head encountered in the proof DAG onto the bridge and
    // ingest the resulting Thm. Confirms the full path:
    //   source → upstream EGraph → ProofStore → our types → EThm.
    let src = r#"
        (datatype U (A) (B))
        (union (A) (B))
        (prove (= (A) (B)))
    "#;
    let mut kernel = Kernel::new();
    let mut bridge = KernelEgglogBridge::new(&mut kernel);
    let _thm =
        ingest_via_oracle(&mut bridge, src).expect("upstream proof should ingest end-to-end");
}

// =====================================================================
// Negative path — programs without (prove …) surface BridgeError
// =====================================================================

#[test]
fn ingest_via_oracle_without_prove_errors() {
    let src = "(datatype U (A))";
    let mut kernel = Kernel::new();
    let mut bridge = KernelEgglogBridge::new(&mut kernel);
    let err = ingest_via_oracle(&mut bridge, src)
        .expect_err("upstream run with no (prove …) should be a hard error");
    assert!(matches!(err, BridgeError::Malformed(_)));
}

#[test]
fn ingest_via_oracle_with_syntax_error_errors() {
    let src = "(this is not valid egglog";
    let mut kernel = Kernel::new();
    let mut bridge = KernelEgglogBridge::new(&mut kernel);
    let err = ingest_via_oracle(&mut bridge, src)
        .expect_err("upstream parse error should propagate as BridgeError");
    assert!(matches!(err, BridgeError::Malformed(_)));
}
