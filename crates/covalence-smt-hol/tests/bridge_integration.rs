//! Integration tests for the Alethe → HOL bridge.
//!
//! These exercise the *stable boundary*: the trait + driver + `HolAletheBridge`
//! impl. Most Alethe rules are not yet wired through to the kernel, so we
//! verify two things:
//!
//!   1. Problem ingestion + `(assume ...)` succeed end-to-end on the QF_UF
//!      fixtures (sort/fun translation, `assume_rule` calls).
//!   2. The first `(step ...)` surfaces a `NotImplemented` error tagged with
//!      the Alethe rule name — i.e. the failure mode is loud, structured, and
//!      tells the next implementer exactly which rule to wire up.

use std::path::PathBuf;

use covalence_hol::{BOOL_TYCON_ID, EQ_CONST_ID, FUN_TYCON_ID, HolKernel};
use covalence_smt::{parse_alethe, parse_smtlib2};
use covalence_smt_hol::{
    AletheBridge, BridgeError, HolAletheBridge, ingest_problem, ingest_proof,
};
use covalence_types::Decision;

fn asset_path(problem: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../assets/tests/smt")
        .join(problem)
}

fn load_problem_and_proof(name: &str) -> (covalence_smt::SmtProblem, covalence_smt::AletheProof) {
    let p_path = asset_path(name).join("problem.smt2");
    let a_path = asset_path(name).join("proof.alethe");
    let problem = parse_smtlib2(&std::fs::read_to_string(&p_path).unwrap()).unwrap();
    let proof = parse_alethe(&std::fs::read_to_string(&a_path).unwrap()).unwrap();
    (problem, proof)
}

fn mk_kernel() -> HolKernel {
    HolKernel::new(FUN_TYCON_ID, BOOL_TYCON_ID, EQ_CONST_ID)
}

// =====================================================================
// trivial-unsat — assume + assume + resolution
// =====================================================================

#[test]
fn trivial_unsat_problem_ingests() {
    let (problem, _) = load_problem_and_proof("trivial-unsat");
    let mut kernel = mk_kernel();
    let mut bridge = HolAletheBridge::new(&mut kernel).unwrap();

    ingest_problem(&mut bridge, &problem).expect("problem should ingest cleanly");
}

#[test]
fn trivial_unsat_proof_punts_on_resolution() {
    let (problem, proof) = load_problem_and_proof("trivial-unsat");
    let mut kernel = mk_kernel();
    let mut bridge = HolAletheBridge::new(&mut kernel).unwrap();

    ingest_problem(&mut bridge, &problem).unwrap();
    let err = ingest_proof(&mut bridge, &proof)
        .expect_err("resolution is not yet wired up");
    match err {
        BridgeError::NotImplemented(rule) => {
            assert!(
                rule.contains("resolution"),
                "expected resolution rule in error, got: {rule}"
            );
        }
        other => panic!("expected NotImplemented(resolution), got {other:?}"),
    }
}

// =====================================================================
// cvc5-qf-uf — exercises `! :named` annotations end-to-end
// =====================================================================

#[test]
fn cvc5_qf_uf_problem_ingests() {
    // QF_UF with `(not (p a))`, `(= a b)`, `(p b)` — exercises `not` and
    // the curried application path. Should ingest cleanly.
    let (problem, _) = load_problem_and_proof("cvc5-qf-uf");
    let mut kernel = mk_kernel();
    let mut bridge = HolAletheBridge::new(&mut kernel).unwrap();

    ingest_problem(&mut bridge, &problem).expect("QF_UF problem should ingest");
}

#[test]
fn cvc5_qf_uf_assumes_succeed_steps_punt() {
    // The cvc5-generated proof has `:named` annotations that the bridge must
    // strip transparently. All assumes should succeed; the first step uses
    // `equiv_pos2` which we haven't wired up.
    let (problem, proof) = load_problem_and_proof("cvc5-qf-uf");
    let mut kernel = mk_kernel();
    let mut bridge = HolAletheBridge::new(&mut kernel).unwrap();

    ingest_problem(&mut bridge, &problem).unwrap();
    let err = ingest_proof(&mut bridge, &proof).expect_err("steps are not yet wired up");
    match err {
        BridgeError::NotImplemented(what) => {
            // First step is t0 with rule `equiv_pos2`.
            assert!(
                what.contains("equiv_pos2"),
                "expected first step to punt on equiv_pos2, got: {what}"
            );
        }
        other => panic!("expected NotImplemented from first step, got {other:?}"),
    }
}

// =====================================================================
// Decision starts at Unknown
// =====================================================================

#[test]
fn fresh_bridge_decision_is_unknown() {
    let mut kernel = mk_kernel();
    let bridge = HolAletheBridge::new(&mut kernel).unwrap();
    assert_eq!(bridge.decision(), Decision::Unknown);
}

// =====================================================================
// Sort + const declarations register correctly
// =====================================================================

#[test]
fn declare_sort_and_fun_succeed() {
    let mut kernel = mk_kernel();
    let mut bridge = HolAletheBridge::new(&mut kernel).unwrap();

    // trivial-unsat has `(declare-const a Bool)`.
    let (problem, _) = load_problem_and_proof("trivial-unsat");
    ingest_problem(&mut bridge, &problem).unwrap();

    let (a_id, _ty) = bridge.lookup_fun("a").expect("`a` should be declared");
    assert_eq!(bridge.names().resolve(a_id).map(|s| s.as_str()), Some("a"));

    // cvc5-qf-uf declares a parameterless sort `U` and constants `a`, `b`, `p`.
    let mut kernel2 = mk_kernel();
    let mut bridge2 = HolAletheBridge::new(&mut kernel2).unwrap();
    let (problem2, _) = load_problem_and_proof("cvc5-qf-uf");
    ingest_problem(&mut bridge2, &problem2).unwrap();
    assert!(bridge2.lookup_sort("U").is_some());
    assert!(bridge2.lookup_fun("a").is_some());
    assert!(bridge2.lookup_fun("b").is_some());
    assert!(bridge2.lookup_fun("p").is_some());
}

// =====================================================================
// Unknown rule → UnknownRule (not NotImplemented)
// =====================================================================

#[test]
fn assume_then_unknown_rule_step() {
    use covalence_sexp::{SExp, SExpr};

    let mut kernel = mk_kernel();
    let mut bridge = HolAletheBridge::new(&mut kernel).unwrap();

    // Set up a single boolean variable so the assume succeeds.
    bridge
        .declare_fun("p", &[], &SExp::symbol("Bool"))
        .unwrap();
    let p_term: SExpr = SExp::symbol("p");
    let thm = bridge.assume("h1", &p_term).unwrap();

    // step with empty clause + an unknown rule → currently NotImplemented
    // (the bridge punts on every rule for now).
    let err = bridge
        .step("t1", &[], "totally-made-up-rule", &[thm], &[], &[])
        .expect_err("every rule is currently NotImplemented");
    assert!(matches!(err, BridgeError::NotImplemented(_)));
}
