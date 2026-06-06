//! Integration tests for the Alethe → Prover bridge.
//!
//! Exercises the *stable boundary*: trait + driver + `KernelAletheBridge`
//! impl against `covalence_kernel::Kernel`. Most Alethe rules are not yet
//! wired through, so we verify two things:
//!
//!   1. Problem ingestion + `(assume ...)` succeed end-to-end on the QF_UF
//!      fixtures (sort/fun translation, kernel `assume`).
//!   2. The first `(step ...)` surfaces a `NotImplemented` error tagged
//!      with the Alethe rule name — loud, structured failure that tells
//!      the next implementer exactly which rule to wire up.

use std::path::PathBuf;

use covalence_kernel::Kernel;
use covalence_smt::{parse_alethe, parse_smtlib2};
use covalence_smt_hol::{
    AletheBridge, BridgeError, KernelAletheBridge, ingest_problem, ingest_proof,
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

// =====================================================================
// trivial-unsat — assume + assume + resolution
// =====================================================================

#[test]
fn trivial_unsat_problem_ingests() {
    let (problem, _) = load_problem_and_proof("trivial-unsat");
    let mut kernel = Kernel::new();
    let mut bridge = KernelAletheBridge::new(&mut kernel);

    ingest_problem(&mut bridge, &problem).expect("problem should ingest cleanly");
}

#[test]
fn trivial_unsat_proof_punts_on_resolution() {
    let (problem, proof) = load_problem_and_proof("trivial-unsat");
    let mut kernel = Kernel::new();
    let mut bridge = KernelAletheBridge::new(&mut kernel);

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
// cvc5-qf-uf — exercises `! :named` annotations + `not` end-to-end
// =====================================================================

#[test]
fn cvc5_qf_uf_problem_ingests() {
    let (problem, _) = load_problem_and_proof("cvc5-qf-uf");
    let mut kernel = Kernel::new();
    let mut bridge = KernelAletheBridge::new(&mut kernel);

    ingest_problem(&mut bridge, &problem).expect("QF_UF problem should ingest");
}

#[test]
fn cvc5_qf_uf_assumes_succeed_steps_punt() {
    let (problem, proof) = load_problem_and_proof("cvc5-qf-uf");
    let mut kernel = Kernel::new();
    let mut bridge = KernelAletheBridge::new(&mut kernel);

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
    let mut kernel = Kernel::new();
    let bridge = KernelAletheBridge::new(&mut kernel);
    assert_eq!(bridge.decision(), Decision::Unknown);
}

// =====================================================================
// Sort + const declarations register
// =====================================================================

#[test]
fn declare_sort_and_fun_succeed() {
    let mut kernel = Kernel::new();
    let mut bridge = KernelAletheBridge::new(&mut kernel);

    let (problem, _) = load_problem_and_proof("trivial-unsat");
    ingest_problem(&mut bridge, &problem).unwrap();

    // trivial-unsat: `(declare-const a Bool)`.
    assert!(bridge.lookup_fun("a").is_some());

    // cvc5-qf-uf declares sort `U` and constants `a`, `b`, `p`.
    let mut kernel2 = Kernel::new();
    let mut bridge2 = KernelAletheBridge::new(&mut kernel2);
    let (problem2, _) = load_problem_and_proof("cvc5-qf-uf");
    ingest_problem(&mut bridge2, &problem2).unwrap();
    assert!(bridge2.lookup_sort("U").is_some());
    assert!(bridge2.lookup_fun("a").is_some());
    assert!(bridge2.lookup_fun("b").is_some());
    assert!(bridge2.lookup_fun("p").is_some());
}

// =====================================================================
// Direct step call — bridge punts with NotImplemented
// =====================================================================

#[test]
fn assume_then_unknown_rule_step() {
    use covalence_sexp::{SExp, SExpr};

    let mut kernel = Kernel::new();
    let mut bridge = KernelAletheBridge::new(&mut kernel);

    bridge
        .declare_fun("p", &[], &SExp::symbol("Bool"))
        .unwrap();
    let p_term: SExpr = SExp::symbol("p");
    let thm = bridge.assume("h1", &p_term).unwrap();

    let err = bridge
        .step("t1", &[], "totally-made-up-rule", &[thm], &[], &[])
        .expect_err("every rule is currently NotImplemented");
    assert!(matches!(err, BridgeError::NotImplemented(_)));
}
