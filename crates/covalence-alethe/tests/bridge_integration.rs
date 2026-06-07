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

use covalence_alethe::{
    AletheBridge, BridgeError, KernelAletheBridge, ingest_problem, ingest_proof,
};
use covalence_kernel::Kernel;
use covalence_smt::{parse_alethe, parse_smtlib2};
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
fn trivial_unsat_proof_closes() {
    let (problem, proof) = load_problem_and_proof("trivial-unsat");
    let mut kernel = Kernel::new();
    let mut bridge = KernelAletheBridge::new(&mut kernel);

    ingest_problem(&mut bridge, &problem).unwrap();
    ingest_proof(&mut bridge, &proof).expect("trivial-unsat proof should close");
    assert_eq!(bridge.decision(), Decision::Unsat);
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
fn cvc5_qf_uf_proof_closes() {
    let (problem, proof) = load_problem_and_proof("cvc5-qf-uf");
    let mut kernel = Kernel::new();
    let mut bridge = KernelAletheBridge::new(&mut kernel);

    ingest_problem(&mut bridge, &problem).unwrap();
    ingest_proof(&mut bridge, &proof).expect("cvc5-qf-uf proof should close");
    assert_eq!(bridge.decision(), Decision::Unsat);
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

    bridge.declare_fun("p", &[], &SExp::symbol("Bool")).unwrap();
    let p_term: SExpr = SExp::symbol("p");
    let thm = bridge.assume("h1", &p_term).unwrap();

    let err = bridge
        .step("t1", &[], "totally-made-up-rule", &[thm], &[], &[])
        .expect_err("every rule is currently NotImplemented");
    assert!(matches!(err, BridgeError::NotImplemented(_)));
}

// =====================================================================
// cvc5-uflia-simple — LIA term ingestion + refl/trans rule handlers
// =====================================================================

#[test]
fn cvc5_uflia_simple_problem_ingests() {
    let (problem, _) = load_problem_and_proof("cvc5-uflia-simple");
    let mut kernel = Kernel::new();
    let mut bridge = KernelAletheBridge::new(&mut kernel);

    ingest_problem(&mut bridge, &problem).expect("QF_UFLIA problem should ingest");
    assert!(bridge.lookup_fun("f").is_some());
    assert!(bridge.lookup_fun("x").is_some());
}

#[test]
fn refl_step_succeeds() {
    use covalence_sexp::SExp;

    let mut kernel = Kernel::new();
    let mut bridge = KernelAletheBridge::new(&mut kernel);
    bridge.declare_fun("x", &[], &SExp::symbol("Int")).unwrap();

    // `(step t1 (cl (= x x)) :rule refl)`
    let clause = vec![SExp::List(vec![
        SExp::symbol("="),
        SExp::symbol("x"),
        SExp::symbol("x"),
    ])];
    let thm = bridge
        .step("t1", &clause, "refl", &[], &[], &[])
        .expect("refl should succeed");
    // Sanity: a Thm exists; we don't inspect its contents (kernel-internal).
    let _ = thm;
}

#[test]
fn trans_step_chains() {
    use covalence_sexp::SExp;

    let mut kernel = Kernel::new();
    let mut bridge = KernelAletheBridge::new(&mut kernel);
    bridge.declare_fun("x", &[], &SExp::symbol("Int")).unwrap();

    let eq_xx = SExp::List(vec![
        SExp::symbol("="),
        SExp::symbol("x"),
        SExp::symbol("x"),
    ]);

    // One refl: `x = x`. Chain it with *itself* via trans — midpoint is
    // structurally identical, so the kernel's UF-level-0 check is happy.
    let xx = bridge
        .step("t0", std::slice::from_ref(&eq_xx), "refl", &[], &[], &[])
        .unwrap();
    let _chained = bridge
        .step(
            "t1",
            std::slice::from_ref(&eq_xx),
            "trans",
            &[xx.clone(), xx],
            &[],
            &[],
        )
        .expect("trans of refl with itself should chain");
}

#[test]
fn cong_step_closes_function_equality() {
    use covalence_sexp::SExp;

    // Setup: `f : Int -> Int`, `x : Int`. Premise `(= x 0)` → derive
    // `(= (f x) (f 0))` via cong.
    let mut kernel = Kernel::new();
    let mut bridge = KernelAletheBridge::new(&mut kernel);
    bridge
        .declare_fun("f", &[SExp::symbol("Int")], &SExp::symbol("Int"))
        .unwrap();
    bridge.declare_fun("x", &[], &SExp::symbol("Int")).unwrap();

    let eq_x0 = SExp::List(vec![
        SExp::symbol("="),
        SExp::symbol("x"),
        SExp::symbol("0"),
    ]);
    let prem = bridge.assume("a0", &eq_x0).unwrap();

    let fx_eq_f0 = SExp::List(vec![
        SExp::symbol("="),
        SExp::List(vec![SExp::symbol("f"), SExp::symbol("x")]),
        SExp::List(vec![SExp::symbol("f"), SExp::symbol("0")]),
    ]);
    let _ = bridge
        .step(
            "t1",
            std::slice::from_ref(&fx_eq_f0),
            "cong",
            &[prem],
            &[],
            &[],
        )
        .expect("cong over `x = 0` should close `f x = f 0`");
}

#[test]
fn hole_trust_theory_rewrite_succeeds() {
    use covalence_sexp::{SExp, parse_smt};

    // `(step ... (cl (= x y)) :rule hole :args ("TRUST_THEORY_REWRITE" …))`
    // The args list models cvc5's emission: a quoted string tag plus
    // some opaque metadata we ignore.
    let mut kernel = Kernel::new();
    let mut bridge = KernelAletheBridge::new(&mut kernel);
    bridge.declare_fun("x", &[], &SExp::symbol("Int")).unwrap();
    bridge.declare_fun("y", &[], &SExp::symbol("Int")).unwrap();

    let clause = vec![SExp::List(vec![
        SExp::symbol("="),
        SExp::symbol("x"),
        SExp::symbol("y"),
    ])];
    let args =
        parse_smt(r#""TRUST_THEORY_REWRITE" foo 3 6"#).expect("SMT-LIB string literal parses");
    let _ = bridge
        .step("t0", &clause, "hole", &[], &args, &[])
        .expect("hole TRUST_THEORY_REWRITE should accept the equality");
}

#[test]
fn hole_unknown_tag_still_punts() {
    use covalence_sexp::{SExp, parse_smt};

    let mut kernel = Kernel::new();
    let mut bridge = KernelAletheBridge::new(&mut kernel);
    bridge.declare_fun("x", &[], &SExp::symbol("Int")).unwrap();

    let clause = vec![SExp::List(vec![
        SExp::symbol("="),
        SExp::symbol("x"),
        SExp::symbol("x"),
    ])];
    let args = parse_smt(r#""SOME_OTHER_TRUST""#).unwrap();
    let err = bridge
        .step("t0", &clause, "hole", &[], &args, &[])
        .expect_err("unknown hole variety should punt");
    assert!(matches!(err, BridgeError::NotImplemented(_)));
}

#[test]
fn cvc5_uflia_simple_proof_closes() {
    let (problem, proof) = load_problem_and_proof("cvc5-uflia-simple");
    let mut kernel = Kernel::new();
    let mut bridge = KernelAletheBridge::new(&mut kernel);

    ingest_problem(&mut bridge, &problem).unwrap();
    ingest_proof(&mut bridge, &proof).expect("UFLIA proof should close");
    assert_eq!(bridge.decision(), Decision::Unsat);
}
