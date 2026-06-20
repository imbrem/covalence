//! End-to-end checks of [`HolAletheBridge`]: an SMT-LIB problem + its
//! Alethe proof go in, a kernel-verified [`Decision`] comes out.
//!
//! The `embedded_*` tests pin exact cvc5 output (captured from
//! `cvc5 1.3.4 --dump-proofs --proof-format=alethe`) so they run with no
//! solver present. The `live_*` tests (feature `cvc5`) actually shell out
//! to a `cvc5` binary on `$PATH` and check the same verdict.

use covalence_alethe::error::BridgeError;
use covalence_alethe::{HolAletheBridge, ingest_alethe};
use covalence_smt::{Decision, parse_alethe, parse_smtlib2};

/// Parse a problem + proof and run them through a fresh bridge.
fn check(problem_smt: &str, proof_alethe: &str) -> Decision {
    let problem = parse_smtlib2(problem_smt).expect("parse problem");
    let proof = parse_alethe(proof_alethe).expect("parse proof");
    let mut bridge = HolAletheBridge::new();
    ingest_alethe(&mut bridge, &problem, &proof).expect("ingest")
}

// ---------------------------------------------------------------------
// P1 — pure propositional resolution: `a` and `¬a`.
// ---------------------------------------------------------------------

const P1_PROBLEM: &str = "\
(set-logic QF_UF)
(declare-const a Bool)
(assert a)
(assert (not a))
";

const P1_PROOF: &str = "\
(assume a0 a)
(assume a1 (! (not a) :named @p_1))
(step t0 (cl) :rule resolution :premises (a0 a1))
";

#[test]
fn embedded_p1_propositional_resolution() {
    assert_eq!(check(P1_PROBLEM, P1_PROOF), Decision::Unsat);
}

// ---------------------------------------------------------------------
// UF1 — uninterpreted functions: `a = b`, `p a`, `¬(p b)`.
// Exercises cong, equiv_pos2, and chained resolution.
// ---------------------------------------------------------------------

const UF1_PROBLEM: &str = "\
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun p (U) Bool)
(assert (= a b))
(assert (p a))
(assert (not (p b)))
";

const UF1_PROOF: &str = "\
(assume a0 (! (= a b) :named @p_1))
(assume a1 (! (p a) :named @p_2))
(assume a2 (! (not (! (p b) :named @p_3)) :named @p_4))
(step t0 (cl (not (! (= @p_2 @p_3) :named @p_5)) (not @p_2) @p_3) :rule equiv_pos2)
(step t1 (cl @p_5) :rule cong :premises (a0))
(step t2 (cl @p_3) :rule resolution :premises (t0 t1 a1))
(step t3 (cl) :rule resolution :premises (a2 t2))
";

#[test]
fn embedded_uf1_congruence() {
    assert_eq!(check(UF1_PROBLEM, UF1_PROOF), Decision::Unsat);
}

// ---------------------------------------------------------------------
// Negative: a proof that never reaches the empty clause stays Unknown.
// ---------------------------------------------------------------------

#[test]
fn unfinished_proof_is_unknown() {
    // A real congruence step over the UF1 signature, but no empty clause
    // is ever derived — so the verdict must stay Unknown, not Unsat.
    let proof = "\
(assume a0 (= a b))
(step t1 (cl (= (p a) (p b))) :rule cong :premises (a0))
";
    assert_eq!(check(UF1_PROBLEM, proof), Decision::Unknown);
}

// ---------------------------------------------------------------------
// INT-A — closed integer arithmetic: ¬(1 + 2 = 3). The `hole` steps
// (1+2=3, 3=3=true, ¬true=false) are all re-derived in the kernel.
// ---------------------------------------------------------------------

const INTA_PROBLEM: &str = "\
(set-logic QF_LIA)
(assert (not (= (+ 1 2) 3)))
";

const INTA_PROOF: &str = "\
(assume a0 (! (not (! (= (+ 1 2) 3) :named @p_1)) :named @p_2))
(step t0 (cl (not (! (= @p_2 false) :named @p_3)) (not @p_2) false) :rule equiv_pos2)
(step t1 (cl @p_1) :rule hole :args (\"untranslated rewrite\"))
(step t2 (cl (! (= 3 3) :named @p_5)) :rule refl)
(step t3 (cl (= @p_1 @p_5)) :rule cong :premises (t1 t2))
(step t4 (cl (= @p_5 true)) :rule hole :args (\"untranslated rewrite\"))
(step t5 (cl (= @p_1 true)) :rule trans :premises (t3 t4))
(step t6 (cl (= @p_2 (! (not true) :named @p_4))) :rule cong :premises (t5))
(step t7 (cl (= @p_4 false)) :rule hole :args (\"untranslated rewrite\"))
(step t8 (cl @p_3) :rule trans :premises (t6 t7))
(step t9 (cl false) :rule resolution :premises (t0 t8 a0))
(step t10 (cl (not false)) :rule false)
(step t11 (cl) :rule resolution :premises (t9 t10))
";

#[test]
fn embedded_inta_closed_arithmetic() {
    assert_eq!(check(INTA_PROBLEM, INTA_PROOF), Decision::Unsat);
}

// ---------------------------------------------------------------------
// IMP — the `implies` rule: (p ⟹ q), p, ¬q.
// ---------------------------------------------------------------------

const IMP_PROBLEM: &str = "\
(set-logic QF_UF)
(declare-fun p () Bool)
(declare-fun q () Bool)
(assert (=> p q))
(assert p)
(assert (not q))
";

const IMP_PROOF: &str = "\
(assume a0 (! (=> p q) :named @p_1))
(assume a1 p)
(assume a2 (! (not q) :named @p_2))
(step t0 (cl (not p) q) :rule implies :premises (a0))
(step t1 (cl q) :rule resolution :premises (t0 a1))
(step t2 (cl) :rule resolution :premises (t1 a2))
";

#[test]
fn embedded_imp_implies_rule() {
    assert_eq!(check(IMP_PROBLEM, IMP_PROOF), Decision::Unsat);
}

// ---------------------------------------------------------------------
// AND — the `and` projection rule: p = (q ∧ r), p, ¬q.
// ---------------------------------------------------------------------

const AND_PROBLEM: &str = "\
(set-logic QF_UF)
(declare-fun p () Bool)
(declare-fun q () Bool)
(declare-fun r () Bool)
(assert (= p (and q r)))
(assert p)
(assert (not q))
";

const AND_PROOF: &str = "\
(assume a0 (! (= p (! (and q r) :named @p_1)) :named @p_2))
(assume a1 p)
(assume a2 (! (not q) :named @p_3))
(step t0 (cl (not @p_2) (not p) @p_1) :rule equiv_pos2)
(step t1 (cl @p_1) :rule resolution :premises (t0 a0 a1))
(step t2 (cl q) :rule and :premises (t1) :args (0))
(step t3 (cl) :rule resolution :premises (t2 a2))
";

#[test]
fn embedded_and_projection_rule() {
    assert_eq!(check(AND_PROBLEM, AND_PROOF), Decision::Unsat);
}

#[test]
fn unrecomputable_hole_is_reported_not_silently_trusted() {
    // The recompute hook discharges closed/structural rewrites, but a
    // rewrite between two *distinct* uninterpreted terms has no shared
    // normal form — it must be refused (NotImplemented), never trusted.
    let proof = "\
(assume a0 (= a b))
(step t1 (cl (= a b)) :rule hole :args (\"untranslated rewrite\"))
";
    let problem = parse_smtlib2(UF1_PROBLEM).unwrap();
    let proof = parse_alethe(proof).unwrap();
    let mut bridge = HolAletheBridge::new();
    let err = ingest_alethe(&mut bridge, &problem, &proof).unwrap_err();
    assert!(matches!(err, BridgeError::NotImplemented(_)), "got {err:?}");
}

// ---------------------------------------------------------------------
// LA1 — the Farkas core (`la_generic`): x < 0 ∧ 0 < x ⟹ ⊥.
//
// The `la_generic` step emits the tautology clause
// `(cl (not (< x 0)) (not (< 0 x)))` with coefficients (1,1); the bridge
// re-derives `{x<0, 0<x} ⊢ F` through `int::lt_trans` + `int::lt_irrefl`
// and clausifies it. Resolution against the two assumptions closes.
// ---------------------------------------------------------------------

const LA1_PROBLEM: &str = "\
(set-logic QF_LIA)
(declare-fun x () Int)
(assert (< x 0))
(assert (< 0 x))
";

const LA1_PROOF: &str = "\
(assume a0 (< x 0))
(assume a1 (< 0 x))
(step t0 (cl (not (< x 0)) (not (< 0 x))) :rule la_generic :args (1 1))
(step t1 (cl (not (< 0 x))) :rule resolution :premises (t0 a0))
(step t2 (cl) :rule resolution :premises (t1 a1))
";

#[test]
fn embedded_la1_farkas_two_literal() {
    assert_eq!(check(LA1_PROBLEM, LA1_PROOF), Decision::Unsat);
}

#[test]
fn la_generic_rejects_non_contradictory_pair() {
    // `x < 0` and `0 < y` do NOT chain — the Farkas check must refuse
    // (NotImplemented), never fabricate a refutation.
    let problem = "\
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (< x 0))
(assert (< 0 y))
";
    let proof = "\
(assume a0 (< x 0))
(assume a1 (< 0 y))
(step t0 (cl (not (< x 0)) (not (< 0 y))) :rule la_generic :args (1 1))
";
    let problem = parse_smtlib2(problem).unwrap();
    let proof = parse_alethe(proof).unwrap();
    let mut bridge = HolAletheBridge::new();
    let err = ingest_alethe(&mut bridge, &problem, &proof).unwrap_err();
    assert!(matches!(err, BridgeError::NotImplemented(_)), "got {err:?}");
}

// ---------------------------------------------------------------------
// Live cvc5 — generate the proof ourselves and check it.
// ---------------------------------------------------------------------

#[cfg(feature = "cvc5")]
mod live {
    use super::*;
    use covalence_smt::{Cvc5Solver, SmtSolver};

    fn solve_and_check(problem_smt: &str) -> Decision {
        let problem = parse_smtlib2(problem_smt).expect("parse problem");
        let proof = Cvc5Solver::from_path()
            .solve(&problem)
            .expect("cvc5 produced an Alethe proof");
        let mut bridge = HolAletheBridge::new();
        ingest_alethe(&mut bridge, &problem, &proof).expect("ingest cvc5 proof")
    }

    #[test]
    fn live_p1() {
        assert_eq!(solve_and_check(P1_PROBLEM), Decision::Unsat);
    }

    #[test]
    fn live_uf1() {
        assert_eq!(solve_and_check(UF1_PROBLEM), Decision::Unsat);
    }

    #[test]
    fn live_inta_closed_arithmetic() {
        // cvc5's real proof of ¬(1+2=3) leans entirely on `hole` rewrites
        // that are closed arithmetic — our recompute hook discharges them.
        assert_eq!(solve_and_check(INTA_PROBLEM), Decision::Unsat);
    }

    #[test]
    fn live_imp() {
        assert_eq!(solve_and_check(IMP_PROBLEM), Decision::Unsat);
    }

    #[test]
    fn live_and() {
        assert_eq!(solve_and_check(AND_PROBLEM), Decision::Unsat);
    }

    /// ¬¬p, ¬p — cvc5 discharges the double-negation via a `(¬¬p = p)`
    /// hole, which `simp` re-derives.
    #[test]
    fn live_double_negation() {
        let problem = "\
(set-logic QF_UF)
(declare-fun p () Bool)
(assert (not (not p)))
(assert (not p))
";
        assert_eq!(solve_and_check(problem), Decision::Unsat);
    }
}
