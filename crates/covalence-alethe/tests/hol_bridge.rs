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

#[test]
fn untranslated_hole_is_reported_not_silently_trusted() {
    // cvc5 emits `hole` for rewrites it cannot express in Alethe. We must
    // refuse it (NotImplemented), never wave it through.
    let proof = "\
(assume a0 (= a b))
(step t1 (cl (= b b)) :rule hole :args (\"untranslated rewrite\"))
";
    let problem = parse_smtlib2(UF1_PROBLEM).unwrap();
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
}
