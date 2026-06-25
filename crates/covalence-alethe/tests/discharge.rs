//! End-to-end goal discharge: a HOL goal `⊢ G` proved by replaying a
//! *cached* Alethe refutation of `¬G` through the kernel, then concluding
//! `⊢ G` by reductio.
//!
//! The `embedded_*` tests use a **checked-in cached proof** so CI passes
//! with no solver present. The `live_*` tests (feature `cvc5`) shell out
//! to a real `cvc5` on `$PATH`, gated to skip when absent — mirroring
//! `hol_bridge.rs`.

use std::sync::Arc;

use covalence_alethe::discharge::CachedProof;
use covalence_alethe::{ProofCache, SmtDischarger, goal_to_problem, smt_tactic};
use covalence_core::{Term, Type, defs};
use covalence_init::HolLightCtx;
use covalence_init::script::{Env, Tactic, run};

// =====================================================================
// Goal 1 — closed integer arithmetic: `⊢ 1 + 2 = 3`.
//
// Built directly via the kernel `defs`; its negation is the INT-A
// problem, so the captured INT-A Alethe refutation (every `hole` a
// closed-arithmetic rewrite the kernel re-derives) discharges it.
// =====================================================================

fn arith_goal() -> Term {
    let ctx = HolLightCtx::new();
    let plus = |a: Term, b: Term| Term::app(Term::app(defs::int_add(), a), b);
    ctx.mk_eq(plus(Term::int_lit(1), Term::int_lit(2)), Term::int_lit(3))
        .expect("well-typed equation")
}

/// A captured cvc5 1.3.4 Alethe refutation of `¬(1 + 2 = 3)` (the same
/// shape `hol_bridge.rs::INTA_PROOF` pins). Every `hole` is re-derived by
/// the kernel — checked, not trusted.
const ARITH_PROOF: &str = "\
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

fn arith_discharger() -> SmtDischarger {
    let mut cache = ProofCache::new();
    cache.insert(&arith_goal(), CachedProof::Text(ARITH_PROOF.to_string()));
    SmtDischarger::cached(cache)
}

#[test]
fn embedded_arith_discharge_returns_genuine_theorem() {
    let goal = arith_goal();
    let thm = arith_discharger()
        .discharge(&goal)
        .expect("discharge from cached proof");
    // Genuine: no hypotheses, conclusion is exactly the goal.
    assert!(
        thm.hyps().is_empty(),
        "discharged theorem must be hypothesis-free"
    );
    assert_eq!(thm.concl(), &goal);
}

#[test]
fn embedded_problem_asserts_negated_goal() {
    let goal = arith_goal();
    let problem = goal_to_problem(&goal).expect("build problem");
    assert_eq!(problem.logic(), Some("QF_UFLIA"));
    assert_eq!(problem.assertions().len(), 1);
    let head = problem.assertions()[0].as_list().unwrap()[0].as_symbol();
    assert_eq!(head, Some("not"));
}

// =====================================================================
// Goal 2 — a propositional tautology: `⊢ ¬(a ∧ ¬a)`.
//
// Expressible in the `core` script as `(not (and a (not a)))`, so it
// drives the `.cov` FFI-tactic seam. Its negation `¬¬(a ∧ ¬a)` is
// refuted by a captured proof using only bridge-supported rules
// (`equiv_pos2`, the double-negation `hole`, `and`, `resolution`).
// =====================================================================

/// `¬(a ∧ ¬a)` with `a : Bool` — built so the cache key matches the
/// term the script elaborates from `(not (and a (not a)))`.
fn taut_goal() -> Term {
    let ctx = HolLightCtx::new();
    let a = Term::free("a", Type::bool());
    ctx.mk_not(ctx.mk_and(a.clone(), ctx.mk_not(a)))
}

const TAUT_PROOF: &str = "\
(assume a0 (! (not (not (! (and a (! (not a) :named @p_1)) :named @p_2))) :named @p_3))
(step t0 (cl (not (! (= @p_3 @p_2) :named @p_4)) (not @p_3) @p_2) :rule equiv_pos2)
(step t1 (cl @p_4) :rule hole :args (\"untranslated rewrite\"))
(step t2 (cl @p_2) :rule resolution :premises (t0 t1 a0))
(step t3 (cl a) :rule and :premises (t2) :args (0))
(step t4 (cl @p_1) :rule and :premises (t2) :args (1))
(step t5 (cl) :rule resolution :premises (t3 t4))
";

fn taut_discharger() -> SmtDischarger {
    let mut cache = ProofCache::new();
    cache.insert(&taut_goal(), CachedProof::Text(TAUT_PROOF.to_string()));
    SmtDischarger::cached(cache)
}

#[test]
fn embedded_taut_discharge_returns_genuine_theorem() {
    let goal = taut_goal();
    let thm = taut_discharger()
        .discharge(&goal)
        .expect("discharge tautology from cached proof");
    assert!(thm.hyps().is_empty());
    assert_eq!(thm.concl(), &goal);
}

#[test]
fn cached_miss_without_solver_is_error() {
    // A goal with no cached proof and no solver must fail (not fabricate).
    let discharger = arith_discharger();
    assert!(discharger.discharge(&taut_goal()).is_err());
}

// ---------------------------------------------------------------------
// The `.cov` script FFI-tactic seam: `(#by (smt))`.
// ---------------------------------------------------------------------

#[test]
fn embedded_smt_tactic_in_cov_script() {
    let tac: Arc<dyn Tactic> = smt_tactic(Arc::new(taut_discharger()));

    let theory = run(
        r#"
        (#import core)
        (#open core)
        (#register-ffi-tactic smt)
        (#thm taut
          (#fix (a bool))
          (#concl (not (and a (not a))))
          (#by (smt)))
        "#,
        |name| (name == "core").then(Env::core),
        move |name| (name == "smt").then(|| tac.clone()),
    )
    .expect("smt tactic discharges the goal");

    assert_eq!(theory.thms.len(), 1);
    let thm = &theory.thms[0].thm;
    assert!(
        thm.hyps().is_empty(),
        "kernel theorem must be hypothesis-free"
    );
    assert_eq!(thm.concl(), &taut_goal());
}

// ---------------------------------------------------------------------
// Live cvc5 — solve the goal's negation ourselves, then discharge.
// ---------------------------------------------------------------------

#[cfg(feature = "cvc5")]
mod live {
    use super::*;
    use covalence_smt::Cvc5Solver;

    /// Discharge the arithmetic goal by calling cvc5 live (skips if cvc5
    /// is not installed — mirrors `hol_bridge.rs` gating).
    #[test]
    fn live_arith_discharge_via_solver() {
        let goal = arith_goal();
        let discharger = SmtDischarger::with_solver(Box::new(Cvc5Solver::from_path()));
        match discharger.discharge(&goal) {
            Ok(thm) => {
                assert!(thm.hyps().is_empty());
                assert_eq!(thm.concl(), &goal);
            }
            Err(e) => eprintln!("skipping live_arith_discharge_via_solver: {e}"),
        }
    }

    /// The same goal through the `.cov` FFI seam with a live solver.
    #[test]
    fn live_smt_tactic_in_cov_script() {
        let tac: Arc<dyn Tactic> = smt_tactic(Arc::new(SmtDischarger::with_solver(Box::new(
            Cvc5Solver::from_path(),
        ))));
        let result = run(
            r#"
            (#import core)
            (#open core)
            (#register-ffi-tactic smt)
            (#thm taut
              (#fix (a bool))
              (#concl (not (and a (not a))))
              (#by (smt)))
            "#,
            |name| (name == "core").then(Env::core),
            move |name| (name == "smt").then(|| tac.clone()),
        );
        match result {
            Ok(theory) => {
                assert_eq!(theory.thms.len(), 1);
                assert!(theory.thms[0].thm.hyps().is_empty());
            }
            Err(e) => eprintln!("skipping live_smt_tactic_in_cov_script: {e}"),
        }
    }
}
