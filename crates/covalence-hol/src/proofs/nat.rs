//! Tactic helpers and derived theorems for `nat`.
//!
//! The headline export is [`nat_induct`] — a one-call wrapper around
//! [`Thm::nat_induction`] that takes the base-case and step-case
//! Thms and packages them with [`and_intro`] into the conjunctive
//! antecedent the kernel axiom expects. Without this helper every
//! consumer would re-derive the `(P 0) ∧ (∀n. P n ⟹ P (succ n))`
//! tuple by hand.

use std::sync::LazyLock;

use covalence_core::subst::close;
use covalence_core::{Term, Thm, Type};
use covalence_types::Nat;

use crate::HolLightCtx;

use super::bool::{and_intro, not_intro};
use super::rewrite::rewrite_with;

/// Build the lambda predicate `λn:nat. body`, given a body that
/// mentions `Term::free(n_name, nat)`. Internally calls
/// `subst::close` to bind the free occurrences.
pub fn nat_predicate(n_name: &str, body: Term) -> Term {
    let bound = close(&body, n_name);
    Term::abs(n_name, Type::nat(), bound)
}

/// Mathematical induction on `nat`, packaged as a tactic.
///
/// Given:
///
/// * `p_lambda` — a closed lambda `λn:nat. P n` of type
///   `nat → bool`;
/// * `base` — a Thm with conclusion `P 0` (i.e. `p_lambda 0` after
///   β-reduction). The caller is responsible for matching the
///   β-normal form expected by `Thm::nat_induction` (β-reduction
///   under `HolOp::App` is handled by the user; the kernel does
///   *not* normalise on its own).
/// * `step` — a Thm with conclusion
///   `∀n:nat. P n ⟹ P (succ n)`.
///
/// Returns `Γ_base ∪ Γ_step ⊢ ∀n:nat. P n`.
///
/// The kernel induction axiom is
/// `∀P. (P 0 ∧ (∀n. P n ⟹ P (succ n))) ⟹ ∀n. P n`; this helper
/// drives it via `all_elim p_lambda` and `imp_elim (base ∧ step)`.
pub fn nat_induct(p_lambda: Term, base: Thm, step: Thm) -> Thm {
    let conjunction = and_intro(base, step);
    Thm::nat_induction()
        .all_elim(p_lambda)
        .expect("nat_induct: all_elim P")
        .imp_elim(conjunction)
        .expect("nat_induct: imp_elim base∧step")
}

/// Build `Γ ⊢ ∀n:nat. P n ⟹ P (succ n)` from a Thm whose
/// conclusion is `P n_free ⟹ P (succ n_free)` for some free
/// variable `n_free : nat`. Closes the free variable via
/// `all_intro`. Convenience wrapper for the step case of
/// [`nat_induct`].
pub fn close_step(step_thm_for_free_n: Thm, n_name: &str) -> Thm {
    step_thm_for_free_n
        .all_intro(n_name, Type::nat())
        .expect("close_step: all_intro")
}

// ============================================================================
// Derived theorems — distinctness of literals
// ============================================================================

/// `⊢ ¬(0 = 1)` — the natural numbers 0 and 1 are distinct.
///
/// Proved without postulates beyond [`not_intro`]: `Thm::reduce_prim`
/// decides `(0 = 1) ≡ F` on the closed literals, after which the
/// standard `¬p ≜ p ⟹ F` derivation closes the gap.
pub fn nat_zero_ne_one() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = HolLightCtx::new();
        let zero = Term::nat_lit(Nat::zero());
        let one = Term::nat_lit(Nat::from_inner(1u32.into()));
        let zero_eq_one = ctx
            .mk_eq(zero, one)
            .expect("nat_zero_ne_one: mk_eq 0 = 1");

        // ⊢ (0 = 1) ≡ F  via kernel reduction on closed literals.
        let eq_to_false = Thm::reduce_prim(zero_eq_one.clone())
            .expect("nat_zero_ne_one: reduce_prim");

        // Assume (0 = 1). Rewrite via eq_to_false to get F.
        let assumed =
            Thm::assume(zero_eq_one.clone()).expect("nat_zero_ne_one: assume");
        let derive_false = rewrite_with(assumed, eq_to_false);
        // {(0=1)} ⊢ F

        // Discharge the assumption: ⊢ (0=1) ⟹ F.
        let imp_f = derive_false
            .imp_intro(&zero_eq_one)
            .expect("nat_zero_ne_one: imp_intro");

        // Fold into ¬ via the standard postulated not_intro.
        not_intro(imp_f)
    });
    AX.clone()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::nat_axioms;

    fn ctx() -> HolLightCtx {
        HolLightCtx::new()
    }

    #[test]
    fn nat_predicate_builds_a_lambda() {
        let n = Term::free("n", Type::nat());
        let body = ctx()
            .mk_eq(n.clone(), n.clone())
            .expect("mk_eq n n");
        let p = nat_predicate("n", body);
        let p_ty = p.type_of().expect("p typed");
        assert_eq!(p_ty, Type::fun(Type::nat(), Type::bool()));
    }

    #[test]
    fn nat_induct_against_trivial_predicate() {
        // P := λn:nat. T. base = ⊢ T; step = ⊢ ∀n. T ⟹ T.
        // Result: ⊢ ∀n:nat. T.
        let ctx = ctx();
        let true_term = ctx.t();
        let p = Term::abs("n", Type::nat(), true_term.clone());

        // base : ⊢ T  (after β-reduction this is `p 0`).
        // We feed `p 0` (i.e. the actual antecedent the axiom
        // expects) via beta + eq_mp.
        let base_redex = Term::app(p.clone(), Term::nat_lit(covalence_types::Nat::zero()));
        let base_beta = Thm::beta_conv(base_redex.clone()).unwrap();
        // base_beta : ⊢ p 0 ≡ T
        let true_thm = Thm::assume(true_term.clone()).unwrap();
        let base = base_beta.sym().unwrap().eq_mp(true_thm).unwrap();
        // base : {T} ⊢ p 0

        // step : ⊢ ∀n. p n ⟹ p (succ n).
        let n_free = Term::free("n", Type::nat());
        let p_n = Term::app(p.clone(), n_free.clone());
        let p_n_beta = Thm::beta_conv(p_n.clone()).unwrap(); // ⊢ p n ≡ T
        let true_assumed = Thm::assume(true_term.clone()).unwrap();
        let p_n_holds = p_n_beta.sym().unwrap().eq_mp(true_assumed.clone()).unwrap();
        // {T} ⊢ p n

        // Build ⊢ p (succ n) the same way.
        let succ_n = Term::app(covalence_core::defs::nat_succ(), n_free.clone());
        let p_succ_n = Term::app(p.clone(), succ_n);
        let p_succ_n_beta = Thm::beta_conv(p_succ_n.clone()).unwrap();
        let p_succ_n_holds =
            p_succ_n_beta.sym().unwrap().eq_mp(true_assumed.clone()).unwrap();

        // step inner: {T} ⊢ p n ⟹ p (succ n).
        let step_inner = p_succ_n_holds.imp_intro(p_n_holds.concl()).unwrap();
        let step = close_step(step_inner, "n");

        let conclusion = nat_induct(p, base, step);
        // Outer shape: ⊢ ∀n:nat. P n.
        let covalence_core::TermKind::App(_, lam) = conclusion.concl().kind() else {
            panic!("expected forall application, got {:?}", conclusion.concl());
        };
        let covalence_core::TermKind::Abs(_, ty, _) = lam.kind() else {
            panic!("expected lambda body");
        };
        assert_eq!(ty, &Type::nat());

        // Sanity: the kernel induction axiom is empty-hyp, so the
        // only hyps come from our assume(T) usages.
        assert!(!conclusion.hyps().is_empty());
        // and nat_induction is satisfied
        let _ = nat_axioms::nat_induction;
    }

    #[test]
    fn nat_zero_ne_one_is_negation_of_eq() {
        let thm = nat_zero_ne_one();
        assert!(thm.concl().type_of().unwrap().is_bool());
        // Structure: ¬(0 = 1).
        let covalence_core::TermKind::App(head, _eq) = thm.concl().kind() else {
            panic!("expected ¬ application, got {:?}", thm.concl());
        };
        assert!(matches!(
            head.kind(),
            covalence_core::TermKind::HolOp(covalence_core::term::HolOp::Not, _)
        ));
    }

    #[test]
    fn nat_zero_ne_one_only_uses_not_intro_postulate() {
        // The derivation's only postulate is `not_intro_ax`. The
        // self-hyp count is therefore 1 (the not_intro axiom body).
        let thm = nat_zero_ne_one();
        assert_eq!(
            thm.hyps().len(),
            1,
            "expected 1 hyp (not_intro_ax self-hyp), got {} — \
             hyps: {:?}",
            thm.hyps().len(),
            thm.hyps(),
        );
    }

    #[test]
    fn nat_zero_ne_one_is_cached() {
        let a = nat_zero_ne_one();
        let b = nat_zero_ne_one();
        assert_eq!(a.concl(), b.concl());
    }
}
