//! Helpers and derived theorems for `nat`.
//!
//! Induction itself is now the kernel rule [`Thm::nat_induct`] — call
//! it directly with a base proof `⊢ p 0` and a step proof
//! `⊢ p n ⟹ p (succ n)` (free `n`), no packaging required. The
//! helpers here build the motive ([`nat_predicate`]) and the
//! distinctness theorem [`nat_zero_ne_one`].

use std::sync::LazyLock;

use covalence_core::subst::close;
use covalence_core::{Term, Thm, Type};
use covalence_types::Nat;

use crate::HolLightCtx;

use super::rewrite::rewrite_with;

/// Build the lambda predicate `λn:nat. body`, given a body that
/// mentions `Term::free(n_name, nat)`. Internally calls
/// `subst::close` to bind the free occurrences.
pub fn nat_predicate(n_name: &str, body: Term) -> Term {
    let bound = close(&body, n_name);
    Term::abs(n_name, Type::nat(), bound)
}

// ============================================================================
// Derived theorems — distinctness of literals
// ============================================================================

/// `⊢ ¬(0 = 1)` — the natural numbers 0 and 1 are distinct.
///
/// **Fully derived, zero hypotheses.** `Thm::reduce_prim` decides
/// `(0 = 1) ≡ F` on the closed literals; assuming `0 = 1` and
/// rewriting yields `{0=1} ⊢ F`; `imp_intro` discharges to
/// `⊢ (0=1) ⟹ F`; and the (now also derived) [`Thm::not_intro`] folds it
/// into `⊢ ¬(0=1)`. No postulate anywhere in the chain.
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

        // Fold into ¬ via the derived not-introduction kernel method.
        imp_f.not_intro().expect("nat_zero_ne_one: not_intro")
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
        // P := λn:nat. T. base = ⊢ p 0; step = ⊢ p n ⟹ p (succ n).
        // The kernel rule reads back P and n from the shapes and
        // returns ⊢ ∀n:nat. p n.
        let true_term = ctx().t();
        let p = Term::abs("n", Type::nat(), true_term.clone());

        // base : {T} ⊢ p 0  (in the applied `p 0` shape the rule wants)
        let base_redex = Term::app(p.clone(), Term::nat_lit(Nat::zero()));
        let base = Thm::beta_conv(base_redex)
            .unwrap()
            .sym()
            .unwrap()
            .eq_mp(Thm::assume(true_term.clone()).unwrap())
            .unwrap();

        // step : {T} ⊢ p n ⟹ p (succ n)  (free n, NOT generalised)
        let n_free = Term::free("n", Type::nat());
        let true_assumed = Thm::assume(true_term.clone()).unwrap();
        let p_n_holds = Thm::beta_conv(Term::app(p.clone(), n_free.clone()))
            .unwrap()
            .sym()
            .unwrap()
            .eq_mp(true_assumed.clone())
            .unwrap();
        let succ_n = Term::app(covalence_core::defs::nat_succ(), n_free);
        let p_succ_n_holds = Thm::beta_conv(Term::app(p.clone(), succ_n))
            .unwrap()
            .sym()
            .unwrap()
            .eq_mp(true_assumed)
            .unwrap();
        let step = p_succ_n_holds.imp_intro(p_n_holds.concl()).unwrap();

        let conclusion = Thm::nat_induct(base, step).unwrap();
        // Outer shape: ⊢ ∀n:nat. p n.
        let covalence_core::TermKind::App(_, lam) = conclusion.concl().kind() else {
            panic!("expected forall application, got {:?}", conclusion.concl());
        };
        let covalence_core::TermKind::Abs(_, ty, _) = lam.kind() else {
            panic!("expected lambda body");
        };
        assert_eq!(ty, &Type::nat());

        // The rule unions base/step hyps, so the `assume(T)`
        // scaffolding propagates: `{T} ⊢ ∀n:nat. p n`.
        assert!(!conclusion.hyps().is_empty());
        // and the derived axiom form is available
        let _ = nat_axioms::nat_induction;
    }

    #[test]
    fn nat_zero_ne_one_is_negation_of_eq() {
        let thm = nat_zero_ne_one();
        assert!(thm.concl().type_of().unwrap().is_bool());
        // Structure: ¬(0 = 1) — `not` connective spec applied to the
        // equation.
        let covalence_core::TermKind::App(head, _eq) = thm.concl().kind() else {
            panic!("expected ¬ application, got {:?}", thm.concl());
        };
        let covalence_core::TermKind::Spec(h, _) = head.kind() else {
            panic!("expected `not` spec head, got {:?}", head);
        };
        assert!(h.ptr_eq(&covalence_core::defs::not_spec()));
    }

    #[test]
    fn nat_zero_ne_one_is_axiom_free() {
        // The connective rules are now derived, not postulated, so the
        // whole `¬(0=1)` derivation is hypothesis-free.
        let thm = nat_zero_ne_one();
        assert!(
            thm.hyps().is_empty(),
            "expected 0 hyps (fully derived), got {} — hyps: {:?}",
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
