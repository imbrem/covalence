//! Peano proofs for `Type::nat()`.
//!
//! Provides bona-fide *proofs* of the classical Peano axioms, built
//! from more primitive kernel facts. Every proved theorem has empty
//! hypotheses (no `Thm::assume` audit trail).
//!
//! Surface form: each proof produces a Pure-meta-quantified theorem,
//! e.g.
//!
//! ```text
//! ⊢ ⋀m n:nat. Trueprop ((succ m = succ n) ⟹ (m = n))
//! ```
//!
//! rather than the fully-HOL-wrapped form
//! `⊢ Trueprop (∀m n:nat. ...)`. Both shapes carry the same content;
//! converting the outermost `⋀` to HOL `∀` requires
//! [`Thm::forall_reflection`] specialised at a lambda predicate, which
//! callers can do downstream when needed.

use covalence_core::{Arith, Prim, Term, Thm, Type};

use crate::HolLightCtx;
use crate::bridge::{hol_eq_from_pure_eq, lift_imp_to_hol, pure_eq_from_hol_eq};

// ============================================================================
// Helpers
// ============================================================================

fn nat_ty() -> Type {
    Type::nat()
}

fn succ_fn() -> Term {
    Term::prim(Prim::NatArith(Arith::Succ))
}

fn succ(t: Term) -> Term {
    Term::app(succ_fn(), t)
}

fn pred_fn() -> Term {
    Term::prim(Prim::NatArith(Arith::Pred))
}

fn pred(t: Term) -> Term {
    Term::app(pred_fn(), t)
}

fn trueprop(p: Term, ctx: &HolLightCtx) -> Term {
    ctx.mk_trueprop(p).expect("trueprop: arg is bool-typed")
}

fn hol_eq(lhs: Term, rhs: Term, ctx: &HolLightCtx) -> Term {
    ctx.mk_eq(lhs, rhs).expect("hol_eq: same-typed args")
}

// ============================================================================
// nat_succ_inj
// ============================================================================

/// `⊢ ⋀m n:nat. Trueprop ((succ m = succ n) ⟹ (m = n))`.
///
/// Strategy: assume `succ m = succ n`; apply `pred` to both sides via
/// `cong_app`; rewrite each side using `pred (succ k) = k`
/// ([`Thm::nat_pred_succ`]); conclude `m = n`. The result is
/// `Pure-imp`-bodied; we lift to HOL imp under one `Trueprop` via
/// `lift_imp_to_hol`, then universally close at `n` and `m` with
/// `all_intro` (Pure metas).
pub fn prove_nat_succ_inj() -> Thm {
    let ctx = HolLightCtx::new();
    let nat = nat_ty();
    let m = Term::free("m", nat.clone());
    let n = Term::free("n", nat.clone());

    // Kernel axiom `Thm::nat_pred_succ`:  ⋀n:nat. Trueprop (pred (succ n) = n)
    // → ⊢ Trueprop (pred (succ m) = m)
    let pred_m_hol = Thm::nat_pred_succ()
        .all_elim(m.clone())
        .expect("nat_succ_inj: all_elim m");
    // → ⊢ Trueprop (pred (succ n) = n)
    let pred_n_hol = Thm::nat_pred_succ()
        .all_elim(n.clone())
        .expect("nat_succ_inj: all_elim n");

    // Convert each to Pure meta-eq.
    let pred_m_pure = pure_eq_from_hol_eq(
        pred_m_hol,
        nat.clone(),
        pred(succ(m.clone())),
        m.clone(),
    );
    let pred_n_pure = pure_eq_from_hol_eq(
        pred_n_hol,
        nat.clone(),
        pred(succ(n.clone())),
        n.clone(),
    );

    // Assume the antecedent.
    let antecedent = trueprop(hol_eq(succ(m.clone()), succ(n.clone()), &ctx), &ctx);
    let assumed = Thm::assume(antecedent.clone()).expect("nat_succ_inj: assume");

    // → succ m ≡ succ n
    let succ_pure_eq = pure_eq_from_hol_eq(
        assumed,
        nat.clone(),
        succ(m.clone()),
        succ(n.clone()),
    );

    // → pred (succ m) ≡ pred (succ n) via cong_app
    let pred_succ_eq = Thm::refl(pred_fn())
        .expect("nat_succ_inj: refl pred_fn")
        .cong_app(succ_pure_eq)
        .expect("nat_succ_inj: cong_app pred");

    // → m ≡ n via trans
    let m_to_pred = pred_m_pure
        .sym()
        .expect("nat_succ_inj: sym pred_m_pure")
        .trans(pred_succ_eq)
        .expect("nat_succ_inj: trans (sym + cong)");
    let m_eq_n_pure = m_to_pred
        .trans(pred_n_pure)
        .expect("nat_succ_inj: trans (final)");

    // Lift back to Trueprop (m = n).
    let m_eq_n_hol = hol_eq_from_pure_eq(m_eq_n_pure, nat.clone(), m.clone(), n.clone());

    // Pure-level imp.
    let pure_imp = m_eq_n_hol
        .imp_intro(&antecedent)
        .expect("nat_succ_inj: imp_intro");

    // Lift Pure imp → Trueprop (A ⟹ B).
    let hol_imp_body = lift_imp_to_hol(
        pure_imp,
        hol_eq(succ(m.clone()), succ(n.clone()), &ctx),
        hol_eq(m.clone(), n.clone(), &ctx),
    );

    // Universally close.
    hol_imp_body
        .all_intro("n", nat.clone())
        .expect("nat_succ_inj: all_intro n")
        .all_intro("m", nat)
        .expect("nat_succ_inj: all_intro m")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn nat_succ_inj_has_empty_hyps() {
        let thm = prove_nat_succ_inj();
        assert!(
            thm.hyps().is_empty(),
            "proved Peano axiom should have empty hyps, got {} hyp(s)",
            thm.hyps().len()
        );
    }

    #[test]
    fn nat_succ_inj_concl_is_prop() {
        let thm = prove_nat_succ_inj();
        assert!(thm.concl().type_of().unwrap().is_prop());
    }

    #[test]
    fn nat_succ_inj_concl_is_correct_shape() {
        // Outer shape: ⋀m. ⋀n. Trueprop (succ m = succ n ⟹ m = n)
        let thm = prove_nat_succ_inj();
        let outer = thm.concl();
        // First binder: m
        let covalence_core::TermKind::All(_, ty1, _body1) = outer.kind() else {
            panic!("not ⋀m, got {outer:?}");
        };
        assert_eq!(ty1, &Type::nat());
    }
}
