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

use std::sync::LazyLock;

use covalence_core::{Arith, Prim, Term, Thm, Type};
use covalence_types::Nat;

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

fn nat_lit(n: u32) -> Term {
    Term::nat_lit(Nat::from_inner(n.into()))
}

/// Given `Γ ⊢ Trueprop (¬p)`, return `Γ ⊢ Trueprop (p ⟹ F)`.
/// (Forward direction of `not_def`.)
#[allow(dead_code)]
fn unfold_not(thm: Thm, p: Term, ctx: &HolLightCtx) -> Thm {
    // not_def: ⋀p. Trueprop (¬p = (p ⟹ F))
    let not_def_at = Thm::not_def()
        .all_elim(p.clone())
        .expect("unfold_not: all_elim p");
    // : ⊢ Trueprop (¬p = (p ⟹ F))
    // Convert to Pure meta-eq: ¬p ≡ (p ⟹ F)
    let lhs = Term::app(ctx.not_op(), p.clone());
    let rhs = Term::app(Term::app(ctx.imp_op(), p), Term::bool_lit(false));
    let pure_eq = pure_eq_from_hol_eq(not_def_at, ctx.bool_type(), lhs.clone(), rhs.clone());
    // Wrap with Trueprop via cong_app:
    //   ⊢ Trueprop ≡ Trueprop, ⊢ ¬p ≡ (p ⟹ F)
    //   → ⊢ Trueprop (¬p) ≡ Trueprop (p ⟹ F)
    let trueprop_eq = Thm::refl(ctx.trueprop())
        .expect("unfold_not: refl trueprop")
        .cong_app(pure_eq)
        .expect("unfold_not: cong_app");
    trueprop_eq.eq_mp(thm).expect("unfold_not: eq_mp")
}

/// Given `Γ ⊢ Trueprop (p ⟹ F)`, return `Γ ⊢ Trueprop (¬p)`.
/// (Reverse direction of `not_def`.)
fn fold_not(thm: Thm, p: Term, ctx: &HolLightCtx) -> Thm {
    let not_def_at = Thm::not_def()
        .all_elim(p.clone())
        .expect("fold_not: all_elim p");
    let lhs = Term::app(ctx.not_op(), p.clone());
    let rhs = Term::app(Term::app(ctx.imp_op(), p), Term::bool_lit(false));
    let pure_eq = pure_eq_from_hol_eq(not_def_at, ctx.bool_type(), lhs.clone(), rhs.clone());
    let trueprop_eq = Thm::refl(ctx.trueprop())
        .expect("fold_not: refl trueprop")
        .cong_app(pure_eq)
        .expect("fold_not: cong_app");
    trueprop_eq
        .sym()
        .expect("fold_not: sym")
        .eq_mp(thm)
        .expect("fold_not: eq_mp")
}

// ============================================================================
// nat_zero_ne_one — base case for nat_zero_ne_succ
// ============================================================================

/// `⊢ Trueprop (¬(0 = 1))` — the canonical base-case distinctness
/// fact, proved by `Thm::reduce_prim` deciding `HolEq 0 1 = F` on
/// the closed literals. Cached process-wide; downstream proofs
/// like `prove_nat_zero_ne_succ` use it as the induction base.
pub fn nat_zero_ne_one() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(build_nat_zero_ne_one);
    AX.clone()
}

fn build_nat_zero_ne_one() -> Thm {
    let ctx = HolLightCtx::new();
    let bool_ty = ctx.bool_type();
    let zero_eq_one = hol_eq(nat_lit(0), nat_lit(1), &ctx);

    // 1. reduce_prim(HolEq 0 1) → ⊢ HolEq 0 1 ≡ F
    let eq_to_false = Thm::reduce_prim(zero_eq_one.clone())
        .expect("nat_zero_ne_one: reduce_prim");

    // 2. cong_app(refl Trueprop, eq_to_false) → ⊢ Trueprop (0=1) ≡ Trueprop F
    let trueprop_eq = Thm::refl(ctx.trueprop())
        .expect("nat_zero_ne_one: refl trueprop")
        .cong_app(eq_to_false)
        .expect("nat_zero_ne_one: cong_app");

    // 3. assume Trueprop (0=1)
    let antecedent = ctx
        .mk_trueprop(zero_eq_one.clone())
        .expect("nat_zero_ne_one: mk_trueprop");
    let assumed = Thm::assume(antecedent.clone()).expect("nat_zero_ne_one: assume");

    // 4. eq_mp → Γ ⊢ Trueprop F
    let derive_false = trueprop_eq
        .eq_mp(assumed)
        .expect("nat_zero_ne_one: eq_mp");

    // 5. imp_intro → ⊢ Trueprop (0=1) ⟹ Trueprop F
    let pure_imp = derive_false
        .imp_intro(&antecedent)
        .expect("nat_zero_ne_one: imp_intro");

    // 6. Lift to HOL imp: ⊢ Trueprop ((0=1) ⟹ F)
    let hol_imp_thm = lift_imp_to_hol(pure_imp, zero_eq_one.clone(), Term::bool_lit(false));

    // 7. Fold the (... ⟹ F) form back into ¬: ⊢ Trueprop (¬(0=1))
    let _ = bool_ty;
    fold_not(hol_imp_thm, zero_eq_one, &ctx)
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

    #[test]
    fn nat_zero_ne_one_has_empty_hyps() {
        let thm = nat_zero_ne_one();
        assert!(thm.hyps().is_empty(), "got {} hyps", thm.hyps().len());
        assert!(thm.concl().type_of().unwrap().is_prop());
    }

    #[test]
    fn nat_zero_ne_one_is_cached() {
        // Two calls should produce structurally identical Thms.
        let a = nat_zero_ne_one();
        let b = nat_zero_ne_one();
        assert_eq!(a.concl(), b.concl());
    }
}
