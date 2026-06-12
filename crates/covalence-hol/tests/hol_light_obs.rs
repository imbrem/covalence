//! Tests for `covalence-hol`'s HOL Light bootstrap.
//!
//! With HOL folded into core, the HOL primitives (`bool`, `=`,
//! connectives, quantifiers, `Trueprop`) are first-class kernel
//! atoms — not observer objects. The bridge axioms
//! (`eq_reflection`, `iff_intro`, `forall_reflection`,
//! `imp_reflection`) still live here as `Thm::assume`-postulated
//! lazy theorems. This file exercises:
//!
//! - `HolLightCtx` constructors (`mk_eq`, `mk_trueprop`, `mk_imp`,
//!   etc.) building `HolOp` terms.
//! - Bridge axioms: well-typedness, specialisation, end-to-end use.

use covalence_core::{HolOp, Term, Thm, Type, TypeKind};
use covalence_hol::HolLightCtx;

// ============================================================================
// HolOp labels (now part of covalence-core)
// ============================================================================

#[test]
fn hol_op_variants_have_labels() {
    assert_eq!(HolOp::Eq.label(), "=");
    assert_eq!(HolOp::Trueprop.label(), "Trueprop");
    assert_eq!(HolOp::Forall.label(), "!");
    assert_eq!(HolOp::Exists.label(), "?");
    assert_eq!(HolOp::Select.label(), "@");
    assert_eq!(HolOp::Imp.label(), "==>");
    assert_eq!(HolOp::Not.label(), "~");
    assert_eq!(HolOp::And.label(), "/\\");
    assert_eq!(HolOp::Or.label(), "\\/");
    assert_eq!(HolOp::Iff.label(), "<=>");
}

// ============================================================================
// HolLightCtx — types
// ============================================================================

#[test]
fn ctx_bool_is_the_canonical_bool_type() {
    let ctx = HolLightCtx::new();
    let b = ctx.bool_type();
    assert_eq!(b, Type::bool());
    // After the Pure→HOL collapse, `bool` is a first-class
    // `TypeKind::Bool` variant (no longer the named-Tycon hack).
    assert!(matches!(b.kind(), TypeKind::Bool));
    assert!(b.is_bool());
}

#[test]
fn ctx_bool_is_distinct_from_pure_prop() {
    let ctx = HolLightCtx::new();
    let hol_bool = ctx.bool_type();
    assert_ne!(hol_bool, Type::prop(), "HOL bool must not be Pure prop");
}

#[test]
fn all_contexts_share_one_hol_theory() {
    // HolLightCtx is a zero-sized handle on process-global lazy statics.
    // Two contexts produce the SAME HOL theory.
    let a = HolLightCtx::new();
    let b = HolLightCtx::new();
    assert_eq!(a.bool_type(), b.bool_type());
    assert_eq!(a.t(), b.t());
    assert_eq!(a.trueprop(), b.trueprop());
}

// ============================================================================
// HolLightCtx — constants and constructors
// ============================================================================

#[test]
fn ctx_t_and_f_have_bool_type() {
    let ctx = HolLightCtx::new();
    assert_eq!(ctx.t().type_of().unwrap(), ctx.bool_type());
    assert_eq!(ctx.f().type_of().unwrap(), ctx.bool_type());
}

#[test]
fn mk_eq_returns_a_bool_typed_term() {
    let ctx = HolLightCtx::new();
    let a = Term::free("a", ctx.bool_type());
    let b = Term::free("b", ctx.bool_type());
    let eq = ctx.mk_eq(a, b).unwrap();
    assert_eq!(eq.type_of().unwrap(), ctx.bool_type());
}

#[test]
fn mk_eq_two_calls_with_same_args_share_observer_identity() {
    // Process-global Eq observer means structurally-equal mk_eq results.
    let ctx = HolLightCtx::new();
    let a = Term::free("a", ctx.bool_type());
    let b = Term::free("b", ctx.bool_type());
    let e1 = ctx.mk_eq(a.clone(), b.clone()).unwrap();
    let e2 = ctx.mk_eq(a, b).unwrap();
    assert_eq!(e1, e2);
}

#[test]
fn connectives_and_quantifiers_return_bool() {
    let ctx = HolLightCtx::new();
    let p = Term::free("p", ctx.bool_type());
    let q = Term::free("q", ctx.bool_type());
    for built in [
        ctx.mk_imp(p.clone(), q.clone()),
        ctx.mk_and(p.clone(), q.clone()),
        ctx.mk_or(p.clone(), q.clone()),
        ctx.mk_iff(p.clone(), q.clone()),
        ctx.mk_not(p.clone()),
    ] {
        assert_eq!(built.type_of().unwrap(), ctx.bool_type());
    }
}

#[test]
fn forall_constructs_well_typed_term() {
    let ctx = HolLightCtx::new();
    // ∀x:bool. x = x
    let body = {
        let x = Term::bound(0);
        let eq_at = ctx.eq_at(ctx.bool_type());
        Term::app(Term::app(eq_at, x.clone()), x)
    };
    let forall_x = ctx.mk_forall("x", ctx.bool_type(), body);
    assert_eq!(forall_x.type_of().unwrap(), ctx.bool_type());
}

#[test]
fn is_true_is_false_is_trueprop() {
    let ctx = HolLightCtx::new();
    assert!(ctx.is_true(&ctx.t()));
    assert!(!ctx.is_true(&ctx.f()));
    assert!(ctx.is_false(&ctx.f()));
    assert!(!ctx.is_false(&ctx.t()));
    let p = Term::free("p", ctx.bool_type());
    let tp_p = ctx.mk_trueprop(p).unwrap();
    let covalence_core::TermKind::App(tp_head, _) = tp_p.kind() else {
        panic!("expected App");
    };
    assert!(ctx.is_trueprop(tp_head));
}

// ============================================================================
// Trueprop
// ============================================================================

#[test]
fn trueprop_at_bool_to_prop() {
    let ctx = HolLightCtx::new();
    let tp = ctx.trueprop();
    let ty = tp.type_of().unwrap();
    assert_eq!(ty, Type::fun(ctx.bool_type(), Type::prop()));
}

#[test]
fn mk_trueprop_wraps_bool_term_to_prop() {
    let ctx = HolLightCtx::new();
    let p = Term::free("p", ctx.bool_type());
    let tp_p = ctx.mk_trueprop(p).unwrap();
    assert!(tp_p.type_of().unwrap().is_prop());
}

#[test]
fn mk_trueprop_rejects_non_bool() {
    let ctx = HolLightCtx::new();
    let p = Term::free("p", Type::bytes()); // bytes, not HOL bool
    assert!(ctx.mk_trueprop(p).is_err());
}

// ============================================================================
// eq_reflection axiom + HOL Light rule derivations
// ============================================================================

#[test]
fn eq_reflection_axiom_is_well_typed() {
    let ctx = HolLightCtx::new();
    let ax = ctx.eq_reflection_axiom();
    // Thm::assume gives {φ} ⊢ φ — one hyp identical to concl.
    assert_eq!(ax.hyps().len(), 1);
    assert_eq!(ax.hyps().iter().next().unwrap(), ax.concl());
    assert!(ax.concl().type_of().unwrap().is_prop());
}

#[test]
fn forall_reflection_axiom_is_well_typed() {
    let ctx = HolLightCtx::new();
    let ax = ctx.forall_reflection_axiom();
    assert_eq!(ax.hyps().len(), 1);
    assert_eq!(ax.hyps().iter().next().unwrap(), ax.concl());
    assert!(ax.concl().type_of().unwrap().is_prop());
}

#[test]
fn imp_reflection_axiom_is_well_typed() {
    let ctx = HolLightCtx::new();
    let ax = ctx.imp_reflection_axiom();
    assert_eq!(ax.hyps().len(), 1);
    assert_eq!(ax.hyps().iter().next().unwrap(), ax.concl());
    assert!(ax.concl().type_of().unwrap().is_prop());
}

#[test]
fn forall_reflection_specialises_via_inst_tfree() {
    let ctx = HolLightCtx::new();
    let at_bool = ctx
        .forall_reflection_axiom()
        .inst_tfree("a", ctx.bool_type())
        .unwrap();
    assert!(at_bool.concl().type_of().unwrap().is_prop());
}

#[test]
fn eq_reflection_axiom_is_globally_cached() {
    let ctx = HolLightCtx::new();
    let a = ctx.eq_reflection_axiom();
    let b = ctx.eq_reflection_axiom();
    // Same Pure Thm (cached via LazyLock; Pure Thm cloned cheaply).
    assert_eq!(a.concl(), b.concl());
}

#[test]
fn eq_reflection_specialises_via_inst_tfree() {
    let ctx = HolLightCtx::new();
    let at_bool = ctx
        .eq_reflection_axiom()
        .inst_tfree("a", ctx.bool_type())
        .unwrap();
    assert!(at_bool.concl().type_of().unwrap().is_prop());
}

#[test]
fn derive_pure_meta_eq_from_hol_eq() {
    // From ⊢ Trueprop (Eq a b) derive ⊢ a ≡ b via eq_reflection
    // forward direction. The HOL TRANS / EQ_MP / MK_COMB derivations
    // start with this conversion.
    let ctx = HolLightCtx::new();
    let a = Term::free("a", ctx.bool_type());
    let b = Term::free("b", ctx.bool_type());
    let source =
        Thm::assume(ctx.mk_trueprop(ctx.mk_eq(a.clone(), b.clone()).unwrap()).unwrap()).unwrap();

    let meta_eq = ctx
        .eq_reflection_axiom()
        .inst_tfree("a", ctx.bool_type())
        .unwrap()
        .all_elim(a.clone())
        .unwrap()
        .all_elim(b.clone())
        .unwrap()
        .eq_mp(source)
        .unwrap();
    assert_eq!(meta_eq.concl(), &Term::eq(a, b));
}

#[test]
fn derive_hol_eq_from_pure_meta_eq() {
    // From Pure refl ⊢ a ≡ a derive ⊢ Trueprop (Eq a a) via
    // eq_reflection backward direction. HOL REFL derivation.
    let ctx = HolLightCtx::new();
    let a = Term::free("a", ctx.bool_type());
    let meta_refl = Thm::refl(a.clone()).unwrap();

    let hol_refl = ctx
        .eq_reflection_axiom()
        .inst_tfree("a", ctx.bool_type())
        .unwrap()
        .all_elim(a.clone())
        .unwrap()
        .all_elim(a.clone())
        .unwrap()
        .sym()
        .unwrap()
        .eq_mp(meta_refl)
        .unwrap();
    let expected = ctx.mk_trueprop(ctx.mk_eq(a.clone(), a).unwrap()).unwrap();
    assert_eq!(hol_refl.concl(), &expected);
    // eq_reflection axiom appears as the single hyp (the axiom's
    // self-assume).
    assert_eq!(hol_refl.hyps().len(), 1);
}

#[test]
fn hol_trans_derivation_via_eq_reflection() {
    // Derive HOL TRANS the Isabelle/HOL way:
    //   ⊢ Trueprop (a = b), ⊢ Trueprop (b = c) → ⊢ Trueprop (a = c)
    let ctx = HolLightCtx::new();
    let a = Term::free("a", ctx.bool_type());
    let b = Term::free("b", ctx.bool_type());
    let c = Term::free("c", ctx.bool_type());

    let h_ab =
        Thm::assume(ctx.mk_trueprop(ctx.mk_eq(a.clone(), b.clone()).unwrap()).unwrap()).unwrap();
    let h_bc =
        Thm::assume(ctx.mk_trueprop(ctx.mk_eq(b.clone(), c.clone()).unwrap()).unwrap()).unwrap();
    let axiom = ctx
        .eq_reflection_axiom()
        .inst_tfree("a", ctx.bool_type())
        .unwrap();

    // Convert each HOL source to Pure meta-eq via forward direction.
    let pure_ab = axiom
        .clone()
        .all_elim(a.clone())
        .unwrap()
        .all_elim(b.clone())
        .unwrap()
        .eq_mp(h_ab)
        .unwrap();
    let pure_bc = axiom
        .clone()
        .all_elim(b.clone())
        .unwrap()
        .all_elim(c.clone())
        .unwrap()
        .eq_mp(h_bc)
        .unwrap();
    // Pure trans.
    let pure_ac = pure_ab.trans(pure_bc).unwrap();
    // Convert back to HOL via backward direction.
    let hol_ac = axiom
        .all_elim(a.clone())
        .unwrap()
        .all_elim(c.clone())
        .unwrap()
        .sym()
        .unwrap()
        .eq_mp(pure_ac)
        .unwrap();
    let expected = ctx.mk_trueprop(ctx.mk_eq(a, c).unwrap()).unwrap();
    assert_eq!(hol_ac.concl(), &expected);
    // hyps: eq_reflection + h_ab + h_bc = 3 hyps.
    assert_eq!(hol_ac.hyps().len(), 3);
}
