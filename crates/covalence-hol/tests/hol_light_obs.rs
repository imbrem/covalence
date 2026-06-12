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

