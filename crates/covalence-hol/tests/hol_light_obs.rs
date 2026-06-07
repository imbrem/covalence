//! Tests for the HolLight observer family and its ObsEq policy.

use covalence_hol::{HolLight, HolLightCtx};
use covalence_pure::{Term, TermKind, Thm, Type, TypeKind};

#[test]
fn ctx_bool_is_a_tycon_obs() {
    let ctx = HolLightCtx::new();
    let b = ctx.bool_type();
    match b.kind() {
        TypeKind::TyConObs(_, hint, args) => {
            assert_eq!(hint.as_str(), "bool");
            assert!(args.is_empty());
        }
        _ => panic!("expected TyConObs, got {:?}", b),
    }
}

#[test]
fn ctx_bool_is_distinct_from_pure_prop_and_pure_bool() {
    let ctx = HolLightCtx::new();
    let hol_bool = ctx.bool_type();
    // The HOL `bool` (TyConObs identity) is not Pure's structural
    // `Type::bool()` (which is Tycon("bool", []) — structural).
    assert_ne!(hol_bool, Type::bool(), "HOL bool must not collide with Pure's structural bool");
    assert_ne!(hol_bool, Type::prop(), "HOL bool must not be Pure prop");
}

#[test]
fn two_independent_contexts_give_distinct_hol_bools() {
    let a = HolLightCtx::new();
    let b = HolLightCtx::new();
    assert_ne!(a.bool_type(), b.bool_type(), "fresh ctxs have fresh HOL theories");
}

#[test]
fn ctx_t_and_f_have_bool_type() {
    let ctx = HolLightCtx::new();
    assert_eq!(ctx.t().type_of().unwrap(), ctx.bool_type());
    assert_eq!(ctx.f().type_of().unwrap(), ctx.bool_type());
}

#[test]
fn mk_eq_constructs_a_bool_typed_application() {
    let ctx = HolLightCtx::new();
    let a = Term::free("a", ctx.bool_type());
    let b = Term::free("b", ctx.bool_type());
    let eq = ctx.mk_eq(a.clone(), b.clone()).unwrap();
    assert_eq!(eq.type_of().unwrap(), ctx.bool_type());
}

#[test]
fn mk_eq_two_calls_with_same_args_produce_structurally_equal_terms() {
    let ctx = HolLightCtx::new();
    let a = Term::free("a", ctx.bool_type());
    let b = Term::free("b", ctx.bool_type());
    let e1 = ctx.mk_eq(a.clone(), b.clone()).unwrap();
    let e2 = ctx.mk_eq(a, b).unwrap();
    assert_eq!(e1, e2, "shared eq observer identity → structurally equal terms");
}

#[test]
fn obs_eq_at_eq_a_a_equates_to_true() {
    // ⊢ Eq a a ≡ True via the HolLight ObsEq policy.
    let ctx = HolLightCtx::new();
    let a = Term::free("a", ctx.bool_type());
    let eq_a_a = ctx.mk_eq(a.clone(), a).unwrap();
    let truth = ctx.t();
    let thm = Thm::obs_eq::<HolLight>(eq_a_a.clone(), truth.clone()).unwrap();
    assert!(thm.hyps().is_empty());
    let TermKind::Eq(lhs, rhs) = thm.concl().kind() else {
        panic!("expected Eq");
    };
    assert_eq!(lhs, &eq_a_a);
    assert_eq!(rhs, &truth);
}

#[test]
fn obs_eq_at_eq_a_b_does_not_collapse_to_true() {
    // Eq a b (with a ≠ b) is NOT equated to True by the policy.
    let ctx = HolLightCtx::new();
    let a = Term::free("a", ctx.bool_type());
    let b = Term::free("b", ctx.bool_type());
    let eq_ab = ctx.mk_eq(a, b).unwrap();
    let truth = ctx.t();
    assert!(Thm::obs_eq::<HolLight>(eq_ab, truth).is_err());
}

#[test]
fn obs_eq_sym_at_bool_eq() {
    // ⊢ Eq a b ≡ Eq b a via the HolLight ObsEq policy.
    let ctx = HolLightCtx::new();
    let a = Term::free("a", ctx.bool_type());
    let b = Term::free("b", ctx.bool_type());
    let eq_ab = ctx.mk_eq(a.clone(), b.clone()).unwrap();
    let eq_ba = ctx.mk_eq(b, a).unwrap();
    let thm = Thm::obs_eq::<HolLight>(eq_ab, eq_ba).unwrap();
    assert!(thm.hyps().is_empty());
}

#[test]
fn imp_and_or_iff_construct_correctly() {
    let ctx = HolLightCtx::new();
    let p = Term::free("p", ctx.bool_type());
    let q = Term::free("q", ctx.bool_type());
    for built in [
        ctx.mk_imp(p.clone(), q.clone()),
        ctx.mk_and(p.clone(), q.clone()),
        ctx.mk_or(p.clone(), q.clone()),
        ctx.mk_iff(p.clone(), q.clone()),
    ] {
        assert_eq!(built.type_of().unwrap(), ctx.bool_type());
    }
}

#[test]
fn mk_not_constructs_bool_typed_term() {
    let ctx = HolLightCtx::new();
    let p = Term::free("p", ctx.bool_type());
    let np = ctx.mk_not(p);
    assert_eq!(np.type_of().unwrap(), ctx.bool_type());
}

#[test]
fn forall_constructs_well_typed() {
    let ctx = HolLightCtx::new();
    // ∀x:bool. x = x  — first build (= x x) with x as Bound(0), then wrap.
    let x = Term::bound(0);
    let body = {
        // Need x : bool. But Bound(0) has type bool only inside the binder.
        // Use ctx.mk_eq inside the binder. ctx.mk_eq requires type_of, which
        // works on closed terms. For testing, build directly:
        let a = ctx.bool_type();
        let eq_at = ctx.eq_at(a);
        Term::app(Term::app(eq_at, x.clone()), x)
    };
    let forall_x = ctx.mk_forall("x", ctx.bool_type(), body);
    // type_of works only if the result is closed. ∀ wraps in a λ then
    // applies — when we computed the body's type, x had to be checked
    // in context. Let's just check the structure.
    let _ = forall_x.type_of().unwrap();
}

#[test]
fn hol_light_variants_have_labels() {
    assert_eq!(HolLight::Eq.label(), "=");
    assert_eq!(HolLight::True.label(), "T");
    assert_eq!(HolLight::False.label(), "F");
    assert_eq!(HolLight::Bool.label(), "bool");
}

#[test]
fn ctx_is_true_and_is_false() {
    let ctx = HolLightCtx::new();
    let t = ctx.t();
    let f = ctx.f();
    assert!(ctx.is_true(&t));
    assert!(!ctx.is_true(&f));
    assert!(ctx.is_false(&f));
    assert!(!ctx.is_false(&t));
}

#[test]
fn is_true_distinguishes_across_contexts() {
    let ctx1 = HolLightCtx::new();
    let ctx2 = HolLightCtx::new();
    // ctx1's T is not ctx2's T.
    assert!(!ctx2.is_true(&ctx1.t()));
}
