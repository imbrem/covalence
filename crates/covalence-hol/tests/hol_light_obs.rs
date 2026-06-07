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
    let thm = Thm::obs_eq::<HolLight>(eq_a_a.clone(), truth.clone(), None).unwrap();
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
    assert!(Thm::obs_eq::<HolLight>(eq_ab, truth, None).is_err());
}

#[test]
fn obs_eq_sym_at_bool_eq() {
    // ⊢ Eq a b ≡ Eq b a via the HolLight ObsEq policy.
    let ctx = HolLightCtx::new();
    let a = Term::free("a", ctx.bool_type());
    let b = Term::free("b", ctx.bool_type());
    let eq_ab = ctx.mk_eq(a.clone(), b.clone()).unwrap();
    let eq_ba = ctx.mk_eq(b, a).unwrap();
    let thm = Thm::obs_eq::<HolLight>(eq_ab, eq_ba, None).unwrap();
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

// ============================================================================
// HOL Light bootstrap via Thm::obs_true + HolHint policy
// ============================================================================

#[test]
fn trueprop_at_bool_to_prop() {
    let ctx = HolLightCtx::new();
    let tp = ctx.trueprop();
    let ty = tp.type_of().unwrap();
    assert_eq!(ty, Type::fun(ctx.bool_type(), Type::prop()));
}

#[test]
fn mk_trueprop_wraps_a_bool_term_as_prop() {
    let ctx = HolLightCtx::new();
    let p = Term::free("p", ctx.bool_type());
    let tp_p = ctx.mk_trueprop(p).unwrap();
    assert!(tp_p.type_of().unwrap().is_prop());
}

#[test]
fn hol_refl_via_obs_true_no_hint() {
    // HOL: ⊢ a = a (at any type) — encoded as ⊢ Trueprop (Eq a a).
    // Mintable via Thm::obs_true with no hint (policy recognises
    // structural refl).
    let ctx = HolLightCtx::new();
    let a = Term::free("a", ctx.bool_type());
    let eq_a_a = ctx.mk_eq(a.clone(), a).unwrap();
    let tp_eq = ctx.mk_trueprop(eq_a_a.clone()).unwrap();

    let thm = covalence_pure::Thm::obs_true::<HolLight>(tp_eq.clone(), None).unwrap();
    assert!(thm.hyps().is_empty(), "HOL refl needs no hypotheses");
    assert_eq!(thm.concl(), &tp_eq);
}

#[test]
fn hol_refl_via_obs_true_with_explicit_hint() {
    // Same as above but with HolHint::Refl explicitly passed.
    let ctx = HolLightCtx::new();
    let a = Term::blob(bytes::Bytes::from_static(b"hello"));
    let eq_a_a = ctx.mk_eq(a.clone(), a).unwrap();
    let tp_eq = ctx.mk_trueprop(eq_a_a).unwrap();

    let hint = covalence_hol::HolHint::Refl;
    let thm =
        covalence_pure::Thm::obs_true::<HolLight>(tp_eq.clone(), Some(&hint as &dyn std::any::Any))
            .unwrap();
    assert!(thm.hyps().is_empty());
    assert_eq!(thm.concl(), &tp_eq);
}

#[test]
fn hol_refl_obs_true_rejects_non_refl_eq() {
    // Without a hint, the policy only fires on `Eq a a` structurally.
    // `Eq a b` with a ≠ b is refused.
    let ctx = HolLightCtx::new();
    let a = Term::free("a", ctx.bool_type());
    let b = Term::free("b", ctx.bool_type());
    let eq_a_b = ctx.mk_eq(a, b).unwrap();
    let tp_eq = ctx.mk_trueprop(eq_a_b).unwrap();
    let result = covalence_pure::Thm::obs_true::<HolLight>(tp_eq, None);
    assert!(result.is_err());
}

#[test]
fn hol_sym_via_obs_true_with_source_thm() {
    // HOL sym: from ⊢ Trueprop (Eq a b) derive ⊢ Trueprop (Eq b a).
    let ctx = HolLightCtx::new();
    let a = Term::free("a", ctx.bool_type());
    let b = Term::free("b", ctx.bool_type());

    // Source theorem: assume ⊢ Trueprop (Eq a b).
    let eq_a_b = ctx.mk_eq(a.clone(), b.clone()).unwrap();
    let tp_eq_a_b = ctx.mk_trueprop(eq_a_b).unwrap();
    let source = covalence_pure::Thm::assume(tp_eq_a_b).unwrap();

    // Want: ⊢ Trueprop (Eq b a).
    let eq_b_a = ctx.mk_eq(b, a).unwrap();
    let tp_eq_b_a = ctx.mk_trueprop(eq_b_a).unwrap();

    let hint = covalence_hol::HolHint::Sym {
        source: source.clone(),
    };
    let thm = covalence_pure::Thm::obs_true::<HolLight>(
        tp_eq_b_a.clone(),
        Some(&hint as &dyn std::any::Any),
    )
    .unwrap();
    assert_eq!(thm.concl(), &tp_eq_b_a);
}

#[test]
fn hol_trans_via_obs_true_with_two_source_thms() {
    // HOL trans: ⊢ Eq a b + ⊢ Eq b c → ⊢ Eq a c (all in Trueprop).
    let ctx = HolLightCtx::new();
    let a = Term::free("a", ctx.bool_type());
    let b = Term::free("b", ctx.bool_type());
    let c = Term::free("c", ctx.bool_type());

    let ab = covalence_pure::Thm::assume(
        ctx.mk_trueprop(ctx.mk_eq(a.clone(), b.clone()).unwrap()).unwrap(),
    )
    .unwrap();
    let bc = covalence_pure::Thm::assume(
        ctx.mk_trueprop(ctx.mk_eq(b, c.clone()).unwrap()).unwrap(),
    )
    .unwrap();

    // Want: ⊢ Trueprop (Eq a c).
    let ac = ctx.mk_eq(a, c).unwrap();
    let tp_ac = ctx.mk_trueprop(ac).unwrap();
    let hint = covalence_hol::HolHint::Trans {
        ab: ab.clone(),
        bc: bc.clone(),
    };
    let thm =
        covalence_pure::Thm::obs_true::<HolLight>(tp_ac.clone(), Some(&hint as &dyn std::any::Any))
            .unwrap();
    assert_eq!(thm.concl(), &tp_ac);
}

#[test]
fn hol_trans_rejects_when_middle_term_mismatches() {
    let ctx = HolLightCtx::new();
    let a = Term::free("a", ctx.bool_type());
    let b = Term::free("b", ctx.bool_type());
    let c = Term::free("c", ctx.bool_type());
    let d = Term::free("d", ctx.bool_type());

    // ab is Eq a b; bc is Eq d c (middle terms don't match: b ≠ d).
    let ab = covalence_pure::Thm::assume(
        ctx.mk_trueprop(ctx.mk_eq(a.clone(), b).unwrap()).unwrap(),
    )
    .unwrap();
    let bc = covalence_pure::Thm::assume(
        ctx.mk_trueprop(ctx.mk_eq(d, c.clone()).unwrap()).unwrap(),
    )
    .unwrap();

    let ac = ctx.mk_eq(a, c).unwrap();
    let tp_ac = ctx.mk_trueprop(ac).unwrap();
    let hint = covalence_hol::HolHint::Trans { ab, bc };
    let result =
        covalence_pure::Thm::obs_true::<HolLight>(tp_ac, Some(&hint as &dyn std::any::Any));
    assert!(result.is_err(), "trans with mismatched middle should be refused");
}
