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
fn all_contexts_share_one_hol_theory() {
    // HolLightCtx is a zero-sized handle on process-global lazy statics.
    // Two contexts produce the SAME HOL theory — same HOL bool, same Eq,
    // same Trueprop. This is intentional: HOL Light is one theory per
    // process.
    let a = HolLightCtx::new();
    let b = HolLightCtx::new();
    assert_eq!(a.bool_type(), b.bool_type());
    assert_eq!(a.t(), b.t());
    assert_eq!(a.trueprop(), b.trueprop());
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
fn is_true_recognises_shared_global_t() {
    // With process-global lazy statics, every context shares the same
    // `T` observer Arc, so any context can identify any other's `T`.
    let ctx1 = HolLightCtx::new();
    let ctx2 = HolLightCtx::new();
    assert!(ctx2.is_true(&ctx1.t()));
    assert!(ctx1.is_true(&ctx2.t()));
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
fn hol_refl_at_blob_via_obs_true() {
    // HOL refl at type bytes (using a blob literal as the witness).
    let ctx = HolLightCtx::new();
    let a = Term::blob(bytes::Bytes::from_static(b"hello"));
    let eq_a_a = ctx.mk_eq(a.clone(), a).unwrap();
    let tp_eq = ctx.mk_trueprop(eq_a_a).unwrap();

    let thm = covalence_pure::Thm::obs_true::<HolLight>(tp_eq.clone(), None).unwrap();
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
fn hol_sym_as_lazy_theorem_via_obs_imp() {
    // HOL sym as a lazy theorem:
    //   ⊢ Trueprop (Eq a b) ⟹ Trueprop (Eq b a)
    // The user can then imp_elim with a concrete ⊢ Trueprop (Eq a b)
    // to get the specialised result.
    let ctx = HolLightCtx::new();
    let a = Term::free("a", ctx.bool_type());
    let b = Term::free("b", ctx.bool_type());

    let hyp = ctx.mk_trueprop(ctx.mk_eq(a.clone(), b.clone()).unwrap()).unwrap();
    let concl = ctx.mk_trueprop(ctx.mk_eq(b.clone(), a.clone()).unwrap()).unwrap();

    let lazy = covalence_pure::Thm::obs_imp::<HolLight>(concl.clone(), vec![hyp.clone()], None)
        .unwrap();
    // Concl: hyp ⟹ concl.
    let expected = covalence_pure::Term::imp(hyp.clone(), concl.clone());
    assert_eq!(lazy.concl(), &expected);
    // No hypotheses (sym is unconditional).
    assert!(lazy.hyps().is_empty());

    // Use the lazy theorem: from ⊢ Trueprop (Eq a b) derive ⊢ Trueprop (Eq b a).
    let source = covalence_pure::Thm::assume(hyp).unwrap();
    let derived = lazy.imp_elim(source).unwrap();
    assert_eq!(derived.concl(), &concl);
}

#[test]
fn hol_trans_as_lazy_theorem_via_obs_imp() {
    // ⊢ Trueprop (Eq a b) ⟹ Trueprop (Eq b c) ⟹ Trueprop (Eq a c).
    let ctx = HolLightCtx::new();
    let a = Term::free("a", ctx.bool_type());
    let b = Term::free("b", ctx.bool_type());
    let c = Term::free("c", ctx.bool_type());

    let h_ab = ctx.mk_trueprop(ctx.mk_eq(a.clone(), b.clone()).unwrap()).unwrap();
    let h_bc = ctx.mk_trueprop(ctx.mk_eq(b.clone(), c.clone()).unwrap()).unwrap();
    let concl = ctx.mk_trueprop(ctx.mk_eq(a.clone(), c.clone()).unwrap()).unwrap();

    let lazy = covalence_pure::Thm::obs_imp::<HolLight>(
        concl.clone(),
        vec![h_ab.clone(), h_bc.clone()],
        None,
    )
    .unwrap();
    let expected = covalence_pure::Term::imp(
        h_ab.clone(),
        covalence_pure::Term::imp(h_bc.clone(), concl.clone()),
    );
    assert_eq!(lazy.concl(), &expected);

    // Discharge both hyps via imp_elim chain.
    let ab_thm = covalence_pure::Thm::assume(h_ab).unwrap();
    let bc_thm = covalence_pure::Thm::assume(h_bc).unwrap();
    let step1 = lazy.imp_elim(ab_thm).unwrap();
    let final_ = step1.imp_elim(bc_thm).unwrap();
    assert_eq!(final_.concl(), &concl);
}

#[test]
fn hol_trans_rejects_when_middle_term_mismatches() {
    let ctx = HolLightCtx::new();
    let a = Term::free("a", ctx.bool_type());
    let b = Term::free("b", ctx.bool_type());
    let c = Term::free("c", ctx.bool_type());
    let d = Term::free("d", ctx.bool_type());

    let h_ab = ctx.mk_trueprop(ctx.mk_eq(a.clone(), b).unwrap()).unwrap();
    let h_dc = ctx.mk_trueprop(ctx.mk_eq(d, c.clone()).unwrap()).unwrap();
    let concl = ctx.mk_trueprop(ctx.mk_eq(a, c).unwrap()).unwrap();
    let result = covalence_pure::Thm::obs_imp::<HolLight>(concl, vec![h_ab, h_dc], None);
    assert!(result.is_err(), "trans with mismatched middle should be refused");
}

#[test]
fn hol_mk_comb_as_lazy_theorem_via_obs_imp() {
    // ⊢ Trueprop (Eq f g) ⟹ Trueprop (Eq x y) ⟹ Trueprop (Eq (f x) (g y)).
    let ctx = HolLightCtx::new();
    let alpha_to_bool = Type::fun(ctx.bool_type(), ctx.bool_type());
    let f = Term::free("f", alpha_to_bool.clone());
    let g = Term::free("g", alpha_to_bool);
    let x = Term::free("x", ctx.bool_type());
    let y = Term::free("y", ctx.bool_type());

    let h_fg = ctx.mk_trueprop(ctx.mk_eq(f.clone(), g.clone()).unwrap()).unwrap();
    let h_xy = ctx.mk_trueprop(ctx.mk_eq(x.clone(), y.clone()).unwrap()).unwrap();
    let fx = Term::app(f.clone(), x.clone());
    let gy = Term::app(g.clone(), y.clone());
    let concl = ctx.mk_trueprop(ctx.mk_eq(fx, gy).unwrap()).unwrap();

    let lazy = covalence_pure::Thm::obs_imp::<HolLight>(
        concl.clone(),
        vec![h_fg.clone(), h_xy.clone()],
        None,
    )
    .unwrap();
    let expected = covalence_pure::Term::imp(
        h_fg,
        covalence_pure::Term::imp(h_xy, concl),
    );
    assert_eq!(lazy.concl(), &expected);
}

#[test]
fn hol_eq_mp_at_bool_as_lazy_theorem_via_obs_imp() {
    // ⊢ Trueprop (Eq p q) ⟹ Trueprop p ⟹ Trueprop q.
    let ctx = HolLightCtx::new();
    let p = Term::free("p", ctx.bool_type());
    let q = Term::free("q", ctx.bool_type());

    let h_pq = ctx.mk_trueprop(ctx.mk_eq(p.clone(), q.clone()).unwrap()).unwrap();
    let h_p = ctx.mk_trueprop(p).unwrap();
    let concl = ctx.mk_trueprop(q).unwrap();

    let lazy = covalence_pure::Thm::obs_imp::<HolLight>(
        concl.clone(),
        vec![h_pq.clone(), h_p.clone()],
        None,
    )
    .unwrap();
    let expected = covalence_pure::Term::imp(h_pq, covalence_pure::Term::imp(h_p, concl));
    assert_eq!(lazy.concl(), &expected);
}

#[test]
fn hol_beta_via_obs_true_with_no_hint() {
    // HOL BETA: ⊢ (λx:bool. x) y = y.
    // Encoded: ⊢ Trueprop (Eq ((λx:bool. Bound 0) y) y).
    let ctx = HolLightCtx::new();
    let y = Term::free("y", ctx.bool_type());
    let body = Term::bound(0);
    let lam = Term::abs("x", ctx.bool_type(), body);
    let lhs = Term::app(lam, y.clone());
    let beta_concl = ctx.mk_trueprop(ctx.mk_eq(lhs, y).unwrap()).unwrap();
    let thm = covalence_pure::Thm::obs_true::<HolLight>(beta_concl.clone(), None).unwrap();
    assert_eq!(thm.concl(), &beta_concl);
}

#[test]
fn hol_beta_rejects_non_beta_redex() {
    // Trueprop (Eq f y) where f is a free var (not an Abs).
    let ctx = HolLightCtx::new();
    let f = Term::free("f", Type::fun(ctx.bool_type(), ctx.bool_type()));
    let y = Term::free("y", ctx.bool_type());
    let app = Term::app(f, y.clone());
    let bad = ctx.mk_trueprop(ctx.mk_eq(app, y).unwrap()).unwrap();
    let result = covalence_pure::Thm::obs_true::<HolLight>(bad, None);
    assert!(result.is_err(), "non-β-redex must be refused (also not refl)");
}

// NOTE: ABS, INST, INST_TYPE, DEDUCT_ANTISYM cannot soundly fit the
// `obs_imp` lazy-theorem pattern — see module docs for the analysis.
// They live in the (forthcoming) PureHol kernel adapter where each
// rule takes the actual source theorems and applies Pure's existing
// primitives (`cong_abs`, `inst_tfree`, `imp_intro`, etc.) with the
// correct discipline (hyp-side-conditions, uniform substitution).
//
// What we used to have for ABS/INST in this file was UNSOUND — see
// the audit commit for details. The check_*_pattern helpers for
// those rules were removed.

// ============================================================================
// Edge-case tests for the SOUND rules
// ============================================================================

#[test]
fn hol_refl_at_higher_order_term() {
    // ⊢ Trueprop (Eq (λx:bool. x) (λx:bool. x)).
    let ctx = HolLightCtx::new();
    let id_lambda = Term::abs("x", ctx.bool_type(), Term::bound(0));
    let eq = ctx.mk_eq(id_lambda.clone(), id_lambda).unwrap();
    let tp = ctx.mk_trueprop(eq).unwrap();
    let thm = covalence_pure::Thm::obs_true::<HolLight>(tp.clone(), None).unwrap();
    assert_eq!(thm.concl(), &tp);
}

#[test]
fn hol_refl_at_nested_app() {
    // ⊢ Trueprop (Eq (f (g x)) (f (g x))) — nested application.
    let ctx = HolLightCtx::new();
    let g = Term::free("g", Type::fun(ctx.bool_type(), ctx.bool_type()));
    let f = Term::free("f", Type::fun(ctx.bool_type(), ctx.bool_type()));
    let x = Term::free("x", ctx.bool_type());
    let inner = Term::app(g, x);
    let outer = Term::app(f, inner);
    let eq = ctx.mk_eq(outer.clone(), outer).unwrap();
    let tp = ctx.mk_trueprop(eq).unwrap();
    let thm = covalence_pure::Thm::obs_true::<HolLight>(tp.clone(), None).unwrap();
    assert_eq!(thm.concl(), &tp);
}

#[test]
fn hol_beta_with_bound_var_unused() {
    // (λx:bool. y) z reduces to y (x doesn't appear in body).
    let ctx = HolLightCtx::new();
    let y = Term::free("y", ctx.bool_type());
    let z = Term::free("z", ctx.bool_type());
    let lam = Term::abs("x", ctx.bool_type(), y.clone()); // body doesn't use x
    let app = Term::app(lam, z);
    let eq = ctx.mk_eq(app, y).unwrap();
    let tp = ctx.mk_trueprop(eq).unwrap();
    let thm = covalence_pure::Thm::obs_true::<HolLight>(tp.clone(), None).unwrap();
    assert_eq!(thm.concl(), &tp);
}

#[test]
fn hol_beta_rejects_when_rhs_is_wrong() {
    // (λx. x) y β-reduces to y. Asserting the RHS is z (≠ y) must fail.
    let ctx = HolLightCtx::new();
    let y = Term::free("y", ctx.bool_type());
    let z = Term::free("z", ctx.bool_type());
    let id_lambda = Term::abs("x", ctx.bool_type(), Term::bound(0));
    let app = Term::app(id_lambda, y);
    let bad_eq = ctx.mk_eq(app, z).unwrap();
    let bad_tp = ctx.mk_trueprop(bad_eq).unwrap();
    let result = covalence_pure::Thm::obs_true::<HolLight>(bad_tp, None);
    assert!(result.is_err());
}

#[test]
fn hol_trans_reflexive_case() {
    // a = a, a = a → a = a (degenerate but should still work).
    let ctx = HolLightCtx::new();
    let a = Term::free("a", ctx.bool_type());
    let h = ctx.mk_trueprop(ctx.mk_eq(a.clone(), a.clone()).unwrap()).unwrap();
    let lazy = covalence_pure::Thm::obs_imp::<HolLight>(
        h.clone(),
        vec![h.clone(), h.clone()],
        None,
    )
    .unwrap();
    // Concl: h ⟹ h ⟹ h.
    let expected = covalence_pure::Term::imp(
        h.clone(),
        covalence_pure::Term::imp(h.clone(), h),
    );
    assert_eq!(lazy.concl(), &expected);
}

#[test]
fn hol_trans_rejects_wrong_endpoint() {
    // Sources are about (a,b) and (b,c), but concl asks for (a,d).
    let ctx = HolLightCtx::new();
    let a = Term::free("a", ctx.bool_type());
    let b = Term::free("b", ctx.bool_type());
    let c = Term::free("c", ctx.bool_type());
    let d = Term::free("d", ctx.bool_type());
    let h_ab = ctx.mk_trueprop(ctx.mk_eq(a.clone(), b.clone()).unwrap()).unwrap();
    let h_bc = ctx.mk_trueprop(ctx.mk_eq(b, c).unwrap()).unwrap();
    let bad_concl = ctx.mk_trueprop(ctx.mk_eq(a, d).unwrap()).unwrap();
    let result = covalence_pure::Thm::obs_imp::<HolLight>(bad_concl, vec![h_ab, h_bc], None);
    assert!(result.is_err());
}

#[test]
fn hol_mk_comb_at_higher_order() {
    // f = g, x = y → (f x) = (g y) for higher-order x.
    let ctx = HolLightCtx::new();
    let alpha_to_alpha = Type::fun(ctx.bool_type(), ctx.bool_type());
    let f_ty = Type::fun(alpha_to_alpha.clone(), ctx.bool_type());
    let f = Term::free("f", f_ty.clone());
    let g = Term::free("g", f_ty);
    let x = Term::free("x", alpha_to_alpha.clone());
    let y = Term::free("y", alpha_to_alpha);

    let h_fg = ctx.mk_trueprop(ctx.mk_eq(f.clone(), g.clone()).unwrap()).unwrap();
    let h_xy = ctx.mk_trueprop(ctx.mk_eq(x.clone(), y.clone()).unwrap()).unwrap();
    let concl = ctx
        .mk_trueprop(ctx.mk_eq(Term::app(f, x), Term::app(g, y)).unwrap())
        .unwrap();
    let lazy = covalence_pure::Thm::obs_imp::<HolLight>(
        concl.clone(),
        vec![h_fg.clone(), h_xy.clone()],
        None,
    )
    .unwrap();
    let expected = covalence_pure::Term::imp(h_fg, covalence_pure::Term::imp(h_xy, concl));
    assert_eq!(lazy.concl(), &expected);
}

#[test]
fn hol_eq_mp_rejects_when_p_doesnt_match() {
    // h1 = Trueprop (Eq p q), h2 = Trueprop r (≠ p). Should refuse.
    let ctx = HolLightCtx::new();
    let p = Term::free("p", ctx.bool_type());
    let q = Term::free("q", ctx.bool_type());
    let r = Term::free("r", ctx.bool_type());
    let h_eq = ctx.mk_trueprop(ctx.mk_eq(p, q.clone()).unwrap()).unwrap();
    let h_r = ctx.mk_trueprop(r).unwrap();
    let concl = ctx.mk_trueprop(q).unwrap();
    let result = covalence_pure::Thm::obs_imp::<HolLight>(concl, vec![h_eq, h_r], None);
    assert!(result.is_err());
}

#[test]
fn hol_sym_at_blob_literals() {
    // sym at a non-free-variable type — using blob literals as terms.
    let ctx = HolLightCtx::new();
    let a = Term::blob(bytes::Bytes::from_static(b"a"));
    let b = Term::blob(bytes::Bytes::from_static(b"b"));
    let h = ctx.mk_trueprop(ctx.mk_eq(a.clone(), b.clone()).unwrap()).unwrap();
    let concl = ctx.mk_trueprop(ctx.mk_eq(b, a).unwrap()).unwrap();
    let lazy = covalence_pure::Thm::obs_imp::<HolLight>(
        concl.clone(),
        vec![h.clone()],
        None,
    )
    .unwrap();
    let expected = covalence_pure::Term::imp(h, concl);
    assert_eq!(lazy.concl(), &expected);
}

#[test]
fn obs_imp_rejects_zero_hyps_consistently() {
    // No matching arms for 0 hyps in the ObsImp policy. Even refl
    // shape should be refused (refl is in ObsTrue, not ObsImp).
    let ctx = HolLightCtx::new();
    let a = Term::free("a", ctx.bool_type());
    let tp = ctx.mk_trueprop(ctx.mk_eq(a.clone(), a).unwrap()).unwrap();
    let result = covalence_pure::Thm::obs_imp::<HolLight>(tp, vec![], None);
    assert!(result.is_err(), "obs_imp policy rejects 0 hyps");
}

#[test]
fn ctx_is_trueprop_identifies_trueprop_observer() {
    let ctx = HolLightCtx::new();
    let p = Term::free("p", ctx.bool_type());
    let tp_p = ctx.mk_trueprop(p).unwrap();
    let TermKind::App(tp_head, _) = tp_p.kind() else {
        panic!("expected App at top of mk_trueprop result");
    };
    assert!(ctx.is_trueprop(tp_head));
    assert!(!ctx.is_trueprop(&ctx.t()));
}

// ============================================================================
// Isabelle/HOL-style derivations via the eq_reflection axiom
// ============================================================================

#[test]
fn eq_reflection_axiom_well_typed() {
    let ctx = HolLightCtx::new();
    let ax = ctx.eq_reflection_axiom();
    // assume(φ) gives {φ} ⊢ φ — one hyp identical to the concl.
    assert_eq!(ax.hyps().len(), 1);
    assert_eq!(ax.hyps().iter().next().unwrap(), ax.concl());
    // Concl is well-typed at prop.
    assert!(ax.concl().type_of().unwrap().is_prop());
}

#[test]
fn eq_reflection_specialises_via_inst_tfree() {
    let ctx = HolLightCtx::new();
    let ax = ctx.eq_reflection_axiom();
    // Specialise 'a := bool — the most common case for HOL Light.
    let at_bool = ax.inst_tfree("a", ctx.bool_type()).unwrap();
    // The instantiated axiom is still a Pure prop.
    assert!(at_bool.concl().type_of().unwrap().is_prop());
}

#[test]
fn isabelle_style_derive_pure_meta_eq_from_hol_eq() {
    // From a HOL theorem ⊢ Trueprop (Eq a b) derive ⊢ a ≡ b
    // (the meta-equality), the way Isabelle/HOL does it: instantiate
    // eq_reflection at the relevant terms, then eq_mp.
    let ctx = HolLightCtx::new();
    let a = Term::free("a", ctx.bool_type());
    let b = Term::free("b", ctx.bool_type());
    let hol_eq_ab = ctx.mk_trueprop(ctx.mk_eq(a.clone(), b.clone()).unwrap()).unwrap();
    let source = covalence_pure::Thm::assume(hol_eq_ab).unwrap();

    // axiom at α := bool, then specialised at a, b.
    let axiom = ctx
        .eq_reflection_axiom()
        .inst_tfree("a", ctx.bool_type())
        .unwrap()
        .all_elim(a.clone())
        .unwrap()
        .all_elim(b.clone())
        .unwrap();
    // axiom : ⊢ Trueprop (Eq a b) ≡ (a ≡ b)
    // Use eq_mp with source: ⊢ a ≡ b.
    let meta_eq = axiom.eq_mp(source).unwrap();
    assert_eq!(meta_eq.concl(), &covalence_pure::Term::eq(a, b));
}

#[test]
fn isabelle_style_derive_hol_eq_from_pure_meta_eq() {
    // From ⊢ a ≡ b (Pure meta-eq, e.g., refl on a if b = a) derive
    // ⊢ Trueprop (Eq a b) (HOL eq). Reverse direction of the bridge.
    let ctx = HolLightCtx::new();
    let a = Term::free("a", ctx.bool_type());
    // Pure refl gives ⊢ a ≡ a.
    let meta_refl = covalence_pure::Thm::refl(a.clone()).unwrap();

    let axiom = ctx
        .eq_reflection_axiom()
        .inst_tfree("a", ctx.bool_type())
        .unwrap()
        .all_elim(a.clone())
        .unwrap()
        .all_elim(a.clone())
        .unwrap();
    // axiom: ⊢ Trueprop (Eq a a) ≡ (a ≡ a)
    // sym: ⊢ (a ≡ a) ≡ Trueprop (Eq a a)
    let sym = axiom.sym().unwrap();
    // eq_mp with refl: ⊢ Trueprop (Eq a a)
    let hol_thm = sym.eq_mp(meta_refl).unwrap();

    let expected = ctx.mk_trueprop(ctx.mk_eq(a.clone(), a).unwrap()).unwrap();
    assert_eq!(hol_thm.concl(), &expected);
    // The eq_reflection axiom (instantiated at bool) shows up as a hyp —
    // exactly like ETA/SELECT/INFINITY in HOL Light.
    assert_eq!(hol_thm.hyps().len(), 1);
}

#[test]
fn isabelle_style_hol_trans_via_eq_reflection() {
    // Derive HOL TRANS the Isabelle/HOL way:
    //   ⊢ Trueprop (a = b), ⊢ Trueprop (b = c) → ⊢ Trueprop (a = c)
    // via eq_reflection bridge + Pure trans.
    let ctx = HolLightCtx::new();
    let a = Term::free("a", ctx.bool_type());
    let b = Term::free("b", ctx.bool_type());
    let c = Term::free("c", ctx.bool_type());

    let h_ab =
        covalence_pure::Thm::assume(ctx.mk_trueprop(ctx.mk_eq(a.clone(), b.clone()).unwrap()).unwrap())
            .unwrap();
    let h_bc =
        covalence_pure::Thm::assume(ctx.mk_trueprop(ctx.mk_eq(b.clone(), c.clone()).unwrap()).unwrap())
            .unwrap();

    let axiom = ctx
        .eq_reflection_axiom()
        .inst_tfree("a", ctx.bool_type())
        .unwrap();

    // Convert h_ab to ⊢ a ≡ b.
    let pure_ab = axiom
        .clone()
        .all_elim(a.clone())
        .unwrap()
        .all_elim(b.clone())
        .unwrap()
        .eq_mp(h_ab)
        .unwrap();
    // Convert h_bc to ⊢ b ≡ c.
    let pure_bc = axiom
        .clone()
        .all_elim(b.clone())
        .unwrap()
        .all_elim(c.clone())
        .unwrap()
        .eq_mp(h_bc)
        .unwrap();
    // Pure trans: ⊢ a ≡ c.
    let pure_ac = pure_ab.trans(pure_bc).unwrap();
    // Convert back to HOL: instantiate axiom at a, c; sym; eq_mp.
    let hol_ac = axiom
        .all_elim(a.clone())
        .unwrap()
        .all_elim(c.clone())
        .unwrap()
        .sym()
        .unwrap()
        .eq_mp(pure_ac)
        .unwrap();
    // Concl: ⊢ Trueprop (a = c).
    let expected = ctx.mk_trueprop(ctx.mk_eq(a, c).unwrap()).unwrap();
    assert_eq!(hol_ac.concl(), &expected);
    // The eq_reflection axiom appears as a hypothesis (along with the
    // two HOL source hypotheses).
    assert_eq!(hol_ac.hyps().len(), 3);
}
