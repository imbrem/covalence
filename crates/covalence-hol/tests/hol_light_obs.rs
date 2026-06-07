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

#[test]
fn hol_abs_as_lazy_theorem_via_obs_imp() {
    // HOL ABS: ⊢ Trueprop (Eq s t) ⟹ Trueprop (Eq (λx. s) (λx. t)).
    let ctx = HolLightCtx::new();
    let x = Term::free("x", ctx.bool_type());
    let f = Term::free("f", Type::fun(ctx.bool_type(), ctx.bool_type()));
    let g = Term::free("g", Type::fun(ctx.bool_type(), ctx.bool_type()));
    let s = Term::app(f, x.clone());
    let t = Term::app(g, x.clone());

    let hyp = ctx.mk_trueprop(ctx.mk_eq(s.clone(), t.clone()).unwrap()).unwrap();

    // λx:bool. f x  and  λx:bool. g x
    let f2 = Term::free("f", Type::fun(ctx.bool_type(), ctx.bool_type()));
    let g2 = Term::free("g", Type::fun(ctx.bool_type(), ctx.bool_type()));
    let s_body = Term::app(f2, Term::bound(0));
    let t_body = Term::app(g2, Term::bound(0));
    let lam_s = Term::abs("x", ctx.bool_type(), s_body);
    let lam_t = Term::abs("x", ctx.bool_type(), t_body);
    let concl = ctx.mk_trueprop(ctx.mk_eq(lam_s, lam_t).unwrap()).unwrap();

    let lazy =
        covalence_pure::Thm::obs_imp::<HolLight>(concl.clone(), vec![hyp.clone()], None).unwrap();
    let expected = covalence_pure::Term::imp(hyp, concl);
    assert_eq!(lazy.concl(), &expected);
}

#[test]
fn hol_abs_rejects_when_hyp_doesnt_match_lambda_bodies() {
    // hyp: Trueprop (Eq a a)  (mismatched with concl's bodies).
    // concl: Trueprop (Eq (λx:bool. f x) (λx:bool. g x)).
    // policy should refuse because opening (f x) ≠ a structurally.
    let ctx = HolLightCtx::new();
    let a = Term::free("a", ctx.bool_type());
    let hyp = ctx.mk_trueprop(ctx.mk_eq(a.clone(), a).unwrap()).unwrap();

    let f = Term::free("f", Type::fun(ctx.bool_type(), ctx.bool_type()));
    let g = Term::free("g", Type::fun(ctx.bool_type(), ctx.bool_type()));
    let s_body = Term::app(f, Term::bound(0));
    let t_body = Term::app(g, Term::bound(0));
    let lam_s = Term::abs("x", ctx.bool_type(), s_body);
    let lam_t = Term::abs("x", ctx.bool_type(), t_body);
    let concl = ctx.mk_trueprop(ctx.mk_eq(lam_s, lam_t).unwrap()).unwrap();

    let result = covalence_pure::Thm::obs_imp::<HolLight>(concl, vec![hyp], None);
    assert!(result.is_err(), "ABS with mismatched bodies should be refused");
}

#[test]
fn hol_inst_via_obs_imp_with_inst_hint() {
    // HOL INST: ⊢ Trueprop (f x) ⟹ Trueprop (f y) given x:=y.
    let ctx = HolLightCtx::new();
    let f = Term::free("f", Type::fun(ctx.bool_type(), ctx.bool_type()));
    let x = Term::free("x", ctx.bool_type());
    let y = Term::free("y", ctx.bool_type());

    let p = Term::app(f.clone(), x);
    let p_inst = Term::app(f, y.clone());
    let hyp = ctx.mk_trueprop(p).unwrap();
    let concl = ctx.mk_trueprop(p_inst).unwrap();

    let hint: std::sync::Arc<dyn covalence_pure::Hint> =
        std::sync::Arc::new(covalence_hol::InstHint {
            subs: vec![("x".to_string(), y)],
        });
    let lazy = covalence_pure::Thm::obs_imp::<HolLight>(
        concl.clone(),
        vec![hyp.clone()],
        Some(hint),
    )
    .unwrap();
    let expected = covalence_pure::Term::imp(hyp, concl);
    assert_eq!(lazy.concl(), &expected);
}

// NOTE: HOL INST_TYPE doesn't fit the lazy-theorem encoding when the
// substituted term has free vars — Pure's Thm::build enforces
// cross-term free-var-type consistency, which fails for `⊢ hyp ⟹ concl`
// when hyp uses `x : 'a` and concl uses `x : bool`. INST_TYPE is
// instead best exposed via Pure's existing `Thm::inst_tfree` at the
// PureHol kernel-adapter level (planned follow-up). The InstTypeHint
// policy hook is still there for cases where free-var-types don't
// collide (e.g., blob-only or de-Bruijn-only terms).

#[test]
fn hol_inst_rejects_when_substitution_doesnt_match_concl() {
    let ctx = HolLightCtx::new();
    let f = Term::free("f", Type::fun(ctx.bool_type(), ctx.bool_type()));
    let x = Term::free("x", ctx.bool_type());
    let y = Term::free("y", ctx.bool_type());
    let z = Term::free("z", ctx.bool_type());

    let p = Term::app(f.clone(), x);
    let bad_concl_body = Term::app(f, z); // p[x:=z], not p[x:=y]
    let hyp = ctx.mk_trueprop(p).unwrap();
    let bad_concl = ctx.mk_trueprop(bad_concl_body).unwrap();

    // hint says x := y, but concl uses z.
    let hint: std::sync::Arc<dyn covalence_pure::Hint> =
        std::sync::Arc::new(covalence_hol::InstHint {
            subs: vec![("x".to_string(), y)],
        });
    let result =
        covalence_pure::Thm::obs_imp::<HolLight>(bad_concl, vec![hyp], Some(hint));
    assert!(result.is_err());
}
