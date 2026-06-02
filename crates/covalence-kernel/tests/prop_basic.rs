//! Phase 4 acceptance tests: Context, Prop, Thm + inference rules.

use std::sync::Arc;

use covalence_kernel::{
    Arena, Context, PrimOp1, PrimOp2, ProofError, Prop, TermDef, TermRef, Thm,
};

#[test]
fn empty_context_is_empty() {
    let ctx = Context::empty();
    assert_eq!(ctx.len(), 0);
    assert!(ctx.is_empty());
    assert!(ctx.parent().is_none());
}

#[test]
fn extend_grows_context() {
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::Bool(true));
    let p = Arc::new(Prop::new(Context::empty(), t));
    let ctx = Context::extend(Context::empty(), p.clone());
    assert_eq!(ctx.len(), 1);
    assert!(!ctx.is_empty());
    assert!(ctx.parent().is_some());
    assert!(Arc::ptr_eq(ctx.assumption(0).unwrap(), &p));
}

#[test]
fn nested_contexts_chain_through_parent() {
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::Bool(true));
    let f = a.alloc_term(TermDef::Bool(false));

    let p1 = Arc::new(Prop::new(Context::empty(), t));
    let p2 = Arc::new(Prop::new(Context::empty(), f));

    let ctx1 = Context::extend(Context::empty(), p1.clone());
    let ctx2 = Context::extend(ctx1.clone(), p2.clone());

    assert_eq!(ctx2.len(), 2);
    assert!(Arc::ptr_eq(ctx2.assumption(0).unwrap(), &p1));
    assert!(Arc::ptr_eq(ctx2.assumption(1).unwrap(), &p2));
    assert!(Arc::ptr_eq(ctx2.parent().unwrap(), &ctx1));
}

#[test]
fn contains_prop_searches_chain() {
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::Bool(true));
    let p = Arc::new(Prop::new(Context::empty(), t));

    let root = Context::empty();
    assert!(!root.contains_prop(&p));

    let ctx = Context::extend(root.clone(), p.clone());
    assert!(ctx.contains_prop(&p));

    let f = a.alloc_term(TermDef::Bool(false));
    let q = Arc::new(Prop::new(Context::empty(), f));
    let ctx2 = Context::extend(ctx, q.clone());
    assert!(ctx2.contains_prop(&p));
    assert!(ctx2.contains_prop(&q));
}

// ---------------------------------------------------------------------------
// Inference rules
// ---------------------------------------------------------------------------

#[test]
fn thm_refl_concludes_eq() {
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::Bool(true));
    let thm = Thm::refl(&mut a, Context::empty(), t).unwrap();
    match a.term_def(thm.concl()) {
        TermDef::Eq(l, r) => {
            assert_eq!(l.as_local(), Some(t));
            assert_eq!(r.as_local(), Some(t));
        }
        other => panic!("expected Eq(t, t), got {other:?}"),
    }
    assert!(thm.context().is_empty());
}

#[test]
fn thm_refl_rejects_ill_typed_input() {
    let mut a = Arena::new();
    // Bound(0) at the top level is Unbound(1) — not well-typed.
    let b0 = a.alloc_term(TermDef::Bound(0));
    let err = Thm::refl(&mut a, Context::empty(), b0).unwrap_err();
    assert_eq!(err, ProofError::IllTypedInput);
}

#[test]
fn thm_assume_extracts_assumption_concl() {
    let mut a = Arena::new();
    let f = a.alloc_term(TermDef::Bool(false));
    let prop = Arc::new(Prop::new(Context::empty(), f));
    let ctx = Context::extend(Context::empty(), prop.clone());
    let thm = Thm::assume(&a, ctx.clone(), prop.clone()).unwrap();
    assert_eq!(thm.concl(), f);
    assert!(Arc::ptr_eq(thm.context(), &ctx));
}

#[test]
fn thm_assume_rejects_prop_not_in_ctx() {
    let mut a = Arena::new();
    let f = a.alloc_term(TermDef::Bool(false));
    let prop = Arc::new(Prop::new(Context::empty(), f));
    let err = Thm::assume(&a, Context::empty(), prop).unwrap_err();
    assert_eq!(err, ProofError::AssumptionNotInContext);
}

#[test]
fn context_survives_pop_via_arc() {
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::Bool(true));
    let prop = Arc::new(Prop::new(Context::empty(), t));

    let thm = {
        let extended = Context::extend(Context::empty(), prop.clone());
        Thm::assume(&a, extended, prop.clone()).unwrap()
    };

    assert_eq!(thm.context().len(), 1);
    assert!(thm.context().contains_prop(&prop));
}

#[test]
fn refl_can_be_cloned() {
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::Bool(true));
    let thm = Thm::refl(&mut a, Context::empty(), t).unwrap();
    let thm2 = thm.clone();
    assert_eq!(thm.concl(), thm2.concl());
}

#[test]
fn add_assumption_extends_context() {
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::Bool(true));
    let thm = Thm::refl(&mut a, Context::empty(), t).unwrap();
    let original_concl = thm.concl();

    let f = a.alloc_term(TermDef::Bool(false));
    let extra = Arc::new(Prop::new(Context::empty(), f));
    let weakened = thm.add_assumption(&a, extra.clone()).unwrap();

    assert_eq!(weakened.concl(), original_concl);
    assert_eq!(weakened.context().len(), 1);
    assert!(weakened.context().contains_prop(&extra));
}

#[test]
fn add_assumption_rejects_ill_typed() {
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::Bool(true));
    let thm = Thm::refl(&mut a, Context::empty(), t).unwrap();
    // A Prop carrying an ill-typed conclusion.
    let b0 = a.alloc_term(TermDef::Bound(0));
    let extra = Arc::new(Prop::new(Context::empty(), b0));
    let err = thm.add_assumption(&a, extra).unwrap_err();
    assert_eq!(err, ProofError::IllTypedInput);
}

#[test]
fn add_assumption_stacks_multiple() {
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::Bool(true));
    let thm = Thm::refl(&mut a, Context::empty(), t).unwrap();

    let p1 = Arc::new(Prop::new(Context::empty(), t));
    let f = a.alloc_term(TermDef::Bool(false));
    let p2 = Arc::new(Prop::new(Context::empty(), f));

    let weakened = thm
        .add_assumption(&a, p1.clone())
        .unwrap()
        .add_assumption(&a, p2.clone())
        .unwrap();
    assert_eq!(weakened.context().len(), 2);
    assert!(weakened.context().contains_prop(&p1));
    assert!(weakened.context().contains_prop(&p2));
}

#[test]
fn not_from_false_derives_negation() {
    let mut a = Arena::new();
    let false_term = a.alloc_term(TermDef::Bool(false));
    let false_prop = Arc::new(Prop::new(Context::empty(), false_term));
    let ctx = Context::extend(Context::empty(), false_prop.clone());
    let thm_false = Thm::assume(&a, ctx.clone(), false_prop).unwrap();
    let t = a.alloc_term(TermDef::Bool(true));
    let not_t = Thm::not_from_false(&mut a, thm_false, t).unwrap();
    match a.term_def(not_t.concl()) {
        TermDef::Op1(PrimOp1::LogicalNot, x) => {
            assert_eq!(x.as_local(), Some(t));
        }
        other => panic!("expected Op1(LogicalNot, True), got {other:?}"),
    }
    assert!(Arc::ptr_eq(not_t.context(), &ctx));
}

#[test]
fn not_from_false_rejects_non_false_conclusion() {
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::Bool(true));
    let thm = Thm::refl(&mut a, Context::empty(), t).unwrap();
    let p = a.alloc_term(TermDef::Bool(true));
    let err = Thm::not_from_false(&mut a, thm, p).unwrap_err();
    assert_eq!(err, ProofError::ConclusionNotFalse);
}

#[test]
fn nonlinear_thm_clone_combine() {
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::Bool(true));
    let thm = Thm::refl(&mut a, Context::empty(), t).unwrap();

    let f = a.alloc_term(TermDef::Bool(false));
    let p_extra = Arc::new(Prop::new(Context::empty(), f));

    let thm1 = thm.clone().add_assumption(&a, p_extra.clone()).unwrap();
    let thm2 = thm.add_assumption(&a, p_extra.clone()).unwrap();

    assert_eq!(thm1.concl(), thm2.concl());
    assert!(thm1.context().contains_prop(&p_extra));
    assert!(thm2.context().contains_prop(&p_extra));
}

#[test]
fn sym_flips_equality() {
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::Bool(true));
    let refl_thm = Thm::refl(&mut a, Context::empty(), t).unwrap();
    let flipped = Thm::sym(&mut a, refl_thm).unwrap();
    match a.term_def(flipped.concl()) {
        TermDef::Eq(l, r) => {
            assert_eq!(l.as_local(), Some(t));
            assert_eq!(r.as_local(), Some(t));
        }
        other => panic!("expected Eq, got {other:?}"),
    }
}

#[test]
fn sym_rejects_non_equality() {
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::Bool(true));
    let assumption_prop = Arc::new(Prop::new(Context::empty(), t));
    let ctx = Context::extend(Context::empty(), assumption_prop.clone());
    let thm = Thm::assume(&a, ctx, assumption_prop).unwrap();
    let err = Thm::sym(&mut a, thm).unwrap_err();
    assert_eq!(err, ProofError::ExpectedEquality);
}

#[test]
fn trans_chains_equalities() {
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::Bool(true));
    let ctx = Context::empty();
    let ab = Thm::refl(&mut a, ctx.clone(), t).unwrap();
    let bc = Thm::refl(&mut a, ctx.clone(), t).unwrap();
    let ac = Thm::trans(&mut a, ab, bc).unwrap();
    match a.term_def(ac.concl()) {
        TermDef::Eq(l, r) => {
            assert_eq!(l.as_local(), Some(t));
            assert_eq!(r.as_local(), Some(t));
        }
        other => panic!("expected Eq, got {other:?}"),
    }
}

#[test]
fn trans_via_uf_midpoint_match() {
    let mut a = Arena::new();
    let n1 = a.alloc_term(TermDef::nat_inline(5));
    let n2 = a.alloc_term(TermDef::nat_inline(5));
    a.union(TermRef::local(n1), TermRef::local(n2)).unwrap();

    let ctx = Context::empty();
    let ab = Thm::refl(&mut a, ctx.clone(), n1).unwrap();
    let bc = Thm::refl(&mut a, ctx.clone(), n2).unwrap();
    let ac = Thm::trans(&mut a, ab, bc).unwrap();
    match a.term_def(ac.concl()) {
        TermDef::Eq(l, r) => {
            assert_eq!(l.as_local(), Some(n1));
            assert_eq!(r.as_local(), Some(n2));
        }
        other => panic!("expected Eq, got {other:?}"),
    }
}

#[test]
fn trans_rejects_context_mismatch() {
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::Bool(true));
    let prop = Arc::new(Prop::new(Context::empty(), t));
    let ctx1 = Context::empty();
    let ctx2 = Context::extend(Context::empty(), prop);
    let ab = Thm::refl(&mut a, ctx1, t).unwrap();
    let bc = Thm::refl(&mut a, ctx2, t).unwrap();
    let err = Thm::trans(&mut a, ab, bc).unwrap_err();
    assert_eq!(err, ProofError::ContextMismatch);
}

#[test]
fn eq_mp_derives_rhs_from_lhs() {
    let mut a = Arena::new();
    let p = a.alloc_term(TermDef::Bool(true));
    let p_prop = Arc::new(Prop::new(Context::empty(), p));
    let ctx = Context::extend(Context::empty(), p_prop.clone());
    let p_thm = Thm::assume(&a, ctx.clone(), p_prop).unwrap();
    let pq = Thm::refl(&mut a, ctx.clone(), p).unwrap();
    let q_thm = Thm::eq_mp(&mut a, pq, p_thm).unwrap();
    assert_eq!(q_thm.concl(), p);
}

#[test]
fn eq_mp_rejects_lhs_mismatch() {
    let mut a = Arena::new();
    let p = a.alloc_term(TermDef::Bool(true));
    let q = a.alloc_term(TermDef::Bool(false));
    let q_prop = Arc::new(Prop::new(Context::empty(), q));
    let ctx = Context::extend(Context::empty(), q_prop.clone());
    let q_thm = Thm::assume(&a, ctx.clone(), q_prop).unwrap();
    let pq = Thm::refl(&mut a, ctx.clone(), p).unwrap();
    let err = Thm::eq_mp(&mut a, pq, q_thm).unwrap_err();
    assert_eq!(err, ProofError::LhsMismatch);
}

#[test]
fn mp_derives_consequent_from_implication() {
    // We need a Thm whose conclusion is Op2(LogicalImp, p, q), and
    // a Thm whose conclusion is p. Easiest: assume both.
    let mut a = Arena::new();
    let p = a.alloc_term(TermDef::Bool(true));
    let q = a.alloc_term(TermDef::Bool(false));
    let imp = a.alloc_term(TermDef::Op2(
        PrimOp2::LogicalImp,
        TermRef::local(p),
        TermRef::local(q),
    ));
    let imp_prop = Arc::new(Prop::new(Context::empty(), imp));
    let p_prop = Arc::new(Prop::new(Context::empty(), p));
    let ctx = Context::extend(
        Context::extend(Context::empty(), imp_prop.clone()),
        p_prop.clone(),
    );
    let imp_thm = Thm::assume(&a, ctx.clone(), imp_prop).unwrap();
    let p_thm = Thm::assume(&a, ctx.clone(), p_prop).unwrap();
    let q_thm = Thm::mp(&mut a, imp_thm, p_thm).unwrap();
    assert_eq!(q_thm.concl(), q);
}

#[test]
fn mp_rejects_non_implication() {
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::Bool(true));
    let prop_t = Arc::new(Prop::new(Context::empty(), t));
    let ctx = Context::extend(Context::empty(), prop_t.clone());
    let thm = Thm::assume(&a, ctx.clone(), prop_t.clone()).unwrap();
    let ant = Thm::assume(&a, ctx, prop_t).unwrap();
    let err = Thm::mp(&mut a, thm, ant).unwrap_err();
    assert_eq!(err, ProofError::ExpectedImplication);
}

#[test]
fn cong_at_depth_1_subsumes_mk_comb() {
    // The classical MK_COMB rule (Comb-congruence) falls out of
    // depth-1 cong: if f ≡ g and x ≡ y, then Comb(f, x) ≡ Comb(g, y).
    let mut a = Arena::new();
    let bool_ty = a.bool_ty();
    let f_to_b = a.alloc_type(covalence_kernel::TypeDef::Fun(bool_ty, bool_ty));
    let name_f = a.intern_string("f".into());
    let f = a.alloc_term(TermDef::Const(name_f, f_to_b));
    let x = a.alloc_term(TermDef::Bool(true));
    let fx_1 = a.alloc_term(TermDef::Comb(TermRef::local(f), TermRef::local(x)));
    let fx_2 = a.alloc_term(TermDef::Comb(TermRef::local(f), TermRef::local(x)));

    let ctx = Context::empty();
    let thm = Thm::cong(
        &mut a,
        ctx,
        TermRef::local(fx_1),
        TermRef::local(fx_2),
        1,
    )
    .unwrap();
    match a.term_def(thm.concl()) {
        TermDef::Eq(l, r) => {
            assert_eq!(*l, TermRef::local(fx_1));
            assert_eq!(*r, TermRef::local(fx_2));
        }
        other => panic!("expected Eq, got {other:?}"),
    }
}

#[test]
fn cong_rejects_non_congruent_terms() {
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::Bool(true));
    let f = a.alloc_term(TermDef::Bool(false));
    let ctx = Context::empty();
    let err = Thm::cong(&mut a, ctx, TermRef::local(t), TermRef::local(f), 5)
        .unwrap_err();
    assert_eq!(err, ProofError::NotCongruent);
}

#[test]
fn cong_accepts_ill_typed_inputs() {
    // Congruence is the only rule exempt from well-typed-input —
    // confirm an obviously ill-typed term (Comb of mismatched
    // function-arg types) can still take part in a cong proof.
    let mut a = Arena::new();
    let bool_ty = a.bool_ty();
    let b_to_b = a.alloc_type(covalence_kernel::TypeDef::Fun(bool_ty, bool_ty));
    let name_g = a.intern_string("g".into());
    let g = a.alloc_term(TermDef::Const(name_g, b_to_b));
    let n = a.alloc_term(TermDef::nat_inline(0));
    // Comb(g, n) — g expects bool, gets nat → ill-typed.
    let bad = a.alloc_term(TermDef::Comb(TermRef::local(g), TermRef::local(n)));
    assert!(!a.is_well_typed(bad));
    let ctx = Context::empty();
    let thm =
        Thm::cong(&mut a, ctx, TermRef::local(bad), TermRef::local(bad), 0).unwrap();
    assert!(matches!(a.term_def(thm.concl()), TermDef::Eq(_, _)));
}

#[test]
fn beta_reduces_redex_to_equality() {
    // (λ_:bool. Bound(0)) True — redex. β-rule gives ((λ. Bound(0)) True) = True.
    let mut a = Arena::new();
    let bool_ty = a.bool_ty();
    let b0 = a.alloc_term(TermDef::Bound(0));
    let abs = a.alloc_term(TermDef::Abs(bool_ty, TermRef::local(b0)));
    // Abs body uses Bound(0), so the Abs (before infer) is marked
    // IllTyped at alloc_term. Run infer to get its proper type.
    let _ = a.infer(abs);
    let t = a.alloc_term(TermDef::Bool(true));
    let comb = a.alloc_term(TermDef::Comb(TermRef::local(abs), TermRef::local(t)));
    // The Comb of (bool→bool) and bool is well-typed.
    let thm = Thm::beta(&mut a, Context::empty(), comb).unwrap();
    match a.term_def(thm.concl()) {
        TermDef::Eq(l, r) => {
            assert_eq!(l.as_local(), Some(comb));
            // RHS is the substituted body — True.
            assert_eq!(r.as_local(), Some(t));
        }
        other => panic!("expected Eq, got {other:?}"),
    }
}

#[test]
fn beta_rejects_non_redex() {
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::Bool(true));
    let err = Thm::beta(&mut a, Context::empty(), t).unwrap_err();
    assert_eq!(err, ProofError::ExpectedBetaRedex);
}

#[test]
fn beta_rejects_ill_typed_redex() {
    // Comb without a well-typed redex.
    let mut a = Arena::new();
    let bool_ty = a.bool_ty();
    let b0 = a.alloc_term(TermDef::Bound(0));
    let abs = a.alloc_term(TermDef::Abs(bool_ty, TermRef::local(b0)));
    // Don't run infer — abs's cached type_info stays IllTyped. The
    // Comb on it is therefore also not well-typed at alloc.
    let t = a.alloc_term(TermDef::Bool(true));
    let comb = a.alloc_term(TermDef::Comb(TermRef::local(abs), TermRef::local(t)));
    let err = Thm::beta(&mut a, Context::empty(), comb).unwrap_err();
    assert_eq!(err, ProofError::IllTypedInput);
}

#[test]
fn thm_field_is_kernel_only() {
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::Bool(true));
    let thm = Thm::refl(&mut a, Context::empty(), t).unwrap();
    let prop_ref = thm.prop();
    let _: &Prop = prop_ref;
}

#[test]
fn reduce_yields_eq_of_original_and_reduced() {
    // Not(True) reduces to False — the Thm carries that equality.
    use covalence_kernel::PrimOp1;
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::Bool(true));
    let not_t = a.alloc_term(TermDef::Op1(PrimOp1::LogicalNot, TermRef::local(t)));
    let thm = Thm::reduce(&mut a, Context::empty(), not_t).unwrap();
    match a.term_def(thm.concl()) {
        TermDef::Eq(l, r) => {
            assert_eq!(*l, TermRef::local(not_t));
            assert_eq!(a.term_def(r.as_local().unwrap()), &TermDef::Bool(false));
        }
        other => panic!("expected Eq, got {other:?}"),
    }
}

#[test]
fn reduce_rejects_unreducible_term() {
    // A bare True has no rule firing — reduce errors.
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::Bool(true));
    let err = Thm::reduce(&mut a, Context::empty(), t).unwrap_err();
    assert_eq!(err, ProofError::NotReducible);
}

#[test]
fn reduce_rejects_ill_typed_input() {
    // Op1 applied to a wrong-type arg is ill-typed; reduce refuses.
    use covalence_kernel::PrimOp1;
    let mut a = Arena::new();
    let n = a.alloc_term(TermDef::nat_inline(3));
    // LogicalNot on a Nat — ill-typed.
    let bad = a.alloc_term(TermDef::Op1(PrimOp1::LogicalNot, TermRef::local(n)));
    assert!(!a.is_well_typed(bad));
    let err = Thm::reduce(&mut a, Context::empty(), bad).unwrap_err();
    assert_eq!(err, ProofError::IllTypedInput);
}

#[test]
fn abs_binds_free_var_in_both_sides_of_equality() {
    // refl(x) gives ⊢ x = x. abs(_, x, bool) gives ⊢ (λ_:bool. Bound(0))
    // = (λ_:bool. Bound(0)).
    let mut a = Arena::new();
    let bool_ty = a.bool_ty();
    let xname = a.intern_string("x".into());
    let x = a.alloc_term(TermDef::Free(xname, bool_ty));

    let refl_x = Thm::refl(&mut a, Context::empty(), x).unwrap();
    let thm = Thm::abs(&mut a, refl_x, xname, bool_ty).unwrap();
    let (l, r) = match a.term_def(thm.concl()) {
        TermDef::Eq(l, r) => (*l, *r),
        other => panic!("expected Eq, got {other:?}"),
    };
    let l_def = *a.term_def(l.as_local().unwrap());
    let r_def = *a.term_def(r.as_local().unwrap());
    match (l_def, r_def) {
        (TermDef::Abs(ty1, b1), TermDef::Abs(ty2, b2)) => {
            assert_eq!(ty1, bool_ty);
            assert_eq!(ty2, bool_ty);
            assert_eq!(a.term_def(b1.as_local().unwrap()), &TermDef::Bound(0));
            assert_eq!(a.term_def(b2.as_local().unwrap()), &TermDef::Bound(0));
        }
        other => panic!("expected Abs/Abs, got {other:?}"),
    }
}

#[test]
fn abs_rejects_variable_free_in_assumption() {
    // Assumption: x = True (where x is the variable we'd bind). Trying
    // to abs over x with this assumption in scope would let the binder
    // capture x's reference.
    let mut a = Arena::new();
    let bool_ty = a.bool_ty();
    let xname = a.intern_string("x".into());
    let x = a.alloc_term(TermDef::Free(xname, bool_ty));
    let t = a.alloc_term(TermDef::Bool(true));
    let x_eq_true = a.alloc_term(TermDef::Eq(TermRef::local(x), TermRef::local(t)));

    let assum = std::sync::Arc::new(Prop::new(Context::empty(), x_eq_true));
    let ctx = Context::extend(Context::empty(), assum);
    let refl_x = Thm::refl(&mut a, ctx, x).unwrap();
    let err = Thm::abs(&mut a, refl_x, xname, bool_ty).unwrap_err();
    assert_eq!(err, ProofError::VariableEscapesAssumption);
}

#[test]
fn abs_allows_variable_not_free_in_assumption() {
    // Assumption mentions a different free `y` — abs over `x` is fine.
    let mut a = Arena::new();
    let bool_ty = a.bool_ty();
    let xname = a.intern_string("x".into());
    let yname = a.intern_string("y".into());
    let x = a.alloc_term(TermDef::Free(xname, bool_ty));
    let y = a.alloc_term(TermDef::Free(yname, bool_ty));
    let t = a.alloc_term(TermDef::Bool(true));
    let y_eq_true = a.alloc_term(TermDef::Eq(TermRef::local(y), TermRef::local(t)));

    let assum = std::sync::Arc::new(Prop::new(Context::empty(), y_eq_true));
    let ctx = Context::extend(Context::empty(), assum);
    let refl_x = Thm::refl(&mut a, ctx, x).unwrap();
    let thm = Thm::abs(&mut a, refl_x, xname, bool_ty).unwrap();
    assert!(matches!(a.term_def(thm.concl()), TermDef::Eq(_, _)));
}

#[test]
fn inst_substitutes_free_in_conclusion() {
    // refl(x) gives ⊢ x = x. inst with True for x gives ⊢ True = True.
    let mut a = Arena::new();
    let bool_ty = a.bool_ty();
    let xname = a.intern_string("x".into());
    let x = a.alloc_term(TermDef::Free(xname, bool_ty));
    let t = a.alloc_term(TermDef::Bool(true));

    let refl_x = Thm::refl(&mut a, Context::empty(), x).unwrap();
    let thm = Thm::inst(&mut a, refl_x, xname, bool_ty, TermRef::local(t)).unwrap();
    match a.term_def(thm.concl()) {
        TermDef::Eq(l, r) => {
            assert_eq!(a.term_def(l.as_local().unwrap()), &TermDef::Bool(true));
            assert_eq!(a.term_def(r.as_local().unwrap()), &TermDef::Bool(true));
        }
        other => panic!("expected Eq, got {other:?}"),
    }
}

#[test]
fn inst_substitutes_in_context_assumptions() {
    // Assumption: y = True. Thm: y ⊢ y (via assume).
    // INST x ↦ True (irrelevant — x doesn't appear). Result still has y in ctx.
    let mut a = Arena::new();
    let bool_ty = a.bool_ty();
    let xname = a.intern_string("x".into());
    let yname = a.intern_string("y".into());
    let _x = a.alloc_term(TermDef::Free(xname, bool_ty));
    let y = a.alloc_term(TermDef::Free(yname, bool_ty));
    let t = a.alloc_term(TermDef::Bool(true));

    // Context: { x = True } where x is the variable we'll INST.
    let x_free = a.alloc_term(TermDef::Free(xname, bool_ty));
    let x_eq_true = a.alloc_term(TermDef::Eq(TermRef::local(x_free), TermRef::local(t)));
    let assum = std::sync::Arc::new(Prop::new(Context::empty(), x_eq_true));
    let ctx = Context::extend(Context::empty(), assum);
    let refl_y = Thm::refl(&mut a, ctx, y).unwrap();
    let thm = Thm::inst(&mut a, refl_y, xname, bool_ty, TermRef::local(t)).unwrap();
    // Context should now have True = True (x substituted to True).
    let new_ctx = thm.context();
    assert_eq!(new_ctx.len(), 1);
    let new_assum_concl = new_ctx.assumption(0).unwrap().concl;
    match a.term_def(new_assum_concl) {
        TermDef::Eq(l, r) => {
            assert_eq!(a.term_def(l.as_local().unwrap()), &TermDef::Bool(true));
            assert_eq!(a.term_def(r.as_local().unwrap()), &TermDef::Bool(true));
        }
        other => panic!("expected Eq(True, True), got {other:?}"),
    }
}

#[test]
fn inst_rejects_type_mismatched_replacement() {
    // x : bool, replacement is a Nat — type mismatch.
    let mut a = Arena::new();
    let bool_ty = a.bool_ty();
    let xname = a.intern_string("x".into());
    let x = a.alloc_term(TermDef::Free(xname, bool_ty));
    let n = a.alloc_term(TermDef::nat_inline(7));
    let refl_x = Thm::refl(&mut a, Context::empty(), x).unwrap();
    let err =
        Thm::inst(&mut a, refl_x, xname, bool_ty, TermRef::local(n)).unwrap_err();
    assert_eq!(err, ProofError::TypeMismatch);
}

#[test]
fn deduct_antisym_yields_eq_of_concls() {
    // ⊢ True (assume True from ctx {True}) + ⊢ True (likewise) → ⊢ True = True
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::Bool(true));
    let assum = std::sync::Arc::new(Prop::new(Context::empty(), t));
    let ctx = Context::extend(Context::empty(), assum.clone());
    let thm_p = Thm::assume(&a, ctx.clone(), assum.clone()).unwrap();
    let thm_q = Thm::assume(&a, ctx, assum).unwrap();
    let thm = Thm::deduct_antisym_rule(&mut a, thm_p, thm_q).unwrap();
    match a.term_def(thm.concl()) {
        TermDef::Eq(l, r) => {
            assert_eq!(a.term_def(l.as_local().unwrap()), &TermDef::Bool(true));
            assert_eq!(a.term_def(r.as_local().unwrap()), &TermDef::Bool(true));
        }
        other => panic!("expected Eq, got {other:?}"),
    }
    // Both A1 and A2 contained {True} = {q} and {p} respectively, so both got
    // removed — the result context is empty.
    assert!(thm.context().is_empty());
}

#[test]
fn deduct_antisym_cancels_each_concl_from_other_ctx() {
    // Canonical use case. A1 = {p, q, y}, thm_p = A1 ⊢ p. A2 = {p, q, z},
    // thm_q = A2 ⊢ q. (A1 \ {q}) ∪ (A2 \ {p}) = {p, y} ∪ {q, z}, deduped
    // by canonical → {p, y, q, z}. Result concl: p = q.
    let mut a = Arena::new();
    let bool_ty = a.bool_ty();
    let pname = a.intern_string("p".into());
    let qname = a.intern_string("q".into());
    let yname = a.intern_string("y".into());
    let zname = a.intern_string("z".into());
    let p = a.alloc_term(TermDef::Free(pname, bool_ty));
    let q = a.alloc_term(TermDef::Free(qname, bool_ty));
    let y = a.alloc_term(TermDef::Free(yname, bool_ty));
    let z = a.alloc_term(TermDef::Free(zname, bool_ty));
    let assum_p = std::sync::Arc::new(Prop::new(Context::empty(), p));
    let assum_q = std::sync::Arc::new(Prop::new(Context::empty(), q));
    let assum_y = std::sync::Arc::new(Prop::new(Context::empty(), y));
    let assum_z = std::sync::Arc::new(Prop::new(Context::empty(), z));

    let ctx1 = Context::flat(vec![assum_p.clone(), assum_q.clone(), assum_y.clone()]);
    let thm_p = Thm::assume(&a, ctx1, assum_p.clone()).unwrap();
    let ctx2 = Context::flat(vec![assum_p.clone(), assum_q.clone(), assum_z.clone()]);
    let thm_q = Thm::assume(&a, ctx2, assum_q.clone()).unwrap();

    let thm = Thm::deduct_antisym_rule(&mut a, thm_p, thm_q).unwrap();
    assert_eq!(thm.context().len(), 4);
    match a.term_def(thm.concl()) {
        TermDef::Eq(l, r) => {
            assert_eq!(*l, TermRef::local(p));
            assert_eq!(*r, TermRef::local(q));
        }
        other => panic!("expected Eq(p, q), got {other:?}"),
    }
}

#[test]
fn deduct_antisym_rejects_type_mismatched_concls() {
    // p : bool (True), q : Nat (0). Eq(p, q) would be ill-typed.
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::Bool(true));
    let n = a.alloc_term(TermDef::nat_inline(0));
    let assum_t = std::sync::Arc::new(Prop::new(Context::empty(), t));
    let assum_n = std::sync::Arc::new(Prop::new(Context::empty(), n));
    let ctx_t = Context::extend(Context::empty(), assum_t.clone());
    let ctx_n = Context::extend(Context::empty(), assum_n.clone());
    let thm_p = Thm::assume(&a, ctx_t, assum_t).unwrap();
    let thm_q = Thm::assume(&a, ctx_n, assum_n).unwrap();
    let err = Thm::deduct_antisym_rule(&mut a, thm_p, thm_q).unwrap_err();
    assert_eq!(err, ProofError::TypeMismatch);
}

#[test]
fn abs_rejects_non_equality_thm() {
    // Thm::assume on a non-Eq concl — abs should reject.
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::Bool(true));
    let assum = std::sync::Arc::new(Prop::new(Context::empty(), t));
    let ctx = Context::extend(Context::empty(), assum.clone());
    let thm_t = Thm::assume(&a, ctx, assum).unwrap();
    let bool_ty = a.bool_ty();
    let xname = a.intern_string("x".into());
    let err = Thm::abs(&mut a, thm_t, xname, bool_ty).unwrap_err();
    assert_eq!(err, ProofError::ExpectedEquality);
}
