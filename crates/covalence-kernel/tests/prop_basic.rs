//! Phase 4 acceptance tests: Context, Prop, Thm + initial inference
//! rules.

use std::sync::Arc;

use covalence_kernel::{Arena, Context, PrimOp1, ProofError, Prop, TermDef, TermRef, Thm};

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
    let t = a.alloc_term(TermDef::True);
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
    let t = a.alloc_term(TermDef::True);
    let f = a.alloc_term(TermDef::False);

    let p1 = Arc::new(Prop::new(Context::empty(), t));
    let p2 = Arc::new(Prop::new(Context::empty(), f));

    let ctx1 = Context::extend(Context::empty(), p1.clone());
    let ctx2 = Context::extend(ctx1.clone(), p2.clone());

    assert_eq!(ctx2.len(), 2);
    assert!(Arc::ptr_eq(ctx2.assumption(0).unwrap(), &p1));
    assert!(Arc::ptr_eq(ctx2.assumption(1).unwrap(), &p2));
    // Parent points back to ctx1.
    assert!(Arc::ptr_eq(ctx2.parent().unwrap(), &ctx1));
}

#[test]
fn contains_prop_searches_chain() {
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::True);
    let p = Arc::new(Prop::new(Context::empty(), t));

    let root = Context::empty();
    assert!(!root.contains_prop(&p));

    let ctx = Context::extend(root.clone(), p.clone());
    assert!(ctx.contains_prop(&p));

    // Add another assumption on top; the original is still found.
    let f = a.alloc_term(TermDef::False);
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
    let t = a.alloc_term(TermDef::True);
    let thm = Thm::refl(&mut a, Context::empty(), t);
    // Conclusion is Eq(t, t).
    match a.term_def(thm.concl()) {
        TermDef::Eq(l, r) => {
            assert_eq!(l.as_local(), Some(t));
            assert_eq!(r.as_local(), Some(t));
        }
        other => panic!("expected Eq(t, t), got {other:?}"),
    }
    // Context is empty.
    assert!(thm.context().is_empty());
}

#[test]
fn thm_assume_extracts_assumption_concl() {
    let mut a = Arena::new();
    let f = a.alloc_term(TermDef::False);
    let prop = Arc::new(Prop::new(Context::empty(), f));
    let ctx = Context::extend(Context::empty(), prop.clone());

    // Now ctx ⊢ false (since false is in context).
    let thm = Thm::assume(ctx.clone(), prop.clone()).unwrap();
    assert_eq!(thm.concl(), f);
    assert!(Arc::ptr_eq(thm.context(), &ctx));
}

#[test]
fn thm_assume_rejects_prop_not_in_ctx() {
    let mut a = Arena::new();
    let f = a.alloc_term(TermDef::False);
    let prop = Arc::new(Prop::new(Context::empty(), f));
    // Use the empty context — prop isn't in it.
    let err = Thm::assume(Context::empty(), prop).unwrap_err();
    assert_eq!(err, ProofError::AssumptionNotInContext);
}

#[test]
fn context_survives_pop_via_arc() {
    // Build a Thm under an extended context, then drop the extended
    // context. The Thm's context still points at a live Arc<Context>.
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::True);
    let prop = Arc::new(Prop::new(Context::empty(), t));

    let thm = {
        let extended = Context::extend(Context::empty(), prop.clone());
        Thm::assume(extended, prop.clone()).unwrap()
        // `extended` dropped here.
    };

    // thm.context() is still valid through Arc.
    assert_eq!(thm.context().len(), 1);
    assert!(thm.context().contains_prop(&prop));
}

#[test]
fn refl_can_be_cloned_and_used_twice() {
    // Phase 4 acceptance: nonlinear Thm — clone, derive two
    // consequences. With only refl + assume we can't yet "derive
    // two consequences", but the Clone itself works.
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::True);
    let thm = Thm::refl(&mut a, Context::empty(), t);
    let thm2 = thm.clone();
    assert_eq!(thm.concl(), thm2.concl());
}

#[test]
fn add_assumption_extends_context() {
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::True);
    let thm = Thm::refl(&mut a, Context::empty(), t);
    let original_concl = thm.concl();

    // Add an assumption — Prop carrying False.
    let f = a.alloc_term(TermDef::False);
    let extra = Arc::new(Prop::new(Context::empty(), f));
    let weakened = thm.add_assumption(extra.clone());

    // Conclusion unchanged, context now contains the new assumption.
    assert_eq!(weakened.concl(), original_concl);
    assert_eq!(weakened.context().len(), 1);
    assert!(weakened.context().contains_prop(&extra));
}

#[test]
fn add_assumption_stacks_multiple() {
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::True);
    let thm = Thm::refl(&mut a, Context::empty(), t);

    let p1 = Arc::new(Prop::new(Context::empty(), t));
    let f = a.alloc_term(TermDef::False);
    let p2 = Arc::new(Prop::new(Context::empty(), f));

    let weakened = thm.add_assumption(p1.clone()).add_assumption(p2.clone());
    assert_eq!(weakened.context().len(), 2);
    assert!(weakened.context().contains_prop(&p1));
    assert!(weakened.context().contains_prop(&p2));
}

#[test]
fn not_from_false_derives_negation() {
    // ctx ⊢ False  ⇒  ctx ⊢ ¬p for any p.
    let mut a = Arena::new();
    // First we need a Thm with conclusion False. Use assume on a
    // Prop carrying False that's in the context.
    let false_term = a.alloc_term(TermDef::False);
    let false_prop = Arc::new(Prop::new(Context::empty(), false_term));
    let ctx = Context::extend(Context::empty(), false_prop.clone());
    let thm_false = Thm::assume(ctx.clone(), false_prop).unwrap();

    // Now derive ¬True.
    let t = a.alloc_term(TermDef::True);
    let not_t = Thm::not_from_false(&mut a, thm_false, t).unwrap();

    // Conclusion should be Op1(LogicalNot, True).
    match a.term_def(not_t.concl()) {
        TermDef::Op1(PrimOp1::LogicalNot, x) => {
            assert_eq!(x.as_local(), Some(t));
        }
        other => panic!("expected Op1(LogicalNot, True), got {other:?}"),
    }
    // Context preserved.
    assert!(Arc::ptr_eq(not_t.context(), &ctx));
}

#[test]
fn not_from_false_rejects_non_false_conclusion() {
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::True);
    let thm = Thm::refl(&mut a, Context::empty(), t);
    // refl's conclusion is Eq(t, t), not False. not_from_false rejects.
    let p = a.alloc_term(TermDef::True);
    let err = Thm::not_from_false(&mut a, thm, p).unwrap_err();
    assert_eq!(err, ProofError::ConclusionNotFalse);
}

#[test]
fn nonlinear_thm_clone_combine() {
    // Take a Thm, clone it, derive two consequences (via weakening
    // into different extended contexts), use both.
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::True);
    let thm = Thm::refl(&mut a, Context::empty(), t);

    let f = a.alloc_term(TermDef::False);
    let p_extra = Arc::new(Prop::new(Context::empty(), f));

    let thm1 = thm.clone().add_assumption(p_extra.clone());
    let thm2 = thm.add_assumption(p_extra.clone());

    // Both derived Thms have the same conclusion (the original refl).
    assert_eq!(thm1.concl(), thm2.concl());
    assert!(thm1.context().contains_prop(&p_extra));
    assert!(thm2.context().contains_prop(&p_extra));
}

#[test]
fn sym_flips_equality() {
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::True);
    let refl_thm = Thm::refl(&mut a, Context::empty(), t);
    // refl gives Eq(t, t), which is symmetric to itself.
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
    let t = a.alloc_term(TermDef::True);
    let assumption_prop = Arc::new(Prop::new(Context::empty(), t));
    let ctx = Context::extend(Context::empty(), assumption_prop.clone());
    let thm = Thm::assume(ctx, assumption_prop).unwrap();
    // Conclusion is `True`, not an Eq.
    let err = Thm::sym(&mut a, thm).unwrap_err();
    assert_eq!(err, ProofError::ExpectedEquality);
}

#[test]
fn trans_chains_equalities() {
    // We construct a = b and b = c via refl + sym + manual allocation;
    // for the MVP, the cleanest demo uses refl alone since we lack
    // congruence rules. Two refl Thms on the same term give us
    // (t = t) and (t = t), which chain to (t = t).
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::True);
    let ctx = Context::empty();
    let ab = Thm::refl(&mut a, ctx.clone(), t);
    let bc = Thm::refl(&mut a, ctx.clone(), t);
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
    // Build two structurally-distinct nat literal terms for the same
    // value, union them, then trans should accept them as a valid
    // midpoint.
    let mut a = Arena::new();
    let n1 = a.alloc_term(TermDef::nat_inline(5));
    let n2 = a.alloc_term(TermDef::nat_inline(5));
    a.union(TermRef::local(n1), TermRef::local(n2)).unwrap();

    // ab : n1 = n1  (refl on n1)
    // bc : n2 = n2  (refl on n2)
    // After union, n1 ≡ n2 at level 0, so the trans midpoints match.
    let ctx = Context::empty();
    let ab = Thm::refl(&mut a, ctx.clone(), n1);
    let bc = Thm::refl(&mut a, ctx.clone(), n2);
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
    let t = a.alloc_term(TermDef::True);
    let prop = Arc::new(Prop::new(Context::empty(), t));
    let ctx1 = Context::empty();
    let ctx2 = Context::extend(Context::empty(), prop);
    let ab = Thm::refl(&mut a, ctx1, t);
    let bc = Thm::refl(&mut a, ctx2, t);
    let err = Thm::trans(&mut a, ab, bc).unwrap_err();
    assert_eq!(err, ProofError::ContextMismatch);
}

#[test]
fn eq_mp_derives_rhs_from_lhs() {
    // We want: ctx ⊢ p = q and ctx ⊢ p ⇒ ctx ⊢ q.
    // Easiest setup: put p in the context, assume it, and build
    // p = p via refl. eq_mp then gives us q = p back.
    let mut a = Arena::new();
    let p = a.alloc_term(TermDef::True);
    let p_prop = Arc::new(Prop::new(Context::empty(), p));
    let ctx = Context::extend(Context::empty(), p_prop.clone());
    let p_thm = Thm::assume(ctx.clone(), p_prop).unwrap();
    let pq = Thm::refl(&mut a, ctx.clone(), p);
    // pq is p = p, so eq_mp(pq, p_thm) ⊢ p.
    let q_thm = Thm::eq_mp(&mut a, pq, p_thm).unwrap();
    assert_eq!(q_thm.concl(), p);
}

#[test]
fn eq_mp_rejects_lhs_mismatch() {
    let mut a = Arena::new();
    let p = a.alloc_term(TermDef::True);
    let q = a.alloc_term(TermDef::False);
    let q_prop = Arc::new(Prop::new(Context::empty(), q));
    let ctx = Context::extend(Context::empty(), q_prop.clone());
    let q_thm = Thm::assume(ctx.clone(), q_prop).unwrap();
    // pq = p = p. eq_mp(pq, q_thm) — q_thm.concl is q, doesn't match p.
    let pq = Thm::refl(&mut a, ctx.clone(), p);
    let err = Thm::eq_mp(&mut a, pq, q_thm).unwrap_err();
    assert_eq!(err, ProofError::LhsMismatch);
}

#[test]
fn thm_field_is_kernel_only() {
    // Compile-time test: external code can read prop() but cannot
    // construct a Thm directly from a Prop.
    //
    // The body of this test only verifies that the kernel-constructed
    // Thm exposes its Prop. The "cannot construct directly" guarantee
    // is enforced by the private `prop` field; if external code tried
    //
    //     Thm { prop: my_prop }  // <- would fail: field is private
    //
    // the compiler would reject it.
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::True);
    let thm = Thm::refl(&mut a, Context::empty(), t);
    let prop_ref = thm.prop();
    let _: &Prop = prop_ref;
}
