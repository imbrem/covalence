//! Phase P3 tests: the new `EProp` / `EThm` shape.

use std::sync::Arc;

use covalence_kernel::{EProp, EThm, TermDef, TermRef};

#[test]
fn eprop_default_is_empty() {
    let p = EProp::new();
    assert!(p.precondition.is_none());
    assert!(p.precondition_chain().is_empty());
}

#[test]
fn precondition_chain_walks_innermost_first() {
    let p1 = Arc::new(EProp::new());
    let p2 = Arc::new(EProp::new().with_precondition(p1.clone()));
    let p3 = EProp::new().with_precondition(p2.clone());

    let chain = p3.precondition_chain();
    assert_eq!(chain.len(), 2);
    assert!(Arc::ptr_eq(&chain[0], &p2));
    assert!(Arc::ptr_eq(&chain[1], &p1));
}

#[test]
fn ethm_empty_proves_nothing_yet() {
    let mut prop = EProp::new();
    let bool_ty = prop.egraph.arena.bool_ty();
    let aname = prop.egraph.arena.intern_string("a".into());
    let a = prop.egraph.arena.alloc_term(TermDef::Free(aname, bool_ty));
    let bname = prop.egraph.arena.intern_string("b".into());
    let b = prop.egraph.arena.alloc_term(TermDef::Free(bname, bool_ty));
    let thm = EThm::empty(prop);
    // No unions yet — distinct TermIds are not UF-equal.
    assert!(!thm.eq(TermRef::local(a), TermRef::local(b)));
}

#[test]
fn refl_makes_eq_t_t_equal_to_caller_truth() {
    // Userspace allocates a Bool(true) and threads it through. Refl
    // unions Eq(x, x) with that user-chosen truth.
    let mut prop = EProp::new();
    let bool_ty = prop.egraph.arena.bool_ty();
    let xname = prop.egraph.arena.intern_string("x".into());
    let x = prop.egraph.arena.alloc_term(TermDef::Free(xname, bool_ty));
    let truth = TermRef::local(prop.egraph.arena.alloc_term(TermDef::Bool(true)));
    let mut thm = EThm::empty(prop);

    let eq_ref = thm.refl(x, truth).expect("well-typed Free");

    // Query the Thm: Eq(x, x) is provably equal to truth.
    assert!(thm.eq(eq_ref, truth));
    // The terms `x` and `truth` themselves aren't unified — only
    // the Eq(x, x) wrapper.
    assert!(!thm.eq(TermRef::local(x), truth));
}

#[test]
fn refl_rejects_ill_typed_term() {
    let mut prop = EProp::new();
    let bad = prop.egraph.arena.alloc_term(TermDef::Bound(0));
    let truth = TermRef::local(prop.egraph.arena.alloc_term(TermDef::Bool(true)));
    let mut thm = EThm::empty(prop);
    let err = thm.refl(bad, truth).unwrap_err();
    assert_eq!(err, covalence_kernel::ProofError::IllTypedInput);
}

#[test]
fn refl_returns_eq_termref_decoding_to_eq_t_t() {
    // The eq_ref the caller gets back decodes as Eq(t, t) in the
    // same arena.
    let mut prop = EProp::new();
    let bool_ty = prop.egraph.arena.bool_ty();
    let pname = prop.egraph.arena.intern_string("p".into());
    let p = prop.egraph.arena.alloc_term(TermDef::Free(pname, bool_ty));
    let truth = TermRef::local(prop.egraph.arena.alloc_term(TermDef::Bool(true)));
    let mut thm = EThm::empty(prop);

    let eq_ref = thm.refl(p, truth).unwrap();
    let prop = thm.into_inner();
    let eq_id = eq_ref.as_local().unwrap();
    match prop.egraph.arena.term_def(eq_id) {
        TermDef::Eq(l, r) => {
            assert_eq!(l.as_local(), Some(p));
            assert_eq!(r.as_local(), Some(p));
        }
        other => panic!("expected Eq, got {other:?}"),
    }
}

#[test]
fn one_big_thm_accumulates_facts_across_rule_calls() {
    // Demonstrate the idiomatic flow: one EThm, one user-chosen
    // truth ref, multiple rule calls accumulate unions in the
    // egraph. Each refl call adds another Eq(_, _) -> truth fact.
    let mut prop = EProp::new();
    let bool_ty = prop.egraph.arena.bool_ty();
    let xname = prop.egraph.arena.intern_string("x".into());
    let yname = prop.egraph.arena.intern_string("y".into());
    let x = prop.egraph.arena.alloc_term(TermDef::Free(xname, bool_ty));
    let y = prop.egraph.arena.alloc_term(TermDef::Free(yname, bool_ty));
    let truth = TermRef::local(prop.egraph.arena.alloc_term(TermDef::Bool(true)));
    let mut thm = EThm::empty(prop);

    let eq_xx = thm.refl(x, truth).unwrap();
    let eq_yy = thm.refl(y, truth).unwrap();

    assert!(thm.eq(eq_xx, truth));
    assert!(thm.eq(eq_yy, truth));
    // Both unioned with the same truth → they're now UF-equal to each
    // other transitively.
    assert!(thm.eq(eq_xx, eq_yy));
}
