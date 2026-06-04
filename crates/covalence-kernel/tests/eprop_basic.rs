//! Phase P3 tests: the new `EProp` / `EThm` shape.

use std::sync::Arc;

use covalence_kernel::{EProp, EThm, TermDef};

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
fn ethm_truth_seeds_a_trivially_true_thm() {
    let prop = EProp::new();
    let _thm = EThm::truth(prop);
}

#[test]
fn refl_unions_eq_with_true() {
    // Build a free var `x : Bool` in a fresh EProp, then call refl
    // and check that the resulting Eq(x, x) term is UF-equal to
    // Bool(true) via the canonical truth_ref.
    let mut prop = EProp::new();
    let bool_ty = prop.egraph.arena.bool_ty();
    let name = prop.egraph.arena.intern_string("x".into());
    let x = prop.egraph.arena.alloc_term(TermDef::Free(name, bool_ty));
    let mut thm = EThm::truth(prop);

    let eq_ref = thm.refl(x).expect("well-typed Free is well-typed");

    let mut prop = thm.into_inner();
    assert!(prop.knows_true(eq_ref), "refl should mark Eq(x, x) as true");
}

#[test]
fn refl_rejects_ill_typed_term() {
    let mut prop = EProp::new();
    // Bound(0) at the top level has unbound depth > 0 → IllTyped.
    let bad = prop.egraph.arena.alloc_term(TermDef::Bound(0));
    let mut thm = EThm::truth(prop);
    let err = thm.refl(bad).unwrap_err();
    assert_eq!(err, covalence_kernel::ProofError::IllTypedInput);
}

#[test]
fn refl_returns_the_eq_termref() {
    let mut prop = EProp::new();
    let bool_ty = prop.egraph.arena.bool_ty();
    let name = prop.egraph.arena.intern_string("p".into());
    let p = prop.egraph.arena.alloc_term(TermDef::Free(name, bool_ty));
    let mut thm = EThm::truth(prop);

    let eq_ref = thm.refl(p).unwrap();
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
