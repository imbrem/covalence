//! Phase H tests: content hashing of arenas, Props, and EProps.

use std::sync::Arc;

use covalence_kernel::{
    Arena, Context, EProp, EThm, Prop, TermDef, TermRef,
};

#[test]
fn empty_arenas_hash_identically() {
    let a = Arena::new();
    let b = Arena::new();
    assert_eq!(a.hash(), b.hash());
}

#[test]
fn allocating_a_term_changes_the_hash() {
    let mut a = Arena::new();
    let before = a.hash();
    let _ = a.alloc_term(TermDef::Bool(true));
    let after = a.hash();
    assert_ne!(before, after);
}

#[test]
fn structurally_identical_arenas_hash_the_same() {
    // Build the SAME sequence of allocations in two arenas — same
    // bytes, same hash.
    fn build() -> Arena {
        let mut a = Arena::new();
        let bool_ty = a.bool_ty();
        let xname = a.intern_string("x".into());
        let x = a.alloc_term(TermDef::Free(xname, bool_ty));
        let _ = a.alloc_term(TermDef::Eq(TermRef::local(x), TermRef::local(x)));
        a
    }
    let h1 = build().hash();
    let h2 = build().hash();
    assert_eq!(h1, h2);
}

#[test]
fn allocation_order_changes_the_hash() {
    // Same logical content, different allocation order → different
    // hashes. The kernel does NOT canonicalise: hash → arena is
    // injective; the reverse is not. (Phase H design constraint.)
    let mut a = Arena::new();
    let _ = a.alloc_term(TermDef::Bool(true));
    let _ = a.alloc_term(TermDef::Bool(false));
    let h_tf = a.hash();

    let mut b = Arena::new();
    let _ = b.alloc_term(TermDef::Bool(false));
    let _ = b.alloc_term(TermDef::Bool(true));
    let h_ft = b.hash();

    assert_ne!(h_tf, h_ft);
}

#[test]
fn prop_hash_depends_on_arena_and_concl() {
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::Bool(true));
    let f = a.alloc_term(TermDef::Bool(false));
    let prop_t = Prop::new(Context::empty(), t);
    let prop_f = Prop::new(Context::empty(), f);
    assert_ne!(prop_t.hash(&a), prop_f.hash(&a));
}

#[test]
fn prop_hash_includes_context_preconditions() {
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::Bool(true));
    let f = a.alloc_term(TermDef::Bool(false));

    let assum = Arc::new(Prop::new(Context::empty(), f));
    let ctx = Context::extend(Context::empty(), assum.clone());
    let p_no_ctx = Prop::new(Context::empty(), t);
    let p_with_ctx = Prop::new(ctx, t);
    assert_ne!(p_no_ctx.hash(&a), p_with_ctx.hash(&a));
}

#[test]
fn eprop_hash_distinguishes_distinct_contents() {
    let p1 = EProp::new();
    let mut p2 = EProp::new();
    let _ = p2.egraph.arena.alloc_term(TermDef::Bool(true));
    assert_ne!(p1.hash(), p2.hash());
}

#[test]
fn eprop_hash_includes_precondition_chain() {
    let parent = Arc::new(EProp::new());
    let child = EProp::new().with_precondition(parent.clone());
    let standalone = EProp::new();
    assert_ne!(child.hash(), standalone.hash());
}

#[test]
fn ethm_hash_matches_underlying_eprop() {
    let prop = EProp::new();
    let expected = prop.hash();
    let thm = EThm::empty(prop);
    assert_eq!(thm.hash(), expected);
}
