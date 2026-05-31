//! Phase 1 acceptance tests: arena allocation, builtin variants,
//! closed-flag computation, freezing, foreign imports, and the
//! diamond-import canonical-identity property.

use std::sync::Arc;

use covalence_kernel::{
    Arena, BitsValue, ConstName, TermDef, TermRef, TypeDef, TypeName, TypeRef, TypeVarId, VarName,
};

// ---------------------------------------------------------------------------
// Builtin TypeDef and TermDef variants are constructable directly.
// ---------------------------------------------------------------------------

#[test]
fn alloc_builtin_types() {
    let mut a = Arena::new();
    let bool_id = a.alloc_type(TypeDef::Bool);
    let bits_id = a.alloc_type(TypeDef::Bits);
    let fun_id = a.alloc_type(TypeDef::Fun(
        TypeRef::Local(bool_id),
        TypeRef::Local(bits_id),
    ));

    assert_eq!(a.type_def(bool_id), &TypeDef::Bool);
    assert_eq!(a.type_def(bits_id), &TypeDef::Bits);
    match a.type_def(fun_id) {
        TypeDef::Fun(TypeRef::Local(d), TypeRef::Local(c)) => {
            assert_eq!(*d, bool_id);
            assert_eq!(*c, bits_id);
        }
        other => panic!("expected Fun(Local, Local), got {other:?}"),
    }
}

#[test]
fn alloc_builtin_terms() {
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::True);
    let f = a.alloc_term(TermDef::False);
    let eq = a.alloc_term(TermDef::Eq(TermRef::Local(t), TermRef::Local(f)));

    assert_eq!(a.term_def(t), &TermDef::True);
    assert_eq!(a.term_def(f), &TermDef::False);
    match a.term_def(eq) {
        TermDef::Eq(TermRef::Local(l), TermRef::Local(r)) => {
            assert_eq!(*l, t);
            assert_eq!(*r, f);
        }
        other => panic!("expected Eq, got {other:?}"),
    }
}

#[test]
fn alloc_bits_inline_and_indirect() {
    let mut a = Arena::new();
    // Short: stays inline.
    let short_value = a.alloc_bits(vec![1, 2, 3, 4]);
    assert!(matches!(short_value, BitsValue::Inline(_)));

    // Long: spills to the bitvectors table.
    let long_bytes: Vec<u8> = (0..200).collect();
    let long_value = a.alloc_bits(long_bytes.clone());
    match long_value {
        BitsValue::Indirect(id) => {
            assert_eq!(a.bits(id), long_bytes.as_slice());
        }
        BitsValue::Inline(_) => panic!("expected Indirect for 200-byte literal"),
    }
}

// ---------------------------------------------------------------------------
// Closed flag.
// ---------------------------------------------------------------------------

#[test]
fn closed_true_for_constants_and_builtins() {
    let mut a = Arena::new();
    let bool_ty = a.alloc_type(TypeDef::Bool);
    let t = a.alloc_term(TermDef::True);
    let f = a.alloc_term(TermDef::False);
    let c = a.alloc_term(TermDef::Const(
        ConstName::new("foo"),
        TypeRef::Local(bool_ty),
    ));
    let bits = a.alloc_term(TermDef::Bits(BitsValue::Inline(vec![0xff])));

    for id in [t, f, c, bits] {
        assert!(a.term_uf(id).closed(), "term {id:?} should be closed");
    }
}

#[test]
fn closed_false_for_free_var() {
    let mut a = Arena::new();
    let bool_ty = a.alloc_type(TypeDef::Bool);
    let x = a.alloc_term(TermDef::Free(VarName::new("x"), TypeRef::Local(bool_ty)));
    assert!(!a.term_uf(x).closed());
    assert!(a.term_uf(x).has_free);
}

#[test]
fn closed_propagates_through_comb() {
    let mut a = Arena::new();
    let bool_ty = a.alloc_type(TypeDef::Bool);
    let bool_to_bool =
        a.alloc_type(TypeDef::Fun(TypeRef::Local(bool_ty), TypeRef::Local(bool_ty)));

    let t = a.alloc_term(TermDef::True);
    let neg = a.alloc_term(TermDef::Const(
        ConstName::new("not"),
        TypeRef::Local(bool_to_bool),
    ));
    let app = a.alloc_term(TermDef::Comb(TermRef::Local(neg), TermRef::Local(t)));
    assert!(a.term_uf(app).closed());

    // With a free var inside, openness propagates.
    let x = a.alloc_term(TermDef::Free(VarName::new("x"), TypeRef::Local(bool_ty)));
    let app_open = a.alloc_term(TermDef::Comb(TermRef::Local(neg), TermRef::Local(x)));
    assert!(!a.term_uf(app_open).closed());
}

#[test]
fn abs_binds_one_level_of_bound() {
    let mut a = Arena::new();
    let bool_ty = a.alloc_type(TypeDef::Bool);

    let b0 = a.alloc_term(TermDef::Bound(0));
    // Bound(0) at the top has bound_depth = 1, not closed.
    assert_eq!(a.term_uf(b0).bound_depth, 1);
    assert!(!a.term_uf(b0).closed());

    // Wrapping it in one Abs binds it.
    let abs = a.alloc_term(TermDef::Abs(
        VarName::new("x"),
        TypeRef::Local(bool_ty),
        TermRef::Local(b0),
    ));
    assert_eq!(a.term_uf(abs).bound_depth, 0);
    assert!(a.term_uf(abs).closed());
}

#[test]
fn abs_needs_two_levels_for_bound_one() {
    let mut a = Arena::new();
    let bool_ty = a.alloc_type(TypeDef::Bool);

    let b1 = a.alloc_term(TermDef::Bound(1));
    assert_eq!(a.term_uf(b1).bound_depth, 2);

    let inner = a.alloc_term(TermDef::Abs(
        VarName::new("y"),
        TypeRef::Local(bool_ty),
        TermRef::Local(b1),
    ));
    // After one Abs, bound_depth drops to 1 — still open.
    assert_eq!(a.term_uf(inner).bound_depth, 1);
    assert!(!a.term_uf(inner).closed());

    let outer = a.alloc_term(TermDef::Abs(
        VarName::new("x"),
        TypeRef::Local(bool_ty),
        TermRef::Local(inner),
    ));
    // After two Abs's, it's closed.
    assert_eq!(a.term_uf(outer).bound_depth, 0);
    assert!(a.term_uf(outer).closed());
}

// ---------------------------------------------------------------------------
// Canonical: a fresh term is its own canonical.
// ---------------------------------------------------------------------------

#[test]
fn fresh_term_is_self_canonical() {
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::True);
    let canon = a.canonical_term(&TermRef::Local(t));
    assert_eq!(canon, TermRef::Local(t));
}

#[test]
fn fresh_type_is_self_canonical() {
    let mut a = Arena::new();
    let b = a.alloc_type(TypeDef::Bool);
    let canon = a.canonical_type(&TypeRef::Local(b));
    assert_eq!(canon, TypeRef::Local(b));
}

// ---------------------------------------------------------------------------
// Freezing and unfreezing.
// ---------------------------------------------------------------------------

#[test]
fn freeze_then_read() {
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::True);
    let frozen = a.freeze();
    assert_eq!(frozen.term_def(t), &TermDef::True);
}

#[test]
fn unfreeze_keeps_indices() {
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::True);
    let frozen = a.freeze();
    let mut thawed = Arena::unfreeze(&frozen);

    // Same id still resolves on the thawed copy.
    assert_eq!(thawed.term_def(t), &TermDef::True);
    // And we can keep allocating.
    let f = thawed.alloc_term(TermDef::False);
    assert_eq!(thawed.term_def(f), &TermDef::False);

    // The frozen original is identity-distinct from the thawed copy.
    let frozen_again = thawed.freeze();
    assert!(
        !Arc::ptr_eq(&frozen, &frozen_again),
        "unfreeze must produce a fresh allocation"
    );
}

// ---------------------------------------------------------------------------
// Foreign imports + arena identity.
// ---------------------------------------------------------------------------

#[test]
fn foreign_ref_resolves_back_to_source() {
    // Arena d defines a constant.
    let mut d = Arena::new();
    let bool_ty_d = d.alloc_type(TypeDef::Bool);
    let c_d = d.alloc_term(TermDef::Const(
        ConstName::new("c"),
        TypeRef::Local(bool_ty_d),
    ));
    let d_frozen = d.freeze();

    // Arena a imports d and reads back the constant.
    let mut a = Arena::new();
    a.add_import(d_frozen.clone());
    let foreign = TermRef::Foreign(d_frozen.clone(), c_d);
    let canon = a.canonical_term(&foreign);
    // Canonical is back in d.
    match canon {
        TermRef::Foreign(arc, id) => {
            assert!(Arc::ptr_eq(&arc, &d_frozen));
            assert_eq!(id, c_d);
        }
        other => panic!("expected Foreign(d, c), got {other:?}"),
    }
}

#[test]
fn add_import_dedupes() {
    let d = Arena::new().freeze();
    let mut a = Arena::new();
    a.add_import(d.clone());
    a.add_import(d.clone());
    assert_eq!(a.imports().len(), 1);
    assert!(Arc::ptr_eq(&a.imports()[0], &d));
}

// ---------------------------------------------------------------------------
// Diamond-import test (architecture §4.1).
//
//        D
//       / \
//      B   C
//       \ /
//        A
//
// Both B and C foreign-import the same term x ∈ D. Their copies have
// canonical = (Arc<D>, x_id). Because both copies hold the *same*
// Arc<D> allocation, pointer equality (Arc::ptr_eq) holds and the
// two copies are canonically identical from A's view.
// ---------------------------------------------------------------------------

#[test]
fn diamond_import_regains_canonical_identity() {
    // Build D first and freeze it. This is the shared ancestor.
    let mut d = Arena::new();
    let bool_d = d.alloc_type(TypeDef::Bool);
    let x_d = d.alloc_term(TermDef::Free(VarName::new("x"), TypeRef::Local(bool_d)));
    let d_frozen = d.freeze();

    // Build B importing D, with a term that references x via Foreign.
    let mut b = Arena::new();
    b.add_import(d_frozen.clone());
    let x_in_b = TermRef::Foreign(d_frozen.clone(), x_d);

    // Build C importing D, similarly.
    let mut c = Arena::new();
    c.add_import(d_frozen.clone());
    let x_in_c = TermRef::Foreign(d_frozen.clone(), x_d);

    let b_frozen = b.freeze();
    let c_frozen = c.freeze();

    // Build A importing both B and C. From A's perspective, the two
    // copies of x — one routed through B, one through C — should
    // canonically agree because both ultimately point at (Arc<D>, x_d).
    let mut a = Arena::new();
    a.add_import(b_frozen.clone());
    a.add_import(c_frozen.clone());

    let canon_via_b = a.canonical_term(&x_in_b);
    let canon_via_c = a.canonical_term(&x_in_c);

    assert_eq!(
        canon_via_b, canon_via_c,
        "shared D-subterm should regain canonical identity through both routes"
    );

    match canon_via_b {
        TermRef::Foreign(arc, id) => {
            assert!(
                Arc::ptr_eq(&arc, &d_frozen),
                "canonical should point at the shared D allocation"
            );
            assert_eq!(id, x_d);
        }
        other => panic!("expected Foreign(D, x_d), got {other:?}"),
    }
}

#[test]
fn distinct_arenas_with_same_content_are_not_canonically_equal() {
    // Two separately-built arenas that contain "the same" term are
    // *not* the same arena. Identity is by pointer.
    let mut a1 = Arena::new();
    let b1 = a1.alloc_type(TypeDef::Bool);
    let _t1 = a1.alloc_term(TermDef::Free(VarName::new("x"), TypeRef::Local(b1)));
    let a1_frozen = a1.freeze();

    let mut a2 = Arena::new();
    let b2 = a2.alloc_type(TypeDef::Bool);
    let _t2 = a2.alloc_term(TermDef::Free(VarName::new("x"), TypeRef::Local(b2)));
    let a2_frozen = a2.freeze();

    assert!(
        !Arc::ptr_eq(&a1_frozen, &a2_frozen),
        "fresh allocations must be pointer-distinct"
    );
    // The TermRefs into the two arenas compare unequal even though
    // they hold the same TermId, because the arena pointers differ.
    let r1 = TermRef::Foreign(a1_frozen.clone(), covalence_kernel::TermId(0));
    let r2 = TermRef::Foreign(a2_frozen.clone(), covalence_kernel::TermId(0));
    assert_ne!(r1, r2);
}

// ---------------------------------------------------------------------------
// User-side namespaces stay distinct.
// ---------------------------------------------------------------------------

#[test]
fn const_and_var_names_are_distinct_types() {
    // This is a compile-time check more than a runtime one: ConstName
    // and VarName are distinct types even when they hold the same
    // string content, so callers can't accidentally swap them.
    let c = ConstName::new("foo");
    let v = VarName::new("foo");
    assert_eq!(c.as_str(), v.as_str());
    // (No direct equality possible — they're different types.)
}

#[test]
fn type_name_and_tvar_id_are_distinct() {
    let tn = TypeName::new("list");
    let tv = TypeVarId::new("'a");
    assert_eq!(tn.as_str(), "list");
    assert_eq!(tv.as_str(), "'a");
}
