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
        TypeRef::local(bool_id),
        TypeRef::local(bits_id),
    ));

    assert_eq!(a.type_def(bool_id), &TypeDef::Bool);
    assert_eq!(a.type_def(bits_id), &TypeDef::Bits);
    match a.type_def(fun_id) {
        TypeDef::Fun(d, c) => {
            assert_eq!(d.as_local(), Some(bool_id));
            assert_eq!(c.as_local(), Some(bits_id));
        }
        other => panic!("expected Fun, got {other:?}"),
    }
}

#[test]
fn alloc_builtin_terms() {
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::True);
    let f = a.alloc_term(TermDef::False);
    let eq = a.alloc_term(TermDef::Eq(TermRef::local(t), TermRef::local(f)));

    assert_eq!(a.term_def(t), &TermDef::True);
    assert_eq!(a.term_def(f), &TermDef::False);
    match a.term_def(eq) {
        TermDef::Eq(l, r) => {
            assert_eq!(l.as_local(), Some(t));
            assert_eq!(r.as_local(), Some(f));
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

    // Long: spills to the bits side table.
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
        TypeRef::local(bool_ty),
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
    let x = a.alloc_term(TermDef::Free(VarName::new("x"), TypeRef::local(bool_ty)));
    assert!(!a.term_uf(x).closed());
    assert!(a.term_uf(x).has_free);
}

#[test]
fn closed_propagates_through_comb() {
    let mut a = Arena::new();
    let bool_ty = a.alloc_type(TypeDef::Bool);
    let bool_to_bool = a.alloc_type(TypeDef::Fun(
        TypeRef::local(bool_ty),
        TypeRef::local(bool_ty),
    ));

    let t = a.alloc_term(TermDef::True);
    let neg = a.alloc_term(TermDef::Const(
        ConstName::new("not"),
        TypeRef::local(bool_to_bool),
    ));
    let app = a.alloc_term(TermDef::Comb(TermRef::local(neg), TermRef::local(t)));
    assert!(a.term_uf(app).closed());

    // With a free var inside, openness propagates.
    let x = a.alloc_term(TermDef::Free(VarName::new("x"), TypeRef::local(bool_ty)));
    let app_open = a.alloc_term(TermDef::Comb(TermRef::local(neg), TermRef::local(x)));
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
        TypeRef::local(bool_ty),
        TermRef::local(b0),
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
        TypeRef::local(bool_ty),
        TermRef::local(b1),
    ));
    // After one Abs, bound_depth drops to 1 — still open.
    assert_eq!(a.term_uf(inner).bound_depth, 1);
    assert!(!a.term_uf(inner).closed());

    let outer = a.alloc_term(TermDef::Abs(
        VarName::new("x"),
        TypeRef::local(bool_ty),
        TermRef::local(inner),
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
    let arc = a.freeze();
    let canon = Arena::canonical_term(&arc, TermRef::local(t));
    assert!(Arc::ptr_eq(&canon.0, &arc));
    assert_eq!(canon.1, t);
}

#[test]
fn fresh_type_is_self_canonical() {
    let mut a = Arena::new();
    let b = a.alloc_type(TypeDef::Bool);
    let arc = a.freeze();
    let canon = Arena::canonical_type(&arc, TypeRef::local(b));
    assert!(Arc::ptr_eq(&canon.0, &arc));
    assert_eq!(canon.1, b);
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
        TypeRef::local(bool_ty_d),
    ));
    let d_frozen = d.freeze();

    // Arena a imports d and reads back the constant.
    let mut a = Arena::new();
    let imp_d = a.add_import(d_frozen.clone());
    let foreign_ref = a.foreign_term_ref(imp_d, c_d);
    let a_arc = a.freeze();
    let canon = Arena::canonical_term(&a_arc, foreign_ref);
    // Canonical is back in d.
    assert!(Arc::ptr_eq(&canon.0, &d_frozen));
    assert_eq!(canon.1, c_d);
}

#[test]
fn foreign_term_ref_dedupes() {
    let d = Arena::new().freeze();
    let mut a = Arena::new();
    let imp = a.add_import(d.clone());
    let r1 = a.foreign_term_ref(imp, covalence_kernel::TermId(0));
    let r2 = a.foreign_term_ref(imp, covalence_kernel::TermId(0));
    assert_eq!(r1, r2);
}

#[test]
fn add_import_dedupes() {
    let d = Arena::new().freeze();
    let mut a = Arena::new();
    let i1 = a.add_import(d.clone());
    let i2 = a.add_import(d.clone());
    assert_eq!(i1, i2);
    assert_eq!(a.imports().len(), 1);
    assert!(Arc::ptr_eq(&a.imports()[0], &d));
}

// ---------------------------------------------------------------------------
// Diamond-import test (architecture §4.1).
// ---------------------------------------------------------------------------

#[test]
fn diamond_import_regains_canonical_identity() {
    // Build D first and freeze it.
    let mut d = Arena::new();
    let bool_d = d.alloc_type(TypeDef::Bool);
    let x_d = d.alloc_term(TermDef::Free(VarName::new("x"), TypeRef::local(bool_d)));
    let d_frozen = d.freeze();

    // Build B importing D.
    let mut b = Arena::new();
    let imp_d_in_b = b.add_import(d_frozen.clone());
    let x_in_b = b.foreign_term_ref(imp_d_in_b, x_d);

    // Build C importing D similarly.
    let mut c = Arena::new();
    let imp_d_in_c = c.add_import(d_frozen.clone());
    let x_in_c = c.foreign_term_ref(imp_d_in_c, x_d);

    let b_frozen = b.freeze();
    let c_frozen = c.freeze();

    // Build A importing both.
    let mut a = Arena::new();
    let _imp_b = a.add_import(b_frozen.clone());
    let _imp_c = a.add_import(c_frozen.clone());
    let a_arc = a.freeze();

    let canon_via_b = Arena::canonical_term(&b_frozen, x_in_b);
    let canon_via_c = Arena::canonical_term(&c_frozen, x_in_c);

    assert!(
        Arc::ptr_eq(&canon_via_b.0, &canon_via_c.0),
        "shared D-subterm should resolve to the same arena via both routes"
    );
    assert!(
        Arc::ptr_eq(&canon_via_b.0, &d_frozen),
        "canonical should point at the shared D allocation"
    );
    assert_eq!(canon_via_b.1, x_d);
    assert_eq!(canon_via_c.1, x_d);

    assert_eq!(a_arc.imports().len(), 2);
}

#[test]
fn distinct_arenas_with_same_content_are_not_canonically_equal() {
    let mut a1 = Arena::new();
    let b1 = a1.alloc_type(TypeDef::Bool);
    let _t1 = a1.alloc_term(TermDef::Free(VarName::new("x"), TypeRef::local(b1)));
    let a1_frozen = a1.freeze();

    let mut a2 = Arena::new();
    let b2 = a2.alloc_type(TypeDef::Bool);
    let _t2 = a2.alloc_term(TermDef::Free(VarName::new("x"), TypeRef::local(b2)));
    let a2_frozen = a2.freeze();

    assert!(
        !Arc::ptr_eq(&a1_frozen, &a2_frozen),
        "fresh allocations must be pointer-distinct"
    );

    // A third arena that imports both — foreign refs into a1 vs a2
    // get distinct foreign-table entries even with the same TermId.
    let mut a3 = Arena::new();
    let imp_a1 = a3.add_import(a1_frozen.clone());
    let imp_a2 = a3.add_import(a2_frozen.clone());
    assert_ne!(imp_a1, imp_a2);
    let r1 = a3.foreign_term_ref(imp_a1, covalence_kernel::TermId(0));
    let r2 = a3.foreign_term_ref(imp_a2, covalence_kernel::TermId(0));
    assert_ne!(r1, r2);
}

// ---------------------------------------------------------------------------
// User-side namespaces stay distinct.
// ---------------------------------------------------------------------------

#[test]
fn const_and_var_names_are_distinct_types() {
    let c = ConstName::new("foo");
    let v = VarName::new("foo");
    assert_eq!(c.as_str(), v.as_str());
}

#[test]
fn type_name_and_tvar_id_are_distinct() {
    let tn = TypeName::new("list");
    let tv = TypeVarId::new("'a");
    assert_eq!(tn.as_str(), "list");
    assert_eq!(tv.as_str(), "'a");
}

// ---------------------------------------------------------------------------
// Interning tables.
// ---------------------------------------------------------------------------

#[test]
fn intern_string_dedupes() {
    let mut a = Arena::new();
    let s1 = a.intern_string("foo".into());
    let s2 = a.intern_string("foo".into());
    let s3 = a.intern_string("bar".into());
    assert_eq!(s1, s2);
    assert_ne!(s1, s3);
    assert_eq!(a.string(s1).as_str(), "foo");
    assert_eq!(a.string(s3).as_str(), "bar");
}

#[test]
fn intern_bytes_and_tyargs() {
    let mut a = Arena::new();
    let bool_ty = a.alloc_type(TypeDef::Bool);

    let by = a.intern_bytes(vec![1, 2, 3]);
    assert_eq!(a.bytes_value(by), &[1, 2, 3]);

    let args = a.intern_tyargs(vec![TypeRef::local(bool_ty)]);
    assert_eq!(a.tyargs(args), &[TypeRef::local(bool_ty)]);
}

#[cfg(feature = "int")]
#[test]
fn intern_int_and_nat() {
    use covalence_types::{Int, Nat};
    let mut a = Arena::new();
    let i = a.intern_int(Int::from(-42i64));
    let n = a.intern_nat(Nat::from(99u64));
    assert_eq!(a.int(i), &Int::from(-42i64));
    assert_eq!(a.nat(n), &Nat::from(99u64));
}

// ---------------------------------------------------------------------------
// Copy-ness: TermRef and TypeRef are Copy.
// ---------------------------------------------------------------------------

fn _ref_is_copy() {
    fn assert_copy<T: Copy>() {}
    assert_copy::<TermRef>();
    assert_copy::<TypeRef>();
}

// ---------------------------------------------------------------------------
// Packed-ref shape: TermRef and TypeRef are u32-sized.
// ---------------------------------------------------------------------------

#[test]
fn packed_refs_are_u32_sized() {
    assert_eq!(std::mem::size_of::<TermRef>(), 4);
    assert_eq!(std::mem::size_of::<TypeRef>(), 4);
}
