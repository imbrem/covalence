//! Phase 1 acceptance tests: arena allocation, builtin variants,
//! closed-flag computation, freezing, foreign imports, and the
//! diamond-import canonical-identity property.

use std::sync::Arc;

use covalence_kernel::{Arena, PrimOp2, TermDef, TermRef, TypeDef, TypeInfo, TypeRef};
use covalence_kernel::ty::{BuiltinTy, TypeRefKind};

/// Helper: intern a name and build a Free term in one go.
fn alloc_free(a: &mut Arena, name: &str, ty: TypeRef) -> covalence_kernel::TermId {
    let n = a.intern_string(name.into());
    a.alloc_term(TermDef::Free(n, ty))
}

/// Helper: intern a name and build a Const term.
fn alloc_const(a: &mut Arena, name: &str, ty: TypeRef) -> covalence_kernel::TermId {
    let n = a.intern_string(name.into());
    a.alloc_term(TermDef::Const(n, ty))
}

// ---------------------------------------------------------------------------
// Builtin TypeDef and TermDef variants are constructable directly.
// ---------------------------------------------------------------------------

#[test]
fn alloc_builtin_types_returns_builtin_typerefs() {
    let mut a = Arena::new();
    let bool_ty = a.alloc_type(TypeDef::Bool);
    let bits_ty = a.alloc_type(TypeDef::Bits);
    // alloc_type dedupes nullary primitives to the BuiltinTy TypeRef.
    assert_eq!(bool_ty, a.bool_ty());
    assert_eq!(bits_ty, a.bits_ty());
    assert!(bool_ty.is_builtin());
    assert_eq!(bool_ty.as_builtin(), Some(BuiltinTy::Bool));

    // Fun is user-allocated and gets a local TypeRef.
    let fun_ty = a.alloc_type(TypeDef::Fun(bool_ty, bits_ty));
    assert!(fun_ty.is_local());
    match a.type_def_of(fun_ty) {
        Some(TypeDef::Fun(d, c)) => {
            assert_eq!(d, bool_ty);
            assert_eq!(c, bits_ty);
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
fn alloc_literal_variants() {
    let mut a = Arena::new();
    // fixed-width
    let _u8 = a.alloc_term(TermDef::U8(0xFF));
    let _i32 = a.alloc_term(TermDef::I32(-1));
    let _u64 = a.alloc_term(TermDef::u64_literal(u64::MAX));
    // arbitrary-precision inline
    let _nat = a.alloc_term(TermDef::nat_inline(42));
    let _int = a.alloc_term(TermDef::int_inline(-42));
    // arbitrary-precision stored
    use covalence_types::{Int, Nat};
    let big_nat = a.intern_nat(Nat::from(u128::MAX));
    let big_int = a.intern_int(Int::from(i128::MIN));
    let _ns = a.alloc_term(TermDef::NatStored(big_nat));
    let _is = a.alloc_term(TermDef::IntStored(big_int));
    // bits / bytes
    use bytes::Bytes;
    use covalence_types::Bits;
    let bits_id =
        a.intern_bits(Bits::from_bytes(Bytes::from_static(&[0xAA, 0x55]), 16).unwrap());
    let bytes_id = a.intern_bytes(Bytes::from_static(&[0xDE, 0xAD, 0xBE, 0xEF]));
    let _bs = a.alloc_term(TermDef::BitsStored(bits_id));
    let _bys = a.alloc_term(TermDef::BytesStored(bytes_id));
}

// ---------------------------------------------------------------------------
// Closed flag.
// ---------------------------------------------------------------------------

#[test]
fn closed_true_for_constants_and_builtins() {
    let mut a = Arena::new();
    let bool_ty = a.bool_ty();
    let t = a.alloc_term(TermDef::True);
    let f = a.alloc_term(TermDef::False);
    let c = alloc_const(&mut a, "foo", bool_ty);
    let n = a.alloc_term(TermDef::nat_inline(7));

    for id in [t, f, c, n] {
        assert!(a.term_uf(id).closed(), "term {id:?} should be closed");
    }
}

#[test]
fn closed_false_for_free_var() {
    let mut a = Arena::new();
    let bool_ty = a.bool_ty();
    let x = alloc_free(&mut a, "x", bool_ty);
    assert!(!a.term_uf(x).closed());
    assert!(a.term_uf(x).has_free);
}

#[test]
fn closed_propagates_through_comb() {
    let mut a = Arena::new();
    let bool_ty = a.bool_ty();
    let bool_to_bool = a.alloc_type(TypeDef::Fun(bool_ty, bool_ty));

    let t = a.alloc_term(TermDef::True);
    let neg = alloc_const(&mut a, "not", bool_to_bool);
    let app = a.alloc_term(TermDef::Comb(TermRef::local(neg), TermRef::local(t)));
    assert!(a.term_uf(app).closed());

    let x = alloc_free(&mut a, "x", bool_ty);
    let app_open = a.alloc_term(TermDef::Comb(TermRef::local(neg), TermRef::local(x)));
    assert!(!a.term_uf(app_open).closed());
}

#[test]
fn abs_binds_one_level_of_bound() {
    let mut a = Arena::new();
    let bool_ty = a.bool_ty();

    let b0 = a.alloc_term(TermDef::Bound(0));
    assert_eq!(a.term_uf(b0).bound_depth(), 1);
    assert!(!a.term_uf(b0).closed());

    let abs = a.alloc_term(TermDef::Abs(bool_ty, TermRef::local(b0)));
    assert_eq!(a.term_uf(abs).bound_depth(), 0);
    assert!(a.term_uf(abs).closed());
}

#[test]
fn abs_needs_two_levels_for_bound_one() {
    let mut a = Arena::new();
    let bool_ty = a.bool_ty();

    let b1 = a.alloc_term(TermDef::Bound(1));
    assert_eq!(a.term_uf(b1).bound_depth(), 2);

    let inner = a.alloc_term(TermDef::Abs(bool_ty, TermRef::local(b1)));
    assert_eq!(a.term_uf(inner).bound_depth(), 1);
    assert!(!a.term_uf(inner).closed());

    let outer = a.alloc_term(TermDef::Abs(bool_ty, TermRef::local(inner)));
    assert_eq!(a.term_uf(outer).bound_depth(), 0);
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

    assert_eq!(thawed.term_def(t), &TermDef::True);
    let f = thawed.alloc_term(TermDef::False);
    assert_eq!(thawed.term_def(f), &TermDef::False);

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
    let mut d = Arena::new();
    let d_bool = d.bool_ty();
    let c_d = alloc_const(&mut d, "c", d_bool);
    let d_frozen = d.freeze();

    let mut a = Arena::new();
    let imp_d = a.add_import(d_frozen.clone());
    let foreign_ref = a.foreign_term_ref(imp_d, c_d);
    let a_arc = a.freeze();
    let canon = Arena::canonical_term(&a_arc, foreign_ref);
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

#[test]
fn diamond_import_regains_canonical_identity() {
    let mut d = Arena::new();
    let d_bool = d.bool_ty();
    let x_d = alloc_free(&mut d, "x", d_bool);
    let d_frozen = d.freeze();

    let mut b = Arena::new();
    let imp_d_in_b = b.add_import(d_frozen.clone());
    let x_in_b = b.foreign_term_ref(imp_d_in_b, x_d);

    let mut c = Arena::new();
    let imp_d_in_c = c.add_import(d_frozen.clone());
    let x_in_c = c.foreign_term_ref(imp_d_in_c, x_d);

    let b_frozen = b.freeze();
    let c_frozen = c.freeze();

    let mut a = Arena::new();
    let _imp_b = a.add_import(b_frozen.clone());
    let _imp_c = a.add_import(c_frozen.clone());
    let a_arc = a.freeze();

    let canon_via_b = Arena::canonical_term(&b_frozen, x_in_b);
    let canon_via_c = Arena::canonical_term(&c_frozen, x_in_c);

    assert!(Arc::ptr_eq(&canon_via_b.0, &canon_via_c.0));
    assert!(Arc::ptr_eq(&canon_via_b.0, &d_frozen));
    assert_eq!(canon_via_b.1, x_d);
    assert_eq!(canon_via_c.1, x_d);
    assert_eq!(a_arc.imports().len(), 2);
}

#[test]
fn distinct_arenas_with_same_content_are_not_canonically_equal() {
    let mut a1 = Arena::new();
    let a1_bool = a1.bool_ty();
    let _t1 = alloc_free(&mut a1, "x", a1_bool);
    let a1_frozen = a1.freeze();

    let mut a2 = Arena::new();
    let a2_bool = a2.bool_ty();
    let _t2 = alloc_free(&mut a2, "x", a2_bool);
    let a2_frozen = a2.freeze();

    assert!(!Arc::ptr_eq(&a1_frozen, &a2_frozen));

    let mut a3 = Arena::new();
    let imp_a1 = a3.add_import(a1_frozen.clone());
    let imp_a2 = a3.add_import(a2_frozen.clone());
    assert_ne!(imp_a1, imp_a2);
    let r1 = a3.foreign_term_ref(imp_a1, covalence_kernel::TermId(0));
    let r2 = a3.foreign_term_ref(imp_a2, covalence_kernel::TermId(0));
    assert_ne!(r1, r2);
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
    use bytes::Bytes;
    let mut a = Arena::new();
    let by = a.intern_bytes(Bytes::from_static(&[1, 2, 3]));
    assert_eq!(&a.bytes_value(by)[..], &[1u8, 2, 3][..]);
    let args = a.intern_tyargs(vec![a.bool_ty()]);
    assert_eq!(a.tyargs(args), &[a.bool_ty()]);
}

#[test]
fn intern_int_and_nat() {
    use covalence_types::{Int, Nat};
    let mut a = Arena::new();
    let i = a.intern_int(Int::from(-42i64));
    let n = a.intern_nat(Nat::from(99u64));
    assert_eq!(a.int(i), &Int::from(-42i64));
    assert_eq!(a.nat(n), &Nat::from(99u64));
}

#[test]
fn abs_hint_stored_and_retrieved() {
    let mut a = Arena::new();
    let bool_ty = a.bool_ty();
    let body = a.alloc_term(TermDef::Bound(0));
    let abs = a.alloc_term(TermDef::Abs(bool_ty, TermRef::local(body)));
    assert!(a.abs_hint(abs).is_none());
    let name = a.intern_string("x".into());
    a.set_abs_hint(abs, name);
    assert_eq!(a.abs_hint(abs), Some(name));
}

fn _refs_and_defs_are_copy() {
    fn assert_copy<T: Copy>() {}
    assert_copy::<TermRef>();
    assert_copy::<TypeRef>();
    assert_copy::<TermDef>();
    assert_copy::<TypeDef>();
}

#[test]
fn packed_refs_are_u32_sized() {
    assert_eq!(std::mem::size_of::<TermRef>(), 4);
    assert_eq!(std::mem::size_of::<TypeRef>(), 4);
}

#[test]
fn term_def_fits_three_u32s() {
    assert_eq!(std::mem::size_of::<TermDef>(), 12);
    assert_eq!(std::mem::align_of::<TermDef>(), 4);
}

#[test]
fn alloc_all_primitive_types() {
    let mut a = Arena::new();
    for (def, expected) in [
        (TypeDef::Bool, BuiltinTy::Bool),
        (TypeDef::Bits, BuiltinTy::Bits),
        (TypeDef::Bytes, BuiltinTy::Bytes),
        (TypeDef::Int, BuiltinTy::Int),
        (TypeDef::Nat, BuiltinTy::Nat),
        (TypeDef::U8, BuiltinTy::U8),
        (TypeDef::U16, BuiltinTy::U16),
        (TypeDef::U32, BuiltinTy::U32),
        (TypeDef::U64, BuiltinTy::U64),
        (TypeDef::I8, BuiltinTy::I8),
        (TypeDef::I16, BuiltinTy::I16),
        (TypeDef::I32, BuiltinTy::I32),
        (TypeDef::I64, BuiltinTy::I64),
    ] {
        let r = a.alloc_type(def);
        assert_eq!(r.as_builtin(), Some(expected));
    }
}

#[test]
fn alloc_tvar_and_tyapp_user_allocated() {
    let mut a = Arena::new();
    let name = a.intern_string("'a".into());
    let r_tvar = a.alloc_type(TypeDef::TVar(name));
    assert!(r_tvar.is_local());
    match a.type_def_of(r_tvar) {
        Some(TypeDef::TVar(s)) => assert_eq!(a.string(s).as_str(), "'a"),
        other => panic!("expected TVar, got {other:?}"),
    }
    let list_name = a.intern_string("list".into());
    let args = a.intern_tyargs(vec![a.bool_ty()]);
    let r_tyapp = a.alloc_type(TypeDef::Tyapp(list_name, args));
    assert!(r_tyapp.is_local());
}

#[test]
fn type_def_is_copy() {
    fn assert_copy<T: Copy>() {}
    assert_copy::<TypeDef>();
}

// ---------------------------------------------------------------------------
// Intrinsic type inference at alloc_term.
// ---------------------------------------------------------------------------

#[test]
fn primitives_are_builtins_no_arena_entries() {
    let mut a = Arena::new();
    let _b = a.alloc_type(TypeDef::Bool);
    let _b2 = a.alloc_type(TypeDef::Bool);
    let _n = a.alloc_type(TypeDef::Nat);
    // No arena types allocated for nullary primitives.
    assert_eq!(a.num_types(), 0);
}

#[test]
fn alloc_type_dedupes_primitives() {
    let mut a = Arena::new();
    let r1 = a.alloc_type(TypeDef::Bool);
    let r2 = a.alloc_type(TypeDef::Bool);
    assert_eq!(r1, r2);
    assert_eq!(r1, a.bool_ty());
}

#[test]
fn literals_get_concrete_types() {
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::True);
    let n = a.alloc_term(TermDef::nat_inline(42));
    let u8v = a.alloc_term(TermDef::U8(7));
    let i64v = a.alloc_term(TermDef::i64_literal(-1));
    assert_eq!(a.term_uf(t).type_info, TypeInfo::typed(a.bool_ty()));
    assert_eq!(a.term_uf(n).type_info, TypeInfo::typed(a.nat_ty()));
    assert_eq!(a.term_uf(u8v).type_info, TypeInfo::typed(a.u8_ty()));
    assert_eq!(a.term_uf(i64v).type_info, TypeInfo::typed(a.i64_ty()));
}

#[test]
fn bound_var_is_unbound() {
    let mut a = Arena::new();
    let b0 = a.alloc_term(TermDef::Bound(0));
    let b3 = a.alloc_term(TermDef::Bound(3));
    assert_eq!(a.term_uf(b0).type_info, TypeInfo::unbound(1));
    assert_eq!(a.term_uf(b3).type_info, TypeInfo::unbound(4));
}

#[test]
fn free_var_carries_its_type() {
    let mut a = Arena::new();
    let nat = a.nat_ty();
    let x = alloc_free(&mut a, "x", nat);
    assert_eq!(a.term_uf(x).type_info, TypeInfo::typed(nat));
}

#[test]
fn comb_well_typed_unfolds_function_type() {
    let mut a = Arena::new();
    let bool_ty = a.bool_ty();
    let bool_to_bool = a.alloc_type(TypeDef::Fun(bool_ty, bool_ty));
    let neg = alloc_const(&mut a, "not", bool_to_bool);
    let t = a.alloc_term(TermDef::True);
    let app = a.alloc_term(TermDef::Comb(TermRef::local(neg), TermRef::local(t)));
    assert_eq!(a.term_uf(app).type_info, TypeInfo::typed(bool_ty));
}

#[test]
fn comb_mismatched_domain_is_ill_typed() {
    let mut a = Arena::new();
    let bool_ty = a.bool_ty();
    let bool_to_bool = a.alloc_type(TypeDef::Fun(bool_ty, bool_ty));
    let neg = alloc_const(&mut a, "not", bool_to_bool);
    let n = a.alloc_term(TermDef::nat_inline(0));
    let bad = a.alloc_term(TermDef::Comb(TermRef::local(neg), TermRef::local(n)));
    assert_eq!(a.term_uf(bad).type_info, TypeInfo::ILL_TYPED);
}

#[test]
fn abs_with_typed_body_gets_fun_type() {
    let mut a = Arena::new();
    let bool_ty = a.bool_ty();
    let t = a.alloc_term(TermDef::True);
    let abs = a.alloc_term(TermDef::Abs(bool_ty, TermRef::local(t)));
    let abs_ty = a.term_uf(abs).type_info.as_type().expect("abs typed");
    match a.type_def_of(abs_ty) {
        Some(TypeDef::Fun(d, c)) => {
            assert_eq!(d, bool_ty);
            assert_eq!(c, bool_ty);
        }
        other => panic!("expected Fun, got {other:?}"),
    }
}

#[test]
fn eq_well_typed_yields_bool() {
    let mut a = Arena::new();
    let bool_ty = a.bool_ty();
    let t = a.alloc_term(TermDef::True);
    let f = a.alloc_term(TermDef::False);
    let eq = a.alloc_term(TermDef::Eq(TermRef::local(t), TermRef::local(f)));
    assert_eq!(a.term_uf(eq).type_info, TypeInfo::typed(bool_ty));
}

#[test]
fn eq_mismatched_types_is_ill_typed() {
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::True);
    let n = a.alloc_term(TermDef::nat_inline(0));
    let eq = a.alloc_term(TermDef::Eq(TermRef::local(t), TermRef::local(n)));
    assert_eq!(a.term_uf(eq).type_info, TypeInfo::ILL_TYPED);
}

#[test]
fn id_is_typed_as_alpha_to_alpha() {
    let mut a = Arena::new();
    let bool_ty = a.bool_ty();
    let id = a.alloc_term(TermDef::Id(bool_ty));
    let id_ty = a.term_uf(id).type_info.as_type().unwrap();
    match a.type_def_of(id_ty) {
        Some(TypeDef::Fun(d, c)) => {
            assert_eq!(d, bool_ty);
            assert_eq!(c, bool_ty);
        }
        other => panic!("expected Fun, got {other:?}"),
    }
}

#[test]
fn ill_typed_terms_can_sit_in_the_arena() {
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::True);
    let n = a.alloc_term(TermDef::nat_inline(0));
    let bad = a.alloc_term(TermDef::Eq(TermRef::local(t), TermRef::local(n)));
    assert_eq!(a.term_uf(bad).type_info, TypeInfo::ILL_TYPED);
    assert!(a.term_uf(bad).closed());
}

// ---------------------------------------------------------------------------
// Phase B: PrimOp signature lookup for Op1/Op2/Comp/Iter/Ite/LiftOpN.
// ---------------------------------------------------------------------------

#[test]
fn op1_well_typed_gets_output_type() {
    use covalence_kernel::PrimOp1;
    let mut a = Arena::new();
    // NatSucc : nat → nat
    let n = a.alloc_term(TermDef::nat_inline(7));
    let s = a.alloc_term(TermDef::Op1(PrimOp1::NatSucc, TermRef::local(n)));
    assert_eq!(a.term_uf(s).type_info, TypeInfo::typed(a.nat_ty()));
    // U64Eqz : u64 → bool
    let u = a.alloc_term(TermDef::u64_literal(0));
    let z = a.alloc_term(TermDef::Op1(PrimOp1::U64Eqz, TermRef::local(u)));
    assert_eq!(a.term_uf(z).type_info, TypeInfo::typed(a.bool_ty()));
}

#[test]
fn op1_wrong_input_type_is_ill_typed() {
    use covalence_kernel::PrimOp1;
    let mut a = Arena::new();
    // NatSucc applied to a bool: ill-typed.
    let t = a.alloc_term(TermDef::True);
    let bad = a.alloc_term(TermDef::Op1(PrimOp1::NatSucc, TermRef::local(t)));
    assert_eq!(a.term_uf(bad).type_info, TypeInfo::ILL_TYPED);
}

#[test]
fn op2_well_typed_gets_output_type() {
    let mut a = Arena::new();
    let x = a.alloc_term(TermDef::nat_inline(5));
    let y = a.alloc_term(TermDef::nat_inline(3));
    let sum = a.alloc_term(TermDef::Op2(
        PrimOp2::NatAdd,
        TermRef::local(x),
        TermRef::local(y),
    ));
    assert_eq!(a.term_uf(sum).type_info, TypeInfo::typed(a.nat_ty()));
    let lt = a.alloc_term(TermDef::Op2(
        PrimOp2::NatLt,
        TermRef::local(x),
        TermRef::local(y),
    ));
    assert_eq!(a.term_uf(lt).type_info, TypeInfo::typed(a.bool_ty()));
}

#[test]
fn op2_wrong_input_is_ill_typed() {
    let mut a = Arena::new();
    let x = a.alloc_term(TermDef::nat_inline(5));
    let b = a.alloc_term(TermDef::True);
    let bad = a.alloc_term(TermDef::Op2(
        PrimOp2::NatAdd,
        TermRef::local(x),
        TermRef::local(b),
    ));
    assert_eq!(a.term_uf(bad).type_info, TypeInfo::ILL_TYPED);
}

#[test]
fn op2_shift_takes_nat_count() {
    let mut a = Arena::new();
    // U32Shl : u32 → nat → u32
    let v = a.alloc_term(TermDef::U32(0xFF));
    let n = a.alloc_term(TermDef::nat_inline(4));
    let shifted = a.alloc_term(TermDef::Op2(
        PrimOp2::U32Shl,
        TermRef::local(v),
        TermRef::local(n),
    ));
    assert_eq!(a.term_uf(shifted).type_info, TypeInfo::typed(a.u32_ty()));
}

#[test]
fn lift_op1_is_typed_as_function() {
    use covalence_kernel::PrimOp1;
    let mut a = Arena::new();
    let lifted = a.alloc_term(TermDef::LiftOp1(PrimOp1::NatSucc));
    // Should be nat → nat.
    let ty = a.term_uf(lifted).type_info.as_type().unwrap();
    match a.type_def_of(ty) {
        Some(TypeDef::Fun(d, c)) => {
            assert_eq!(d, a.nat_ty());
            assert_eq!(c, a.nat_ty());
        }
        other => panic!("expected Fun(nat, nat), got {other:?}"),
    }
}

#[test]
fn lift_op2_is_typed_as_curried_function() {
    let mut a = Arena::new();
    // NatAdd lifted is nat → (nat → nat).
    let lifted = a.alloc_term(TermDef::LiftOp2(PrimOp2::NatAdd));
    let outer = a.term_uf(lifted).type_info.as_type().unwrap();
    let (dom, cod) = match a.type_def_of(outer) {
        Some(TypeDef::Fun(d, c)) => (d, c),
        other => panic!("expected outer Fun, got {other:?}"),
    };
    assert_eq!(dom, a.nat_ty());
    // The codomain is nat → nat (an inner Fun).
    match a.type_def_of(cod) {
        Some(TypeDef::Fun(d2, c2)) => {
            assert_eq!(d2, a.nat_ty());
            assert_eq!(c2, a.nat_ty());
        }
        other => panic!("expected inner Fun(nat, nat), got {other:?}"),
    }
}

#[test]
fn iter_well_typed_returns_alpha_to_alpha() {
    use covalence_kernel::PrimOp1;
    let mut a = Arena::new();
    let n = a.alloc_term(TermDef::nat_inline(5));
    let succ = a.alloc_term(TermDef::LiftOp1(PrimOp1::NatSucc));
    // Iter(n, succ) : nat → nat.
    let it = a.alloc_term(TermDef::Iter(TermRef::local(n), TermRef::local(succ)));
    let ty = a.term_uf(it).type_info.as_type().unwrap();
    match a.type_def_of(ty) {
        Some(TypeDef::Fun(d, c)) => {
            assert_eq!(d, a.nat_ty());
            assert_eq!(c, a.nat_ty());
        }
        other => panic!("expected nat→nat, got {other:?}"),
    }
}

#[test]
fn ite_typed_as_alpha_to_alpha() {
    let mut a = Arena::new();
    let cond = a.alloc_term(TermDef::True);
    let then_b = a.alloc_term(TermDef::nat_inline(7));
    let ite = a.alloc_term(TermDef::Ite(TermRef::local(cond), TermRef::local(then_b)));
    let ty = a.term_uf(ite).type_info.as_type().unwrap();
    match a.type_def_of(ty) {
        Some(TypeDef::Fun(d, c)) => {
            assert_eq!(d, a.nat_ty());
            assert_eq!(c, a.nat_ty());
        }
        other => panic!("expected nat→nat, got {other:?}"),
    }
}

#[test]
fn ite_wrong_cond_is_ill_typed() {
    let mut a = Arena::new();
    let n = a.alloc_term(TermDef::nat_inline(0));
    let then_b = a.alloc_term(TermDef::True);
    let bad = a.alloc_term(TermDef::Ite(TermRef::local(n), TermRef::local(then_b)));
    assert_eq!(a.term_uf(bad).type_info, TypeInfo::ILL_TYPED);
}

#[test]
fn comp_well_typed_composes_arrows() {
    use covalence_kernel::PrimOp1;
    let mut a = Arena::new();
    // f : nat → nat (NatSucc lifted)
    let f = a.alloc_term(TermDef::LiftOp1(PrimOp1::NatSucc));
    let g = a.alloc_term(TermDef::LiftOp1(PrimOp1::NatSucc));
    // Comp f g : nat → nat
    let comp = a.alloc_term(TermDef::Comp(TermRef::local(f), TermRef::local(g)));
    let ty = a.term_uf(comp).type_info.as_type().unwrap();
    match a.type_def_of(ty) {
        Some(TypeDef::Fun(d, c)) => {
            assert_eq!(d, a.nat_ty());
            assert_eq!(c, a.nat_ty());
        }
        other => panic!("expected nat→nat, got {other:?}"),
    }
}

#[test]
fn comp_mismatched_middle_type_is_ill_typed() {
    use covalence_kernel::PrimOp1;
    let mut a = Arena::new();
    // f : nat → nat, g : u8 → u8 — middle types don't compose.
    let f = a.alloc_term(TermDef::LiftOp1(PrimOp1::NatSucc));
    let g = a.alloc_term(TermDef::LiftOp1(PrimOp1::U8Popcount));
    let bad = a.alloc_term(TermDef::Comp(TermRef::local(f), TermRef::local(g)));
    assert_eq!(a.term_uf(bad).type_info, TypeInfo::ILL_TYPED);
}

// ---------------------------------------------------------------------------
// Phase B+: `infer` (re-walk under binders) and `set_type_info` (unchecked).
// ---------------------------------------------------------------------------

#[test]
fn infer_resolves_abs_over_bound_zero() {
    // λ_:bool. Bound(0) — alloc_term marks it IllTyped because the
    // re-walk under the binder isn't done eagerly. `infer` does it.
    let mut a = Arena::new();
    let bool_ty = a.bool_ty();
    let b0 = a.alloc_term(TermDef::Bound(0));
    let abs = a.alloc_term(TermDef::Abs(bool_ty, TermRef::local(b0)));
    // Cached type at insertion is IllTyped.
    assert_eq!(a.term_uf(abs).type_info, TypeInfo::ILL_TYPED);
    // infer walks under the binder and computes bool → bool.
    let inferred = a.infer(abs);
    let abs_ty = inferred.as_type().expect("inferred typed");
    match a.type_def_of(abs_ty) {
        Some(TypeDef::Fun(d, c)) => {
            assert_eq!(d, bool_ty);
            assert_eq!(c, bool_ty);
        }
        other => panic!("expected bool → bool, got {other:?}"),
    }
    // The inferred type is cached, so a second call is O(1) and the
    // cache is now Typed.
    assert!(a.term_uf(abs).type_info.is_typed());
    assert_eq!(a.infer(abs), inferred);
}

#[test]
fn infer_handles_nested_abs() {
    // λ_:bool. λ_:nat. Bound(1) — outer bool binder is what Bound(1)
    // refers to from inside the inner Abs. So the term is
    // bool → nat → bool.
    let mut a = Arena::new();
    let bool_ty = a.bool_ty();
    let nat_ty = a.nat_ty();
    let b1 = a.alloc_term(TermDef::Bound(1));
    let inner = a.alloc_term(TermDef::Abs(nat_ty, TermRef::local(b1)));
    let outer = a.alloc_term(TermDef::Abs(bool_ty, TermRef::local(inner)));
    let outer_info = a.infer(outer);
    let outer_ty = outer_info.as_type().expect("outer typed");
    // Walk the Fun chain: outer = bool → (nat → bool).
    let (d, c) = match a.type_def_of(outer_ty) {
        Some(TypeDef::Fun(d, c)) => (d, c),
        other => panic!("expected outer Fun, got {other:?}"),
    };
    assert_eq!(d, bool_ty);
    let (d2, c2) = match a.type_def_of(c) {
        Some(TypeDef::Fun(d, c)) => (d, c),
        other => panic!("expected inner Fun, got {other:?}"),
    };
    assert_eq!(d2, nat_ty);
    assert_eq!(c2, bool_ty);
}

#[test]
fn infer_returns_cached_typed_immediately() {
    // For a term that's already typed at insertion (NatSucc applied
    // to a nat literal), infer just returns the cached value.
    use covalence_kernel::PrimOp1;
    let mut a = Arena::new();
    let n = a.alloc_term(TermDef::nat_inline(7));
    let s = a.alloc_term(TermDef::Op1(PrimOp1::NatSucc, TermRef::local(n)));
    let cached = a.term_uf(s).type_info;
    assert!(cached.is_typed());
    assert_eq!(a.infer(s), cached);
}

#[test]
fn infer_caches_result() {
    let mut a = Arena::new();
    let bool_ty = a.bool_ty();
    let b0 = a.alloc_term(TermDef::Bound(0));
    let abs = a.alloc_term(TermDef::Abs(bool_ty, TermRef::local(b0)));
    assert_eq!(a.term_uf(abs).type_info, TypeInfo::ILL_TYPED);
    let info = a.infer(abs);
    // After infer, the cache is updated.
    assert_eq!(a.term_uf(abs).type_info, info);
    assert!(info.is_typed());
}

#[test]
fn set_type_info_unchecked_overrides_cache() {
    // Demonstrates the unchecked setter: we can stamp any TypeInfo
    // on a term, even one inconsistent with its structure. Soundness
    // is the Thm wrapper's job, not the arena's.
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::True);
    // Pre-condition: True is typed as bool.
    assert_eq!(a.term_uf(t).type_info, TypeInfo::typed(a.bool_ty()));
    // Stomp it with a nonsensical type.
    a.set_type_info(t, TypeInfo::typed(a.nat_ty()));
    assert_eq!(a.term_uf(t).type_info, TypeInfo::typed(a.nat_ty()));
    // Or mark it ill-typed.
    a.set_type_info(t, TypeInfo::ILL_TYPED);
    assert_eq!(a.term_uf(t).type_info, TypeInfo::ILL_TYPED);
}

#[test]
fn infer_on_open_term_with_bound_indices_inside_abs() {
    // λ_:nat. Op1(NatSucc, Bound(0)) — body uses Bound(0) of type
    // nat, NatSucc : nat → nat. Result: nat → nat.
    use covalence_kernel::PrimOp1;
    let mut a = Arena::new();
    let nat_ty = a.nat_ty();
    let b0 = a.alloc_term(TermDef::Bound(0));
    let body = a.alloc_term(TermDef::Op1(PrimOp1::NatSucc, TermRef::local(b0)));
    let abs = a.alloc_term(TermDef::Abs(nat_ty, TermRef::local(body)));
    let info = a.infer(abs);
    let abs_ty = info.as_type().expect("typed");
    match a.type_def_of(abs_ty) {
        Some(TypeDef::Fun(d, c)) => {
            assert_eq!(d, nat_ty);
            assert_eq!(c, nat_ty);
        }
        other => panic!("expected nat → nat, got {other:?}"),
    }
}

#[test]
fn typeref_decodes_to_kind() {
    let mut a = Arena::new();
    let bool_ty = a.bool_ty();
    assert!(matches!(bool_ty.decode(), TypeRefKind::Builtin(BuiltinTy::Bool)));
    let name = a.intern_string("'a".into());
    let tvar = a.alloc_type(TypeDef::TVar(name));
    match tvar.decode() {
        TypeRefKind::Local(_) => (),
        other => panic!("expected Local, got {other:?}"),
    }
}
