//! Phase 1 acceptance tests: arena allocation, builtin variants,
//! closed-flag computation, freezing, foreign imports, and the
//! diamond-import canonical-identity property.

use std::sync::Arc;

use covalence_kernel::{Arena, PrimOp2, TermDef, TermRef, TypeDef, TypeInfo, TypeRef};
use covalence_kernel::reduce;
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
    let nat_ty = a.alloc_type(TypeDef::Nat);
    // alloc_type dedupes nullary primitives to the BuiltinTy TypeRef.
    assert_eq!(bool_ty, a.bool_ty());
    assert_eq!(nat_ty, a.nat_ty());
    assert!(bool_ty.is_builtin());
    assert_eq!(bool_ty.as_builtin(), Some(BuiltinTy::Bool));

    // Fun is user-allocated and gets a local TypeRef.
    let fun_ty = a.alloc_type(TypeDef::Fun(bool_ty, nat_ty));
    assert!(fun_ty.is_local());
    match a.type_def_of(fun_ty) {
        Some(TypeDef::Fun(d, c)) => {
            assert_eq!(d, bool_ty);
            assert_eq!(c, nat_ty);
        }
        other => panic!("expected Fun, got {other:?}"),
    }
}

#[test]
fn alloc_builtin_terms() {
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::Bool(true));
    let f = a.alloc_term(TermDef::Bool(false));
    let eq = a.alloc_term(TermDef::Eq(TermRef::local(t), TermRef::local(f)));

    assert_eq!(a.term_def(t), &TermDef::Bool(true));
    assert_eq!(a.term_def(f), &TermDef::Bool(false));
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
    // arbitrary-precision inline
    let _nat = a.alloc_term(TermDef::nat_inline(42));
    let _int = a.alloc_term(TermDef::int_inline(-42));
    // arbitrary-precision stored
    use covalence_types::{Int, Nat};
    let big_nat = a.intern_nat(Nat::from(u128::MAX));
    let big_int = a.intern_int(Int::from(i128::MIN));
    let _ns = a.alloc_term(TermDef::NatStored(big_nat));
    let _is = a.alloc_term(TermDef::IntStored(big_int));
    // bytes
    use bytes::Bytes;
    let bytes_id = a.intern_bytes(Bytes::from_static(&[0xDE, 0xAD, 0xBE, 0xEF]));
    let _bys = a.alloc_term(TermDef::BytesStored(bytes_id));
}

// ---------------------------------------------------------------------------
// Closed flag.
// ---------------------------------------------------------------------------

#[test]
fn closed_true_for_constants_and_builtins() {
    let mut a = Arena::new();
    let bool_ty = a.bool_ty();
    let t = a.alloc_term(TermDef::Bool(true));
    let f = a.alloc_term(TermDef::Bool(false));
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

    let t = a.alloc_term(TermDef::Bool(true));
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
    let t = a.alloc_term(TermDef::Bool(true));
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
    let t = a.alloc_term(TermDef::Bool(true));
    let frozen = a.freeze();
    assert_eq!(frozen.term_def(t), &TermDef::Bool(true));
}

#[test]
fn unfreeze_keeps_indices() {
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::Bool(true));
    let frozen = a.freeze();
    let mut thawed = Arena::unfreeze(&frozen);

    assert_eq!(thawed.term_def(t), &TermDef::Bool(true));
    let f = thawed.alloc_term(TermDef::Bool(false));
    assert_eq!(thawed.term_def(f), &TermDef::Bool(false));

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
        (TypeDef::Bytes, BuiltinTy::Bytes),
        (TypeDef::Int, BuiltinTy::Int),
        (TypeDef::Nat, BuiltinTy::Nat),
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
    let t = a.alloc_term(TermDef::Bool(true));
    let n = a.alloc_term(TermDef::nat_inline(42));
    let i = a.alloc_term(TermDef::int_inline(-1));
    assert_eq!(a.term_uf(t).type_info, TypeInfo::typed(a.bool_ty()));
    assert_eq!(a.term_uf(n).type_info, TypeInfo::typed(a.nat_ty()));
    assert_eq!(a.term_uf(i).type_info, TypeInfo::typed(a.int_ty()));
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
    let t = a.alloc_term(TermDef::Bool(true));
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
    let t = a.alloc_term(TermDef::Bool(true));
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
    let t = a.alloc_term(TermDef::Bool(true));
    let f = a.alloc_term(TermDef::Bool(false));
    let eq = a.alloc_term(TermDef::Eq(TermRef::local(t), TermRef::local(f)));
    assert_eq!(a.term_uf(eq).type_info, TypeInfo::typed(bool_ty));
}

#[test]
fn eq_mismatched_types_is_ill_typed() {
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::Bool(true));
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
    let t = a.alloc_term(TermDef::Bool(true));
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
    // IntNeg : int → int
    let i = a.alloc_term(TermDef::int_inline(0));
    let z = a.alloc_term(TermDef::Op1(PrimOp1::IntNeg, TermRef::local(i)));
    assert_eq!(a.term_uf(z).type_info, TypeInfo::typed(a.int_ty()));
}

#[test]
fn op1_wrong_input_type_is_ill_typed() {
    use covalence_kernel::PrimOp1;
    let mut a = Arena::new();
    // NatSucc applied to a bool: ill-typed.
    let t = a.alloc_term(TermDef::Bool(true));
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
    let b = a.alloc_term(TermDef::Bool(true));
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
    // IntShl : int → nat → int
    let v = a.alloc_term(TermDef::int_inline(0xFF));
    let n = a.alloc_term(TermDef::nat_inline(4));
    let shifted = a.alloc_term(TermDef::Op2(
        PrimOp2::IntShl,
        TermRef::local(v),
        TermRef::local(n),
    ));
    assert_eq!(a.term_uf(shifted).type_info, TypeInfo::typed(a.int_ty()));
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
    let cond = a.alloc_term(TermDef::Bool(true));
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
    let then_b = a.alloc_term(TermDef::Bool(true));
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
    // f : nat → nat, g : int → int — middle types don't compose.
    let f = a.alloc_term(TermDef::LiftOp1(PrimOp1::NatSucc));
    let g = a.alloc_term(TermDef::LiftOp1(PrimOp1::IntNeg));
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
    let t = a.alloc_term(TermDef::Bool(true));
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

// ---------------------------------------------------------------------------
// Substitution / shifting / β-reduction.
// ---------------------------------------------------------------------------

#[test]
fn shift_leaves_closed_terms_alone() {
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::Bool(true));
    let shifted = a.shift(TermRef::local(t), 0, 5);
    assert_eq!(shifted, TermRef::local(t));
}

#[test]
fn shift_increments_dangling_bound() {
    let mut a = Arena::new();
    let b0 = a.alloc_term(TermDef::Bound(0));
    let shifted = a.shift(TermRef::local(b0), 0, 3);
    let id = shifted.as_local().unwrap();
    assert_eq!(a.term_def(id), &TermDef::Bound(3));
}

#[test]
fn shift_respects_cutoff() {
    // Bound(0) below cutoff=1 stays unchanged; Bound(2) above is shifted.
    let mut a = Arena::new();
    let bool_ty = a.bool_ty();
    let b0 = a.alloc_term(TermDef::Bound(0));
    let b2 = a.alloc_term(TermDef::Bound(2));
    let comb = a.alloc_term(TermDef::Comb(TermRef::local(b0), TermRef::local(b2)));
    // Wrap in Abs to introduce a binder so cutoff=1 makes sense locally.
    let abs = a.alloc_term(TermDef::Abs(bool_ty, TermRef::local(comb)));
    // Shift the Abs's body by amount=5 with cutoff=1.
    // Bound(0) refers to the Abs binder; Bound(2) is the dangling
    // index — should shift to Bound(7).
    let shifted_body = a.shift(TermRef::local(comb), 1, 5);
    let new_comb = shifted_body.as_local().unwrap();
    match a.term_def(new_comb) {
        TermDef::Comb(f, x) => {
            let f_def = a.term_def(f.as_local().unwrap());
            let x_def = a.term_def(x.as_local().unwrap());
            assert_eq!(f_def, &TermDef::Bound(0)); // unchanged
            assert_eq!(x_def, &TermDef::Bound(7)); // 2 + 5
        }
        other => panic!("expected Comb, got {other:?}"),
    }
    let _ = abs; // satisfy unused-var lint
}

#[test]
fn beta_reduces_identity() {
    // (λ_:bool. Bound(0)) True → True
    let mut a = Arena::new();
    let body = a.alloc_term(TermDef::Bound(0));
    let t = a.alloc_term(TermDef::Bool(true));
    let result = a.subst(TermRef::local(body), 0, TermRef::local(t));
    assert_eq!(result, TermRef::local(t));
}

#[test]
fn beta_substitutes_into_arg_position() {
    // (λ_:bool. Op1(LogicalNot, Bound(0))) True → Op1(LogicalNot, True)
    use covalence_kernel::PrimOp1;
    let mut a = Arena::new();
    let bool_ty = a.bool_ty();
    let b0 = a.alloc_term(TermDef::Bound(0));
    let body = a.alloc_term(TermDef::Op1(PrimOp1::LogicalNot, TermRef::local(b0)));
    let t = a.alloc_term(TermDef::Bool(true));
    let result = a.subst(TermRef::local(body), 0, TermRef::local(t));
    let id = result.as_local().unwrap();
    match a.term_def(id) {
        TermDef::Op1(PrimOp1::LogicalNot, x) => {
            assert_eq!(x.as_local(), Some(t));
        }
        other => panic!("expected Op1(Not, _), got {other:?}"),
    }
    // After β, the result is locally closed and bool-typed.
    assert!(a.term_uf(id).closed());
    assert_eq!(a.term_uf(id).type_info, TypeInfo::typed(bool_ty));
}

#[test]
fn beta_decrements_outer_bound_indices() {
    // λ_:bool. ((λ_:bool. Bound(1)) True)
    // After β-reducing the inner abs+true: λ_:bool. Bound(0)
    // (Outer Bound(1) of the inner body refers to the OUTER binder;
    // after substitution removes the inner binder, that Bound becomes
    // Bound(0).)
    let mut a = Arena::new();
    let bool_ty = a.bool_ty();
    let b1 = a.alloc_term(TermDef::Bound(1));
    let t = a.alloc_term(TermDef::Bool(true));
    let result = a.subst(TermRef::local(b1), 0, TermRef::local(t));
    let id = result.as_local().unwrap();
    // Bound(1) was bound by the outer binder (not the one we're
    // substituting), so it should decrement to Bound(0).
    assert_eq!(a.term_def(id), &TermDef::Bound(0));
    let _ = bool_ty;
}

#[test]
fn beta_under_nested_abs_shifts_replacement() {
    // body  = λ_:bool. Bound(1)   — body has dangling Bound(1).
    // β-reduce(body, depth=0, arg=Bound(0))
    // → λ_:bool. Bound(0_shifted_by_1) = λ_:bool. Bound(1)
    //   (Bound(0) gets shifted up by 1 when crossing the nested Abs.)
    // Actually we substitute body[Bound(0) ↦ arg], but body's outermost
    // expression IS an Abs, so we go under it. Bound(1) inside the
    // nested Abs refers to the outer-er binder (the one we're
    // substituting away). It becomes arg, shifted by depth=1.
    // arg = Bound(0); shifted by 1 = Bound(1).
    let mut a = Arena::new();
    let bool_ty = a.bool_ty();
    let b1 = a.alloc_term(TermDef::Bound(1));
    let inner = a.alloc_term(TermDef::Abs(bool_ty, TermRef::local(b1)));
    let b0 = a.alloc_term(TermDef::Bound(0));
    let result = a.subst(TermRef::local(inner), 0, TermRef::local(b0));
    // Result should be λ_:bool. Bound(1).
    let abs_id = result.as_local().unwrap();
    match a.term_def(abs_id) {
        TermDef::Abs(_, body_ref) => {
            let body_def = a.term_def(body_ref.as_local().unwrap());
            assert_eq!(body_def, &TermDef::Bound(1));
        }
        other => panic!("expected Abs, got {other:?}"),
    }
}

#[test]
fn subst_skips_irrelevant_subterms_fast() {
    // A closed subterm (no dangling Bound) doesn't need shifting/
    // substituting; subst should reuse the original TermRef.
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::Bool(true)); // closed
    let arg = a.alloc_term(TermDef::Bool(false));
    // subst(True, 0, False) = True (no Bound(0) inside).
    let result = a.subst(TermRef::local(t), 0, TermRef::local(arg));
    assert_eq!(result, TermRef::local(t));
}

// ---------------------------------------------------------------------------
// Union-find primitives.
// ---------------------------------------------------------------------------

#[test]
fn fresh_terms_not_equal_at_level_0() {
    let mut a = Arena::new();
    let x = a.alloc_term(TermDef::Bool(true));
    let y = a.alloc_term(TermDef::Bool(false));
    assert!(!a.eq_at_level_0(TermRef::local(x), TermRef::local(y)));
}

#[test]
fn term_is_equal_to_itself() {
    let mut a = Arena::new();
    let x = a.alloc_term(TermDef::Bool(true));
    assert!(a.eq_at_level_0(TermRef::local(x), TermRef::local(x)));
}

#[test]
fn union_makes_two_terms_equal() {
    let mut a = Arena::new();
    // Two separately-allocated NatInline(5) terms — different TermIds,
    // same logical value. Initially not eq at level 0.
    let n1 = a.alloc_term(TermDef::nat_inline(5));
    let n2 = a.alloc_term(TermDef::nat_inline(5));
    assert!(!a.eq_at_level_0(TermRef::local(n1), TermRef::local(n2)));
    a.union(TermRef::local(n1), TermRef::local(n2)).unwrap();
    assert!(a.eq_at_level_0(TermRef::local(n1), TermRef::local(n2)));
}

#[test]
fn union_is_transitive_via_walk() {
    let mut a = Arena::new();
    let x = a.alloc_term(TermDef::nat_inline(1));
    let y = a.alloc_term(TermDef::nat_inline(2));
    let z = a.alloc_term(TermDef::nat_inline(3));
    a.union(TermRef::local(x), TermRef::local(y)).unwrap();
    a.union(TermRef::local(y), TermRef::local(z)).unwrap();
    // After x→y→z, x and z resolve to the same canonical.
    assert!(a.eq_at_level_0(TermRef::local(x), TermRef::local(z)));
}

#[test]
fn union_self_is_noop() {
    let mut a = Arena::new();
    let x = a.alloc_term(TermDef::Bool(true));
    let canon_before = a.canonical_local(TermRef::local(x));
    a.union(TermRef::local(x), TermRef::local(x)).unwrap();
    let canon_after = a.canonical_local(TermRef::local(x));
    assert_eq!(canon_before, canon_after);
}

#[test]
fn union_if_congruent_step_succeeds_on_matching_combs() {
    use covalence_kernel::PrimOp1;
    let mut a = Arena::new();
    let bool_ty = a.bool_ty();
    let bool_to_bool = a.alloc_type(TypeDef::Fun(bool_ty, bool_ty));
    let neg = alloc_const(&mut a, "not", bool_to_bool);
    let t = a.alloc_term(TermDef::Bool(true));
    // Two structurally-identical Comb(neg, True) terms with separate TermIds.
    let app1 = a.alloc_term(TermDef::Comb(TermRef::local(neg), TermRef::local(t)));
    let app2 = a.alloc_term(TermDef::Comb(TermRef::local(neg), TermRef::local(t)));
    assert!(!a.eq_at_level_0(TermRef::local(app1), TermRef::local(app2)));
    // Children (neg and t) are already eq at level 0 (literally same TermIds).
    let fired = a
        .union_if_congruent(TermRef::local(app1), TermRef::local(app2), 1)
        .unwrap();
    assert!(fired);
    assert!(a.eq_at_level_0(TermRef::local(app1), TermRef::local(app2)));
    let _ = PrimOp1::LogicalNot;
}

#[test]
fn union_if_congruent_step_propagates_via_children_union() {
    let mut a = Arena::new();
    // x and y are two distinct nat literals; we union them.
    let x = a.alloc_term(TermDef::nat_inline(7));
    let y = a.alloc_term(TermDef::nat_inline(7));
    a.union(TermRef::local(x), TermRef::local(y)).unwrap();
    // Now Op1(NatSucc, x) and Op1(NatSucc, y) should match via cong.
    use covalence_kernel::PrimOp1;
    let sx = a.alloc_term(TermDef::Op1(PrimOp1::NatSucc, TermRef::local(x)));
    let sy = a.alloc_term(TermDef::Op1(PrimOp1::NatSucc, TermRef::local(y)));
    assert!(!a.eq_at_level_0(TermRef::local(sx), TermRef::local(sy)));
    let fired = a
        .union_if_congruent(TermRef::local(sx), TermRef::local(sy), 1)
        .unwrap();
    assert!(fired);
    assert!(a.eq_at_level_0(TermRef::local(sx), TermRef::local(sy)));
}

#[test]
fn union_if_congruent_step_fails_on_different_shapes() {
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::Bool(true));
    let n = a.alloc_term(TermDef::nat_inline(0));
    let fired = a
        .union_if_congruent(TermRef::local(t), TermRef::local(n), 1)
        .unwrap();
    assert!(!fired);
    assert!(!a.eq_at_level_0(TermRef::local(t), TermRef::local(n)));
}

#[test]
fn union_if_congruent_step_fails_when_children_not_equal() {
    let mut a = Arena::new();
    use covalence_kernel::PrimOp1;
    // Two NatSucc applied to different unequal nat literals.
    let x = a.alloc_term(TermDef::nat_inline(1));
    let y = a.alloc_term(TermDef::nat_inline(2));
    let sx = a.alloc_term(TermDef::Op1(PrimOp1::NatSucc, TermRef::local(x)));
    let sy = a.alloc_term(TermDef::Op1(PrimOp1::NatSucc, TermRef::local(y)));
    let fired = a
        .union_if_congruent(TermRef::local(sx), TermRef::local(sy), 1)
        .unwrap();
    assert!(!fired);
}

#[test]
fn canonical_local_stops_at_foreign() {
    let mut d = Arena::new();
    let d_bool = d.bool_ty();
    let c = alloc_const(&mut d, "c", d_bool);
    let d_frozen = d.freeze();
    let mut a = Arena::new();
    let imp = a.add_import(d_frozen.clone());
    let foreign_ref = a.foreign_term_ref(imp, c);
    // canonical_local returns the foreign ref unchanged.
    let canon = a.canonical_local(foreign_ref);
    assert_eq!(canon, foreign_ref);
}

#[test]
fn union_with_foreign_lhs_updates_local_canonical() {
    // Local term l, foreign term f. union(l, f) sets l's canonical to f.
    let mut d = Arena::new();
    let d_bool = d.bool_ty();
    let foreign_const = alloc_const(&mut d, "c", d_bool);
    let d_frozen = d.freeze();
    let mut a = Arena::new();
    let imp = a.add_import(d_frozen);
    let f_ref = a.foreign_term_ref(imp, foreign_const);
    let l = a.alloc_term(TermDef::Bool(true));
    a.union(TermRef::local(l), f_ref).unwrap();
    assert_eq!(a.canonical_local(TermRef::local(l)), f_ref);
    assert!(a.eq_at_level_0(TermRef::local(l), f_ref));
}

// ---------------------------------------------------------------------------
// Reduce (Phase 3b §10): literal-arg evaluation + identity rules.
// ---------------------------------------------------------------------------

#[test]
fn reduce_logical_not_on_true() {
    use covalence_kernel::PrimOp1;
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::Bool(true));
    let not_t = a.alloc_term(TermDef::Op1(PrimOp1::LogicalNot, TermRef::local(t)));
    let reduced = reduce::step(&mut a, TermRef::local(not_t)).unwrap_or(TermRef::local(not_t));
    assert_eq!(a.term_def(reduced.as_local().unwrap()), &TermDef::Bool(false));
}

#[test]
fn reduce_logical_and_truth_table() {
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::Bool(true));
    let f = a.alloc_term(TermDef::Bool(false));
    let tt = a.alloc_term(TermDef::Op2(PrimOp2::LogicalAnd, TermRef::local(t), TermRef::local(t)));
    let r = reduce::step(&mut a, TermRef::local(tt)).unwrap_or(TermRef::local(tt));
    assert_eq!(a.term_def(r.as_local().unwrap()), &TermDef::Bool(true));
    let tf = a.alloc_term(TermDef::Op2(PrimOp2::LogicalAnd, TermRef::local(t), TermRef::local(f)));
    let r = reduce::step(&mut a, TermRef::local(tf)).unwrap_or(TermRef::local(tf));
    assert_eq!(a.term_def(r.as_local().unwrap()), &TermDef::Bool(false));
    let ft = a.alloc_term(TermDef::Op2(PrimOp2::LogicalAnd, TermRef::local(f), TermRef::local(t)));
    let r = reduce::step(&mut a, TermRef::local(ft)).unwrap_or(TermRef::local(ft));
    assert_eq!(a.term_def(r.as_local().unwrap()), &TermDef::Bool(false));
}

#[test]
fn reduce_nat_succ() {
    use covalence_kernel::PrimOp1;
    let mut a = Arena::new();
    let five = a.alloc_term(TermDef::nat_inline(5));
    let succ_five = a.alloc_term(TermDef::Op1(PrimOp1::NatSucc, TermRef::local(five)));
    let r = reduce::step(&mut a, TermRef::local(succ_five)).unwrap_or(TermRef::local(succ_five));
    assert_eq!(a.term_def(r.as_local().unwrap()), &TermDef::nat_inline(6));
}

#[test]
fn reduce_nat_add() {
    let mut a = Arena::new();
    let five = a.alloc_term(TermDef::nat_inline(5));
    let three = a.alloc_term(TermDef::nat_inline(3));
    let sum = a.alloc_term(TermDef::Op2(
        PrimOp2::NatAdd,
        TermRef::local(five),
        TermRef::local(three),
    ));
    let r = reduce::step(&mut a, TermRef::local(sum)).unwrap_or(TermRef::local(sum));
    assert_eq!(a.term_def(r.as_local().unwrap()), &TermDef::nat_inline(8));
}

#[test]
fn reduce_nat_overflow_promotes_to_stored() {
    let mut a = Arena::new();
    let big = a.alloc_term(TermDef::nat_inline(u64::MAX));
    let one = a.alloc_term(TermDef::nat_inline(1));
    let sum = a.alloc_term(TermDef::Op2(
        PrimOp2::NatAdd,
        TermRef::local(big),
        TermRef::local(one),
    ));
    let r = reduce::step(&mut a, TermRef::local(sum)).unwrap_or(TermRef::local(sum));
    let def = a.term_def(r.as_local().unwrap());
    match def {
        TermDef::NatStored(id) => {
            use covalence_types::Nat;
            let expected = Nat::from(u64::MAX) + Nat::from(1u64);
            assert_eq!(a.nat(*id), &expected);
        }
        other => panic!("expected NatStored, got {other:?}"),
    }
}

#[test]
fn reduce_nat_div_by_zero_pinned_to_zero() {
    let mut a = Arena::new();
    let x = a.alloc_term(TermDef::nat_inline(42));
    let zero = a.alloc_term(TermDef::nat_inline(0));
    let q = a.alloc_term(TermDef::Op2(
        PrimOp2::NatDiv,
        TermRef::local(x),
        TermRef::local(zero),
    ));
    let r = reduce::step(&mut a, TermRef::local(q)).unwrap_or(TermRef::local(q));
    assert_eq!(a.term_def(r.as_local().unwrap()), &TermDef::nat_inline(0));
}

#[test]
fn reduce_nat_comparisons() {
    let mut a = Arena::new();
    let two = a.alloc_term(TermDef::nat_inline(2));
    let three = a.alloc_term(TermDef::nat_inline(3));
    // 2 < 3 = True
    let lt = a.alloc_term(TermDef::Op2(
        PrimOp2::NatLt,
        TermRef::local(two),
        TermRef::local(three),
    ));
    let r = reduce::step(&mut a, TermRef::local(lt)).unwrap_or(TermRef::local(lt));
    assert_eq!(a.term_def(r.as_local().unwrap()), &TermDef::Bool(true));
    // 3 ≤ 2 = False
    let le = a.alloc_term(TermDef::Op2(
        PrimOp2::NatLe,
        TermRef::local(three),
        TermRef::local(two),
    ));
    let r = reduce::step(&mut a, TermRef::local(le)).unwrap_or(TermRef::local(le));
    assert_eq!(a.term_def(r.as_local().unwrap()), &TermDef::Bool(false));
}

#[test]
fn reduce_int_arithmetic() {
    let mut a = Arena::new();
    let five = a.alloc_term(TermDef::int_inline(5));
    let neg_three = a.alloc_term(TermDef::int_inline(-3));
    let sum = a.alloc_term(TermDef::Op2(
        PrimOp2::IntAdd,
        TermRef::local(five),
        TermRef::local(neg_three),
    ));
    let r = reduce::step(&mut a, TermRef::local(sum)).unwrap_or(TermRef::local(sum));
    assert_eq!(a.term_def(r.as_local().unwrap()), &TermDef::int_inline(2));
}

#[test]
fn reduce_nat_popcount() {
    use covalence_kernel::PrimOp1;
    let mut a = Arena::new();
    let v = a.alloc_term(TermDef::nat_inline(0xF0F0));
    let pop = a.alloc_term(TermDef::Op1(PrimOp1::NatPopcount, TermRef::local(v)));
    let r = reduce::step(&mut a, TermRef::local(pop)).unwrap_or(TermRef::local(pop));
    assert_eq!(a.term_def(r.as_local().unwrap()), &TermDef::nat_inline(8));
}

#[test]
fn reduce_noop_on_unreducible() {
    // A free variable can't be reduced — reduce returns it unchanged.
    let mut a = Arena::new();
    let nat = a.nat_ty();
    let x = alloc_free(&mut a, "x", nat);
    let r = reduce::step(&mut a, TermRef::local(x)).unwrap_or(TermRef::local(x));
    assert_eq!(r, TermRef::local(x));
}

// ---------------------------------------------------------------------------
// Rewrite primitive (§4.4).
// ---------------------------------------------------------------------------

#[test]
fn rewrite_replaces_term_def_in_place() {
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::Bool(true));
    assert_eq!(a.term_def(t), &TermDef::Bool(true));
    // Stomp it with False — kernel doesn't validate.
    a.rewrite(t, TermDef::Bool(false));
    assert_eq!(a.term_def(t), &TermDef::Bool(false));
}

#[test]
fn rewrite_updates_type_info() {
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::Bool(true));
    assert_eq!(a.term_uf(t).type_info, TypeInfo::typed(a.bool_ty()));
    // Rewrite to a nat literal — type_info now reflects nat.
    a.rewrite(t, TermDef::nat_inline(42));
    assert_eq!(a.term_uf(t).type_info, TypeInfo::typed(a.nat_ty()));
}

#[test]
fn rewrite_updates_has_free_flag() {
    let mut a = Arena::new();
    // Start with a closed term.
    let t = a.alloc_term(TermDef::Bool(true));
    assert!(!a.term_uf(t).has_free);
    // Rewrite to a Free variable — has_free now true.
    let name = a.intern_string("x".into());
    let bool_ty = a.bool_ty();
    a.rewrite(t, TermDef::Free(name, bool_ty));
    assert!(a.term_uf(t).has_free);
    assert!(!a.term_uf(t).closed());
}

#[test]
fn rewrite_propagates_to_parents() {
    // A parent term holding a Local(t) child sees the new shape of t.
    let mut a = Arena::new();
    let t = a.alloc_term(TermDef::Bool(true));
    let parent = a.alloc_term(TermDef::Op1(
        covalence_kernel::PrimOp1::LogicalNot,
        TermRef::local(t),
    ));
    // Originally: Not(True). reduce → False.
    let r = reduce::step(&mut a, TermRef::local(parent)).unwrap_or(TermRef::local(parent));
    assert_eq!(a.term_def(r.as_local().unwrap()), &TermDef::Bool(false));
    // Now rewrite t to False (unchecked).
    a.rewrite(t, TermDef::Bool(false));
    // Parent's Op1 still points at the same TermId; structural lookup
    // of t now returns False. Reducing parent again gives True.
    let r2 = reduce::step(&mut a, TermRef::local(parent)).unwrap_or(TermRef::local(parent));
    assert_eq!(a.term_def(r2.as_local().unwrap()), &TermDef::Bool(true));
}

#[test]
fn rewrite_preserves_term_id_and_uf_canonical_chain() {
    // The TermId is reused. Pre-rewrite unions also stay in effect.
    let mut a = Arena::new();
    let x = a.alloc_term(TermDef::Bool(true));
    let y = a.alloc_term(TermDef::Bool(false));
    // Union them first.
    a.union(TermRef::local(x), TermRef::local(y)).unwrap();
    assert!(a.eq_at_level_0(TermRef::local(x), TermRef::local(y)));
    // Rewrite x to a different shape — the union still holds.
    a.rewrite(x, TermDef::nat_inline(0));
    assert!(a.eq_at_level_0(TermRef::local(x), TermRef::local(y)));
    // x's def is updated.
    assert_eq!(a.term_def(x), &TermDef::nat_inline(0));
}

// ---------------------------------------------------------------------------
// abstract_over / contains_free.
// ---------------------------------------------------------------------------

#[test]
fn abstract_over_replaces_free_with_bound() {
    let mut a = Arena::new();
    let bool_ty = a.bool_ty();
    let xname = a.intern_string("x".into());
    let x = a.alloc_term(TermDef::Free(xname, bool_ty));
    let r = a.abstract_over(TermRef::local(x), xname, bool_ty, 0);
    assert_eq!(a.term_def(r.as_local().unwrap()), &TermDef::Bound(0));
}

#[test]
fn abstract_over_leaves_other_frees_alone() {
    let mut a = Arena::new();
    let bool_ty = a.bool_ty();
    let xname = a.intern_string("x".into());
    let yname = a.intern_string("y".into());
    let y = a.alloc_term(TermDef::Free(yname, bool_ty));
    let r = a.abstract_over(TermRef::local(y), xname, bool_ty, 0);
    // y is untouched.
    assert_eq!(r, TermRef::local(y));
}

#[test]
fn abstract_over_bumps_depth_under_inner_abs() {
    // λx. Comb(f, x_outer) — abstracting x_outer should produce
    // λx. Comb(f, Bound(1)) since we crossed one Abs.
    let mut a = Arena::new();
    let bool_ty = a.bool_ty();
    let b_to_b = a.alloc_type(TypeDef::Fun(bool_ty, bool_ty));
    let xname = a.intern_string("x".into());
    let fname = a.intern_string("f".into());
    let x_free = a.alloc_term(TermDef::Free(xname, bool_ty));
    let f = a.alloc_term(TermDef::Free(fname, b_to_b));
    let comb = a.alloc_term(TermDef::Comb(TermRef::local(f), TermRef::local(x_free)));
    // Wrap in a fresh Abs (binder unrelated to x).
    let outer = a.alloc_term(TermDef::Abs(bool_ty, TermRef::local(comb)));
    // Abstract over x_free at depth 0 → inside the outer Abs, depth becomes 1.
    let r = a.abstract_over(TermRef::local(outer), xname, bool_ty, 0);
    let r_def = *a.term_def(r.as_local().unwrap());
    let body = match r_def {
        TermDef::Abs(_, b) => b,
        other => panic!("expected Abs, got {other:?}"),
    };
    let body_def = *a.term_def(body.as_local().unwrap());
    match body_def {
        TermDef::Comb(_, arg) => {
            assert_eq!(a.term_def(arg.as_local().unwrap()), &TermDef::Bound(1));
        }
        other => panic!("expected Comb under Abs, got {other:?}"),
    }
}

#[test]
fn contains_free_detects_target_variable() {
    let mut a = Arena::new();
    let bool_ty = a.bool_ty();
    let xname = a.intern_string("x".into());
    let yname = a.intern_string("y".into());
    let x = a.alloc_term(TermDef::Free(xname, bool_ty));
    let y = a.alloc_term(TermDef::Free(yname, bool_ty));
    // Eq(x, y) contains x.
    let eq = a.alloc_term(TermDef::Eq(TermRef::local(x), TermRef::local(y)));
    assert!(a.contains_free(TermRef::local(eq), xname, bool_ty));
    assert!(a.contains_free(TermRef::local(eq), yname, bool_ty));
    // Different type for the same name → not present.
    let nat_ty = a.nat_ty();
    assert!(!a.contains_free(TermRef::local(eq), xname, nat_ty));
}

#[test]
fn subst_free_replaces_target_variable() {
    let mut a = Arena::new();
    let bool_ty = a.bool_ty();
    let xname = a.intern_string("x".into());
    let x = a.alloc_term(TermDef::Free(xname, bool_ty));
    let t = a.alloc_term(TermDef::Bool(true));
    let r = a.subst_free(TermRef::local(x), xname, bool_ty, TermRef::local(t));
    assert_eq!(a.term_def(r.as_local().unwrap()), &TermDef::Bool(true));
}

#[test]
fn subst_free_shifts_replacement_under_inner_abs() {
    // λ_:bool. x  — substituting x with a Bound(0) (open replacement)
    // should shift the replacement to Bound(1) inside the inner Abs.
    let mut a = Arena::new();
    let bool_ty = a.bool_ty();
    let xname = a.intern_string("x".into());
    let x = a.alloc_term(TermDef::Free(xname, bool_ty));
    // Build λ_:bool. x — Abs wrapping the Free.
    let body = a.alloc_term(TermDef::Abs(bool_ty, TermRef::local(x)));
    let open_b0 = a.alloc_term(TermDef::Bound(0));
    let r = a.subst_free(TermRef::local(body), xname, bool_ty, TermRef::local(open_b0));
    let r_def = *a.term_def(r.as_local().unwrap());
    let inner = match r_def {
        TermDef::Abs(_, b) => b,
        other => panic!("expected Abs, got {other:?}"),
    };
    assert_eq!(a.term_def(inner.as_local().unwrap()), &TermDef::Bound(1));
}

#[test]
fn contains_free_uses_has_free_fast_path() {
    // A closed term (no Frees) returns false without walking.
    let mut a = Arena::new();
    let bool_ty = a.bool_ty();
    let t = a.alloc_term(TermDef::Bool(true));
    let xname = a.intern_string("x".into());
    assert!(!a.contains_free(TermRef::local(t), xname, bool_ty));
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
