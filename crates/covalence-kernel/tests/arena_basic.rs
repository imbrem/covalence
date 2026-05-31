//! Phase 1 acceptance tests: arena allocation, builtin variants,
//! closed-flag computation, freezing, foreign imports, and the
//! diamond-import canonical-identity property.

use std::sync::Arc;

use covalence_kernel::{Arena, TermDef, TermKind, TermRef, TypeDef, TypeRef};

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
fn alloc_literal_variants() {
    let mut a = Arena::new();
    // fixed-width
    let _u8 = a.alloc_term(TermDef::U8(0xFF));
    let _i32 = a.alloc_term(TermDef::I32(-1));
    let _u64 = a.alloc_term(TermDef::U64(u64::MAX));
    // arbitrary-precision inline
    let _nat = a.alloc_term(TermDef::NatInline(42));
    let _int = a.alloc_term(TermDef::IntInline(-42));
    // arbitrary-precision stored
    use covalence_types::{Int, Nat};
    let big_nat = a.intern_nat(Nat::from(u128::MAX));
    let big_int = a.intern_int(Int::from(i128::MIN));
    let _ns = a.alloc_term(TermDef::NatStored(big_nat));
    let _is = a.alloc_term(TermDef::IntStored(big_int));
    // bits / bytes
    let bits_id = a.intern_bits(vec![0xAA, 0x55]);
    let bytes_id = a.intern_bytes(vec![0xDE, 0xAD, 0xBE, 0xEF]);
    let _bs = a.alloc_term(TermDef::BitsStored(bits_id));
    let _bys = a.alloc_term(TermDef::BytesStored(bytes_id));
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
    let c = alloc_const(&mut a, "foo", TypeRef::local(bool_ty));
    let n = a.alloc_term(TermDef::NatInline(7));

    for id in [t, f, c, n] {
        assert!(a.term_uf(id).closed(), "term {id:?} should be closed");
    }
}

#[test]
fn closed_false_for_free_var() {
    let mut a = Arena::new();
    let bool_ty = a.alloc_type(TypeDef::Bool);
    let x = alloc_free(&mut a, "x", TypeRef::local(bool_ty));
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
    let neg = alloc_const(&mut a, "not", TypeRef::local(bool_to_bool));
    let app = a.alloc_term(TermDef::Comb(TermRef::local(neg), TermRef::local(t)));
    assert!(a.term_uf(app).closed());

    // With a free var inside, openness propagates.
    let x = alloc_free(&mut a, "x", TypeRef::local(bool_ty));
    let app_open = a.alloc_term(TermDef::Comb(TermRef::local(neg), TermRef::local(x)));
    assert!(!a.term_uf(app_open).closed());
}

#[test]
fn abs_binds_one_level_of_bound() {
    let mut a = Arena::new();
    let bool_ty = a.alloc_type(TypeDef::Bool);

    let b0 = a.alloc_term(TermDef::Bound(0));
    assert_eq!(a.term_uf(b0).bound_depth, 1);
    assert!(!a.term_uf(b0).closed());

    let abs = a.alloc_term(TermDef::Abs(TypeRef::local(bool_ty), TermRef::local(b0)));
    assert_eq!(a.term_uf(abs).bound_depth, 0);
    assert!(a.term_uf(abs).closed());
}

#[test]
fn abs_needs_two_levels_for_bound_one() {
    let mut a = Arena::new();
    let bool_ty = a.alloc_type(TypeDef::Bool);

    let b1 = a.alloc_term(TermDef::Bound(1));
    assert_eq!(a.term_uf(b1).bound_depth, 2);

    let inner = a.alloc_term(TermDef::Abs(TypeRef::local(bool_ty), TermRef::local(b1)));
    assert_eq!(a.term_uf(inner).bound_depth, 1);
    assert!(!a.term_uf(inner).closed());

    let outer = a.alloc_term(TermDef::Abs(
        TypeRef::local(bool_ty),
        TermRef::local(inner),
    ));
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
    let bool_ty_d = d.alloc_type(TypeDef::Bool);
    let c_d = alloc_const(&mut d, "c", TypeRef::local(bool_ty_d));
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

// ---------------------------------------------------------------------------
// Diamond-import test (architecture §4.1).
// ---------------------------------------------------------------------------

#[test]
fn diamond_import_regains_canonical_identity() {
    let mut d = Arena::new();
    let bool_d = d.alloc_type(TypeDef::Bool);
    let x_d = alloc_free(&mut d, "x", TypeRef::local(bool_d));
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
    let _t1 = alloc_free(&mut a1, "x", TypeRef::local(b1));
    let a1_frozen = a1.freeze();

    let mut a2 = Arena::new();
    let b2 = a2.alloc_type(TypeDef::Bool);
    let _t2 = alloc_free(&mut a2, "x", TypeRef::local(b2));
    let a2_frozen = a2.freeze();

    assert!(
        !Arc::ptr_eq(&a1_frozen, &a2_frozen),
        "fresh allocations must be pointer-distinct"
    );

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
    let mut a = Arena::new();
    let bool_ty = a.alloc_type(TypeDef::Bool);

    let by = a.intern_bytes(vec![1, 2, 3]);
    assert_eq!(a.bytes_value(by), &[1, 2, 3]);

    let args = a.intern_tyargs(vec![TypeRef::local(bool_ty)]);
    assert_eq!(a.tyargs(args), &[TypeRef::local(bool_ty)]);
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

// ---------------------------------------------------------------------------
// Abs display hints (side table).
// ---------------------------------------------------------------------------

#[test]
fn abs_hint_stored_and_retrieved() {
    let mut a = Arena::new();
    let bool_ty = a.alloc_type(TypeDef::Bool);
    let body = a.alloc_term(TermDef::Bound(0));
    let abs = a.alloc_term(TermDef::Abs(TypeRef::local(bool_ty), TermRef::local(body)));

    // No hint by default.
    assert!(a.abs_hint(abs).is_none());

    // Set and retrieve.
    let name = a.intern_string("x".into());
    a.set_abs_hint(abs, name);
    assert_eq!(a.abs_hint(abs), Some(name));
}

// ---------------------------------------------------------------------------
// Copy-ness: TermRef, TypeRef, TermDef, TypeDef are all Copy.
// ---------------------------------------------------------------------------

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

// ---------------------------------------------------------------------------
// Expanded primitive type set.
// ---------------------------------------------------------------------------

#[test]
fn alloc_all_primitive_types() {
    let mut a = Arena::new();
    let prims = [
        TypeDef::Bool,
        TypeDef::Bits,
        TypeDef::Bytes,
        TypeDef::Int,
        TypeDef::Nat,
        TypeDef::U8,
        TypeDef::U16,
        TypeDef::U32,
        TypeDef::U64,
        TypeDef::I8,
        TypeDef::I16,
        TypeDef::I32,
        TypeDef::I64,
    ];
    for p in &prims {
        let id = a.alloc_type(*p);
        assert_eq!(a.type_def(id), p);
    }
}

#[test]
fn alloc_tvar_uses_str_id() {
    let mut a = Arena::new();
    let name = a.intern_string("'a".into());
    let id = a.alloc_type(TypeDef::TVar(name));
    match a.type_def(id) {
        TypeDef::TVar(s) => assert_eq!(a.string(*s).as_str(), "'a"),
        other => panic!("expected TVar, got {other:?}"),
    }
}

#[test]
fn alloc_tyapp_uses_str_id_and_tyargs_id() {
    let mut a = Arena::new();
    let bool_ty = a.alloc_type(TypeDef::Bool);
    let name = a.intern_string("list".into());
    let args = a.intern_tyargs(vec![TypeRef::local(bool_ty)]);
    let id = a.alloc_type(TypeDef::Tyapp(name, args));
    match a.type_def(id) {
        TypeDef::Tyapp(n, ar) => {
            assert_eq!(a.string(*n).as_str(), "list");
            let arg_list = a.tyargs(*ar);
            assert_eq!(arg_list.len(), 1);
            assert_eq!(arg_list[0].as_local(), Some(bool_ty));
        }
        other => panic!("expected Tyapp, got {other:?}"),
    }
}

#[test]
fn type_def_is_copy() {
    fn assert_copy<T: Copy>() {}
    assert_copy::<TypeDef>();
}

// ---------------------------------------------------------------------------
// Combinators: Ite / Iter / Eps / Forall / Exists / Ne / Id / Comp /
// LiftOp1 / LiftOp2.
// ---------------------------------------------------------------------------

#[test]
fn alloc_combinator_variants() {
    use covalence_kernel::{PrimOp1, PrimOp2};

    let mut a = Arena::new();
    let bool_ty = a.alloc_type(TypeDef::Bool);
    let nat_ty = a.alloc_type(TypeDef::Nat);

    // A few sample terms.
    let t = a.alloc_term(TermDef::True);
    let f = a.alloc_term(TermDef::False);
    let zero = a.alloc_term(TermDef::NatInline(0));

    // Ne(true, false)
    let ne = a.alloc_term(TermDef::Ne(TermRef::local(t), TermRef::local(f)));
    assert!(matches!(a.term_def(ne), TermDef::Ne(_, _)));

    // Id(bool)
    let id_bool = a.alloc_term(TermDef::Id(TypeRef::local(bool_ty)));
    assert!(matches!(a.term_def(id_bool), TermDef::Id(_)));

    // Comp(true, false) — types are nonsensical for true Comp use, but
    // we're testing storage, not type checking.
    let comp = a.alloc_term(TermDef::Comp(TermRef::local(t), TermRef::local(f)));
    assert!(matches!(a.term_def(comp), TermDef::Comp(_, _)));

    // Iter(0, NatSucc-lifted)
    let succ_lifted = a.alloc_term(TermDef::LiftOp1(PrimOp1::NatSucc));
    let iter = a.alloc_term(TermDef::Iter(
        TermRef::local(zero),
        TermRef::local(succ_lifted),
    ));
    assert!(matches!(a.term_def(iter), TermDef::Iter(_, _)));

    // Ite(true, true)
    let ite = a.alloc_term(TermDef::Ite(TermRef::local(t), TermRef::local(t)));
    assert!(matches!(a.term_def(ite), TermDef::Ite(_, _)));

    // Eps(nat, predicate)
    let pred = a.alloc_term(TermDef::Bound(0));
    let pred_abs = a.alloc_term(TermDef::Abs(TypeRef::local(nat_ty), TermRef::local(pred)));
    let eps = a.alloc_term(TermDef::Eps(
        TypeRef::local(nat_ty),
        TermRef::local(pred_abs),
    ));
    assert!(matches!(a.term_def(eps), TermDef::Eps(_, _)));

    // Forall, Exists with a closed predicate.
    let always_true = a.alloc_term(TermDef::Abs(TypeRef::local(nat_ty), TermRef::local(t)));
    let forall = a.alloc_term(TermDef::Forall(TermRef::local(always_true)));
    let exists = a.alloc_term(TermDef::Exists(TermRef::local(always_true)));
    assert!(matches!(a.term_def(forall), TermDef::Forall(_)));
    assert!(matches!(a.term_def(exists), TermDef::Exists(_)));

    // LiftOp2
    let add_lifted = a.alloc_term(TermDef::LiftOp2(PrimOp2::NatAdd));
    assert!(matches!(a.term_def(add_lifted), TermDef::LiftOp2(_)));
}

#[test]
fn kind_folds_per_op_variants_into_op1_op2() {
    use covalence_kernel::{PrimOp1, PrimOp2};

    let mut a = Arena::new();
    let nat_ty = a.alloc_type(TypeDef::Nat);
    let x = alloc_free(&mut a, "x", TypeRef::local(nat_ty));
    let y = alloc_free(&mut a, "y", TypeRef::local(nat_ty));

    // NatSucc(x) in TermDef becomes TermKind::Op1(NatSucc, x).
    let succ = a.alloc_term(TermDef::NatSucc(TermRef::local(x)));
    match a.kind(succ) {
        TermKind::Op1(op, child) => {
            assert_eq!(op, PrimOp1::NatSucc);
            assert_eq!(child.as_local(), Some(x));
        }
        other => panic!("expected Op1, got {other:?}"),
    }

    // NatAdd(x, y) in TermDef becomes TermKind::Op2(NatAdd, x, y).
    let add = a.alloc_term(TermDef::NatAdd(TermRef::local(x), TermRef::local(y)));
    match a.kind(add) {
        TermKind::Op2(op, a_ref, b_ref) => {
            assert_eq!(op, PrimOp2::NatAdd);
            assert_eq!(a_ref.as_local(), Some(x));
            assert_eq!(b_ref.as_local(), Some(y));
        }
        other => panic!("expected Op2, got {other:?}"),
    }

    // Non-op variants pass through identically.
    let t = a.alloc_term(TermDef::True);
    assert_eq!(a.kind(t), TermKind::True);
    let n = a.alloc_term(TermDef::NatInline(42));
    assert_eq!(a.kind(n), TermKind::NatInline(42));
}

#[test]
fn per_op_variants_with_accessors() {
    use covalence_kernel::{PrimOp1, PrimOp2};

    let mut a = Arena::new();
    let nat_ty = a.alloc_type(TypeDef::Nat);
    let x = alloc_free(&mut a, "x", TypeRef::local(nat_ty));
    let y = alloc_free(&mut a, "y", TypeRef::local(nat_ty));

    // Unary primop application: NatSucc(x)
    let succ_x = a.alloc_term(TermDef::NatSucc(TermRef::local(x)));
    let (op, child) = a.term_def(succ_x).as_op1().expect("as_op1");
    assert_eq!(op, PrimOp1::NatSucc);
    assert_eq!(child.as_local(), Some(x));

    // Binary primop application: NatAdd(x, y)
    let add_xy = a.alloc_term(TermDef::NatAdd(TermRef::local(x), TermRef::local(y)));
    let (op2, a_ref, b_ref) = a.term_def(add_xy).as_op2().expect("as_op2");
    assert_eq!(op2, PrimOp2::NatAdd);
    assert_eq!(a_ref.as_local(), Some(x));
    assert_eq!(b_ref.as_local(), Some(y));

    // Non-op variants return None.
    let t = a.alloc_term(TermDef::True);
    assert!(a.term_def(t).as_op1().is_none());
    assert!(a.term_def(t).as_op2().is_none());

    // A fixed-width op
    let u32_x = a.alloc_term(TermDef::U32(42));
    let popcount = a.alloc_term(TermDef::U32Popcount(TermRef::local(u32_x)));
    let (op, _) = a.term_def(popcount).as_op1().unwrap();
    assert_eq!(op, PrimOp1::U32Popcount);
}

#[test]
fn per_op_closed_flag_propagates() {
    let mut a = Arena::new();
    let nat_ty = a.alloc_type(TypeDef::Nat);

    let x = alloc_free(&mut a, "x", TypeRef::local(nat_ty));
    let zero = a.alloc_term(TermDef::NatInline(0));

    // NatAdd(free, closed) is open
    let open_add = a.alloc_term(TermDef::NatAdd(TermRef::local(x), TermRef::local(zero)));
    assert!(!a.term_uf(open_add).closed());
    assert!(a.term_uf(open_add).has_free);

    // NatAdd(closed, closed) is closed
    let closed_add = a.alloc_term(TermDef::NatAdd(
        TermRef::local(zero),
        TermRef::local(zero),
    ));
    assert!(a.term_uf(closed_add).closed());
}

#[test]
fn combinator_closed_flags() {
    use covalence_kernel::PrimOp1;
    let mut a = Arena::new();
    let bool_ty = a.alloc_type(TypeDef::Bool);

    // Id / LiftOp / LiftOp2: closed regardless.
    let id = a.alloc_term(TermDef::Id(TypeRef::local(bool_ty)));
    assert!(a.term_uf(id).closed());
    let lift = a.alloc_term(TermDef::LiftOp1(PrimOp1::LogicalNot));
    assert!(a.term_uf(lift).closed());

    // Forall over a free var: open.
    let x = alloc_free(&mut a, "x", TypeRef::local(bool_ty));
    let forall_x = a.alloc_term(TermDef::Forall(TermRef::local(x)));
    assert!(!a.term_uf(forall_x).closed());
    assert!(a.term_uf(forall_x).has_free);

    // Ne propagates from both sides.
    let t = a.alloc_term(TermDef::True);
    let ne_closed = a.alloc_term(TermDef::Ne(TermRef::local(t), TermRef::local(t)));
    assert!(a.term_uf(ne_closed).closed());
    let ne_open = a.alloc_term(TermDef::Ne(TermRef::local(t), TermRef::local(x)));
    assert!(!a.term_uf(ne_open).closed());

    // Eps propagates from its predicate body.
    let body = a.alloc_term(TermDef::Bound(0));
    let pred = a.alloc_term(TermDef::Abs(TypeRef::local(bool_ty), TermRef::local(body)));
    let eps = a.alloc_term(TermDef::Eps(
        TypeRef::local(bool_ty),
        TermRef::local(pred),
    ));
    assert!(a.term_uf(eps).closed());
}
