//! Integration tests for the `int` (Grothendieck `(nat×nat)/~`) and
//! `rat` (`(int×int)/~` by cross-multiplication) derived types in
//! `covalence_hol_eval::defs`.
//!
//! Two flavours of assertion:
//!   - **type structure** of the quotient type specs and the op
//!     accessors,
//!   - **definitional-body shape**: the defined ops carry a `.tm()`
//!     body whose `type_of()` matches the recorded `.ty()`; the
//!     declaration-only ops (`ratLe`) carry none.
//!
//! We cannot *prove* derived equalities here; closed-literal reduction
//! semantics live in `covalence-hol-eval`'s `tests/audit_reduce.rs`
//! (the cert path — the kernel no longer carries an in-TCB reducer).

use covalence_core::{Type, TypeKind};
use covalence_hol_eval::defs;
/// Pin the pure tier: these are `Thm<CoreLang>` unit tests (stage E1).
type Thm = covalence_core::Thm;

// ============================================================================
// 1. `int` type structure
// ============================================================================

#[test]
fn int_type_kind_is_spec_int() {
    let int_ty = Type::int();
    let TypeKind::Spec(spec, args) = int_ty.kind() else {
        panic!("Type::int() is not a Spec: {:?}", int_ty.kind());
    };
    assert_eq!(spec.symbol().label(), "int");
    assert!(args.is_empty(), "int takes no type args");
}

#[test]
fn int_ty_spec_carrier_is_powerset_of_pair() {
    // Carrier of the quotient = (prod nat nat) → bool.
    let want = Type::fun(defs::prod(Type::nat(), Type::nat()), Type::bool());
    assert_eq!(defs::int_ty_spec().ty(), Some(&want));
}

#[test]
fn int_ty_spec_has_close_predicate() {
    // The quotient close/relation predicate is recorded as the `tm`.
    assert!(defs::int_ty_spec().tm().is_some());
}

#[test]
fn int_zero_has_int_type() {
    assert_eq!(defs::int_zero().type_of().unwrap(), Type::int());
}

// ============================================================================
// 2. Int op accessor types
// ============================================================================

fn ii_i() -> Type {
    // int → int → int
    Type::fun(Type::int(), Type::fun(Type::int(), Type::int()))
}
fn i_i() -> Type {
    // int → int
    Type::fun(Type::int(), Type::int())
}
fn ii_b() -> Type {
    // int → int → bool
    Type::fun(Type::int(), Type::fun(Type::int(), Type::bool()))
}

#[test]
fn binary_int_ops_have_int_int_to_int_type() {
    assert_eq!(defs::int_add().type_of().unwrap(), ii_i());
    assert_eq!(defs::int_sub().type_of().unwrap(), ii_i());
    assert_eq!(defs::int_mul().type_of().unwrap(), ii_i());
}

#[test]
fn unary_int_ops_have_int_to_int_type() {
    assert_eq!(defs::int_neg().type_of().unwrap(), i_i());
    assert_eq!(defs::int_succ().type_of().unwrap(), i_i());
    assert_eq!(defs::int_pred().type_of().unwrap(), i_i());
    assert_eq!(defs::int_sgn().type_of().unwrap(), i_i());
}

#[test]
fn int_abs_has_int_to_nat_type() {
    assert_eq!(
        defs::int_abs().type_of().unwrap(),
        Type::fun(Type::int(), Type::nat())
    );
}

#[test]
fn int_comparisons_have_int_int_to_bool_type() {
    assert_eq!(defs::int_le().type_of().unwrap(), ii_b());
    assert_eq!(defs::int_lt().type_of().unwrap(), ii_b());
}

#[test]
fn int_div_mod_have_int_int_to_int_type() {
    assert_eq!(defs::int_div().type_of().unwrap(), ii_i());
    assert_eq!(defs::int_mod().type_of().unwrap(), ii_i());
}

// ============================================================================
// 3. Definitional bodies type-check (defined ops) / are absent (decl-only)
// ============================================================================

/// For a defined op spec, assert it has a body whose `type_of()`
/// agrees with the recorded signature.
fn assert_body_typechecks(spec: defs::TermSpec) {
    let label = spec.symbol().label().to_string();
    let tm = spec
        .tm()
        .unwrap_or_else(|| panic!("{label}: expected a definitional body"));
    let recorded = spec
        .ty()
        .unwrap_or_else(|| panic!("{label}: expected a recorded type"))
        .clone();
    let body_ty = tm
        .type_of()
        .unwrap_or_else(|e| panic!("{label}: body type_of failed: {e:?}"));
    assert_eq!(body_ty, recorded, "{label}: body type mismatch");
}

#[test]
fn defined_int_op_bodies_typecheck() {
    assert_body_typechecks(defs::int_add_spec());
    assert_body_typechecks(defs::int_sub_spec());
    assert_body_typechecks(defs::int_mul_spec());
    assert_body_typechecks(defs::int_neg_spec());
    assert_body_typechecks(defs::int_succ_spec());
    assert_body_typechecks(defs::int_pred_spec());
    assert_body_typechecks(defs::int_le_spec());
    assert_body_typechecks(defs::int_lt_spec());
    assert_body_typechecks(defs::int_abs_spec());
    assert_body_typechecks(defs::int_sgn_spec());
}

#[test]
fn int_div_mod_have_let_style_bodies() {
    // intDiv/intMod are now defined (truncating division built from
    // intSgn/intAbs/intMul/intSub + natDiv/natToInt), so they carry a
    // let-style body whose type is the spec's own type — `unfold_term_spec`
    // succeeds and reduces them.
    for spec in [defs::int_div_spec(), defs::int_mod_spec()] {
        let ty = spec.ty().expect("recorded signature");
        let body = spec.tm().expect("let-style body present");
        assert_eq!(
            &body.type_of().unwrap(),
            ty,
            "let-style: body has the spec's declared type"
        );
    }
    // And the unfolding equation is derivable.
    assert!(Thm::unfold_term_spec(defs::int_div()).is_ok());
    assert!(Thm::unfold_term_spec(defs::int_mod()).is_ok());
}

// ============================================================================
// 5. `rat` type structure
// ============================================================================

#[test]
fn rat_type_kind_is_spec_rat() {
    let rat_ty = defs::rat_ty();
    let TypeKind::Spec(spec, args) = rat_ty.kind() else {
        panic!("rat_ty() is not a Spec: {:?}", rat_ty.kind());
    };
    assert_eq!(spec.symbol().label(), "rat");
    assert!(args.is_empty(), "rat takes no type args");
}

#[test]
fn rat_spec_carrier_is_powerset_of_int_pair() {
    // Carrier of the quotient = (prod int int.pos) → bool — the
    // denominator is drawn from the strictly-positive integers.
    let want = Type::fun(defs::prod(Type::int(), defs::int_pos_ty()), Type::bool());
    assert_eq!(defs::rat_spec().ty(), Some(&want));
}

#[test]
fn rat_spec_has_close_predicate() {
    assert!(defs::rat_spec().tm().is_some());
}

#[test]
fn rat_le_has_rat_rat_to_bool_type() {
    let want = Type::fun(defs::rat_ty(), Type::fun(defs::rat_ty(), Type::bool()));
    assert_eq!(defs::rat_le().type_of().unwrap(), want);
}

#[test]
fn rat_le_is_declaration_only() {
    assert!(
        defs::rat_le_spec().tm().is_none(),
        "ratLe should be declaration-only"
    );
    assert!(defs::rat_le_spec().ty().is_some());
}

// ===========================================================================
// int.pos — the strictly-positive integers subtype (rat's denominator)
// ===========================================================================

#[test]
fn int_pos_kind_is_spec_labelled() {
    let ty = defs::int_pos_ty();
    match ty.kind() {
        TypeKind::Spec(spec, args) => {
            assert_eq!(spec.symbol().label(), "int.pos");
            assert!(args.is_empty());
        }
        other => panic!("expected TypeKind::Spec, got {other:?}"),
    }
}

#[test]
fn int_pos_is_subtype_of_int_with_predicate() {
    let spec = defs::int_pos_spec();
    // carrier is `int`; the selector predicate `λx. 0 < x` is present.
    assert_eq!(spec.ty(), Some(&Type::int()));
    let pred = spec.tm().expect("int.pos has a selector predicate");
    // predicate : int → bool
    assert_eq!(
        pred.type_of().unwrap(),
        Type::fun(Type::int(), Type::bool())
    );
}

#[test]
fn int_pos_spec_is_shared_singleton() {
    assert!(defs::int_pos_spec().ptr_eq(&defs::int_pos_spec()));
}
