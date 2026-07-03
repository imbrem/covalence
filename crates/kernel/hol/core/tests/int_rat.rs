//! Integration tests for the `int` (Grothendieck `(nat×nat)/~`) and
//! `rat` (`(int×int)/~` by cross-multiplication) derived types in
//! `covalence_core::defs`.
//!
//! Three flavours of assertion:
//!   - **type structure** of the quotient type specs and the op
//!     accessors,
//!   - **definitional-body shape**: the defined ops carry a `.tm()`
//!     body whose `type_of()` matches the recorded `.ty()`; the
//!     declaration-only ops (`intDiv`/`intMod`/`ratLe`) carry none,
//!   - **literal reduction** via the real kernel rule
//!     `Thm::reduce_prim` (closed applications to literal args), which
//!     goes through `builtins::reduce_spec` independent of the bodies.
//!
//! We cannot *prove* derived equalities here, so the only equational
//! facts asserted are `reduce_prim` one-step reductions on literals.

use covalence_core::defs;
use covalence_core::{Term, TermKind, Thm, Type, TypeKind};
use covalence_types::{Int, Nat, Sign};

// ============================================================================
// Literal + reduction helpers (mirrors builtins.rs `#[cfg(test)]` style)
// ============================================================================

fn nat(n: u32) -> Term {
    Term::nat_lit(Nat::from_inner(n.into()))
}

fn int(n: i32) -> Term {
    let nat = Nat::from_inner((n.unsigned_abs()).into());
    let sign = if n == 0 {
        Sign::Zero
    } else if n > 0 {
        Sign::Positive
    } else {
        Sign::Negative
    };
    Term::int_lit(Int::from_sign_nat(sign, nat))
}

fn bool_lit(b: bool) -> Term {
    Term::bool_lit(b)
}

/// `f a` — one-arg application.
fn un(f: Term, a: Term) -> Term {
    Term::app(f, a)
}

/// `f a b` — two-arg application.
fn bin(f: Term, a: Term, b: Term) -> Term {
    Term::app(Term::app(f, a), b)
}

/// Reduce `t` one step and assert the conclusion is the HOL equation
/// `t = want`. Walks the conclusion `App(App(Eq, lhs), rhs)`.
fn assert_reduces(t: Term, want: Term) {
    let thm =
        Thm::reduce_prim(t.clone()).unwrap_or_else(|e| panic!("reduce failed for {t:?}: {e:?}"));
    let TermKind::App(eq_lhs_app, rhs) = thm.concl().kind() else {
        panic!("concl is not an App: {:?}", thm.concl());
    };
    let TermKind::App(eq_op, lhs) = eq_lhs_app.kind() else {
        panic!("concl LHS is not an App: {:?}", thm.concl());
    };
    assert!(
        matches!(eq_op.kind(), TermKind::Eq(_)),
        "concl head is not HOL =: {:?}",
        thm.concl()
    );
    assert_eq!(lhs, &t, "LHS mismatch");
    assert_eq!(rhs, &want, "RHS mismatch");
}

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
// 4. Literal reduction edge cases (via Thm::reduce_prim)
// ============================================================================

#[test]
fn int_add_literals() {
    assert_reduces(bin(defs::int_add(), int(-3), int(4)), int(1));
    assert_reduces(bin(defs::int_add(), int(0), int(0)), int(0));
    assert_reduces(bin(defs::int_add(), int(-5), int(-7)), int(-12));
}

#[test]
fn int_sub_literals() {
    assert_reduces(bin(defs::int_sub(), int(3), int(7)), int(-4));
    assert_reduces(bin(defs::int_sub(), int(-3), int(-3)), int(0));
}

#[test]
fn int_mul_literals() {
    assert_reduces(bin(defs::int_mul(), int(-2), int(-3)), int(6));
    assert_reduces(bin(defs::int_mul(), int(-2), int(3)), int(-6));
    assert_reduces(bin(defs::int_mul(), int(0), int(99)), int(0));
}

#[test]
fn int_neg_literals() {
    assert_reduces(un(defs::int_neg(), int(7)), int(-7));
    assert_reduces(un(defs::int_neg(), int(-7)), int(7));
    assert_reduces(un(defs::int_neg(), int(0)), int(0));
}

#[test]
fn int_abs_literals() {
    assert_reduces(un(defs::int_abs(), int(-12)), nat(12));
    assert_reduces(un(defs::int_abs(), int(12)), nat(12));
    assert_reduces(un(defs::int_abs(), int(0)), nat(0));
}

#[test]
fn int_sgn_literals() {
    assert_reduces(un(defs::int_sgn(), int(-9)), int(-1));
    assert_reduces(un(defs::int_sgn(), int(0)), int(0));
    assert_reduces(un(defs::int_sgn(), int(9)), int(1));
}

#[test]
fn int_succ_pred_literals() {
    assert_reduces(un(defs::int_succ(), int(-1)), int(0));
    assert_reduces(un(defs::int_succ(), int(41)), int(42));
    assert_reduces(un(defs::int_pred(), int(0)), int(-1));
    assert_reduces(un(defs::int_pred(), int(-41)), int(-42));
}

#[test]
fn int_div_literals() {
    assert_reduces(bin(defs::int_div(), int(17), int(5)), int(3));
    // Truncation toward zero on the negative dividend.
    assert_reduces(bin(defs::int_div(), int(-17), int(5)), int(-3));
    // Division by zero → 0 (kernel convention).
    assert_reduces(bin(defs::int_div(), int(17), int(0)), int(0));
    assert_reduces(bin(defs::int_div(), int(-17), int(0)), int(0));
}

#[test]
fn int_mod_literals() {
    assert_reduces(bin(defs::int_mod(), int(17), int(5)), int(2));
    // x mod 0 = x (Euclidean convention, matching int.mod's body).
    assert_reduces(bin(defs::int_mod(), int(17), int(0)), int(17));
    assert_reduces(bin(defs::int_mod(), int(-17), int(0)), int(-17));
}

#[test]
fn int_le_literals() {
    assert_reduces(bin(defs::int_le(), int(-3), int(2)), bool_lit(true));
    assert_reduces(bin(defs::int_le(), int(2), int(2)), bool_lit(true));
    assert_reduces(bin(defs::int_le(), int(5), int(-1)), bool_lit(false));
}

#[test]
fn int_lt_literals() {
    assert_reduces(bin(defs::int_lt(), int(-3), int(2)), bool_lit(true));
    assert_reduces(bin(defs::int_lt(), int(2), int(2)), bool_lit(false));
    assert_reduces(bin(defs::int_lt(), int(5), int(-1)), bool_lit(false));
}

#[test]
fn partial_application_does_not_reduce() {
    // A binary op applied to a single literal is not a closed-form
    // reduction; `reduce_prim` errors.
    assert!(Thm::reduce_prim(un(defs::int_add(), int(1))).is_err());
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
