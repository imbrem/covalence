//! Integration tests for the `option` / `result` catalogue entries.
//!
//! `option α := coprod α unit` and `result α β := coprod α β` are
//! opaque newtypes over `coprod`; their constructors/eliminators are
//! *defined* (carry definitional bodies) via the kernel `abs`/`rep`
//! coercions plus the coprod injections/eliminator.
//!
//! The kernel does not prove equations, so these tests check only
//! types, definitional-body type-checking, structure, and identity —
//! never derived equalities like `optionCase d f none = d`.

use covalence_core::defs::*;
use covalence_core::{Term, Type, TermKind, TypeKind};

// ---------------------------------------------------------------------------
// helpers
// ---------------------------------------------------------------------------

fn t(name: &str) -> Type {
    Type::tfree(name)
}

/// Assert a term has exactly the given type.
fn assert_ty(term: &Term, expected: &Type) {
    assert_eq!(&term.type_of().unwrap(), expected);
}

/// Pull the `(spec, args)` out of a `TypeKind::Spec`, asserting the label.
fn type_spec_label<'a>(ty: &'a Type) -> (&'a TypeSpec, &'a [Type]) {
    match ty.kind() {
        TypeKind::Spec(spec, args) => (spec, args.as_slice()),
        other => panic!("expected TypeKind::Spec, got {other:?}"),
    }
}

/// Pull the term-spec label out of a `TermKind::Spec` constructor leaf.
fn term_spec_label(term: &Term) -> String {
    match term.kind() {
        TermKind::Spec(spec, _) => spec.symbol().label().to_string(),
        other => panic!("expected TermKind::Spec, got {other:?}"),
    }
}

// ===========================================================================
// 1. Type-correctness of accessors
// ===========================================================================

#[test]
fn none_at_nat_is_option_nat() {
    assert_ty(&none(Type::nat()), &option(Type::nat()));
}

#[test]
fn none_at_tfree_is_option_tfree() {
    assert_ty(&none(t("a")), &option(t("a")));
}

#[test]
fn some_at_nat_is_arrow_into_option() {
    let expected = Type::fun(Type::nat(), option(Type::nat()));
    assert_ty(&some(Type::nat()), &expected);
}

#[test]
fn some_at_bool_is_arrow_into_option() {
    let expected = Type::fun(Type::bool(), option(Type::bool()));
    assert_ty(&some(Type::bool()), &expected);
}

#[test]
fn option_case_nat_int_full_signature() {
    // optionCase α β : β → (α → β) → option α → β
    let alpha = Type::nat();
    let beta = Type::int();
    let expected = Type::fun(
        beta.clone(),
        Type::fun(
            Type::fun(alpha.clone(), beta.clone()),
            Type::fun(option(alpha), beta),
        ),
    );
    assert_ty(&option_case(Type::nat(), Type::int()), &expected);
}

#[test]
fn option_case_tfree_mix_signature() {
    let alpha = t("x");
    let beta = t("y");
    let expected = Type::fun(
        beta.clone(),
        Type::fun(
            Type::fun(alpha.clone(), beta.clone()),
            Type::fun(option(alpha), beta),
        ),
    );
    assert_ty(&option_case(t("x"), t("y")), &expected);
}

#[test]
fn is_some_at_nat_is_predicate_on_option() {
    let expected = Type::fun(option(Type::nat()), Type::bool());
    assert_ty(&is_some(Type::nat()), &expected);
}

#[test]
fn from_some_at_int_extracts_to_carrier() {
    let expected = Type::fun(option(Type::int()), Type::int());
    assert_ty(&from_some(Type::int()), &expected);
}

#[test]
fn ok_at_nat_int_is_arrow_into_result() {
    // ok α β : α → result α β
    let expected = Type::fun(Type::nat(), result(Type::nat(), Type::int()));
    assert_ty(&ok(Type::nat(), Type::int()), &expected);
}

#[test]
fn err_at_nat_int_is_arrow_from_beta() {
    // err α β : β → result α β
    let expected = Type::fun(Type::int(), result(Type::nat(), Type::int()));
    assert_ty(&err(Type::nat(), Type::int()), &expected);
}

#[test]
fn ok_and_err_with_tfree_mix() {
    let alpha = t("e");
    let beta = t("v");
    assert_ty(
        &ok(alpha.clone(), beta.clone()),
        &Type::fun(alpha.clone(), result(alpha.clone(), beta.clone())),
    );
    assert_ty(
        &err(alpha.clone(), beta.clone()),
        &Type::fun(beta.clone(), result(alpha, beta)),
    );
}

// ===========================================================================
// 2. Newtype carriers
// ===========================================================================

#[test]
fn option_carrier_is_coprod_alpha_unit() {
    let spec = option_spec();
    let expected = coprod(t("a"), Type::unit());
    assert_eq!(spec.ty(), Some(&expected));
}

#[test]
fn result_carrier_is_coprod_alpha_beta() {
    let spec = result_spec();
    let expected = coprod(t("a"), t("b"));
    assert_eq!(spec.ty(), Some(&expected));
}

// ===========================================================================
// 3. Definitional bodies — each spec carries a body, and the body's
//    type equals the spec's recorded `.ty()`.
// ===========================================================================

#[test]
fn all_option_result_specs_carry_bodies() {
    assert!(some_spec().tm().is_some(), "some has a body");
    assert!(none_spec().tm().is_some(), "none has a body");
    assert!(option_case_spec().tm().is_some(), "optionCase has a body");
    assert!(is_some_spec().tm().is_some(), "isSome has a body");
    assert!(from_some_spec().tm().is_some(), "fromSome has a body");
    assert!(ok_spec().tm().is_some(), "ok has a body");
    assert!(err_spec().tm().is_some(), "err has a body");
}

/// For every constructor/eliminator spec, the body type-checks and its
/// type equals the spec's recorded `.ty()`.
#[test]
fn spec_bodies_typecheck_to_recorded_type() {
    let specs: [(&str, TermSpec); 7] = [
        ("some", some_spec()),
        ("none", none_spec()),
        ("optionCase", option_case_spec()),
        ("isSome", is_some_spec()),
        ("fromSome", from_some_spec()),
        ("ok", ok_spec()),
        ("err", err_spec()),
    ];
    for (label, spec) in specs {
        let body = spec.tm().unwrap_or_else(|| panic!("{label}: has body"));
        let body_ty = body
            .type_of()
            .unwrap_or_else(|e| panic!("{label}: body type-of: {e:?}"));
        let recorded = spec.ty().unwrap_or_else(|| panic!("{label}: has ty"));
        assert_eq!(&body_ty, recorded, "{label}: body type vs recorded ty");
    }
}

#[test]
fn none_body_type_is_polymorphic_option() {
    // none's body is `abs (inr unit) : option 'a` — a *value*, not a
    // function. Its recorded type is `option 'a`.
    let spec = none_spec();
    let body_ty = spec.tm().unwrap().type_of().unwrap();
    assert_eq!(&body_ty, &option(t("a")));
}

// ===========================================================================
// 4. Structure / Display
// ===========================================================================

#[test]
fn option_nat_kind_is_spec_labelled_option() {
    let (spec, args) = {
        let ty = option(Type::nat());
        let (s, a) = type_spec_label(&ty);
        (s.symbol().label().to_string(), a.to_vec())
    };
    assert_eq!(spec, "option");
    assert_eq!(args, vec![Type::nat()]);
}

#[test]
fn result_nat_int_kind_is_spec_labelled_result() {
    let ty = result(Type::nat(), Type::int());
    let (spec, args) = type_spec_label(&ty);
    assert_eq!(spec.symbol().label(), "result");
    assert_eq!(args, [Type::nat(), Type::int()]);
}

#[test]
fn constructor_term_leaf_labels() {
    assert_eq!(term_spec_label(&some(Type::nat())), "option.some");
    assert_eq!(term_spec_label(&none(Type::nat())), "option.none");
    assert_eq!(term_spec_label(&ok(Type::nat(), Type::int())), "result.ok");
    assert_eq!(term_spec_label(&err(Type::nat(), Type::int())), "result.err");
    assert_eq!(
        term_spec_label(&option_case(Type::nat(), Type::int())),
        "option.case"
    );
    assert_eq!(term_spec_label(&is_some(Type::nat())), "option.isSome");
    assert_eq!(term_spec_label(&from_some(Type::nat())), "option.fromSome");
}

#[test]
fn option_type_display() {
    assert_eq!(format!("{}", option(Type::nat())), "(option nat)");
}

#[test]
fn result_type_display() {
    assert_eq!(
        format!("{}", result(Type::nat(), Type::int())),
        "(result nat int)"
    );
}

#[test]
fn spec_singletons_are_shared() {
    assert!(option_spec().ptr_eq(&option_spec()));
    assert!(result_spec().ptr_eq(&result_spec()));
    assert!(some_spec().ptr_eq(&some_spec()));
    assert!(option_case_spec().ptr_eq(&option_case_spec()));
    assert!(ok_spec().ptr_eq(&ok_spec()));
}

// ===========================================================================
// 5. Edge cases
// ===========================================================================

#[test]
fn nested_option_of_option() {
    // option (option nat)
    let inner = option(Type::nat());
    let outer = option(inner.clone());
    let (spec, args) = type_spec_label(&outer);
    assert_eq!(spec.symbol().label(), "option");
    assert_eq!(args, [inner.clone()]);
    // the single arg is itself an `option` Spec.
    let (inner_spec, inner_args) = type_spec_label(&args[0]);
    assert_eq!(inner_spec.symbol().label(), "option");
    assert_eq!(inner_args, [Type::nat()]);
}

#[test]
fn some_at_nested_option_typechecks() {
    let inner = option(Type::nat());
    let expected = Type::fun(inner.clone(), option(inner.clone()));
    assert_ty(&some(inner), &expected);
}

#[test]
fn result_same_types_both_sides() {
    // result nat nat — α and β coincide.
    let ty = result(Type::nat(), Type::nat());
    let (spec, args) = type_spec_label(&ty);
    assert_eq!(spec.symbol().label(), "result");
    assert_eq!(args, [Type::nat(), Type::nat()]);
    // ok / err at coinciding types both land in `result nat nat`.
    assert_ty(
        &ok(Type::nat(), Type::nat()),
        &Type::fun(Type::nat(), result(Type::nat(), Type::nat())),
    );
    assert_ty(
        &err(Type::nat(), Type::nat()),
        &Type::fun(Type::nat(), result(Type::nat(), Type::nat())),
    );
}

#[test]
fn result_with_unit_error() {
    // result nat unit — common "no-info error" shape.
    let ty = result(Type::nat(), Type::unit());
    let (spec, args) = type_spec_label(&ty);
    assert_eq!(spec.symbol().label(), "result");
    assert_eq!(args, [Type::nat(), Type::unit()]);
    assert_ty(
        &err(Type::nat(), Type::unit()),
        &Type::fun(Type::unit(), result(Type::nat(), Type::unit())),
    );
}

#[test]
fn option_of_tfree() {
    let ty = option(t("a"));
    let (spec, args) = type_spec_label(&ty);
    assert_eq!(spec.symbol().label(), "option");
    assert_eq!(args, [t("a")]);
    // carrier of the *instantiated* leaf is exposed via the shared spec.
    assert_eq!(option_spec().ty(), Some(&coprod(t("a"), Type::unit())));
}

#[test]
fn is_some_and_from_some_at_unit() {
    // option unit is a legitimate type; accessors specialize cleanly.
    assert_ty(
        &is_some(Type::unit()),
        &Type::fun(option(Type::unit()), Type::bool()),
    );
    assert_ty(
        &from_some(Type::unit()),
        &Type::fun(option(Type::unit()), Type::unit()),
    );
}

#[test]
fn option_case_collapsing_branch_types() {
    // optionCase nat nat : nat → (nat → nat) → option nat → nat
    let expected = Type::fun(
        Type::nat(),
        Type::fun(
            Type::fun(Type::nat(), Type::nat()),
            Type::fun(option(Type::nat()), Type::nat()),
        ),
    );
    assert_ty(&option_case(Type::nat(), Type::nat()), &expected);
}
