//! Integration tests for the kernel `abs`/`rep` coercions
//! (`Term::spec_abs` / `Term::spec_rep`), the `unit` bool-subtype
//! `TypeSpec`, and the `Thm::unit_eq` singleton rule.
//!
//! These specs are *defined* but the kernel does not prove their
//! equations; integration tests cannot rewrite/prove. So everything
//! here checks only types (`type_of`), structure (`kind`), and
//! rule success / failure — never a derived equality.

use covalence_core::defs;
use covalence_core::{Term, TermKind, Thm, Type, TypeKind};

// ============================================================================
// Helpers
// ============================================================================

/// The canonical `unit` value term `abs T : unit`.
fn unit_val() -> Term {
    Term::app(
        Term::spec_abs(defs::unit_spec(), vec![]),
        Term::bool_lit(true),
    )
}

/// Walk a HOL equation `App(App(Eq, lhs), rhs)` and return the two
/// sides, asserting the head is a `TermKind::Eq`. Mirrors the
/// conclusion-walking pattern in `builtins.rs`'s `assert_reduces`.
fn parse_hol_eq(concl: &Term) -> (Term, Term) {
    let TermKind::App(eq_lhs_app, rhs) = concl.kind() else {
        panic!("concl is not an App: {concl:?}");
    };
    let TermKind::App(eq_op, lhs) = eq_lhs_app.kind() else {
        panic!("concl LHS is not an App: {concl:?}");
    };
    assert!(
        matches!(eq_op.kind(), TermKind::Eq(_)),
        "concl head is not HOL =: {concl:?}",
    );
    (lhs.clone(), rhs.clone())
}

// ============================================================================
// 1. `Type::unit()` is a bool-subtype TypeSpec
// ============================================================================

#[test]
fn unit_type_is_spec_leaf() {
    let u = Type::unit();
    let TypeKind::Spec(spec, args) = u.kind() else {
        panic!("Type::unit() is not a TypeKind::Spec: {:?}", u.kind());
    };
    assert_eq!(spec.symbol().label(), "unit");
    assert!(args.is_empty(), "unit is a 0-ary spec");
}

#[test]
fn unit_carrier_is_bool() {
    assert_eq!(defs::unit_spec().ty(), Some(&Type::bool()));
}

#[test]
fn unit_has_selector_predicate() {
    assert!(
        defs::unit_spec().tm().is_some(),
        "unit_spec should carry the λb. b = T predicate"
    );
}

#[test]
fn unit_type_is_stable_across_calls() {
    assert_eq!(Type::unit(), Type::unit());
}

#[test]
fn unit_type_is_not_bool() {
    // The carrier is bool, but the wrapper type is distinct.
    assert_ne!(Type::unit(), Type::bool());
}

#[test]
fn unit_spec_is_self_consistent_handle() {
    // Two calls return ptr_eq handles (LazyLock-cached).
    assert!(defs::unit_spec().ptr_eq(&defs::unit_spec()));
}

// ============================================================================
// 2. `spec_abs` / `spec_rep` types
// ============================================================================

#[test]
fn option_abs_type() {
    // abs : coprod(nat, unit) -> option(nat)
    let abs = Term::spec_abs(defs::option_spec(), vec![Type::nat()]);
    let expected = Type::fun(
        defs::coprod(Type::nat(), Type::unit()),
        defs::option(Type::nat()),
    );
    assert_eq!(abs.type_of().unwrap(), expected);
}

#[test]
fn option_rep_type() {
    // rep : option(nat) -> coprod(nat, unit)
    let rep = Term::spec_rep(defs::option_spec(), vec![Type::nat()]);
    let expected = Type::fun(
        defs::option(Type::nat()),
        defs::coprod(Type::nat(), Type::unit()),
    );
    assert_eq!(rep.type_of().unwrap(), expected);
}

#[test]
fn option_abs_rep_are_inverse_shaped() {
    // domain of abs == codomain of rep, and vice-versa.
    let abs_ty = Term::spec_abs(defs::option_spec(), vec![Type::nat()])
        .type_of()
        .unwrap();
    let rep_ty = Term::spec_rep(defs::option_spec(), vec![Type::nat()])
        .type_of()
        .unwrap();
    let (TypeKind::Fun(abs_dom, abs_cod), TypeKind::Fun(rep_dom, rep_cod)) =
        (abs_ty.kind(), rep_ty.kind())
    else {
        panic!("abs/rep are not function-typed");
    };
    assert_eq!(abs_dom, rep_cod, "abs domain == rep codomain (carrier)");
    assert_eq!(abs_cod, rep_dom, "abs codomain == rep domain (wrapper)");
}

#[test]
fn result_abs_rep_types() {
    // carrier of result is `coprod a b`; here a = nat, b = bool.
    let args = vec![Type::nat(), Type::bool()];
    let carrier = defs::coprod(Type::nat(), Type::bool());
    let wrapper = defs::result(Type::nat(), Type::bool());

    let abs = Term::spec_abs(defs::result_spec(), args.clone());
    assert_eq!(
        abs.type_of().unwrap(),
        Type::fun(carrier.clone(), wrapper.clone())
    );

    let rep = Term::spec_rep(defs::result_spec(), args);
    assert_eq!(rep.type_of().unwrap(), Type::fun(wrapper, carrier));
}

#[test]
fn coprod_abs_rep_types() {
    // carrier of coprod is the tagged relation `a -> b -> bool -> bool`.
    let args = vec![Type::nat(), Type::bool()];
    let carrier = Type::fun(
        Type::nat(),
        Type::fun(Type::bool(), Type::fun(Type::bool(), Type::bool())),
    );
    let wrapper = defs::coprod(Type::nat(), Type::bool());

    let abs = Term::spec_abs(defs::coprod_spec(), args.clone());
    assert_eq!(
        abs.type_of().unwrap(),
        Type::fun(carrier.clone(), wrapper.clone())
    );

    let rep = Term::spec_rep(defs::coprod_spec(), args);
    assert_eq!(rep.type_of().unwrap(), Type::fun(wrapper, carrier));
}

#[test]
fn prod_abs_rep_types() {
    // carrier of prod is `a -> b -> bool`.
    let args = vec![Type::nat(), Type::bool()];
    let carrier = Type::fun(
        Type::nat(),
        Type::fun(Type::bool(), Type::bool()),
    );
    let wrapper = defs::prod(Type::nat(), Type::bool());

    let abs = Term::spec_abs(defs::prod_spec(), args.clone());
    assert_eq!(
        abs.type_of().unwrap(),
        Type::fun(carrier.clone(), wrapper.clone())
    );

    let rep = Term::spec_rep(defs::prod_spec(), args);
    assert_eq!(rep.type_of().unwrap(), Type::fun(wrapper, carrier));
}

#[test]
fn int_abs_rep_types() {
    // int is a 0-ary quotient spec; carrier is `(prod nat nat) -> bool`
    // (the powerset the quotient closure lives in).
    let carrier = Type::fun(
        defs::prod(Type::nat(), Type::nat()),
        Type::bool(),
    );
    let wrapper = Type::spec(defs::int_ty_spec(), vec![]);

    let abs = Term::spec_abs(defs::int_ty_spec(), vec![]);
    assert_eq!(
        abs.type_of().unwrap(),
        Type::fun(carrier.clone(), wrapper.clone())
    );

    let rep = Term::spec_rep(defs::int_ty_spec(), vec![]);
    assert_eq!(rep.type_of().unwrap(), Type::fun(wrapper, carrier));
}

#[test]
fn int_wrapper_is_type_int() {
    // The int spec's 0-ary wrapper should be exactly `Type::int()`.
    assert_eq!(Type::spec(defs::int_ty_spec(), vec![]), Type::int());
}

#[test]
fn unit_abs_rep_types() {
    // unit is a 0-ary subtype spec; carrier is `bool`.
    let abs = Term::spec_abs(defs::unit_spec(), vec![]);
    assert_eq!(
        abs.type_of().unwrap(),
        Type::fun(Type::bool(), Type::unit())
    );

    let rep = Term::spec_rep(defs::unit_spec(), vec![]);
    assert_eq!(
        rep.type_of().unwrap(),
        Type::fun(Type::unit(), Type::bool())
    );
}

#[test]
fn list_abs_rep_types() {
    // carrier of list is `stream(option a)`.
    let carrier = defs::stream(defs::option(Type::nat()));
    let wrapper = defs::list(Type::nat());

    let abs = Term::spec_abs(defs::list_spec(), vec![Type::nat()]);
    assert_eq!(
        abs.type_of().unwrap(),
        Type::fun(carrier.clone(), wrapper.clone())
    );

    let rep = Term::spec_rep(defs::list_spec(), vec![Type::nat()]);
    assert_eq!(rep.type_of().unwrap(), Type::fun(wrapper, carrier));
}

#[test]
fn polymorphic_option_abs_rep_types() {
    // Edge case: polymorphic type args via tfree.
    let a = Type::tfree("a");
    let carrier = defs::coprod(a.clone(), Type::unit());
    let wrapper = defs::option(a.clone());

    let abs = Term::spec_abs(defs::option_spec(), vec![a.clone()]);
    assert_eq!(
        abs.type_of().unwrap(),
        Type::fun(carrier.clone(), wrapper.clone())
    );

    let rep = Term::spec_rep(defs::option_spec(), vec![a]);
    assert_eq!(rep.type_of().unwrap(), Type::fun(wrapper, carrier));
}

#[test]
fn polymorphic_result_abs_type() {
    // Two distinct polymorphic args.
    let a = Type::tfree("a");
    let b = Type::tfree("b");
    let abs = Term::spec_abs(defs::result_spec(), vec![a.clone(), b.clone()]);
    let expected = Type::fun(defs::coprod(a.clone(), b.clone()), defs::result(a, b));
    assert_eq!(abs.type_of().unwrap(), expected);
}

#[test]
fn rep_then_abs_type_composition_lines_up() {
    // Conceptual abs∘rep round trip: rep takes wrapper -> carrier,
    // abs takes carrier -> wrapper. Feeding rep's output into abs is
    // well-typed iff abs's domain == rep's codomain.
    let abs = Term::spec_abs(defs::option_spec(), vec![Type::nat()]);
    let rep = Term::spec_rep(defs::option_spec(), vec![Type::nat()]);
    let TypeKind::Fun(abs_dom, _) = abs.type_of().unwrap().kind().clone() else {
        panic!("abs not function-typed");
    };
    let TypeKind::Fun(_, rep_cod) = rep.type_of().unwrap().kind().clone() else {
        panic!("rep not function-typed");
    };
    assert_eq!(
        abs_dom, rep_cod,
        "abs(rep(x)) is well-typed: abs domain matches rep codomain"
    );
}

// ============================================================================
// 3. `Thm::unit_eq`
// ============================================================================

#[test]
fn unit_eq_succeeds_for_two_unit_values() {
    let u1 = unit_val();
    let u2 = unit_val();
    let thm = Thm::unit_eq(u1.clone(), u2.clone()).expect("unit_eq on two unit values");
    let (lhs, rhs) = parse_hol_eq(thm.concl());
    assert_eq!(lhs, u1, "lhs is the first input");
    assert_eq!(rhs, u2, "rhs is the second input");
}

#[test]
fn unit_eq_no_hyps() {
    let thm = Thm::unit_eq(unit_val(), unit_val()).unwrap();
    assert!(
        thm.hyps().iter().next().is_none(),
        "unit_eq carries no hypotheses"
    );
}

#[test]
fn unit_eq_with_free_unit_vars() {
    let u1 = Term::free("u", Type::unit());
    let v2 = Term::free("v", Type::unit());
    let thm = Thm::unit_eq(u1.clone(), v2.clone()).expect("unit_eq on two free unit vars");
    let (lhs, rhs) = parse_hol_eq(thm.concl());
    assert_eq!(lhs, u1);
    assert_eq!(rhs, v2);
}

#[test]
fn unit_eq_mixes_value_and_free_var() {
    let u1 = unit_val();
    let v2 = Term::free("u", Type::unit());
    let thm = Thm::unit_eq(u1.clone(), v2.clone()).expect("unit_eq on value and free var");
    let (lhs, rhs) = parse_hol_eq(thm.concl());
    assert_eq!(lhs, u1);
    assert_eq!(rhs, v2);
}

#[test]
fn unit_eq_reflexive_same_term() {
    let u = unit_val();
    let thm = Thm::unit_eq(u.clone(), u.clone()).expect("unit_eq of a unit term with itself");
    let (lhs, rhs) = parse_hol_eq(thm.concl());
    assert_eq!(lhs, u);
    assert_eq!(rhs, u);
}

#[test]
fn unit_eq_no_obs() {
    // No observation leaves: a fully trusted theorem.
    let thm = Thm::unit_eq(unit_val(), unit_val()).unwrap();
    assert!(thm.has_no_obs());
}

// ---- failure cases ----

#[test]
fn unit_eq_rejects_nat_in_first_position() {
    let bad = Term::nat_lit(covalence_types::Nat::zero());
    assert!(Thm::unit_eq(bad, unit_val()).is_err());
}

#[test]
fn unit_eq_rejects_nat_in_second_position() {
    let bad = Term::nat_lit(covalence_types::Nat::zero());
    assert!(Thm::unit_eq(unit_val(), bad).is_err());
}

#[test]
fn unit_eq_rejects_bool_in_first_position() {
    // A bool-typed term is NOT a unit-typed term, even though the
    // carrier is bool.
    assert!(Thm::unit_eq(Term::bool_lit(true), unit_val()).is_err());
}

#[test]
fn unit_eq_rejects_bool_in_second_position() {
    assert!(Thm::unit_eq(unit_val(), Term::bool_lit(false)).is_err());
}

#[test]
fn unit_eq_rejects_two_nats() {
    let a = Term::nat_lit(covalence_types::Nat::zero());
    let b = Term::nat_lit(covalence_types::Nat::zero());
    assert!(Thm::unit_eq(a, b).is_err());
}

#[test]
fn unit_eq_rejects_free_var_of_wrong_type() {
    let bad = Term::free("x", Type::nat());
    assert!(Thm::unit_eq(bad.clone(), unit_val()).is_err());
    assert!(Thm::unit_eq(unit_val(), bad).is_err());
}

// ============================================================================
// unit.nil — the canonical unit element (catalogue term)
// ============================================================================

#[test]
fn unit_nil_has_type_unit() {
    assert_eq!(defs::unit_nil().type_of().unwrap(), Type::unit());
}

#[test]
fn unit_nil_label_is_dotted() {
    assert_eq!(defs::unit_nil_spec().symbol().label(), "unit.nil");
}

#[test]
fn unit_nil_body_typechecks_to_unit() {
    let spec = defs::unit_nil_spec();
    let body = spec.tm().expect("unit.nil has a definitional body (abs T)");
    assert_eq!(body.type_of().unwrap(), Type::unit());
    assert_eq!(spec.ty(), Some(&Type::unit()));
}

#[test]
fn unit_nil_spec_is_shared_singleton() {
    assert!(defs::unit_nil_spec().ptr_eq(&defs::unit_nil_spec()));
}

#[test]
fn unit_eq_relates_unit_nil_to_itself_and_others() {
    // The catalogue element equals itself, a fresh free unit var, and
    // the raw `abs T` representative — all by the singleton rule.
    assert!(Thm::unit_eq(defs::unit_nil(), defs::unit_nil()).is_ok());
    assert!(Thm::unit_eq(defs::unit_nil(), Term::free("u", Type::unit())).is_ok());
    assert!(Thm::unit_eq(defs::unit_nil(), unit_val()).is_ok());
}

#[test]
fn unit_nil_kind_is_spec_leaf() {
    match defs::unit_nil().kind() {
        TermKind::Spec(spec, args) => {
            assert_eq!(spec.symbol().label(), "unit.nil");
            assert!(args.is_empty());
        }
        other => panic!("expected TermKind::Spec, got {other:?}"),
    }
}
