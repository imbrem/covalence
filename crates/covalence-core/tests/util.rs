//! Integration tests for the small utility catalogue entries:
//! `fail : 'a` (the unspecified value) and the `cond` conditional plus
//! its `Term::cond` builder.

use covalence_core::defs;
use covalence_core::{Term, TermKind, Type};

// ===========================================================================
// fail : 'a := ε(λx. T)
// ===========================================================================

#[test]
fn fail_at_nat_has_type_nat() {
    assert_eq!(defs::fail(Type::nat()).type_of().unwrap(), Type::nat());
}

#[test]
fn fail_at_tfree_is_polymorphic() {
    let a = Type::tfree("a");
    assert_eq!(defs::fail(a.clone()).type_of().unwrap(), a);
}

#[test]
fn fail_label_is_fail() {
    assert_eq!(defs::fail_spec().symbol().label(), "fail");
}

#[test]
fn fail_body_is_an_epsilon_of_polymorphic_type() {
    let spec = defs::fail_spec();
    let body = spec.tm().expect("fail has a body (ε λx. T)");
    // The body has the bare polymorphic type 'a.
    assert_eq!(body.type_of().unwrap(), Type::tfree("a"));
    assert_eq!(spec.ty(), Some(&Type::tfree("a")));
}

#[test]
fn fail_kind_is_spec_leaf() {
    match defs::fail(Type::int()).kind() {
        TermKind::Spec(spec, args) => {
            assert_eq!(spec.symbol().label(), "fail");
            assert_eq!(args.as_slice(), &[Type::int()]);
        }
        other => panic!("expected TermKind::Spec, got {other:?}"),
    }
}

// ===========================================================================
// cond + Term::cond
// ===========================================================================

#[test]
fn cond_accessor_is_polymorphic_conditional() {
    // cond α : bool → α → α → α
    let alpha = Type::nat();
    let expected = Type::fun(
        Type::bool(),
        Type::fun(alpha.clone(), Type::fun(alpha.clone(), alpha.clone())),
    );
    assert_eq!(defs::cond(alpha).type_of().unwrap(), expected);
}

#[test]
fn term_cond_builds_well_typed_application() {
    // Term::ite-style builder: `cond b x y : α`, α inferred from `x`.
    let b = Term::free("b", Type::bool());
    let x = Term::nat_lit(1u32);
    let y = Term::nat_lit(2u32);
    let t = Term::cond(b, x, y);
    assert_eq!(t.type_of().unwrap(), Type::nat());
}

#[test]
fn term_cond_head_is_the_cond_spec() {
    // Unwind `cond b x y` to its head and check the leaf is `bool.cond`.
    let t = Term::cond(
        Term::free("b", Type::bool()),
        Term::int_lit(covalence_types::Int::zero()),
        Term::int_lit(covalence_types::Int::one()),
    );
    let mut head = &t;
    while let TermKind::App(f, _) = head.kind() {
        head = f;
    }
    match head.kind() {
        TermKind::Spec(spec, args) => {
            assert_eq!(spec.symbol().label(), "bool.cond");
            assert_eq!(args.as_slice(), &[Type::int()]);
        }
        other => panic!("expected cond Spec head, got {other:?}"),
    }
}

#[test]
fn term_cond_matches_manual_application() {
    let b = Term::free("b", Type::bool());
    let x = Term::nat_lit(7u32);
    let y = Term::nat_lit(9u32);
    let manual = Term::app(
        Term::app(Term::app(defs::cond(Type::nat()), b.clone()), x.clone()),
        y.clone(),
    );
    assert_eq!(Term::cond(b, x, y), manual);
}
