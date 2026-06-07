//! Round-trip tests for the canonical S-expression syntax.

use bytes::Bytes;
use covalence_pure::{Term, Thm, Type};
use covalence_pure_shell::sexp::{
    UnitObs, term_from_sexp, term_to_sexp, thm_to_sexp, type_from_sexp, type_to_sexp,
};
use covalence_sexp::{SExpr, parse, prettyprint};

fn text(s: &SExpr) -> String {
    let mut buf = Vec::new();
    prettyprint(std::slice::from_ref(s), &mut buf).unwrap();
    String::from_utf8(buf).unwrap()
}

fn parse_one(s: &str) -> SExpr {
    let mut sexps = parse(s).expect("parse failed");
    assert_eq!(sexps.len(), 1, "expected exactly one s-expression");
    sexps.pop().unwrap()
}

fn ty_roundtrip(ty: &Type) {
    let s = type_to_sexp(ty, &UnitObs).expect("serialise failed");
    let printed = text(&s);
    let parsed = parse_one(&printed);
    let back = type_from_sexp(&parsed, &UnitObs).expect("type parse failed");
    assert_eq!(ty, &back, "type round-trip mismatch via text: {}", printed);
}

fn term_roundtrip(t: &Term) {
    let s = term_to_sexp(t, &UnitObs).expect("serialise failed");
    let printed = text(&s);
    let parsed = parse_one(&printed);
    let back = term_from_sexp(&parsed, &UnitObs).expect("term parse failed");
    assert_eq!(t, &back, "term round-trip mismatch via text: {}", printed);
}

#[test]
fn type_roundtrip_basic() {
    ty_roundtrip(&Type::prop());
    ty_roundtrip(&Type::bytes());
    ty_roundtrip(&Type::tfree("a"));
    ty_roundtrip(&Type::fun(Type::bytes(), Type::prop()));
    ty_roundtrip(&Type::tycon("bool", vec![]));
    ty_roundtrip(&Type::tycon("list", vec![Type::tfree("a")]));
    ty_roundtrip(&Type::fun(
        Type::tfree("a"),
        Type::fun(Type::tfree("b"), Type::prop()),
    ));
}

#[test]
fn term_roundtrip_basic() {
    term_roundtrip(&Term::abs("x", Type::bytes(), Term::bound(0)));
    term_roundtrip(&Term::free("x", Type::bytes()));
    term_roundtrip(&Term::const_("c", Type::fun(Type::bytes(), Type::prop())));
    let x = Term::free("x", Type::bytes());
    term_roundtrip(&Term::eq(x.clone(), x.clone()));
    let phi = Term::eq(x.clone(), x.clone());
    term_roundtrip(&Term::imp(phi.clone(), phi.clone()));
    term_roundtrip(&Term::all(
        "x",
        Type::bytes(),
        Term::eq(Term::bound(0), Term::bound(0)),
    ));
    term_roundtrip(&Term::blob(Bytes::from_static(b"hello world")));
    term_roundtrip(&Term::blob(Bytes::from_static(&[0, 1, 2, 0xff])));
}

#[test]
fn thm_serialises() {
    let x = Term::free("x", Type::bytes());
    let thm = Thm::refl(x).unwrap();
    let s = thm_to_sexp(&thm, &UnitObs).expect("serialise failed");
    let printed = text(&s);
    let _ = parse_one(&printed);
    assert!(printed.contains("thm"));
    assert!(printed.contains("hyps"));
    assert!(printed.contains("concl"));
}

#[test]
fn types_dont_collide_in_sexp() {
    let a = Type::prop();
    let b = Type::tycon("prop", vec![]);
    assert_ne!(a, b);
    let sa = type_to_sexp(&a, &UnitObs).expect("a");
    let sb = type_to_sexp(&b, &UnitObs).expect("b");
    assert_ne!(text(&sa), text(&sb));
}

#[test]
fn trivial_observer_roundtrips_through_nil() {
    // (obs () τ) round-trips for the trivial `()` observer via UnitObs.
    let t = Term::obs((), Type::bytes());
    let s = term_to_sexp(&t, &UnitObs).expect("serialise failed");
    let printed = text(&s);
    assert!(printed.contains("obs"));
    assert!(printed.contains("()"));
    let parsed = parse_one(&printed);
    let back = term_from_sexp(&parsed, &UnitObs).expect("parse failed");
    // Note: `back` will be a *different* Object Arc, so `t != back` at
    // the kernel pointer-identity level. But both are well-typed
    // observations of `()` at the chosen type.
    assert_eq!(back.type_of().unwrap(), Type::bytes());
}

#[test]
fn alpha_equivalent_terms_compare_equal_after_roundtrip() {
    let a = Term::abs("x", Type::bytes(), Term::bound(0));
    let b = Term::abs("y", Type::bytes(), Term::bound(0));
    assert_eq!(a, b, "α-equivalent terms compare equal");

    let printed_a = text(&term_to_sexp(&a, &UnitObs).unwrap());
    let printed_b = text(&term_to_sexp(&b, &UnitObs).unwrap());
    assert_ne!(printed_a, printed_b, "hints survive printing");
    let parsed_a = term_from_sexp(&parse_one(&printed_a), &UnitObs).unwrap();
    let parsed_b = term_from_sexp(&parse_one(&printed_b), &UnitObs).unwrap();
    assert_eq!(parsed_a, parsed_b, "α-equivalence survives round-trip");
}
