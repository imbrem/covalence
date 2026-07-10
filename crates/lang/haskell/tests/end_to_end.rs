//! End-to-end tests: parse real Haskell snippets, lower them through the
//! canonical Haskell ⇒ SExpr desugaring, and realize them through each demo
//! backend.

use covalence_haskell::ast::{Expr, Lit};
use covalence_haskell::backends::{NoLitBackend, PeanoBackend, TextBackend};
use covalence_haskell::lower::{expr_to_sexpr, lower, lower_decl};
use covalence_haskell::parse::{parse_expr, parse_module};
use covalence_haskell::sexpr::Nat;

/// Haskell source ⇒ canonical S-expression text (via the canonical lowering).
fn sexpr(src: &str) -> String {
    let e = parse_expr(src).unwrap_or_else(|err| panic!("parse `{src}` failed: {err}"));
    expr_to_sexpr(&e).to_text()
}

// --------------------------------------------------------------------------
// Parsing
// --------------------------------------------------------------------------

#[test]
fn parses_identity_lambda() {
    assert_eq!(
        parse_expr("\\x -> x").unwrap(),
        Expr::lam("x", Expr::Var("x".into()))
    );
}

#[test]
fn multi_param_lambda_desugars() {
    // `\f x -> f x` ⇝ `\f -> \x -> (f x)`
    let expected = Expr::lam(
        "f",
        Expr::lam("x", Expr::app(Expr::Var("f".into()), Expr::Var("x".into()))),
    );
    assert_eq!(parse_expr("\\f x -> f x").unwrap(), expected);
}

#[test]
fn nat_literal_is_covalence_nat() {
    assert_eq!(
        parse_expr("42").unwrap(),
        Expr::Lit(Lit::Nat(Nat::from(42u64)))
    );
}

#[test]
fn nat_literal_is_arbitrary_precision() {
    // 2^128 — strictly greater than u128::MAX; must parse and lower intact.
    let big = "340282366920938463463374607431768211456";
    assert_eq!(
        parse_expr(big).unwrap(),
        Expr::Lit(Lit::Nat(big.parse().unwrap()))
    );
    assert_eq!(sexpr(big), big);
}

#[test]
fn application_is_left_assoc() {
    assert_eq!(sexpr("f x y"), "((f x) y)");
}

#[test]
fn let_binding_parses() {
    assert_eq!(
        sexpr("let id = \\x -> x in id 5"),
        "(let id (lambda x x) (id 5))"
    );
}

#[test]
fn operator_precedence() {
    // `*` binds tighter than `+`.
    assert_eq!(sexpr("1 + 2 * 3"), "(+ 1 (* 2 3))");
    // `-` is left-associative and same precedence as `+`.
    assert_eq!(sexpr("1 - 2 - 3"), "(- (- 1 2) 3)");
    // `==` is the loosest.
    assert_eq!(sexpr("1 + 2 == 3"), "(== (+ 1 2) 3)");
}

#[test]
fn application_binds_tighter_than_operators() {
    assert_eq!(sexpr("f x + g y"), "(+ (f x) (g y))");
}

#[test]
fn parenthesisation() {
    assert_eq!(sexpr("(1 + 2) * 3"), "(* (+ 1 2) 3)");
}

#[test]
fn map_lambda_over_var() {
    assert_eq!(sexpr("map (\\x -> x) xs"), "((map (lambda x x)) xs)");
}

#[test]
fn string_literal_with_escape() {
    assert_eq!(
        parse_expr("\"hi\\n\"").unwrap(),
        Expr::Lit(Lit::Str("hi\n".into()))
    );
    // ...and it lowers to a quoted, escaped string atom.
    assert_eq!(sexpr("\"hi\\n\""), "\"hi\\n\"");
}

#[test]
fn parse_error_has_position() {
    // The `)` with no matching `(` is a trailing token.
    let err = parse_expr("f x )").unwrap_err();
    assert_eq!(err.pos, 4);
}

// --------------------------------------------------------------------------
// Modules
// --------------------------------------------------------------------------

#[test]
fn module_top_level_defs() {
    let src = "const x y = x\ncompose f g x = f (g x)\n";
    let m = parse_module(src).unwrap();
    assert_eq!(m.len(), 2);

    // `const x y = x` ⇝ `(lambda x (lambda y x))`
    let (name, out) = lower_decl(&m[0], &mut TextBackend).unwrap();
    assert_eq!(name, "const");
    assert_eq!(out, "(lambda x (lambda y x))");

    // `compose f g x = f (g x)`
    let (name, out) = lower_decl(&m[1], &mut TextBackend).unwrap();
    assert_eq!(name, "compose");
    assert_eq!(out, "(lambda f (lambda g (lambda x (f (g x)))))");
}

#[test]
fn module_layout_lite_continuation() {
    // An indented second line continues the first declaration.
    let src = "big a =\n  a + 1\n";
    let m = parse_module(src).unwrap();
    assert_eq!(m.len(), 1);
    let (name, out) = lower_decl(&m[0], &mut TextBackend).unwrap();
    assert_eq!(name, "big");
    assert_eq!(out, "(lambda a (+ a 1))");
}

// --------------------------------------------------------------------------
// Pluggable realization — the centerpiece
// --------------------------------------------------------------------------

#[test]
fn numeric_atom_realization_differs_per_backend() {
    let e = parse_expr("f 3").unwrap();

    let s = lower(&e, &mut TextBackend).unwrap();
    let p = lower(&e, &mut PeanoBackend).unwrap().to_text();

    assert_eq!(s, "(f 3)");
    assert_eq!(p, "(f (S (S (S Z))))");
    assert_ne!(s, p, "same IR must realize differently per backend");
}

#[test]
fn peano_zero_is_z() {
    let e = parse_expr("0").unwrap();
    assert_eq!(lower(&e, &mut PeanoBackend).unwrap().to_text(), "Z");
}

#[test]
fn strict_subset_backend_rejects_literals() {
    // NoLitBackend does not implement nat, so a literal-containing expr fails.
    let with_lit = parse_expr("f 5").unwrap();
    let err = lower(&with_lit, &mut NoLitBackend).unwrap_err();
    assert_eq!(err.0.construct, "natural-number atom");

    // ...but a literal-free expression realizes fine with the same backend.
    let without_lit = parse_expr("\\x -> f x").unwrap();
    assert_eq!(
        lower(&without_lit, &mut NoLitBackend).unwrap(),
        "(lambda x (f x))"
    );
}

#[test]
fn text_backend_agrees_with_canonical_printer() {
    for src in ["f x y", "let id = \\x -> x in id 5", "1 + 2 * 3", "\"s\""] {
        let e = parse_expr(src).unwrap();
        let ir = expr_to_sexpr(&e);
        assert_eq!(
            lower(&e, &mut TextBackend).unwrap(),
            ir.to_text(),
            "TextBackend must agree with SExpr::to_text for `{src}`"
        );
    }
}
