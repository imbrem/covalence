//! End-to-end tests: parse real Haskell snippets and lower them through each
//! demo backend.

use covalence_haskell::ast::{Expr, Lit};
use covalence_haskell::backends::{NoLitLower, PeanoLower, SExprLower};
use covalence_haskell::lower::{lower, lower_decl};
use covalence_haskell::parse::{parse_expr, parse_module};

fn sexpr(src: &str) -> String {
    let e = parse_expr(src).unwrap_or_else(|err| panic!("parse `{src}` failed: {err}"));
    lower(&e, &mut SExprLower).expect("sexpr lowering failed")
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
fn application_is_left_assoc() {
    assert_eq!(sexpr("f x y"), "((f x) y)");
}

#[test]
fn let_binding_parses() {
    assert_eq!(
        sexpr("let id = \\x -> x in id 5"),
        "(let id = (\\x -> x) in (id 5))"
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
    assert_eq!(sexpr("map (\\x -> x) xs"), "((map (\\x -> x)) xs)");
}

#[test]
fn string_literal_with_escape() {
    assert_eq!(
        parse_expr("\"hi\\n\"").unwrap(),
        Expr::Lit(Lit::Str("hi\n".into()))
    );
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

    // `const x y = x` ⇝ `\x -> \y -> x`
    let (name, out) = lower_decl(&m[0], &mut SExprLower).unwrap();
    assert_eq!(name, "const");
    assert_eq!(out, "(\\x -> (\\y -> x))");

    // `compose f g x = f (g x)`
    let (name, out) = lower_decl(&m[1], &mut SExprLower).unwrap();
    assert_eq!(name, "compose");
    assert_eq!(out, "(\\f -> (\\g -> (\\x -> (f (g x)))))");
}

#[test]
fn module_layout_lite_continuation() {
    // An indented second line continues the first declaration.
    let src = "big a =\n  a + 1\n";
    let m = parse_module(src).unwrap();
    assert_eq!(m.len(), 1);
    let (name, out) = lower_decl(&m[0], &mut SExprLower).unwrap();
    assert_eq!(name, "big");
    assert_eq!(out, "(\\a -> (+ a 1))");
}

// --------------------------------------------------------------------------
// Pluggable lowering — the centerpiece
// --------------------------------------------------------------------------

#[test]
fn numeric_literal_lowering_differs_per_backend() {
    let e = parse_expr("f 3").unwrap();

    let s = lower(&e, &mut SExprLower).unwrap();
    let p = lower(&e, &mut PeanoLower).unwrap();

    assert_eq!(s, "(f 3)");
    assert_eq!(p, "(f (S (S (S Z))))");
    assert_ne!(s, p, "same AST must lower differently per backend");
}

#[test]
fn peano_zero_is_z() {
    let e = parse_expr("0").unwrap();
    assert_eq!(lower(&e, &mut PeanoLower).unwrap(), "Z");
}

#[test]
fn strict_subset_backend_rejects_literals() {
    // NoLitLower does not implement nat_lit, so a literal-containing expr fails.
    let with_lit = parse_expr("f 5").unwrap();
    let err = lower(&with_lit, &mut NoLitLower).unwrap_err();
    assert_eq!(err.0.construct, "natural-number literal");

    // ...but a literal-free expression lowers fine with the same backend.
    let without_lit = parse_expr("\\x -> f x").unwrap();
    assert_eq!(
        lower(&without_lit, &mut NoLitLower).unwrap(),
        "(\\x -> (f x))"
    );
}
