//! Tests for the extended expression grammar: `if`/`then`/`else`, list and
//! tuple literals, unit, comments, and top-level type-signature lines. Each
//! construct is checked for parse shape, canonical lowering, print → parse
//! round-trip, and (for a representative operator case) improved error text.

use covalence_haskell::ast::{Expr, Lit};
use covalence_haskell::backends::{DesugarBackend, TextBackend};
use covalence_haskell::lower::{expr_to_sexpr, lower, module_to_text};
use covalence_haskell::parse::{parse_expr, parse_module};
use covalence_haskell::realize::realize;
use covalence_haskell::sexpr::parse_sexpr;

/// Haskell source ⇒ canonical S-expression text (via the canonical lowering).
fn sexpr(src: &str) -> String {
    let e = parse_expr(src).unwrap_or_else(|err| panic!("parse `{src}` failed: {err}"));
    expr_to_sexpr(&e).to_text()
}

/// Assert the canonical text round-trips: `text → parse → realize == text`,
/// and the IR re-parses to the same tree.
fn round_trips(src: &str) {
    let e = parse_expr(src).unwrap_or_else(|err| panic!("parse `{src}`: {err}"));
    let ir = expr_to_sexpr(&e);
    let reparsed = parse_sexpr(&ir.to_text()).unwrap();
    assert_eq!(reparsed, ir, "IR round-trip for `{src}`");
    assert_eq!(
        realize(&reparsed, &mut TextBackend).unwrap(),
        ir.to_text(),
        "TextBackend round-trip for `{src}`"
    );
}

// --------------------------------------------------------------------------
// if / then / else
// --------------------------------------------------------------------------

#[test]
fn if_parses_and_lowers() {
    assert_eq!(
        parse_expr("if b then 1 else 2").unwrap(),
        Expr::if_(
            Expr::Var("b".into()),
            Expr::Lit(Lit::Nat(1u64.into())),
            Expr::Lit(Lit::Nat(2u64.into())),
        )
    );
    assert_eq!(sexpr("if b then 1 else 2"), "(if b 1 2)");
}

#[test]
fn if_nests_and_carries_applications() {
    assert_eq!(sexpr("if f x then g y else h z"), "(if (f x) (g y) (h z))");
    // The else-branch swallows a trailing `if` (right-associative sugar).
    assert_eq!(
        sexpr("if a then b else if c then d else e"),
        "(if a b (if c d e))"
    );
}

#[test]
fn if_under_application_needs_parens() {
    // A bare `if` is not an atom, so it must be parenthesised to be an argument.
    assert_eq!(sexpr("f (if b then 1 else 2)"), "(f (if b 1 2))");
    round_trips("f (if b then 1 else 2)");
}

// --------------------------------------------------------------------------
// list literals
// --------------------------------------------------------------------------

#[test]
fn empty_and_nonempty_lists() {
    assert_eq!(sexpr("[]"), "(list)");
    assert_eq!(sexpr("[1, 2, 3]"), "(list 1 2 3)");
    assert_eq!(sexpr("[f x, g y]"), "(list (f x) (g y))");
    round_trips("[1, 2, 3]");
    round_trips("[]");
}

#[test]
fn nested_lists() {
    assert_eq!(sexpr("[[1], [2, 3]]"), "(list (list 1) (list 2 3))");
}

// --------------------------------------------------------------------------
// tuples and unit
// --------------------------------------------------------------------------

#[test]
fn unit_and_grouping_and_tuples() {
    // `()` is unit; `(e)` is just `e`; `(a, b)` is a tuple.
    assert_eq!(sexpr("()"), "(unit)");
    assert_eq!(sexpr("(1)"), "1");
    assert_eq!(sexpr("(1, 2)"), "(tuple 1 2)");
    assert_eq!(sexpr("(1, 2, 3)"), "(tuple 1 2 3)");
    round_trips("()");
    round_trips("(1, 2, 3)");
}

#[test]
fn tuple_of_mixed_forms() {
    assert_eq!(
        sexpr("(\\x -> x, [1], if b then 0 else 1)"),
        "(tuple (lambda x x) (list 1) (if b 0 1))"
    );
}

// --------------------------------------------------------------------------
// comments
// --------------------------------------------------------------------------

#[test]
fn line_and_block_comments_are_skipped() {
    assert_eq!(sexpr("f -- trailing\n x"), "(f x)");
    assert_eq!(sexpr("f {- inline -} x"), "(f x)");
    // Nested block comments.
    assert_eq!(sexpr("f {- a {- b -} c -} x"), "(f x)");
}

#[test]
fn comments_in_modules() {
    let src = "\
-- the identity combinator
idish x = x -- returns its argument
{- a block
   comment -}
constish x y = x
";
    let m = parse_module(src).unwrap();
    assert_eq!(m.len(), 2);
    assert_eq!(
        module_to_text(&m),
        "(define idish (lambda x x))\n(define constish (lambda x (lambda y x)))\n"
    );
}

// --------------------------------------------------------------------------
// top-level type signatures (parsed and ignored)
// --------------------------------------------------------------------------

#[test]
fn type_signatures_are_parsed_and_ignored() {
    let src = "\
const :: a -> b -> a
const x y = x
mapOption :: (a -> b) -> Option a -> Option b
mapOption g m = m none (compose some g)
";
    let m = parse_module(src).unwrap();
    // Two definitions survive; the two signature lines are dropped.
    assert_eq!(m.len(), 2);
    assert_eq!(m[0].name, "const");
    assert_eq!(m[1].name, "mapOption");
}

// --------------------------------------------------------------------------
// improved error messages
// --------------------------------------------------------------------------

#[test]
fn errors_name_the_found_token() {
    // Missing `then`.
    let err = parse_expr("if b 1 else 2").unwrap_err();
    assert!(
        err.message.contains("expected `then`") && err.message.contains("found"),
        "message was: {}",
        err.message
    );
    // Unclosed list: end of input where `]` or `,` was expected.
    let err = parse_expr("[1, 2").unwrap_err();
    assert!(
        err.message.contains("found end of input"),
        "message was: {}",
        err.message
    );
    // A stray operator where an expression is expected.
    let err = parse_expr("f (* 2)").unwrap_err();
    assert!(
        err.message.contains("found operator `*`"),
        "message was: {}",
        err.message
    );
}

// --------------------------------------------------------------------------
// DesugarBackend — the structural interchange transform
// --------------------------------------------------------------------------

#[test]
fn desugar_backend_rewrites_list_and_unit() {
    let out = lower(&parse_expr("[1, 2, 3]").unwrap(), &mut DesugarBackend)
        .unwrap()
        .to_text();
    assert_eq!(out, "(cons 1 (cons 2 (cons 3 nil)))");
    // Empty list ⇒ bare nil; unit ⇒ bare `unit`.
    assert_eq!(
        lower(&parse_expr("[]").unwrap(), &mut DesugarBackend)
            .unwrap()
            .to_text(),
        "nil"
    );
    assert_eq!(
        lower(&parse_expr("()").unwrap(), &mut DesugarBackend)
            .unwrap()
            .to_text(),
        "unit"
    );
    // Nested lists desugar recursively; non-list heads (`if`, `tuple`, apps)
    // are left structurally intact.
    assert_eq!(
        lower(
            &parse_expr("if b then [1] else (2, 3)").unwrap(),
            &mut DesugarBackend
        )
        .unwrap()
        .to_text(),
        "(if b (cons 1 nil) (tuple 2 3))"
    );
}

/// The desugaring meets third-party S-expression text at the same IR point as
/// the Haskell route: both realize identically.
#[test]
fn desugar_backend_third_party_text_equals_haskell_route() {
    let via_haskell = lower(&parse_expr("[f x, g y]").unwrap(), &mut DesugarBackend).unwrap();
    let ir = parse_sexpr("(list (f x) (g y))").unwrap();
    let via_text = realize(&ir, &mut DesugarBackend).unwrap();
    assert_eq!(via_text, via_haskell);
    assert_eq!(via_text.to_text(), "(cons (f x) (cons (g y) nil))");
}

#[test]
fn full_pipeline_through_text_backend() {
    // A single expression exercising every new construct realizes to text.
    let src = "if member 0 [1, 2] then (some 0, none) else ()";
    let out = lower(&parse_expr(src).unwrap(), &mut TextBackend).unwrap();
    assert_eq!(
        out,
        "(if ((member 0) (list 1 2)) (tuple (some 0) none) (unit))"
    );
}
