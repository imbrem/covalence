//! Third-party interchange tests: the S-expression TEXT layer is a full
//! citizen. Hand-written S-expression text — never touching Haskell syntax —
//! parses and feeds the SAME backends as the Haskell route; and the Haskell
//! route survives a print → parse round-trip unchanged.

use covalence_haskell::backends::{PeanoBackend, TextBackend};
use covalence_haskell::lower::{expr_to_sexpr, lower, module_to_sexprs, module_to_text};
use covalence_haskell::parse::{parse_expr, parse_module};
use covalence_haskell::realize::realize;
use covalence_haskell::sexpr::{SExpr, parse_sexpr, parse_sexprs};

// --------------------------------------------------------------------------
// Hand-written S-expression text == the Haskell route
// --------------------------------------------------------------------------

/// A third party hands us TEXT; it must realize identically to the Haskell
/// source that lowers to the same IR — through the same TextBackend.
#[test]
fn third_party_text_equals_haskell_route_text_backend() {
    let cases = [
        // (hand-written sexpr text, equivalent Haskell source)
        ("(lambda x (f (g x)))", r"\x -> f (g x)"),
        ("(let id (lambda x x) (id 5))", "let id = \\x -> x in id 5"),
        ("(+ 1 (* 2 3))", "1 + 2 * 3"),
        ("((map (lambda x x)) xs)", "map (\\x -> x) xs"),
    ];
    for (text, hs) in cases {
        let ir = parse_sexpr(text).unwrap_or_else(|e| panic!("`{text}`: {e}"));
        let via_text = realize(&ir, &mut TextBackend).unwrap();
        let via_haskell = lower(&parse_expr(hs).unwrap(), &mut TextBackend).unwrap();
        assert_eq!(via_text, via_haskell, "routes disagree for `{text}`");
    }
}

/// Same through a numeral-reinterpreting backend: the IR is the meeting
/// point, so the Peano realization agrees too.
#[test]
fn third_party_text_equals_haskell_route_peano_backend() {
    // NB the canonical lowering curries: `add 2 (h 0)` is `((add 2) (h 0))`.
    let ir = parse_sexpr("((add 2) (h 0))").unwrap();
    let via_text = realize(&ir, &mut PeanoBackend).unwrap();
    let via_haskell = lower(&parse_expr("add 2 (h 0)").unwrap(), &mut PeanoBackend).unwrap();
    assert_eq!(via_text, via_haskell);
    assert_eq!(via_text.to_text(), "((add (S (S Z))) (h Z))");
}

/// Third-party text can also use IR shapes the Haskell front end never emits
/// (an empty list, a digit-leading symbol) — the backends still serve it.
#[test]
fn third_party_text_beyond_the_haskell_image() {
    let ir = parse_sexpr("(f () 1abc)").unwrap();
    assert_eq!(realize(&ir, &mut TextBackend).unwrap(), "(f () 1abc)");
}

// --------------------------------------------------------------------------
// Haskell → SExpr → text → parse → backend == direct
// --------------------------------------------------------------------------

#[test]
fn print_parse_round_trip_equals_direct() {
    let sources = [
        r"\x -> x",
        r"\f x -> f x",
        "let id = \\x -> x in id 5",
        "1 + 2 * 3 == 7",
        "map (\\x -> g x 0) xs",
        "\"hi\\n\"",
        // 2^128: the round-trip must preserve arbitrary-precision literals.
        // (Kept away from PeanoBackend below — a unary numeral of 2^128
        // nodes is exactly the representation the covalence Nat avoids.)
        "f 340282366920938463463374607431768211456",
    ];
    for src in sources {
        let e = parse_expr(src).unwrap_or_else(|err| panic!("parse `{src}`: {err}"));
        let direct = expr_to_sexpr(&e);
        // ... → text → parse: structurally identical IR ...
        let reparsed = parse_sexpr(&direct.to_text()).unwrap();
        assert_eq!(reparsed, direct, "IR round-trip for `{src}`");
        // ... and equal backend output on both routes.
        assert_eq!(
            realize(&reparsed, &mut TextBackend).unwrap(),
            realize(&direct, &mut TextBackend).unwrap(),
            "TextBackend round-trip for `{src}`"
        );
    }
    // The numeral-reinterpreting backend agrees on both routes too (small
    // literals only: Peano numerals are unary).
    for src in ["f 3", "add 2 (h 0)", r"\x -> x"] {
        let direct = expr_to_sexpr(&parse_expr(src).unwrap());
        let reparsed = parse_sexpr(&direct.to_text()).unwrap();
        assert_eq!(
            realize(&reparsed, &mut PeanoBackend).unwrap(),
            realize(&direct, &mut PeanoBackend).unwrap(),
            "PeanoBackend round-trip for `{src}`"
        );
    }
}

/// Whole modules round-trip through the multi-form text layer.
#[test]
fn module_text_round_trips() {
    let m = parse_module("const x y = x\ncompose f g x = f (g x)\n").unwrap();
    let forms = module_to_sexprs(&m);
    let text = module_to_text(&m);
    assert_eq!(parse_sexprs(&text).unwrap(), forms);
}

/// A third party can produce a module as text with comments and layout of
/// their own choosing — it parses to the same forms.
#[test]
fn third_party_module_text_with_trivia() {
    let text = "\
; a third-party producer wrote this by hand
(define const
  (lambda x (lambda y x))) ; comments and multi-line layout are fine
";
    let forms = parse_sexprs(text).unwrap();
    let m = parse_module("const x y = x\n").unwrap();
    assert_eq!(forms, module_to_sexprs(&m));
    // Round-trip through the canonical printer normalizes the layout.
    assert_eq!(
        forms.iter().map(SExpr::to_text).collect::<Vec<_>>(),
        vec!["(define const (lambda x (lambda y x)))"]
    );
}
