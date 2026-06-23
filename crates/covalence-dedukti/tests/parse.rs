//! End-to-end parse tests for the `.dk` reader, plus a vendored fixture
//! (`tests/fixtures/nat.dk`) exercising the full surface.

use covalence_dedukti::entry::{Claim, Command, DeclKind, Entry};
use covalence_dedukti::{Term, parse};

/// Parse `src`, asserting success, and return the [`Signature`](covalence_dedukti::Signature).
fn ok(src: &str) -> covalence_dedukti::Signature {
    parse(src).unwrap_or_else(|e| panic!("parse failed for {src:?}: {e}"))
}

/// The first term parsed from a `def t := <term>.` wrapper.
fn term_of(src: &str) -> Term {
    let sig = ok(&format!("def t := {src}."));
    match &sig.entries[0] {
        Entry::Definition(d) => d.body.clone().expect("body"),
        other => panic!("expected a definition, got {other:?}"),
    }
}

#[test]
fn declarations_and_keywords() {
    let sig = ok("Nat : Type. zero : Nat. succ : Nat -> Nat.");
    assert_eq!(sig.declarations().count(), 3);
    let succ = sig.declarations().nth(2).unwrap();
    assert_eq!(succ.name, "succ");
    assert!(matches!(succ.kind, DeclKind::Static));
    // `Nat -> Nat` is a non-dependent product.
    assert!(matches!(succ.ty, Term::Pi { binder: None, .. }));
}

#[test]
fn application_is_left_associated() {
    let t = term_of("f a b c");
    assert_eq!(t.to_string(), "f a b c");
    let (head, args) = t.unfold_app();
    assert_eq!(head.to_string(), "f");
    assert_eq!(args.len(), 3);
}

#[test]
fn arrow_is_right_associated() {
    let t = term_of("a -> b -> c");
    // Right associativity: a -> (b -> c).
    match t {
        Term::Pi { binder: None, codomain, .. } => {
            assert!(matches!(*codomain, Term::Pi { .. }));
        }
        other => panic!("expected a product, got {other:?}"),
    }
    assert_eq!(term_of("a -> b -> c").to_string(), "a -> b -> c");
}

#[test]
fn dependent_product_and_lambda() {
    let t = term_of("a : Type -> a -> a");
    assert!(matches!(t, Term::Pi { binder: Some(_), .. }));
    let lam = term_of("a : Type => x : a => x");
    match lam {
        Term::Abs { binder: Some(b), ty: Some(_), .. } => assert_eq!(b, "a"),
        other => panic!("expected an annotated lambda, got {other:?}"),
    }
    // Round-trips through Display.
    assert_eq!(term_of("a : Type => x : a => x").to_string(), "a : Type => x : a => x");
}

#[test]
fn anonymous_binder_normalised() {
    // `_ => x` and `_ -> b` normalise their binder to None.
    assert!(matches!(term_of("_ => x"), Term::Abs { binder: None, .. }));
    assert!(matches!(term_of("_ : a -> b"), Term::Pi { binder: None, .. }));
}

#[test]
fn qualified_identifiers() {
    let t = term_of("nat.plus zero nat.zero");
    let (head, _) = t.unfold_app();
    match head {
        Term::Ref(r) => {
            assert_eq!(r.module.as_deref(), Some("nat"));
            assert_eq!(r.name, "plus");
        }
        other => panic!("expected a qualified ref, got {other:?}"),
    }
}

#[test]
fn dot_terminator_not_a_qualifier() {
    // The `.` ending `zero` is a terminator (followed by whitespace), not a
    // module qualifier.
    let sig = ok("zero : Nat. succ : Nat.");
    assert_eq!(sig.declarations().count(), 2);
}

#[test]
fn quoted_identifiers() {
    let sig = ok("{|Coq.Init.weird name|} : Type.");
    assert_eq!(sig.declarations().next().unwrap().name, "Coq.Init.weird name");
}

#[test]
fn nested_comments() {
    let sig = ok("(; outer (; inner ;) still outer ;) Nat : Type.");
    assert_eq!(sig.declarations().count(), 1);
}

#[test]
fn rewrite_rules_grouped_and_named() {
    let sig = ok("[ m ] plus zero m --> m {r} [ n ] plus (succ n) m --> succ (plus n m).");
    let rules: Vec<_> = sig.rules().collect();
    assert_eq!(rules.len(), 2);
    assert_eq!(rules[0].context.len(), 1);
    assert_eq!(rules[1].name.as_ref().unwrap().name, "r");
    assert_eq!(rules[1].lhs.to_string(), "plus (succ n) m");
}

#[test]
fn definition_variants() {
    // type-only (bodyless), body-only, and both.
    assert!(matches!(&ok("def f : Nat.").entries[0], Entry::Definition(d) if d.body.is_none()));
    assert!(matches!(&ok("def f := zero.").entries[0], Entry::Definition(d) if d.ty.is_none()));
    let with_params = ok("def f (x : Nat) (y : Nat) : Nat := x.");
    match &with_params.entries[0] {
        Entry::Definition(d) => assert_eq!(d.params.len(), 2),
        other => panic!("{other:?}"),
    }
}

#[test]
fn bodyless_def_without_type_is_rejected() {
    assert!(parse("def f.").is_err());
}

#[test]
fn ac_declarations() {
    let sig = ok("defac gcd [Nat]. defacu lcm [Nat, succ zero].");
    let mut decls = sig.declarations();
    assert!(matches!(decls.next().unwrap().kind, DeclKind::Ac));
    assert!(matches!(decls.next().unwrap().kind, DeclKind::AcU(_)));
}

#[test]
fn injective_and_theorem() {
    let sig = ok("injective f : Nat -> Nat. thm t : Nat := zero.");
    assert!(matches!(sig.declarations().next().unwrap().kind, DeclKind::Injective));
    assert_eq!(sig.theorems().next().unwrap().name, "t");
}

#[test]
fn commands() {
    let sig = ok(
        "#NAME m. #REQUIRE other. #CHECK a : b. #ASSERTNOT a == b. \
         #EVAL[SNF] a. #PRINT \"hi\". #GDT plus. #FUTURE whatever args.",
    );
    assert_eq!(sig.module_name().map(|s| s.as_str()), Some("m"));
    let cmds: Vec<_> = sig.commands().collect();
    assert!(matches!(cmds[1], Command::Require(m) if m == "other"));
    assert!(matches!(cmds[2], Command::Check { assert: false, negated: false, claim: Claim::HasType(..) }));
    assert!(matches!(cmds[3], Command::Check { assert: true, negated: true, claim: Claim::Convertible(..) }));
    assert!(matches!(cmds[4], Command::Eval { config: Some(c), .. } if c == "SNF"));
    assert!(matches!(cmds[5], Command::Print(s) if s == "hi"));
    assert!(matches!(cmds[7], Command::Other(n) if n == "FUTURE"));
}

#[test]
fn fixture_nat_dk() {
    let src = include_str!("fixtures/nat.dk");
    let sig = ok(src);
    assert_eq!(sig.module_name().map(|s| s.as_str()), Some("nat"));
    assert_eq!(sig.declarations().count(), 6); // Nat zero succ plus mult f gcd lcm ... minus defs
    // 3 static (Nat, zero, succ) + injective f + defac gcd + defacu lcm = 6 declarations
    assert_eq!(sig.definitions().count(), 3); // id, plus, mult
    assert_eq!(sig.theorems().count(), 1); // one_plus
    assert_eq!(sig.rules().count(), 4); // plus(2) + mult(2)
    // Spot-check a parsed rule.
    let mult_succ = sig.rules().find(|r| r.name.as_ref().is_some_and(|n| n.name == "mult_succ"));
    assert!(mult_succ.is_some());
}

#[test]
fn dependent_products_in_declarations() {
    // The shape Dedukti exports use heavily: `Con : n:N -> V n -> N -> V (S n).`
    let sig = ok("Con : n : N -> V n -> N -> V (S n).");
    let ty = &sig.declarations().next().unwrap().ty;
    assert_eq!(ty.to_string(), "n : N -> V n -> N -> V (S n)");
    assert!(matches!(ty, Term::Pi { binder: Some(b), .. } if b == "n"));
}

#[test]
fn wildcard_and_brace_patterns_in_rules() {
    // Wildcards `_` in a left-hand side, and a `{ … }` dot/guard pattern.
    let sig = ok("[m] hd _ (Con _ _ m) --> m. [x] g x {S x} --> x.");
    let rules: Vec<_> = sig.rules().collect();
    assert_eq!(rules[0].lhs.to_string(), "hd _ (Con _ _ m)");
    // The brace sub-pattern is preserved as a `Bracket`.
    let (_, args) = rules[1].lhs.unfold_app();
    assert!(matches!(args[1], Term::Bracket(_)));
    // A `{` only opens a bracket inside a rule LHS — an rhs `{name}` after it
    // begins the next rule rather than being absorbed as an argument.
    assert_eq!(rules.len(), 2);
}

#[test]
fn empty_rule_context() {
    let sig = ok("[ ] plus Z y --> y.");
    assert!(sig.rules().next().unwrap().context.is_empty());
}

#[test]
fn numeric_identifiers() {
    // Dedukti symbols may be named with digits (no numeric literals exist).
    let sig = ok("def 65536 := pw2 16.");
    assert_eq!(sig.definitions().next().unwrap().name, "65536");
}

#[test]
fn error_reports_byte_offset() {
    // Missing `.` terminator.
    let err = parse("Nat : Type").unwrap_err();
    assert!(matches!(err, covalence_dedukti::DkError::UnexpectedEof { .. }));
    let err2 = parse("Nat : Type Nat : Type.").unwrap_err();
    // `Nat` (an aterm) cannot be followed by another atom at top level after
    // the type — actually `Type Nat` parses as application; the failure is the
    // second `:`. Just assert it is a positioned error.
    assert!(matches!(err2, covalence_dedukti::DkError::Unexpected { .. }));
}
