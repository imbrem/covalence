//! End-to-end tests for the HOL backend (`hol` feature): parse a Haskell
//! snippet, lower it through the SAME [`lower`]/[`lower_decl`] driver the demo
//! string backends use, and assert the produced carved `sexpr` kernel `Term`
//! equals the hand-built carved term.
//!
//! These prove the full loop *Haskell source → carved `sexpr` kernel data*, and
//! that the shared parser + `Lower` seam supports a genuine kernel-data backend
//! alongside the string ones — the same input, a different lowering.
#![cfg(feature = "hol")]

use covalence_haskell::hol::HolLower;
use covalence_haskell::lower::{lower, lower_decl};
use covalence_haskell::parse::{parse_expr, parse_module};
use covalence_init::Term;
use covalence_init::init::inductive::carved::carved;

/// `atom <bytes>` — the carved `atom` constructor on a byte literal.
fn atom(bytes: &[u8]) -> Term {
    let c = carved().expect("carved sexpr theory builds");
    Term::app(c.atom.clone(), Term::blob(bytes.to_vec()))
}

fn snil() -> Term {
    carved().expect("carved sexpr theory builds").snil.clone()
}

fn scons(h: Term, t: Term) -> Term {
    let c = carved().expect("carved sexpr theory builds");
    Term::app(Term::app(c.scons.clone(), h), t)
}

/// A proper list `(e₁ … eₙ)`.
fn list(items: Vec<Term>) -> Term {
    let mut acc = snil();
    for it in items.into_iter().rev() {
        acc = scons(it, acc);
    }
    acc
}

fn lower_hs(src: &str) -> Term {
    let e = parse_expr(src).expect("parses");
    lower(&e, &mut HolLower).expect("lowers")
}

#[test]
fn lambda_identity() {
    // \x -> x  ⇒  (lambda x x)
    let got = lower_hs(r"\x -> x");
    let want = list(vec![atom(b"lambda"), atom(b"x"), atom(b"x")]);
    assert_eq!(got, want);
}

#[test]
fn nested_application() {
    // f (g x)  ⇒  (f (g x))
    let got = lower_hs("f (g x)");
    let inner = list(vec![atom(b"g"), atom(b"x")]);
    let want = list(vec![atom(b"f"), inner]);
    assert_eq!(got, want);
}

#[test]
fn binop_plus() {
    // 1 + 2  ⇒  (+ 1 2)   — number atoms are the ASCII decimal bytes.
    let got = lower_hs("1 + 2");
    let want = list(vec![atom(b"+"), atom(b"1"), atom(b"2")]);
    assert_eq!(got, want);
}

#[test]
fn nat_literal_is_ascii_digits() {
    // A multi-digit literal lowers to the ASCII byte-run atom `123`.
    let got = lower_hs("123");
    assert_eq!(got, atom(b"123"));
}

#[test]
fn let_binding() {
    // let y = 1 in y  ⇒  (let y 1 y)
    let got = lower_hs("let y = 1 in y");
    let want = list(vec![atom(b"let"), atom(b"y"), atom(b"1"), atom(b"y")]);
    assert_eq!(got, want);
}

#[test]
fn top_level_decl_compose() {
    // compose f g x = f (g x)
    //   ⇒ body desugars to \f -> \g -> \x -> f (g x)
    //   ⇒ (lambda f (lambda g (lambda x (f (g x)))))
    let module = parse_module("compose f g x = f (g x)").expect("parses");
    assert_eq!(module.len(), 1);
    let (name, term) = lower_decl(&module[0], &mut HolLower).expect("lowers");
    assert_eq!(name, "compose");

    let body = list(vec![atom(b"f"), list(vec![atom(b"g"), atom(b"x")])]);
    let inner = list(vec![atom(b"lambda"), atom(b"x"), body]);
    let mid = list(vec![atom(b"lambda"), atom(b"g"), inner]);
    let want = list(vec![atom(b"lambda"), atom(b"f"), mid]);
    assert_eq!(term, want);
}

/// The lowered term really is a carved `sexpr`: its head constructor is the
/// carved `scons`, and `atom`/`snil` are the carved constructors — i.e. we
/// landed kernel data, not a lookalike.
#[test]
fn output_uses_carved_constructors() {
    let c = carved().expect("carved sexpr theory builds");
    // `x` alone lowers to the carved `atom` applied to a blob.
    let x = lower_hs("x");
    assert_eq!(x, Term::app(c.atom.clone(), Term::blob(b"x".to_vec())));
    // The empty-ish structure bottoms out in the carved `snil`.
    let pair = lower_hs("f x"); // (f x) = scons f (scons x snil)
    assert_eq!(
        pair,
        Term::app(
            Term::app(c.scons.clone(), atom(b"f")),
            Term::app(Term::app(c.scons.clone(), atom(b"x")), c.snil.clone()),
        )
    );
}
