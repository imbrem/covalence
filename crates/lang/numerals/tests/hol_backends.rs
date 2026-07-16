//! Kernel-backend tests (require the `hol` feature).
//!
//! The flagship: `Symbolic.prove_eq(parse("0xABC"), parse("2748"))` returns a
//! hypothesis-free kernel `Thm` — a real proof that the hex and decimal surface
//! forms denote the same value, built with no new TCB. Plus a small `prove_lt`,
//! and a check that `Builtin` agrees with `Symbolic`.

#![cfg(feature = "hol")]

use covalence_numerals::{Builtin, Lit, LiteralGrammar, NumeralBackend, NumeralGrammar, Symbolic};

/// Parse `src` into a [`Lit`] via the default grammar.
fn parse(src: &str) -> Lit {
    NumeralGrammar.parse(src.as_bytes()).expect("parses").0
}

/// Build a [`Lit`] with a backend.
fn build<B: NumeralBackend>(b: &B, lit: &Lit) -> B::Repr {
    covalence_numerals::build(b, lit)
}

#[test]
fn symbolic_proves_0xabc_eq_2748() {
    let b = Symbolic;
    let hex = build(&b, &parse("0xABC"));
    let dec = build(&b, &parse("2748"));

    let thm = b
        .prove_eq(&hex, &dec)
        .expect("Symbolic should prove 0xABC = 2748");

    // The proof is genuine and hypothesis-free.
    assert!(
        thm.hyps().is_empty(),
        "the 0xABC = 2748 proof must carry no hypotheses"
    );
    // …and it concludes the intended equation between the two literal terms.
    let (lhs, rhs) = thm.concl().as_eq().expect("an equation");
    assert_eq!(lhs, &hex.term);
    assert_eq!(rhs, &dec.term);
    // Both sides are the *same* literal term (the common normal form).
    assert_eq!(hex.term, dec.term, "0xABC and 2748 fold to one Nat literal");
}

#[test]
fn symbolic_proves_lt() {
    let b = Symbolic;
    let a = build(&b, &parse("2748"));
    let c = build(&b, &parse("0xABD")); // 2749

    let thm = b
        .prove_lt(&a, &c)
        .expect("Symbolic should prove 2748 < 2749");
    assert!(
        thm.hyps().is_empty(),
        "the < proof must carry no hypotheses"
    );
}

#[test]
fn symbolic_refuses_false_eq() {
    let b = Symbolic;
    let a = build(&b, &parse("2748"));
    let c = build(&b, &parse("2749"));
    assert!(
        b.prove_eq(&a, &c).is_none(),
        "distinct values must not be provably equal"
    );
}

#[test]
fn builtin_agrees_with_symbolic() {
    let sym = Symbolic;
    let bt = Builtin;

    // prove_eq: both prove 0x10 = 16 hypothesis-free.
    let (s_a, s_b) = (build(&sym, &parse("0x10")), build(&sym, &parse("16")));
    let (b_a, b_b) = (build(&bt, &parse("0x10")), build(&bt, &parse("16")));
    let s_eq = sym.prove_eq(&s_a, &s_b).expect("symbolic eq");
    let b_eq = bt.prove_eq(&b_a, &b_b).expect("builtin eq");
    assert!(s_eq.hyps().is_empty() && b_eq.hyps().is_empty());
    // Same conclusion (both `⊢ 0x10 = 16` on identical literal terms).
    assert_eq!(s_eq.concl(), b_eq.concl());

    // prove_lt: both prove 15 < 16.
    let (s_lo, s_hi) = (build(&sym, &parse("15")), build(&sym, &parse("0x10")));
    let (b_lo, b_hi) = (build(&bt, &parse("15")), build(&bt, &parse("0x10")));
    let s_lt = sym.prove_lt(&s_lo, &s_hi).expect("symbolic lt");
    let b_lt = bt.prove_lt(&b_lo, &b_hi).expect("builtin lt");
    assert_eq!(s_lt.concl(), b_lt.concl());
    assert!(s_lt.hyps().is_empty() && b_lt.hyps().is_empty());
}

#[test]
fn symbolic_proves_decimal_to_rat() {
    // A built decimal `mkDec m k`'s canonical rational is the proved injection
    // lemma's RHS; `prove_to_rat` hands back that hypothesis-free lemma.
    use covalence_numerals::backend::Rung;

    let b = Symbolic;
    let d = build(&b, &parse("1.5")); // mkDec 15 1
    assert_eq!(d.rung, Rung::Decimal);

    let dec = match parse("1.5") {
        Lit::Decimal(dec) => dec,
        _ => unreachable!(),
    };
    let r = b
        .canonical_rat_of_decimal(&dec)
        .expect("canonical rational of a decimal");

    let thm = b
        .prove_to_rat(&d, &r)
        .expect("Symbolic should prove toRat (mkDec 15 1) = its canonical rational");
    assert!(
        thm.hyps().is_empty(),
        "toRat proof must carry no hypotheses"
    );
}
