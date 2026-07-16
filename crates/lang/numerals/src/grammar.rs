//! The default [`LiteralGrammar`]: a thin wrapper over the compositional
//! numeral parsers/deparsers in [`covalence_grammar`].
//!
//! Parsing tries the *longest* / most-specific rungs first so a prefix never
//! wins over the whole literal: scientific `1.5e3` before decimal `1.5`, both
//! before a fraction `3/4`, and the bare integer / natural forms last. This
//! makes `NumeralGrammar::parse("1.5e3")` land on [`Lit::Decimal`], not on the
//! `Int` `1` with `.5e3` left over.

use covalence_grammar::{
    IntLit, NatBase, NatLit, decimal, deparse_decimal, deparse_frac, deparse_int, deparse_nat,
    frac, int_any, sci,
};
use covalence_types::Nat;

use crate::lit::{Lit, LiteralGrammar, Style};

/// The default numeral grammar: recognises the whole ladder
/// (`Nat`/`Int`/`Decimal`/`Rat`) via [`covalence_grammar`].
#[derive(Clone, Copy, Debug, Default)]
pub struct NumeralGrammar;

impl NumeralGrammar {
    /// Parse a numeral off the front of a `&str` (the byte path decodes UTF-8
    /// first). Exposed directly for callers already holding a `&str`.
    pub fn parse_str<'a>(&self, src: &'a str) -> Option<(Lit, &'a str)> {
        // Most-specific first: sci ⊃ decimal ⊃ frac ⊃ int ⊃ nat. `sci` and
        // `decimal` share a mantissa prefix, so try `sci` first and fall back.
        if let Some((d, rest)) = sci(src) {
            return Some((Lit::Decimal(d), rest));
        }
        if let Some((d, rest)) = decimal(src) {
            return Some((Lit::Decimal(d), rest));
        }
        if let Some((r, rest)) = frac(src) {
            return Some((Lit::Rat(r), rest));
        }
        // A bare integer literal: keep the `Int` tag only when a sign was
        // written, otherwise collapse to the `Nat` rung so `2748` and `0xABC`
        // are naturals (matching the ladder). `int_any` also recognises the
        // unsigned forms, so parse through it and re-tag.
        let (
            IntLit {
                explicit_sign,
                value,
                base,
            },
            rest,
        ) = int_any(src)?;
        if explicit_sign || value.is_negative() {
            Some((
                Lit::Int {
                    value,
                    base,
                    explicit_sign,
                },
                rest,
            ))
        } else {
            // Non-negative, no explicit sign ⇒ a natural.
            let nat = Nat::try_from(value).expect("non-negative Int is a Nat");
            Some((Lit::Nat { value: nat, base }, rest))
        }
    }
}

impl LiteralGrammar for NumeralGrammar {
    fn parse<'a>(&self, src: &'a [u8]) -> Option<(Lit, &'a [u8])> {
        let s = std::str::from_utf8(src).ok()?;
        let (lit, rest) = self.parse_str(s)?;
        // Recover the byte suffix from the consumed prefix length.
        let consumed = s.len() - rest.len();
        Some((lit, &src[consumed..]))
    }

    fn deparse(&self, lit: &Lit, style: Style) -> Vec<u8> {
        let base = |b: NatBase| match style {
            Style::Native => b,
            Style::Decimal => NatBase::Dec,
        };
        let out = match lit {
            Lit::Nat { value, base: b } => deparse_nat(&NatLit {
                value: value.clone(),
                base: base(*b),
            }),
            Lit::Int {
                value,
                base: b,
                explicit_sign,
            } => deparse_int(&IntLit {
                explicit_sign: *explicit_sign,
                value: value.clone(),
                base: base(*b),
            }),
            Lit::Decimal(d) => deparse_decimal(d),
            Lit::Rat(r) => deparse_frac(r),
        };
        out.into_bytes()
    }
}
