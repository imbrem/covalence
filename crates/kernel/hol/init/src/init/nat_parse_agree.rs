//! `nat_parse_agree` — the **string ⇄ bytes parser agreement** on ASCII
//! digits (stage NP3, deliverable 2).
//!
//! The `string` parser ([`crate::init::nat_parse`]) tests/decodes a character
//! through `char.code c : nat`; the `bytes` parser
//! ([`crate::init::nat_parse_bytes`]) does so through `u8.toNat b : nat`. On
//! the ASCII digit range these two coincide, because a digit *character*
//! `char.mk k` and the digit *byte* `u8_lit k` name the same codepoint `k`:
//!
//! - **[`code_eq_byte_val`]** `⊢ char.code (char.mk k) = u8.toNat (u8_lit k)`
//!   for any Unicode scalar `k` (in particular every ASCII digit) — **the
//!   `char` ⇄ `byte` relation for the digit range**. Both sides reduce to
//!   `k`: `char.code (char.mk k) = k` (the subtype round-trip
//!   [`crate::init::char::code_mk`]) and `u8.toNat (u8_lit k) = k` (the
//!   fixed-width certificate, by `reduce`).
//! - **[`digit_val_agree`]** `⊢ digit_val_dec (char.mk k) =
//!   digit_val_byte_dec (u8_lit k)` for an ASCII digit `k` — the two decimal
//!   digit-value functions agree (both compute `k − 48`).
//!
//! These are exactly the per-element facts the two `nat_of_digits` folds
//! consume, so on corresponding ASCII-digit input the folds compute the same
//! `nat`. The `∀`-quantified whole-string statement (a `map`-fusion induction
//! over the shared fold, keyed on [`code_eq_byte_val`]) is recorded in
//! the generated open-work index.

use covalence_core::{IntTag, Result, Term};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::defs::int_to_nat;

use crate::init::char::{char_lit, code_mk};
use crate::init::ext::{TermExt, ThmExt};

fn lit(k: u64) -> Term {
    covalence_hol_eval::mk_nat(k)
}

/// `u8.toNat (u8_lit k) : nat`.
fn byte_val_lit(k: u8) -> Term {
    Term::app(int_to_nat(IntTag::U8), covalence_hol_eval::mk_u8(k))
}

/// The RHS of an equational theorem.
#[cfg(test)]
fn rhs(thm: &Thm) -> Term {
    thm.concl()
        .as_eq()
        .expect("init::nat_parse_agree: expected an equation")
        .1
        .clone()
}

/// `⊢ u8.toNat (u8_lit k) = k` — the byte's unsigned value is its literal,
/// by the fixed-width certificate (`reduce`). Genuine.
pub fn byte_val_is_lit(k: u8) -> Result<Thm> {
    Thm::refl(byte_val_lit(k))?.rhs_conv(|t| t.reduce())
}

/// `⊢ char.code (char.mk k) = u8.toNat (u8_lit k)` — **the `char` ⇄ `byte`
/// digit relation**: a digit character and the digit byte name the same
/// codepoint `k`. Both sides reduce to `k`. Genuine (hypothesis- and
/// oracle-free) for any ASCII `k` (`k < 0x110000` and not a surrogate).
pub fn code_eq_byte_val(k: u8) -> Result<Thm> {
    let via_char = code_mk(&lit(k as u64))?; // char.code (char.mk k) = k
    let via_byte = byte_val_is_lit(k)?; // u8.toNat (u8_lit k) = k
    via_char.trans(via_byte.sym()?)
}

/// `⊢ digit_val_dec (char.mk k) = digit_val_byte_dec (u8_lit k)` — the two
/// decimal digit-value functions agree on an ASCII digit `k` (both compute
/// `k − 48`). Genuine.
pub fn digit_val_agree(k: u8) -> Result<Thm> {
    // char side: digit_val_dec (char.mk k) = char.code (char.mk k) − 48 = k − 48.
    let char_dv = Term::app(crate::init::nat_parse::digit_val_dec(), char_lit(k as u64));
    let code_rw = code_mk(&lit(k as u64))?; // char.code (char.mk k) = k
    let char_eq = Thm::refl(char_dv)?
        .rhs_conv(|t| t.reduce())? // β: = char.code (char.mk k) − 48
        .rhs_conv(|t| t.rw_all(&code_rw))? // = k − 48
        .rhs_conv(|t| t.reduce())?; // = <literal k−48>
    // byte side: digit_val_byte_dec (u8_lit k) = u8.toNat (u8_lit k) − 48 = k − 48.
    let byte_dv = Term::app(
        crate::init::nat_parse_bytes::digit_val_byte_dec(),
        covalence_hol_eval::mk_u8(k),
    );
    let byte_eq = Thm::refl(byte_dv)?.rhs_conv(|t| t.reduce())?; // = <literal k−48>
    char_eq.trans(byte_eq.sym()?)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn char_code() -> Term {
        covalence_hol_eval::defs::char_code()
    }

    #[test]
    fn code_byte_relation_holds_on_digits() {
        // For every ASCII digit byte, char.code (char.mk k) = u8.toNat (u8_lit k).
        for k in b'0'..=b'9' {
            let thm = code_eq_byte_val(k).unwrap();
            assert!(thm.hyps().is_empty(), "digit relation must be axiom-free");
            let (l, r) = thm.concl().as_eq().unwrap();
            assert_eq!(l, &Term::app(char_code(), char_lit(k as u64)));
            assert_eq!(r, &byte_val_lit(k));
            // both equal the literal k.
            assert_eq!(rhs(&byte_val_is_lit(k).unwrap()), lit(k as u64));
        }
        // The relation also holds for non-digit ASCII (e.g. the '-'/'+' signs
        // and space), since it is really the whole-scalar-range coincidence.
        for k in [b'+', b'-', b' ', b'A', b'z'] {
            assert!(code_eq_byte_val(k).unwrap().hyps().is_empty());
        }
    }

    #[test]
    fn digit_values_agree() {
        // ⊢ digit_val_dec (char.mk k) = digit_val_byte_dec (u8_lit k).
        for k in b'0'..=b'9' {
            let thm = digit_val_agree(k).unwrap();
            assert!(thm.hyps().is_empty());
            let (l, r) = thm.concl().as_eq().unwrap();
            assert_eq!(
                l,
                &Term::app(crate::init::nat_parse::digit_val_dec(), char_lit(k as u64))
            );
            assert_eq!(
                r,
                &Term::app(
                    crate::init::nat_parse_bytes::digit_val_byte_dec(),
                    covalence_hol_eval::mk_u8(k)
                )
            );
            // both sides compute the same value k − 48.
            let shared = Thm::refl(l.clone())
                .unwrap()
                .rhs_conv(|t| t.reduce())
                .unwrap()
                .rhs_conv(|t| t.rw_all(&code_mk(&lit(k as u64)).unwrap()))
                .unwrap()
                .rhs_conv(|t| t.reduce())
                .unwrap();
            assert_eq!(rhs(&shared), lit((k - b'0') as u64));
        }
    }
}
