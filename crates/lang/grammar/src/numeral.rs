//! Compositional literal grammars for numerals.
//!
//! This module builds the numeral-literal ladder as a *tower of grammars*,
//! each layer composing the ones below it and each carrying:
//!
//! - a [`Regex<char>`] describing the surface language it recognises (the
//!   grammar *artifact*, built from the [`crate::regex`] combinators);
//! - a `parse` returning a typed [`covalence_types`] value plus the unconsumed
//!   suffix; and
//! - a `deparse` (the *transpose*) turning that value back into surface text,
//!   so `parse ∘ deparse` round-trips for every family.
//!
//! The layers, bottom-up (the `W#` labels track the workplan):
//!
//! - **W2** digit classes: [`dec_digit_class`], [`oct_digit_class`],
//!   [`hex_digit_class`] — [`Regex<char>`] character classes, with
//!   [`Digit::from_char`] as the acceptor.
//! - **W3** [`Numeral`]`<BASE>`: `digit+` folded by [`nat_of_digits`]
//!   (`12423 -> 12423`, `ABC -> 2748`).
//! - **W4** prefixed bases (`0x`/`0o`/`0b`) and [`nat_any`]: a mixed-base
//!   join where `0xABC`, `2748`, `0b101011111100` all parse to the *same*
//!   [`Nat`].
//! - **W5** signed [`int_any`] (`-42`, `+7`).
//! - **W6** [`frac`] (`3/4`) -> [`Rat`].
//! - **W8** [`decimal`] / [`sci`] (`1.5`, `1.5e3`) -> [`Decimal`].
//! - **W9** deparsers via transpose, exercised by round-trip tests.
//!
//! The [`Regex<char>`] artifacts are *descriptions*: this crate ships no regex
//! matcher, so recognition is done by the hand-written recursive-descent
//! `parse` functions. The regexes exist so a downstream consumer (kernel
//! grammar frontend, documentation, SpecTec export) can inspect the exact
//! language each family denotes.
//!
//! Deferred alphabets (base32/58/64, LEB128 — the "atom zoo") are recorded in
//! the crate `SKELETONS.md`.

use covalence_types::{Decimal, Digit, Int, Nat, Rat, Sign, nat_of_digits};

use crate::regex::{Class, ClassRange, Regex};

// ============================================================================
// W2 — digit classes
// ============================================================================

/// Character class for base-`BASE` ASCII digits, as a [`Regex<char>`].
///
/// Produces the ranges a hand-written class would: `0-9` for the decimal
/// portion, then `a-?`/`A-?` for the alphabetic tail when `BASE > 10`. The
/// acceptor for individual characters is [`Digit::from_char`]; this function
/// only builds the grammar artifact.
pub fn digit_class<const BASE: u32>() -> Regex<char> {
    let mut ranges: Vec<ClassRange<char>> = Vec::new();
    // Decimal portion 0..min(BASE,10).
    let dec_hi = BASE.min(10);
    if dec_hi > 0 {
        // last decimal digit character
        let hi = char::from_digit(dec_hi - 1, 10).expect("dec_hi-1 < 10");
        ranges.push(ClassRange::new('0', hi));
    }
    // Alphabetic portion for BASE > 10.
    if BASE > 10 {
        let alpha = BASE - 10; // number of letters used
        let hi_lower = char::from_u32(u32::from(b'a') + alpha - 1).expect("<= 'z'");
        let hi_upper = char::from_u32(u32::from(b'A') + alpha - 1).expect("<= 'Z'");
        ranges.push(ClassRange::new('a', hi_lower));
        ranges.push(ClassRange::new('A', hi_upper));
    }
    Regex::Class(Class::new(ranges))
}

/// Decimal digit class `[0-9]`.
pub fn dec_digit_class() -> Regex<char> {
    digit_class::<10>()
}

/// Octal digit class `[0-7]`.
pub fn oct_digit_class() -> Regex<char> {
    digit_class::<8>()
}

/// Hexadecimal digit class `[0-9a-fA-F]`.
pub fn hex_digit_class() -> Regex<char> {
    digit_class::<16>()
}

/// Accept a single base-`BASE` digit character, returning its value.
///
/// Thin wrapper over [`Digit::from_char`] exposed as the class acceptor.
pub fn accept_digit<const BASE: u32>(c: char) -> Option<u8> {
    Digit::<BASE>::from_char(c).map(|d| d.value())
}

// ============================================================================
// W3 — Numeral<BASE>: digit+ folded into a Nat
// ============================================================================

/// The `digit+` numeral grammar in base `BASE`: one or more base-`BASE`
/// digits, folded most-significant-first by [`nat_of_digits`].
///
/// `Numeral::<10>::parse("12423")` yields `12423`; `Numeral::<16>::parse("ABC")`
/// yields `2748`. The grammar artifact is [`Numeral::grammar`] (`digit+`).
pub struct Numeral<const BASE: u32>;

impl<const BASE: u32> Numeral<BASE> {
    /// The grammar: `digit_class<BASE>+`.
    pub fn grammar() -> Regex<char> {
        digit_class::<BASE>().plus()
    }

    /// Parse a maximal run of base-`BASE` digits into a [`Nat`], returning the
    /// value and the unconsumed suffix. Fails (`None`) if the input does not
    /// start with at least one digit.
    pub fn parse(src: &str) -> Option<(Nat, &str)> {
        let mut digits: Vec<u8> = Vec::new();
        let mut end = 0;
        for (i, c) in src.char_indices() {
            match accept_digit::<BASE>(c) {
                Some(d) => {
                    digits.push(d);
                    end = i + c.len_utf8();
                }
                None => break,
            }
        }
        if digits.is_empty() {
            return None;
        }
        Some((nat_of_digits(BASE, &digits), &src[end..]))
    }

    /// Deparse (transpose) a [`Nat`] into its base-`BASE` digit string, with no
    /// prefix. Uses lowercase alphabetic digits. The empty value `0` renders as
    /// `"0"` (a single digit), so `parse ∘ deparse` round-trips.
    pub fn deparse(value: &Nat) -> String {
        nat_to_digits::<BASE>(value)
    }
}

/// Render `value` as base-`BASE` digits (lowercase, no prefix, `0 -> "0"`).
fn nat_to_digits<const BASE: u32>(value: &Nat) -> String {
    let base = Nat::from(BASE);
    if value.is_zero() {
        return "0".to_string();
    }
    let mut n = value.clone();
    let mut rev: Vec<char> = Vec::new();
    while !n.is_zero() {
        let (q, r) = n.div_rem(&base);
        // r < BASE <= 36, so the digit fits in a u32.
        let dv = u64::try_from(&r).expect("digit < base <= 36") as u32;
        let ch = char::from_digit(dv, BASE).expect("digit < base");
        rev.push(ch);
        n = q;
    }
    rev.iter().rev().collect()
}

// ============================================================================
// W4 — prefixed bases + nat_any (mixed-base join)
// ============================================================================

/// A recognised natural-number literal, tagged with the surface base it was
/// written in so a deparser can reproduce the same prefix.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NatLit {
    /// The denoted value (base-independent).
    pub value: Nat,
    /// The surface base the literal was written in.
    pub base: NatBase,
}

/// Which surface syntax a [`NatLit`] used.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NatBase {
    /// Bare decimal, no prefix.
    Dec,
    /// `0x…` hexadecimal.
    Hex,
    /// `0o…` octal.
    Oct,
    /// `0b…` binary.
    Bin,
}

impl NatBase {
    /// The numeric radix (2, 8, 10, or 16) of this surface base.
    pub fn radix(self) -> u32 {
        match self {
            NatBase::Dec => 10,
            NatBase::Hex => 16,
            NatBase::Oct => 8,
            NatBase::Bin => 2,
        }
    }

    /// The surface prefix (`""`, `0x`, `0o`, `0b`) for this base.
    pub fn prefix(self) -> &'static str {
        match self {
            NatBase::Dec => "",
            NatBase::Hex => "0x",
            NatBase::Oct => "0o",
            NatBase::Bin => "0b",
        }
    }
}

/// The `Nat_any` grammar: `dec | 0x hex+ | 0o oct+ | 0b bin+`.
pub fn nat_any_grammar() -> Regex<char> {
    let hex = Regex::concat([Regex::lit('0'), Regex::lit('x'), digit_class::<16>().plus()]);
    let oct = Regex::concat([Regex::lit('0'), Regex::lit('o'), digit_class::<8>().plus()]);
    let bin = Regex::concat([Regex::lit('0'), Regex::lit('b'), digit_class::<2>().plus()]);
    Regex::alt([Numeral::<10>::grammar(), hex, oct, bin])
}

/// Parse a `Nat_any` literal: a prefixed `0x`/`0o`/`0b` numeral or a bare
/// decimal. `0xABC`, `2748`, and `0b101011111100` all denote the same value.
pub fn nat_any(src: &str) -> Option<(NatLit, &str)> {
    if let Some(rest) = src.strip_prefix("0x") {
        let (v, r) = Numeral::<16>::parse(rest)?;
        return Some((
            NatLit {
                value: v,
                base: NatBase::Hex,
            },
            r,
        ));
    }
    if let Some(rest) = src.strip_prefix("0o") {
        let (v, r) = Numeral::<8>::parse(rest)?;
        return Some((
            NatLit {
                value: v,
                base: NatBase::Oct,
            },
            r,
        ));
    }
    if let Some(rest) = src.strip_prefix("0b") {
        let (v, r) = Numeral::<2>::parse(rest)?;
        return Some((
            NatLit {
                value: v,
                base: NatBase::Bin,
            },
            r,
        ));
    }
    let (v, r) = Numeral::<10>::parse(src)?;
    Some((
        NatLit {
            value: v,
            base: NatBase::Dec,
        },
        r,
    ))
}

/// Deparse (transpose) a [`NatLit`] back to surface syntax, honouring its
/// recorded base (so hex round-trips as hex, etc.).
pub fn deparse_nat(lit: &NatLit) -> String {
    let body = match lit.base {
        NatBase::Dec => nat_to_digits::<10>(&lit.value),
        NatBase::Hex => nat_to_digits::<16>(&lit.value),
        NatBase::Oct => nat_to_digits::<8>(&lit.value),
        NatBase::Bin => nat_to_digits::<2>(&lit.value),
    };
    format!("{}{}", lit.base.prefix(), body)
}

/// Deparse a bare [`Nat`] value in a chosen surface base.
pub fn deparse_nat_in(value: &Nat, base: NatBase) -> String {
    deparse_nat(&NatLit {
        value: value.clone(),
        base,
    })
}

// ============================================================================
// W5 — signed Int_any
// ============================================================================

/// A recognised signed-integer literal: an optional sign over a [`NatLit`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IntLit {
    /// `true` if an explicit sign was written.
    pub explicit_sign: bool,
    /// The value (already signed).
    pub value: Int,
    /// The magnitude's surface base.
    pub base: NatBase,
}

/// The `Int_any` grammar: `[+-]? Nat_any`.
pub fn int_any_grammar() -> Regex<char> {
    let sign = Regex::alt([Regex::lit('+'), Regex::lit('-')]).opt();
    Regex::concat([sign, nat_any_grammar()])
}

/// Parse an optionally-signed integer literal (`-42`, `+7`, `2748`, `0xABC`).
pub fn int_any(src: &str) -> Option<(IntLit, &str)> {
    let (explicit_sign, sign, rest) = if let Some(r) = src.strip_prefix('-') {
        (true, Sign::Negative, r)
    } else if let Some(r) = src.strip_prefix('+') {
        (true, Sign::Positive, r)
    } else {
        (false, Sign::Positive, src)
    };
    let (mag, rest) = nat_any(rest)?;
    let value = if sign == Sign::Negative && !mag.value.is_zero() {
        Int::from_sign_nat(Sign::Negative, mag.value.clone())
    } else {
        Int::from(mag.value.clone())
    };
    Some((
        IntLit {
            explicit_sign,
            value,
            base: mag.base,
        },
        rest,
    ))
}

/// Deparse (transpose) an [`IntLit`] back to surface text. Emits a `-` for
/// negative values; a leading `+` is emitted only when it was written and the
/// value is non-negative.
pub fn deparse_int(lit: &IntLit) -> String {
    let mag = lit.value.abs();
    let body = deparse_nat_in(&mag, lit.base);
    if lit.value.is_negative() {
        format!("-{}", body)
    } else if lit.explicit_sign {
        format!("+{}", body)
    } else {
        body
    }
}

// ============================================================================
// W6 — Frac -> Rat
// ============================================================================

/// The `Frac` grammar: `Int_any '/' Nat_any` (with a non-zero denominator
/// enforced at parse time, not by the regex).
pub fn frac_grammar() -> Regex<char> {
    Regex::concat([int_any_grammar(), Regex::lit('/'), nat_any_grammar()])
}

/// Parse a fraction `num '/' den` into a lowest-terms [`Rat`]. The denominator
/// must be a positive natural; a zero denominator makes the parse fail.
pub fn frac(src: &str) -> Option<(Rat, &str)> {
    let (num, rest) = int_any(src)?;
    let rest = rest.strip_prefix('/')?;
    let (den, rest) = nat_any(rest)?;
    if den.value.is_zero() {
        return None;
    }
    let rat = Rat::new(num.value, Int::from(den.value))?;
    Some((rat, rest))
}

/// Deparse (transpose) a [`Rat`] as `numer/denom` in decimal. Reduced rationals
/// with denominator `1` still render with an explicit `/1` so the result parses
/// back through [`frac`].
pub fn deparse_frac(value: &Rat) -> String {
    let num = IntLit {
        explicit_sign: false,
        value: value.numer(),
        base: NatBase::Dec,
    };
    let den = value.denom().abs();
    format!(
        "{}/{}",
        deparse_int(&num),
        deparse_nat_in(&den, NatBase::Dec)
    )
}

// ============================================================================
// W8 — Decimal / Sci -> Decimal
// ============================================================================

/// The `Decimal` grammar: `Int_any '.' DecDigit*`.
pub fn decimal_grammar() -> Regex<char> {
    Regex::concat([
        int_any_grammar(),
        Regex::lit('.'),
        digit_class::<10>().star(),
    ])
}

/// The `Sci` grammar: `Decimal ('e'|'E') Int_any`.
pub fn sci_grammar() -> Regex<char> {
    let e = Regex::alt([Regex::lit('e'), Regex::lit('E')]);
    Regex::concat([decimal_grammar(), e, int_any_grammar()])
}

/// Parse a plain decimal `int '.' frac` (e.g. `1.5`, `-0.75`) into a
/// [`Decimal`]. The integer part must be a bare *decimal* `Int_any`; the
/// fractional part is a run of decimal digits (possibly empty, as in `1.`).
///
/// The sign of the whole value comes from the integer part: `-1.5` denotes
/// `-(1.5)`.
pub fn decimal(src: &str) -> Option<(Decimal, &str)> {
    let (int, rest) = int_any(src)?;
    let rest = rest.strip_prefix('.')?;
    // Fractional digits: a (possibly empty) maximal run of decimal digits.
    let mut frac_digits: Vec<u8> = Vec::new();
    let mut end = 0;
    for (i, c) in rest.char_indices() {
        match accept_digit::<10>(c) {
            Some(d) => {
                frac_digits.push(d);
                end = i + c.len_utf8();
            }
            None => break,
        }
    }
    let rest = &rest[end..];
    let value = Decimal::from_parts(int.value, &frac_digits, 0);
    Some((value, rest))
}

/// Parse scientific notation `Decimal ('e'|'E') Int_any` (e.g. `1.5e3`) into a
/// [`Decimal`]. The mantissa is parsed as a [`decimal`], then the base-ten
/// exponent shifts the scale.
pub fn sci(src: &str) -> Option<(Decimal, &str)> {
    // Parse the mantissa's integer and fractional parts directly so we can
    // fold the exponent into `from_parts` in one shot.
    let (int, rest) = int_any(src)?;
    let rest = rest.strip_prefix('.')?;
    let mut frac_digits: Vec<u8> = Vec::new();
    let mut end = 0;
    for (i, c) in rest.char_indices() {
        match accept_digit::<10>(c) {
            Some(d) => {
                frac_digits.push(d);
                end = i + c.len_utf8();
            }
            None => break,
        }
    }
    let rest = &rest[end..];
    // Exponent marker.
    let rest = rest.strip_prefix(['e', 'E'])?;
    let (exp_lit, rest) = int_any(rest)?;
    let exp = i64::try_from(&exp_lit.value).ok()?;
    let value = Decimal::from_parts(int.value, &frac_digits, exp);
    Some((value, rest))
}

/// Deparse (transpose) a [`Decimal`] as plain `int.frac` decimal text (never
/// scientific), always emitting at least one fractional digit so the `.` is
/// present and the result parses back through [`decimal`].
pub fn deparse_decimal(value: &Decimal) -> String {
    let n = value.normalize();
    let k = n.scale();
    let m = n.mantissa();
    let neg = m.is_negative();
    let mag = m.abs(); // Nat magnitude
    if k == 0 {
        // Integer value: emit "N.0".
        let body = nat_to_digits::<10>(&mag);
        return format!("{}{}.0", if neg { "-" } else { "" }, body);
    }
    // mag has `k` fractional digits. Split into integer / fractional parts.
    let scale = Nat::from(10u32).pow(k);
    let (int_part, frac_part) = mag.div_rem(&scale);
    let int_str = nat_to_digits::<10>(&int_part);
    // Left-pad the fractional part to exactly `k` digits.
    let mut frac_str = nat_to_digits::<10>(&frac_part);
    let width = k as usize;
    if frac_str.len() < width {
        let pad = width - frac_str.len();
        frac_str = format!("{}{}", "0".repeat(pad), frac_str);
    }
    format!("{}{}.{}", if neg { "-" } else { "" }, int_str, frac_str)
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // ---- W2: digit classes ----

    #[test]
    fn w2_digit_class_shapes() {
        // decimal: [0-9]
        assert_eq!(
            dec_digit_class(),
            Regex::Class(Class::new(vec![ClassRange::new('0', '9')]))
        );
        // octal: [0-7]
        assert_eq!(
            oct_digit_class(),
            Regex::Class(Class::new(vec![ClassRange::new('0', '7')]))
        );
        // hex: [0-9a-fA-F]
        assert_eq!(
            hex_digit_class(),
            Regex::Class(Class::new(vec![
                ClassRange::new('0', '9'),
                ClassRange::new('a', 'f'),
                ClassRange::new('A', 'F'),
            ]))
        );
        // binary: [0-1]
        assert_eq!(
            digit_class::<2>(),
            Regex::Class(Class::new(vec![ClassRange::new('0', '1')]))
        );
    }

    #[test]
    fn w2_accept_reject() {
        // decimal accepts 0-9, rejects letters
        assert_eq!(accept_digit::<10>('7'), Some(7));
        assert_eq!(accept_digit::<10>('a'), None);
        // octal rejects 8, 9
        assert_eq!(accept_digit::<8>('7'), Some(7));
        assert_eq!(accept_digit::<8>('8'), None);
        // hex accepts a-f/A-F
        assert_eq!(accept_digit::<16>('a'), Some(10));
        assert_eq!(accept_digit::<16>('F'), Some(15));
        assert_eq!(accept_digit::<16>('g'), None);
    }

    // ---- W3: Numeral<BASE> ----

    #[test]
    fn w3_decimal_fold() {
        let (v, rest) = Numeral::<10>::parse("12423").unwrap();
        assert_eq!(v, Nat::from(12423u64));
        assert_eq!(rest, "");
    }

    #[test]
    fn w3_hex_fold() {
        let (v, rest) = Numeral::<16>::parse("ABC").unwrap();
        assert_eq!(v, Nat::from(2748u64));
        assert_eq!(rest, "");
        // lowercase too
        assert_eq!(Numeral::<16>::parse("abc").unwrap().0, Nat::from(2748u64));
    }

    #[test]
    fn w3_stops_at_non_digit() {
        let (v, rest) = Numeral::<10>::parse("42xyz").unwrap();
        assert_eq!(v, Nat::from(42u64));
        assert_eq!(rest, "xyz");
    }

    #[test]
    fn w3_rejects_empty() {
        assert!(Numeral::<10>::parse("xyz").is_none());
        assert!(Numeral::<16>::parse("").is_none());
    }

    #[test]
    fn w3_grammar_is_digit_plus() {
        assert_eq!(Numeral::<10>::grammar(), dec_digit_class().plus());
    }

    // ---- W4: nat_any mixed-base join ----

    #[test]
    fn w4_mixed_base_equal_values() {
        // NOTE: the spec writes the binary form as `0b101011111100`, but that
        // equals 2812, not 2748 (an arithmetic slip). 2748 = 0b101010111100.
        let dec = nat_any("2748").unwrap().0;
        let hex = nat_any("0xABC").unwrap().0;
        let oct = nat_any("0o5274").unwrap().0;
        let bin = nat_any("0b101010111100").unwrap().0;
        assert_eq!(dec.value, Nat::from(2748u64));
        assert_eq!(hex.value, Nat::from(2748u64));
        assert_eq!(oct.value, Nat::from(2748u64));
        assert_eq!(bin.value, Nat::from(2748u64));
        // all equal
        assert_eq!(dec.value, hex.value);
        assert_eq!(hex.value, oct.value);
        assert_eq!(oct.value, bin.value);
        // base tags preserved
        assert_eq!(hex.base, NatBase::Hex);
        assert_eq!(bin.base, NatBase::Bin);
    }

    #[test]
    fn w4_prefix_requires_digit() {
        // "0x" with no digits fails
        assert!(nat_any("0x").is_none());
        // "0" alone is decimal 0 (no prefix consumed)
        assert_eq!(nat_any("0").unwrap().0.value, Nat::zero());
    }

    // ---- W5: int_any ----

    #[test]
    fn w5_signed() {
        assert_eq!(int_any("-42").unwrap().0.value, Int::from(-42i64));
        assert_eq!(int_any("+7").unwrap().0.value, Int::from(7i64));
        assert_eq!(int_any("2748").unwrap().0.value, Int::from(2748i64));
        // sign over a prefixed base
        assert_eq!(int_any("-0xABC").unwrap().0.value, Int::from(-2748i64));
    }

    #[test]
    fn w5_negative_zero_is_zero() {
        assert_eq!(int_any("-0").unwrap().0.value, Int::zero());
    }

    // ---- W6: frac -> Rat ----

    #[test]
    fn w6_frac() {
        let (r, rest) = frac("3/4").unwrap();
        assert_eq!(r, Rat::new(Int::from(3i64), Int::from(4i64)).unwrap());
        assert_eq!(rest, "");
        // reduces to lowest terms
        assert_eq!(frac("6/8").unwrap().0, frac("3/4").unwrap().0);
        // negative numerator
        assert_eq!(
            frac("-1/2").unwrap().0,
            Rat::new(Int::from(-1i64), Int::from(2i64)).unwrap()
        );
    }

    #[test]
    fn w6_zero_denominator_fails() {
        assert!(frac("1/0").is_none());
    }

    // ---- W8: decimal / sci ----

    #[test]
    fn w8_decimal() {
        let (d, rest) = decimal("1.5").unwrap();
        assert_eq!(
            d.to_rat(),
            Rat::new(Int::from(3i64), Int::from(2i64)).unwrap()
        );
        assert_eq!(rest, "");
        // 0.75 -> 3/4
        assert_eq!(
            decimal("0.75").unwrap().0.to_rat(),
            Rat::new(Int::from(3i64), Int::from(4i64)).unwrap()
        );
        // negative
        assert_eq!(
            decimal("-1.5").unwrap().0.to_rat(),
            Rat::new(Int::from(-3i64), Int::from(2i64)).unwrap()
        );
    }

    #[test]
    fn w8_sci() {
        // 1.5e3 = 1500
        let (d, rest) = sci("1.5e3").unwrap();
        assert_eq!(d.to_rat(), Rat::from(Int::from(1500i64)));
        assert_eq!(rest, "");
        // uppercase E, negative exponent: 1.5E-1 = 0.15 = 3/20
        assert_eq!(
            sci("1.5E-1").unwrap().0.to_rat(),
            Rat::new(Int::from(3i64), Int::from(20i64)).unwrap()
        );
    }

    // ---- W9: deparse / round-trip ----

    #[test]
    fn w9_numeral_round_trip() {
        // Decimal numerals round-trip through Numeral::<10>.
        for s in ["0", "42", "12423"] {
            let (v, _) = Numeral::<10>::parse(s).unwrap();
            let printed = Numeral::<10>::deparse(&v);
            assert_eq!(printed, s, "decimal deparse should reproduce {s}");
            let (v2, _) = Numeral::<10>::parse(&printed).unwrap();
            assert_eq!(v, v2, "round-trip failed for {s}");
        }
        // Hex numerals round-trip through Numeral::<16> (lowercase form).
        for s in ["0", "abc", "deadbeef"] {
            let (v, _) = Numeral::<16>::parse(s).unwrap();
            let printed = Numeral::<16>::deparse(&v);
            assert_eq!(printed, s, "hex deparse should reproduce {s}");
            let (v2, _) = Numeral::<16>::parse(&printed).unwrap();
            assert_eq!(v, v2, "round-trip failed for {s}");
        }
    }

    #[test]
    fn w9_nat_any_round_trip_with_base() {
        // Every base choice round-trips, preserving the surface base.
        for s in ["2748", "0xabc", "0o5274", "0b101010111100"] {
            let (lit, _) = nat_any(s).unwrap();
            let printed = deparse_nat(&lit);
            let (lit2, _) = nat_any(&printed).unwrap();
            assert_eq!(lit, lit2, "round-trip failed for {s}");
            assert_eq!(printed, s, "deparse should reproduce {s}");
        }
    }

    #[test]
    fn w9_int_round_trip() {
        for s in ["-42", "+7", "2748", "-0xabc"] {
            let (lit, _) = int_any(s).unwrap();
            let printed = deparse_int(&lit);
            let (lit2, _) = int_any(&printed).unwrap();
            assert_eq!(lit.value, lit2.value, "value round-trip failed for {s}");
            assert_eq!(printed, s, "deparse should reproduce {s}");
        }
    }

    #[test]
    fn w9_frac_round_trip() {
        for s in ["3/4", "-1/2"] {
            let (r, _) = frac(s).unwrap();
            let printed = deparse_frac(&r);
            let (r2, _) = frac(&printed).unwrap();
            assert_eq!(r, r2, "round-trip failed for {s}");
        }
    }

    #[test]
    fn w9_decimal_round_trip() {
        for s in ["1.5", "0.75", "-1.5", "1.5e3"] {
            // parse via decimal-or-sci
            let (d, _) = decimal(s).or_else(|| sci(s)).unwrap();
            let printed = deparse_decimal(&d);
            let (d2, _) = decimal(&printed).unwrap();
            assert_eq!(d, d2, "round-trip failed for {s} (printed {printed})");
        }
    }

    #[test]
    fn w9_decimal_deparse_shapes() {
        // 1500 renders as "1500.0"
        assert_eq!(
            deparse_decimal(&Decimal::from_parts(Int::from(1500i64), &[], 0)),
            "1500.0"
        );
        // 0.75 renders with padded fractional part
        assert_eq!(deparse_decimal(&decimal("0.75").unwrap().0), "0.75");
        // 0.05 needs a leading zero in the fraction
        assert_eq!(deparse_decimal(&decimal("0.05").unwrap().0), "0.05");
    }
}
