//! Base-generic numeral digits.
//!
//! A [`Digit<BASE>`] is a `u8` with the enforced invariant that its value is
//! strictly less than `BASE`. The type-level base makes the common radices
//! ([`OctDigit`], [`DecDigit`], [`HexDigit`]) distinct types, and
//! [`nat_of_digits`] folds a slice of raw digit values into a [`Nat`].

use crate::Nat;

/// A single digit in base `BASE`.
///
/// The wrapped value is guaranteed to be `< BASE` by construction; the only
/// ways to build one ([`Digit::new`] and [`Digit::from_char`]) both reject
/// out-of-range values.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Digit<const BASE: u32>(u8);

/// An octal digit (`0..8`).
pub type OctDigit = Digit<8>;
/// A decimal digit (`0..10`).
pub type DecDigit = Digit<10>;
/// A hexadecimal digit (`0..16`).
pub type HexDigit = Digit<16>;

impl<const BASE: u32> Digit<BASE> {
    /// Wrap a raw digit value, returning `None` if it is not `< BASE`.
    pub fn new(value: u8) -> Option<Self> {
        if (value as u32) < BASE {
            Some(Self(value))
        } else {
            None
        }
    }

    /// Parse a single ASCII digit character (`0-9`, `a-z`, `A-Z`) in base
    /// `BASE`, returning `None` if the character is not a digit or its value
    /// is not `< BASE`.
    pub fn from_char(c: char) -> Option<Self> {
        let value = c.to_digit(BASE)?;
        // `to_digit` already guarantees `value < BASE <= 36`, so the cast is
        // lossless and the invariant holds.
        Some(Self(value as u8))
    }

    /// The numeric value of this digit (always `< BASE`).
    pub fn value(self) -> u8 {
        self.0
    }

    /// Render this digit as a lowercase ASCII character.
    pub fn to_char(self) -> char {
        char::from_digit(self.0 as u32, BASE).expect("digit invariant guarantees value < BASE")
    }
}

impl<const BASE: u32> std::fmt::Debug for Digit<BASE> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Digit<{BASE}>({})", self.0)
    }
}

impl<const BASE: u32> std::fmt::Display for Digit<BASE> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_char())
    }
}

/// Fold a slice of raw digit values (most-significant first) into a [`Nat`]
/// via the left fold `acc |-> acc * base + d`.
///
/// The digits are taken as raw `u8` values; callers are responsible for
/// ensuring each is `< base` (constructed through [`Digit`] this holds).
pub fn nat_of_digits(base: u32, digits: &[u8]) -> Nat {
    let base = Nat::from(base);
    let mut acc = Nat::zero();
    for &d in digits {
        acc = &acc * &base + Nat::from(d);
    }
    acc
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn roundtrip_all_bases() {
        for base in [2u32, 8, 10, 16] {
            for v in 0..base as u8 {
                match base {
                    2 => rt::<2>(v),
                    8 => rt::<8>(v),
                    10 => rt::<10>(v),
                    16 => rt::<16>(v),
                    _ => unreachable!(),
                }
            }
        }
    }

    fn rt<const B: u32>(v: u8) {
        let d = Digit::<B>::new(v).expect("in range");
        assert_eq!(d.value(), v);
        // char round-trip
        let c = d.to_char();
        assert_eq!(Digit::<B>::from_char(c), Some(d));
    }

    #[test]
    fn reject_out_of_range() {
        assert!(Digit::<2>::new(2).is_none());
        assert!(Digit::<8>::new(8).is_none());
        assert!(Digit::<10>::new(10).is_none());
        assert!(Digit::<16>::new(16).is_none());
        // one below the base is always fine
        assert!(Digit::<2>::new(1).is_some());
        assert!(Digit::<16>::new(15).is_some());
    }

    #[test]
    fn from_char_out_of_range() {
        // '9' is not an octal digit
        assert!(OctDigit::from_char('9').is_none());
        // 'a' is not a decimal digit
        assert!(DecDigit::from_char('a').is_none());
        // 'g' is not a hex digit
        assert!(HexDigit::from_char('g').is_none());
        // non-digit char
        assert!(DecDigit::from_char('!').is_none());
    }

    #[test]
    fn hex_case_insensitive() {
        assert_eq!(HexDigit::from_char('a'), HexDigit::new(10));
        assert_eq!(HexDigit::from_char('A'), HexDigit::new(10));
        assert_eq!(HexDigit::from_char('F'), HexDigit::new(15));
    }

    #[test]
    fn to_char_is_lowercase() {
        assert_eq!(HexDigit::new(10).unwrap().to_char(), 'a');
        assert_eq!(HexDigit::new(15).unwrap().to_char(), 'f');
        assert_eq!(DecDigit::new(7).unwrap().to_char(), '7');
    }

    #[test]
    fn fold_decimal() {
        // 12423 in base 10
        assert_eq!(nat_of_digits(10, &[1, 2, 4, 2, 3]), Nat::from(12423u64));
    }

    #[test]
    fn fold_hex_abc() {
        // ABC in base 16 = 2748
        assert_eq!(nat_of_digits(16, &[0xA, 0xB, 0xC]), Nat::from(2748u64));
    }

    #[test]
    fn fold_empty_is_zero() {
        assert_eq!(nat_of_digits(10, &[]), Nat::zero());
    }

    #[test]
    fn fold_matches_from_str_radix() {
        // cross-check the fold against the trusted BigUint parser
        for (s, base) in [("101101", 2u32), ("755", 8), ("deadbeef", 16)] {
            let digits: Vec<u8> = s.chars().map(|c| c.to_digit(base).unwrap() as u8).collect();
            assert_eq!(
                nat_of_digits(base, &digits),
                Nat::from_str_radix(s, base).unwrap()
            );
        }
    }
}
