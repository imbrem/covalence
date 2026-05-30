//! Wrapper crate for arbitrary-precision integers.
//!
//! All usage of `num-bigint` should go through this crate.
//!
//! Provides [`Nat`] (non-negative) and [`Int`] (signed) arbitrary-precision
//! integer types, a [`Sign`] enum, and conversion errors.

mod int;
mod nat;

pub use int::Int;
pub use nat::Nat;

use std::fmt;

/// Sign of an integer value.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Sign {
    Negative,
    Zero,
    Positive,
}

/// Error returned when converting a negative [`Int`] to [`Nat`].
#[derive(Clone, Debug, thiserror::Error)]
#[error("cannot convert negative integer to natural number")]
pub struct NatConvertError;

/// Error returned when parsing a [`Nat`] or [`Int`] from a string.
#[derive(Clone, Debug, thiserror::Error)]
#[error("invalid integer literal: {0}")]
pub struct ParseError(String);

impl ParseError {
    pub(crate) fn new(inner: impl fmt::Display) -> Self {
        Self(inner.to_string())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn nat_to_int() {
        let n = Nat::from(42u64);
        let i = Int::from(n.clone());
        assert_eq!(i, Int::from(42i64));
    }

    #[test]
    fn int_to_nat_positive() {
        let i = Int::from(10i64);
        let n = Nat::try_from(i).unwrap();
        assert_eq!(n, Nat::from(10u64));
    }

    #[test]
    fn int_to_nat_zero() {
        let i = Int::zero();
        let n = Nat::try_from(i).unwrap();
        assert!(n.is_zero());
    }

    #[test]
    fn int_to_nat_negative() {
        let i = Int::from(-1i64);
        assert!(Nat::try_from(i).is_err());
    }

    #[test]
    fn nat_to_u64() {
        let n = Nat::from(123u64);
        assert_eq!(u64::try_from(&n).unwrap(), 123);
    }

    #[test]
    fn nat_to_u128() {
        let n = Nat::from(u128::MAX);
        assert_eq!(u128::try_from(&n).unwrap(), u128::MAX);
    }

    #[test]
    fn nat_to_usize() {
        let n = Nat::from(99usize);
        assert_eq!(usize::try_from(&n).unwrap(), 99);
    }

    #[test]
    fn int_to_i64() {
        let i = Int::from(-42i64);
        assert_eq!(i64::try_from(&i).unwrap(), -42);
    }

    #[test]
    fn int_to_i128() {
        let i = Int::from(i128::MIN);
        assert_eq!(i128::try_from(&i).unwrap(), i128::MIN);
    }

    #[test]
    fn int_to_isize() {
        let i = Int::from(-1isize);
        assert_eq!(isize::try_from(&i).unwrap(), -1);
    }

    #[test]
    fn nat_convert_error_display() {
        let err = NatConvertError;
        assert_eq!(
            err.to_string(),
            "cannot convert negative integer to natural number"
        );
    }
}
