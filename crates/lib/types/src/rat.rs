//! Arbitrary-precision rationals.
//!
//! [`Rat`] wraps `num_rational::BigRational`, always kept in lowest terms
//! with a positive denominator. It is the canonical target for the numeral
//! ladder `Nat ⊂ Int ⊂ Decimal ⊂ Rat`.

use std::fmt;

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use crate::Int;

/// Arbitrary-precision rational number, stored in lowest terms with a
/// positive denominator.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Rat(BigRational);

impl Rat {
    pub fn zero() -> Self {
        Self(BigRational::zero())
    }

    pub fn one() -> Self {
        Self(BigRational::one())
    }

    /// Construct `numer / denom`, reducing to lowest terms.
    ///
    /// Returns `None` if `denom` is zero.
    pub fn new(numer: Int, denom: Int) -> Option<Self> {
        if denom.is_zero() {
            return None;
        }
        Some(Self(BigRational::new(
            numer.into_inner(),
            denom.into_inner(),
        )))
    }

    /// The numerator (sign lives here; denominator is always positive).
    pub fn numer(&self) -> Int {
        Int::from_inner(self.0.numer().clone())
    }

    /// The (positive) denominator.
    pub fn denom(&self) -> Int {
        Int::from_inner(self.0.denom().clone())
    }

    pub fn is_zero(&self) -> bool {
        self.0.is_zero()
    }

    pub fn is_positive(&self) -> bool {
        self.0.is_positive()
    }

    pub fn is_negative(&self) -> bool {
        self.0.is_negative()
    }

    pub fn as_inner(&self) -> &BigRational {
        &self.0
    }

    pub fn into_inner(self) -> BigRational {
        self.0
    }

    pub fn from_inner(inner: BigRational) -> Self {
        Self(inner)
    }
}

impl From<Int> for Rat {
    fn from(i: Int) -> Self {
        Self(BigRational::from(i.into_inner()))
    }
}

impl From<BigInt> for Rat {
    fn from(i: BigInt) -> Self {
        Self(BigRational::from(i))
    }
}

impl fmt::Display for Rat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl fmt::Debug for Rat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Rat({})", self.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reduces_to_lowest_terms() {
        let r = Rat::new(Int::from(6i64), Int::from(8i64)).unwrap();
        assert_eq!(r.numer(), Int::from(3i64));
        assert_eq!(r.denom(), Int::from(4i64));
    }

    #[test]
    fn normalises_sign_to_numerator() {
        let r = Rat::new(Int::from(1i64), Int::from(-2i64)).unwrap();
        assert_eq!(r.numer(), Int::from(-1i64));
        assert_eq!(r.denom(), Int::from(2i64));
    }

    #[test]
    fn zero_denominator_rejected() {
        assert!(Rat::new(Int::from(1i64), Int::zero()).is_none());
    }

    #[test]
    fn from_int() {
        let r = Rat::from(Int::from(5i64));
        assert_eq!(r.numer(), Int::from(5i64));
        assert_eq!(r.denom(), Int::one());
    }
}
