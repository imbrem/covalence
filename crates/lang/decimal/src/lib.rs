//! Backend-neutral capabilities for exact, terminating base-ten decimals.
//!
//! A decimal denotes `coefficient × 10^exponent`.  This is a mathematical
//! subset of the rationals; it is not an IEEE floating-point value.  Backends
//! may use any representation, and advertise only the capabilities they
//! implement.

use covalence_types::Int;

/// Canonical, exact interchange form for a finite decimal.
///
/// `digits` is non-empty, contains only `0..=9`, and has neither a leading nor
/// trailing zero, except that zero is exactly `digits = [0], exponent = 0`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct CanonicalDecimal {
    negative: bool,
    digits: Vec<u8>,
    exponent: Int,
}

/// Invalid canonical decimal input.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CanonicalDecimalError {
    EmptyCoefficient,
    InvalidDigit(u8),
}

impl CanonicalDecimal {
    /// Normalize `(-1)^negative × digits × 10^exponent`.
    pub fn new(
        mut negative: bool,
        mut digits: Vec<u8>,
        mut exponent: Int,
    ) -> Result<Self, CanonicalDecimalError> {
        if digits.is_empty() {
            return Err(CanonicalDecimalError::EmptyCoefficient);
        }
        if let Some(&digit) = digits.iter().find(|&&digit| digit > 9) {
            return Err(CanonicalDecimalError::InvalidDigit(digit));
        }
        let first_nonzero = digits.iter().position(|digit| *digit != 0);
        let Some(first_nonzero) = first_nonzero else {
            return Ok(Self {
                negative: false,
                digits: vec![0],
                exponent: Int::zero(),
            });
        };
        digits.drain(..first_nonzero);
        while digits.last() == Some(&0) {
            digits.pop();
            exponent += Int::from(1_i64);
        }
        if digits == [0] {
            negative = false;
            exponent = Int::zero();
        }
        Ok(Self {
            negative,
            digits,
            exponent,
        })
    }

    pub fn is_negative(&self) -> bool {
        self.negative
    }

    pub fn digits(&self) -> &[u8] {
        &self.digits
    }

    pub fn exponent(&self) -> &Int {
        &self.exponent
    }
}

/// Constructs decimal values. This is the minimum decimal capability.
pub trait DecimalSyntax {
    type Decimal;
    type Error;

    fn from_canonical(&self, value: &CanonicalDecimal) -> Result<Self::Decimal, Self::Error>;
}

/// Observes a backend value without choosing its internal representation.
pub trait DecimalObservation: DecimalSyntax {
    fn canonical(&self, value: &Self::Decimal) -> Result<CanonicalDecimal, Self::Error>;
}

/// Exact ring operations, closed over finite decimals.
pub trait DecimalArithmetic: DecimalSyntax {
    fn neg(&self, value: Self::Decimal) -> Result<Self::Decimal, Self::Error>;
    fn add(&self, left: Self::Decimal, right: Self::Decimal) -> Result<Self::Decimal, Self::Error>;
    fn mul(&self, left: Self::Decimal, right: Self::Decimal) -> Result<Self::Decimal, Self::Error>;
}

/// Exact decimal order.
pub trait DecimalOrder: DecimalSyntax {
    type Ordering;

    fn compare(
        &self,
        left: &Self::Decimal,
        right: &Self::Decimal,
    ) -> Result<Self::Ordering, Self::Error>;
}

/// Optional proof-bearing normalization accelerator.
pub trait DecimalNormalization: DecimalObservation {
    type Equality;

    fn normalize(
        &self,
        value: Self::Decimal,
    ) -> Result<(Self::Decimal, Self::Equality), Self::Error>;
}

/// Algebraic laws supplied by a backend, independently of computation.
pub trait DecimalLaws: DecimalArithmetic {
    type Law;

    fn additive_commutativity(&self) -> Result<Self::Law, Self::Error>;
    fn additive_associativity(&self) -> Result<Self::Law, Self::Error>;
    fn multiplicative_commutativity(&self) -> Result<Self::Law, Self::Error>;
    fn multiplicative_associativity(&self) -> Result<Self::Law, Self::Error>;
    fn distributivity(&self) -> Result<Self::Law, Self::Error>;
}

/// Structure-preserving map between decimal representations.
pub trait DecimalMorphism<Source: DecimalSyntax, Target: DecimalSyntax> {
    type Evidence;
    type Error;

    fn map(
        &self,
        source: &Source,
        target: &Target,
        value: Source::Decimal,
    ) -> Result<(Target::Decimal, Self::Evidence), Self::Error>;
}

/// Two morphisms with proofs that both round trips are identities.
pub trait DecimalIsomorphism<Left: DecimalSyntax, Right: DecimalSyntax> {
    type Evidence;
    type Error;

    fn forward(
        &self,
        left: &Left,
        right: &Right,
        value: Left::Decimal,
    ) -> Result<Right::Decimal, Self::Error>;
    fn backward(
        &self,
        left: &Left,
        right: &Right,
        value: Right::Decimal,
    ) -> Result<Left::Decimal, Self::Error>;
    fn round_trip_laws(&self) -> Result<Self::Evidence, Self::Error>;
}

/// A representation-preserving embedding whose target may contain more values.
pub trait DecimalRefinement<Source: DecimalSyntax, Target: DecimalSyntax> {
    type Evidence;
    type Error;

    fn embed(
        &self,
        source: &Source,
        target: &Target,
        value: Source::Decimal,
    ) -> Result<(Target::Decimal, Self::Evidence), Self::Error>;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn canonicalization_strips_both_kinds_of_redundant_zero() {
        let value =
            CanonicalDecimal::new(false, vec![0, 0, 1, 2, 0, 0], Int::from(-3_i64)).unwrap();
        assert_eq!(value.digits(), &[1, 2]);
        assert_eq!(value.exponent(), &Int::from(-1_i64));
    }

    #[test]
    fn zero_has_one_canonical_form() {
        let value = CanonicalDecimal::new(true, vec![0, 0, 0], Int::from(999_i64)).unwrap();
        assert!(!value.is_negative());
        assert_eq!(value.digits(), &[0]);
        assert_eq!(value.exponent(), &Int::zero());
    }
}
