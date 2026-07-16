//! Finite decimals: rationals whose denominator is a power of ten.
//!
//! A [`Decimal`] is `m / 10^k` for an integer mantissa `m` and a non-negative
//! scale `k`. This is exactly the set of terminating decimal fractions, so it
//! sits strictly between the integers and the rationals in the numeral ladder
//! `Nat ⊂ Int ⊂ Decimal ⊂ Rat ⊂ Real`. [`PosDecimal`] is the positive subset.

use std::cmp::Ordering;
use std::fmt;

use num_bigint::BigInt;

use crate::{Int, Rat};

/// A finite decimal `m / 10^k`.
///
/// Two `Decimal`s that denote the same rational compare equal even when their
/// `(m, k)` representations differ (e.g. `15/10^1` and `150/10^2`); equality
/// and ordering are defined by cross-multiplication, and [`normalize`] picks
/// the canonical representation with the smallest `k`.
///
/// [`normalize`]: Decimal::normalize
#[derive(Clone)]
pub struct Decimal {
    m: Int,
    k: u32,
}

impl Decimal {
    /// Construct `m / 10^k` directly from a mantissa and scale.
    pub fn new(m: Int, k: u32) -> Self {
        Self { m, k }
    }

    /// The mantissa `m`.
    pub fn mantissa(&self) -> &Int {
        &self.m
    }

    /// The scale `k` (the decimal has `k` fractional digits, at most).
    pub fn scale(&self) -> u32 {
        self.k
    }

    /// Build a decimal from an integer part, a fractional-digit part and a
    /// base-ten exponent, mirroring scientific / plain decimal notation.
    ///
    /// The digits of `int` and `frac` are concatenated into a single integer
    /// mantissa `d = int * 10^places ± frac`, and the result denotes
    /// `d * 10^(exp - places)`. This method pushes as much of the exponent as
    /// possible into the mantissa: `k = max(0, places - exp)`, and any surplus
    /// exponent (`exp > places`) multiplies into `m`.
    ///
    /// For example `1.5e3` is `from_parts(1, &[5], 3)`: `d = 15`, `places = 1`,
    /// `exp = 3`, giving `m = 15 * 10^(3-1) = 1500`, `k = 0` — i.e. `1500`, the
    /// true value of `1.5e3`. A plain fraction `0.75` is
    /// `from_parts(0, &[7, 5], 0)`, giving `m = 75, k = 2`.
    ///
    /// (NOTE: the numeral-literals-api spec writes this example as
    /// `Decimal(15000, 0)`, which denotes `15000 ≠ 1.5e3`; that figure is an
    /// arithmetic slip in the spec. We keep `to_rat` sound by producing the
    /// mathematically-correct value. See the crate SKELETONS entry.)
    ///
    /// `frac` is given as the raw decimal digits following the point (each
    /// `0..=9`); its length is the number of fractional places.
    pub fn from_parts(int: Int, frac_digits: &[u8], exp: i64) -> Self {
        let places = frac_digits.len() as i64;
        // Combine int and frac into a single mantissa: int * 10^places ± frac.
        let mut m = &int * &Int::from(10i64).pow(places as u32);
        // Fold the fractional digits (most-significant first).
        let mut frac_val = Int::zero();
        for &d in frac_digits {
            frac_val = &frac_val * &Int::from(10i64) + Int::from(d as i64);
        }
        // A value like -1.5 has int = -1 and denotes -(1.5): the fraction
        // subtracts when the integer part is negative.
        if int.is_negative() {
            m -= frac_val;
        } else {
            m += frac_val;
        }
        // The value so far is m / 10^places; apply the factor 10^exp. When
        // `exp <= places` the exponent shrinks the scale (k = places - exp).
        // When `exp > places` the scale bottoms out at zero and the surplus
        // exponent multiplies into the mantissa.
        let net = places - exp;
        if net >= 0 {
            Decimal { m, k: net as u32 }
        } else {
            let up = (-net) as u32;
            Decimal {
                m: &m * &Int::from(10i64).pow(up),
                k: 0,
            }
        }
    }

    /// The canonical rational this decimal denotes: `m / 10^k`.
    pub fn to_rat(&self) -> Rat {
        let denom = Int::from(10i64).pow(self.k);
        // denom = 10^k is always positive, so `new` cannot fail.
        Rat::new(self.m.clone(), denom).expect("10^k is nonzero")
    }

    /// Return the canonical representation: strip trailing zeros from the
    /// mantissa, reducing `k` accordingly, so that no smaller `k` denotes the
    /// same value.
    pub fn normalize(&self) -> Decimal {
        if self.m.is_zero() {
            return Decimal {
                m: Int::zero(),
                k: 0,
            };
        }
        let ten = Int::from(10i64);
        let mut m = self.m.clone();
        let mut k = self.k;
        while k > 0 {
            let (q, r) = m.div_rem(&ten);
            if r.is_zero() {
                m = q;
                k -= 1;
            } else {
                break;
            }
        }
        Decimal { m, k }
    }
}

impl From<Int> for Decimal {
    fn from(i: Int) -> Self {
        Decimal { m: i, k: 0 }
    }
}

impl fmt::Debug for Decimal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Decimal({} / 10^{})", self.m, self.k)
    }
}

impl fmt::Display for Decimal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.k == 0 {
            return write!(f, "{}", self.m);
        }
        let n = self.normalize();
        write!(f, "{}", n.to_rat())
    }
}

// Equality and ordering by value (cross-multiplication). Since both scales
// are non-negative and the denominators are 10^k, comparing `a.m * 10^b.k`
// with `b.m * 10^a.k` compares the true values.
impl Decimal {
    fn cross(&self, other: &Decimal) -> (BigInt, BigInt) {
        let ten = Int::from(10i64);
        let lhs = &self.m * &ten.pow(other.k);
        let rhs = &other.m * &ten.pow(self.k);
        (lhs.into_inner(), rhs.into_inner())
    }
}

impl PartialEq for Decimal {
    fn eq(&self, other: &Self) -> bool {
        let (l, r) = self.cross(other);
        l == r
    }
}

impl Eq for Decimal {}

impl PartialOrd for Decimal {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Decimal {
    fn cmp(&self, other: &Self) -> Ordering {
        let (l, r) = self.cross(other);
        l.cmp(&r)
    }
}

/// A strictly positive [`Decimal`] (`m > 0`).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct PosDecimal(Decimal);

impl PosDecimal {
    /// Wrap a decimal, returning `None` unless it is strictly positive.
    pub fn new(d: Decimal) -> Option<Self> {
        if d.mantissa().is_positive() {
            Some(Self(d))
        } else {
            None
        }
    }

    /// The underlying decimal.
    pub fn get(&self) -> &Decimal {
        &self.0
    }

    /// Consume into the underlying decimal.
    pub fn into_inner(self) -> Decimal {
        self.0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn from_parts_sci() {
        // 1.5e3 = 1500. d = 15, places = 1, exp = 3 -> m = 15 * 10^(3-1),
        // k = 0. (The spec's `Decimal(15000, 0)` figure is an arithmetic slip;
        // see the crate SKELETONS note — we keep to_rat sound at 1500.)
        let d = Decimal::from_parts(Int::from(1i64), &[5], 3);
        assert_eq!(d.mantissa(), &Int::from(1500i64));
        assert_eq!(d.scale(), 0);
        assert_eq!(d.to_rat(), Rat::from(Int::from(1500i64)));
    }

    #[test]
    fn from_parts_plain_fraction() {
        // 0.75 -> int=0, frac=[7,5], exp=0 -> 75 / 10^2
        let d = Decimal::from_parts(Int::zero(), &[7, 5], 0);
        assert_eq!(
            d.to_rat(),
            Rat::new(Int::from(3i64), Int::from(4i64)).unwrap()
        );
    }

    #[test]
    fn to_rat_three_quarters() {
        // "0.75" as a decimal denotes 3/4
        let d = Decimal::new(Int::from(75i64), 2);
        assert_eq!(
            d.to_rat(),
            Rat::new(Int::from(3i64), Int::from(4i64)).unwrap()
        );
    }

    #[test]
    fn normalize_strips_trailing_zeros() {
        // 1500 / 10^2 == 15 / 10^0
        let d = Decimal::new(Int::from(1500i64), 2);
        let n = d.normalize();
        assert_eq!(n.mantissa(), &Int::from(15i64));
        assert_eq!(n.scale(), 0);
        // value preserved
        assert_eq!(n.to_rat(), d.to_rat());
    }

    #[test]
    fn normalize_partial() {
        // 1200 / 10^3 = 1.2 -> 12 / 10^1
        let d = Decimal::new(Int::from(1200i64), 3);
        let n = d.normalize();
        assert_eq!(n.mantissa(), &Int::from(12i64));
        assert_eq!(n.scale(), 1);
    }

    #[test]
    fn normalize_zero() {
        let d = Decimal::new(Int::zero(), 5);
        let n = d.normalize();
        assert_eq!(n.mantissa(), &Int::zero());
        assert_eq!(n.scale(), 0);
    }

    #[test]
    fn eq_across_scales() {
        // 15/10^1 == 150/10^2
        let a = Decimal::new(Int::from(15i64), 1);
        let b = Decimal::new(Int::from(150i64), 2);
        assert_eq!(a, b);
        // but 15/10^1 != 151/10^2
        let c = Decimal::new(Int::from(151i64), 2);
        assert_ne!(a, c);
    }

    #[test]
    fn ordering() {
        let a = Decimal::new(Int::from(5i64), 1); // 0.5
        let b = Decimal::new(Int::from(75i64), 2); // 0.75
        assert!(a < b);
        let c = Decimal::new(Int::from(-1i64), 0); // -1
        assert!(c < a);
    }

    #[test]
    fn negative_from_parts() {
        // -1.5 -> int=-1, frac=[5], exp=0 -> -15 / 10^1
        let d = Decimal::from_parts(Int::from(-1i64), &[5], 0);
        assert_eq!(
            d.to_rat(),
            Rat::new(Int::from(-3i64), Int::from(2i64)).unwrap()
        );
    }

    #[test]
    fn pos_decimal_rejects_non_positive() {
        assert!(PosDecimal::new(Decimal::new(Int::zero(), 0)).is_none());
        assert!(PosDecimal::new(Decimal::new(Int::from(-1i64), 0)).is_none());
        assert!(PosDecimal::new(Decimal::new(Int::from(1i64), 0)).is_some());
    }
}
