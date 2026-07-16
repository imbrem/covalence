//! A small exact rational over `i128` — enough for Alethe/cvc5 Farkas
//! coefficients, which are tiny in practice. Reduced to lowest terms with a
//! positive denominator on every operation. Overflow (astronomically large
//! coefficients) surfaces as a checked `None` rather than a silent wrap; the
//! replay reports it as `NotSupported` instead of trusting a bogus certificate.

use std::cmp::Ordering;

/// An exact rational `num / den`, always reduced with `den > 0`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Rational {
    num: i128,
    den: i128,
}

fn gcd(a: i128, b: i128) -> i128 {
    let (mut a, mut b) = (a.unsigned_abs(), b.unsigned_abs());
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a as i128
}

impl Rational {
    pub const ZERO: Rational = Rational { num: 0, den: 1 };
    pub const ONE: Rational = Rational { num: 1, den: 1 };

    /// `n / d`, reduced. Returns `None` if `d == 0`.
    pub fn new(num: i128, den: i128) -> Option<Rational> {
        if den == 0 {
            return None;
        }
        let sign = if den < 0 { -1 } else { 1 };
        let g = gcd(num, den).max(1);
        Some(Rational {
            num: sign * (num / g),
            den: (den / g).abs(),
        })
    }

    pub fn from_int(n: i128) -> Rational {
        Rational { num: n, den: 1 }
    }

    pub fn is_zero(&self) -> bool {
        self.num == 0
    }
    pub fn is_integer(&self) -> bool {
        self.den == 1
    }
    /// The numerator (only meaningful together with [`Rational::den`]).
    pub fn num(&self) -> i128 {
        self.num
    }
    pub fn den(&self) -> i128 {
        self.den
    }

    /// Sign: `-1`, `0`, or `1`.
    pub fn signum(&self) -> i32 {
        match self.num.cmp(&0) {
            Ordering::Less => -1,
            Ordering::Equal => 0,
            Ordering::Greater => 1,
        }
    }

    pub fn abs(&self) -> Rational {
        Rational {
            num: self.num.abs(),
            den: self.den,
        }
    }

    pub fn neg(&self) -> Rational {
        Rational {
            num: -self.num,
            den: self.den,
        }
    }

    /// `⌊self⌋` as an integer (mathematical floor, toward −∞).
    pub fn floor(&self) -> i128 {
        self.num.div_euclid(self.den)
    }

    /// Checked add — `None` on `i128` overflow.
    pub fn add(&self, other: &Rational) -> Option<Rational> {
        let num = self
            .num
            .checked_mul(other.den)?
            .checked_add(other.num.checked_mul(self.den)?)?;
        let den = self.den.checked_mul(other.den)?;
        Rational::new(num, den)
    }

    pub fn sub(&self, other: &Rational) -> Option<Rational> {
        self.add(&other.neg())
    }

    /// Checked multiply — `None` on overflow.
    pub fn mul(&self, other: &Rational) -> Option<Rational> {
        Rational::new(
            self.num.checked_mul(other.num)?,
            self.den.checked_mul(other.den)?,
        )
    }
}

impl PartialOrd for Rational {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Rational {
    fn cmp(&self, other: &Self) -> Ordering {
        // den > 0 always, so cross-multiply preserves the inequality.
        // Use i128 widening via i128::checked_mul; on overflow fall back to
        // f64 (only affects pathologically large coefficients).
        match (
            self.num.checked_mul(other.den),
            other.num.checked_mul(self.den),
        ) {
            (Some(l), Some(r)) => l.cmp(&r),
            _ => {
                let l = self.num as f64 / self.den as f64;
                let r = other.num as f64 / other.den as f64;
                l.partial_cmp(&r).unwrap_or(Ordering::Equal)
            }
        }
    }
}

/// Parse an Alethe/SMT-LIB numeral: `1`, `-1`, `1.0`, `-1.5`, `1/4`.
/// (The S-expression forms `(/ 1 4)` and `(- 1)` are unwrapped by the caller
/// before reaching here.)
pub fn parse_numeral(s: &str) -> Option<Rational> {
    let s = s.trim();
    if let Some((n, d)) = s.split_once('/') {
        return Rational::new(n.trim().parse().ok()?, d.trim().parse().ok()?);
    }
    if let Some((int_part, frac_part)) = s.split_once('.') {
        let neg = int_part.starts_with('-');
        let int_abs: i128 = int_part.trim_start_matches('-').parse().ok().or(Some(0))?;
        let frac_digits = frac_part.len() as u32;
        let frac: i128 = if frac_part.is_empty() {
            0
        } else {
            frac_part.parse().ok()?
        };
        let den = 10i128.checked_pow(frac_digits)?;
        let num = int_abs.checked_mul(den)?.checked_add(frac)?;
        return Rational::new(if neg { -num } else { num }, den);
    }
    Some(Rational::from_int(s.parse().ok()?))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reduces_and_signs() {
        assert_eq!(Rational::new(2, 4), Rational::new(1, 2));
        assert_eq!(Rational::new(-1, -2), Rational::new(1, 2));
        assert_eq!(Rational::new(1, -2), Rational::new(-1, 2));
        assert!(Rational::new(1, 0).is_none());
    }

    #[test]
    fn arithmetic() {
        let half = Rational::new(1, 2).unwrap();
        let third = Rational::new(1, 3).unwrap();
        assert_eq!(half.add(&third).unwrap(), Rational::new(5, 6).unwrap());
        assert_eq!(half.mul(&third).unwrap(), Rational::new(1, 6).unwrap());
        assert_eq!(half.sub(&half).unwrap(), Rational::ZERO);
    }

    #[test]
    fn floor_toward_neg_inf() {
        assert_eq!(Rational::new(7, 2).unwrap().floor(), 3);
        assert_eq!(Rational::new(-7, 2).unwrap().floor(), -4);
        assert_eq!(Rational::from_int(5).floor(), 5);
    }

    #[test]
    fn ordering() {
        assert!(Rational::new(1, 3).unwrap() < Rational::new(1, 2).unwrap());
        assert!(Rational::from_int(2) > Rational::new(3, 2).unwrap());
    }

    #[test]
    fn numerals() {
        assert_eq!(parse_numeral("1"), Some(Rational::ONE));
        assert_eq!(parse_numeral("-6"), Some(Rational::from_int(-6)));
        assert_eq!(parse_numeral("1.0"), Some(Rational::ONE));
        assert_eq!(parse_numeral("1/4"), Rational::new(1, 4));
        assert_eq!(parse_numeral("-1.5"), Rational::new(-3, 2));
    }
}
