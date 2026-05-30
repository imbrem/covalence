use std::fmt;
use std::ops::{
    Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Rem, RemAssign, Sub, SubAssign,
};
use std::str::FromStr;

use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Pow, Zero};

use crate::{Nat, NatConvertError, ParseError, Sign};

/// Signed arbitrary-precision integer.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Int(BigInt);

// ---------------------------------------------------------------------------
// Construction
// ---------------------------------------------------------------------------

impl Int {
    pub fn zero() -> Self {
        Self(BigInt::zero())
    }

    pub fn one() -> Self {
        Self(BigInt::one())
    }

    /// Construct from a sign and magnitude.
    pub fn from_sign_nat(sign: Sign, mag: Nat) -> Self {
        let s = match sign {
            Sign::Negative => num_bigint::Sign::Minus,
            Sign::Zero => num_bigint::Sign::NoSign,
            Sign::Positive => num_bigint::Sign::Plus,
        };
        Self(BigInt::from_biguint(s, mag.into_inner()))
    }
}

macro_rules! impl_from_signed {
    ($($t:ty),*) => {
        $(
            impl From<$t> for Int {
                fn from(v: $t) -> Self {
                    Self(BigInt::from(v))
                }
            }
        )*
    };
}

impl_from_signed!(i8, i16, i32, i64, i128, isize);

macro_rules! impl_from_unsigned {
    ($($t:ty),*) => {
        $(
            impl From<$t> for Int {
                fn from(v: $t) -> Self {
                    Self(BigInt::from(v))
                }
            }
        )*
    };
}

impl_from_unsigned!(u64, u128, usize);

// ---------------------------------------------------------------------------
// Predicates
// ---------------------------------------------------------------------------

impl Int {
    pub fn is_zero(&self) -> bool {
        self.0.is_zero()
    }

    pub fn is_positive(&self) -> bool {
        self.0 > BigInt::zero()
    }

    pub fn is_negative(&self) -> bool {
        self.0 < BigInt::zero()
    }
}

// ---------------------------------------------------------------------------
// Sign / magnitude
// ---------------------------------------------------------------------------

impl Int {
    pub fn sign(&self) -> Sign {
        match self.0.sign() {
            num_bigint::Sign::Minus => Sign::Negative,
            num_bigint::Sign::NoSign => Sign::Zero,
            num_bigint::Sign::Plus => Sign::Positive,
        }
    }

    /// Returns the absolute value as a [`Nat`].
    pub fn abs(&self) -> Nat {
        let (_sign, mag) = self.0.clone().into_parts();
        Nat::from_inner(mag)
    }
}

// ---------------------------------------------------------------------------
// Arithmetic methods
// ---------------------------------------------------------------------------

impl Int {
    pub fn pow(&self, exp: u32) -> Int {
        Int(Pow::pow(&self.0, exp))
    }

    pub fn gcd(&self, other: &Int) -> Int {
        Int(self.0.gcd(&other.0))
    }

    pub fn div_rem(&self, other: &Int) -> (Int, Int) {
        let (q, r) = self.0.div_rem(&other.0);
        (Int(q), Int(r))
    }
}

// ---------------------------------------------------------------------------
// Byte encoding
// ---------------------------------------------------------------------------

fn sign_to_num(s: Sign) -> num_bigint::Sign {
    match s {
        Sign::Negative => num_bigint::Sign::Minus,
        Sign::Zero => num_bigint::Sign::NoSign,
        Sign::Positive => num_bigint::Sign::Plus,
    }
}

fn sign_from_num(s: num_bigint::Sign) -> Sign {
    match s {
        num_bigint::Sign::Minus => Sign::Negative,
        num_bigint::Sign::NoSign => Sign::Zero,
        num_bigint::Sign::Plus => Sign::Positive,
    }
}

impl Int {
    pub fn to_bytes_be(&self) -> (Sign, Vec<u8>) {
        let (s, bytes) = self.0.to_bytes_be();
        (sign_from_num(s), bytes)
    }

    pub fn to_bytes_le(&self) -> (Sign, Vec<u8>) {
        let (s, bytes) = self.0.to_bytes_le();
        (sign_from_num(s), bytes)
    }

    pub fn from_bytes_be(sign: Sign, bytes: &[u8]) -> Self {
        Self(BigInt::from_bytes_be(sign_to_num(sign), bytes))
    }

    pub fn from_bytes_le(sign: Sign, bytes: &[u8]) -> Self {
        Self(BigInt::from_bytes_le(sign_to_num(sign), bytes))
    }
}

// ---------------------------------------------------------------------------
// Escape hatch
// ---------------------------------------------------------------------------

impl Int {
    pub fn as_inner(&self) -> &BigInt {
        &self.0
    }

    pub fn into_inner(self) -> BigInt {
        self.0
    }

    pub fn from_inner(inner: BigInt) -> Self {
        Self(inner)
    }
}

// ---------------------------------------------------------------------------
// Display / Debug / FromStr
// ---------------------------------------------------------------------------

impl fmt::Display for Int {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl fmt::Debug for Int {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Int({})", self.0)
    }
}

impl FromStr for Int {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        s.parse::<BigInt>()
            .map(Self)
            .map_err(|e| ParseError::new(e))
    }
}

// ---------------------------------------------------------------------------
// Narrowing conversions to primitives
// ---------------------------------------------------------------------------

macro_rules! impl_try_from_int {
    ($($t:ty),*) => {
        $(
            impl TryFrom<&Int> for $t {
                type Error = NatConvertError;

                fn try_from(i: &Int) -> Result<Self, Self::Error> {
                    <$t>::try_from(&i.0).map_err(|_| NatConvertError)
                }
            }
        )*
    };
}

impl_try_from_int!(i64, i128, isize);

// ---------------------------------------------------------------------------
// Neg
// ---------------------------------------------------------------------------

impl Neg for Int {
    type Output = Int;
    fn neg(self) -> Int {
        Int(-self.0)
    }
}

impl Neg for &Int {
    type Output = Int;
    fn neg(self) -> Int {
        Int(-&self.0)
    }
}

// ---------------------------------------------------------------------------
// Operator macros
// ---------------------------------------------------------------------------

macro_rules! impl_binop {
    ($trait:ident, $method:ident, $inner_method:ident) => {
        impl $trait for Int {
            type Output = Int;
            fn $method(self, rhs: Int) -> Int {
                Int($inner_method(self.0, rhs.0))
            }
        }
        impl $trait<&Int> for Int {
            type Output = Int;
            fn $method(self, rhs: &Int) -> Int {
                Int($inner_method(self.0, &rhs.0))
            }
        }
        impl $trait<Int> for &Int {
            type Output = Int;
            fn $method(self, rhs: Int) -> Int {
                Int($inner_method(&self.0, rhs.0))
            }
        }
        impl $trait for &Int {
            type Output = Int;
            fn $method(self, rhs: &Int) -> Int {
                Int($inner_method(&self.0, &rhs.0))
            }
        }
    };
}

macro_rules! impl_binop_assign {
    ($trait:ident, $method:ident) => {
        impl $trait for Int {
            fn $method(&mut self, rhs: Int) {
                self.0.$method(rhs.0);
            }
        }
        impl $trait<&Int> for Int {
            fn $method(&mut self, rhs: &Int) {
                self.0.$method(&rhs.0);
            }
        }
    };
}

fn int_add<A: Add<B, Output = BigInt>, B>(a: A, b: B) -> BigInt {
    a + b
}
fn int_sub<A: Sub<B, Output = BigInt>, B>(a: A, b: B) -> BigInt {
    a - b
}
fn int_mul<A: Mul<B, Output = BigInt>, B>(a: A, b: B) -> BigInt {
    a * b
}
fn int_div<A: Div<B, Output = BigInt>, B>(a: A, b: B) -> BigInt {
    a / b
}
fn int_rem<A: Rem<B, Output = BigInt>, B>(a: A, b: B) -> BigInt {
    a % b
}

impl_binop!(Add, add, int_add);
impl_binop!(Sub, sub, int_sub);
impl_binop!(Mul, mul, int_mul);
impl_binop!(Div, div, int_div);
impl_binop!(Rem, rem, int_rem);

impl_binop_assign!(AddAssign, add_assign);
impl_binop_assign!(SubAssign, sub_assign);
impl_binop_assign!(MulAssign, mul_assign);
impl_binop_assign!(DivAssign, div_assign);
impl_binop_assign!(RemAssign, rem_assign);

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn construction() {
        assert!(Int::zero().is_zero());
        assert!(Int::one().is_positive());
        assert_eq!(Int::from(0i64), Int::zero());
        assert_eq!(Int::from(1u64), Int::one());
    }

    #[test]
    fn from_sign_nat() {
        let n = Nat::from(42u64);
        assert_eq!(
            Int::from_sign_nat(Sign::Positive, n.clone()),
            Int::from(42i64)
        );
        assert_eq!(
            Int::from_sign_nat(Sign::Negative, n.clone()),
            Int::from(-42i64)
        );
        assert_eq!(Int::from_sign_nat(Sign::Zero, Nat::zero()), Int::zero());
    }

    #[test]
    fn arithmetic() {
        let a = Int::from(10i64);
        let b = Int::from(-3i64);
        assert_eq!(&a + &b, Int::from(7i64));
        assert_eq!(&a - &b, Int::from(13i64));
        assert_eq!(&a * &b, Int::from(-30i64));
        assert_eq!(&a / &b, Int::from(-3i64));
        assert_eq!(&a % &b, Int::from(1i64));
    }

    #[test]
    fn negation() {
        let a = Int::from(42i64);
        assert_eq!(-&a, Int::from(-42i64));
        assert_eq!(-(-a), Int::from(42i64));
    }

    #[test]
    fn sign_and_abs() {
        assert_eq!(Int::from(-5i64).sign(), Sign::Negative);
        assert_eq!(Int::zero().sign(), Sign::Zero);
        assert_eq!(Int::from(5i64).sign(), Sign::Positive);

        assert_eq!(Int::from(-7i64).abs(), Nat::from(7u64));
        assert_eq!(Int::zero().abs(), Nat::zero());
    }

    #[test]
    fn pow_and_gcd() {
        let a = Int::from(-2i64);
        assert_eq!(a.pow(3), Int::from(-8i64));
        assert_eq!(a.pow(4), Int::from(16i64));

        let x = Int::from(-12i64);
        let y = Int::from(8i64);
        // gcd returns non-negative
        assert_eq!(x.gcd(&y), Int::from(4i64));
    }

    #[test]
    fn div_rem() {
        let a = Int::from(17i64);
        let b = Int::from(-5i64);
        let (q, r) = a.div_rem(&b);
        assert_eq!(q, Int::from(-3i64));
        assert_eq!(r, Int::from(2i64));
    }

    #[test]
    fn from_str_roundtrip() {
        let i: Int = "-123456789012345678901234567890".parse().unwrap();
        assert_eq!(i.to_string(), "-123456789012345678901234567890");
    }

    #[test]
    fn from_str_error() {
        assert!("abc".parse::<Int>().is_err());
    }

    #[test]
    fn byte_encoding_roundtrip() {
        let i = Int::from(-0xDEAD_BEEFi64);
        let (sign, bytes) = i.to_bytes_be();
        assert_eq!(Int::from_bytes_be(sign, &bytes), i);

        let (sign, bytes) = i.to_bytes_le();
        assert_eq!(Int::from_bytes_le(sign, &bytes), i);
    }

    #[test]
    fn assign_ops() {
        let mut n = Int::from(10i64);
        n += Int::from(5i64);
        assert_eq!(n, Int::from(15i64));
        n -= Int::from(3i64);
        assert_eq!(n, Int::from(12i64));
        n *= Int::from(-2i64);
        assert_eq!(n, Int::from(-24i64));
        n /= Int::from(4i64);
        assert_eq!(n, Int::from(-6i64));
        n %= Int::from(4i64);
        assert_eq!(n, Int::from(-2i64));
    }

    #[test]
    fn debug_format() {
        let i = Int::from(-7i64);
        assert_eq!(format!("{i:?}"), "Int(-7)");
    }
}
