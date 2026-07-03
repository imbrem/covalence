use std::fmt;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Rem, RemAssign, Sub, SubAssign};
use std::str::FromStr;

use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::{Num, One, Pow, Zero};

use crate::{Int, NatConvertError, ParseError};

/// Non-negative arbitrary-precision integer.
///
/// Subtraction saturates to zero. Use [`checked_sub`](Nat::checked_sub) for the
/// fallible path.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Nat(BigUint);

// ---------------------------------------------------------------------------
// Construction
// ---------------------------------------------------------------------------

impl Nat {
    pub fn zero() -> Self {
        Self(BigUint::zero())
    }

    pub fn one() -> Self {
        Self(BigUint::one())
    }

    /// Parse a non-negative integer from `text` in the given `radix`
    /// (2..=36). Returns an error on empty input or invalid digits.
    pub fn from_str_radix(text: &str, radix: u32) -> Result<Self, ParseError> {
        BigUint::from_str_radix(text, radix)
            .map(Self)
            .map_err(ParseError::new)
    }
}

macro_rules! impl_from_unsigned {
    ($($t:ty),*) => {
        $(
            impl From<$t> for Nat {
                fn from(v: $t) -> Self {
                    Self(BigUint::from(v))
                }
            }
        )*
    };
}

impl_from_unsigned!(u8, u16, u32, u64, u128, usize);

// ---------------------------------------------------------------------------
// Predicates
// ---------------------------------------------------------------------------

impl Nat {
    pub fn is_zero(&self) -> bool {
        self.0.is_zero()
    }

    pub fn is_one(&self) -> bool {
        self.0.is_one()
    }

    /// Returns `self` unchanged (a `Nat` is always non-negative).
    pub fn abs(&self) -> Nat {
        self.clone()
    }
}

// ---------------------------------------------------------------------------
// Arithmetic methods
// ---------------------------------------------------------------------------

impl Nat {
    /// Returns `self - other`, or `None` if `other > self`.
    pub fn checked_sub(&self, other: &Nat) -> Option<Nat> {
        if self.0 >= other.0 {
            Some(Nat(&self.0 - &other.0))
        } else {
            None
        }
    }

    pub fn pow(&self, exp: u32) -> Nat {
        Nat(Pow::pow(&self.0, exp))
    }

    pub fn gcd(&self, other: &Nat) -> Nat {
        Nat(self.0.gcd(&other.0))
    }

    pub fn lcm(&self, other: &Nat) -> Nat {
        Nat(self.0.lcm(&other.0))
    }

    pub fn div_rem(&self, other: &Nat) -> (Nat, Nat) {
        let (q, r) = self.0.div_rem(&other.0);
        (Nat(q), Nat(r))
    }
}

// ---------------------------------------------------------------------------
// Byte encoding
// ---------------------------------------------------------------------------

impl Nat {
    pub fn to_bytes_be(&self) -> Vec<u8> {
        self.0.to_bytes_be()
    }

    pub fn to_bytes_le(&self) -> Vec<u8> {
        self.0.to_bytes_le()
    }

    pub fn from_bytes_be(bytes: &[u8]) -> Self {
        Self(BigUint::from_bytes_be(bytes))
    }

    pub fn from_bytes_le(bytes: &[u8]) -> Self {
        Self(BigUint::from_bytes_le(bytes))
    }
}

// ---------------------------------------------------------------------------
// Escape hatch
// ---------------------------------------------------------------------------

impl Nat {
    pub fn as_inner(&self) -> &BigUint {
        &self.0
    }

    pub fn into_inner(self) -> BigUint {
        self.0
    }

    pub fn from_inner(inner: BigUint) -> Self {
        Self(inner)
    }
}

// ---------------------------------------------------------------------------
// Display / Debug / FromStr
// ---------------------------------------------------------------------------

impl fmt::Display for Nat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl fmt::Debug for Nat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Nat({})", self.0)
    }
}

impl FromStr for Nat {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        s.parse::<BigUint>()
            .map(Self)
            .map_err(|e| ParseError::new(e))
    }
}

// ---------------------------------------------------------------------------
// Conversions: Nat ↔ Int
// ---------------------------------------------------------------------------

impl From<Nat> for Int {
    fn from(n: Nat) -> Self {
        Int::from_inner(n.0.into())
    }
}

impl TryFrom<Int> for Nat {
    type Error = NatConvertError;

    fn try_from(i: Int) -> Result<Self, Self::Error> {
        i.into_inner()
            .try_into()
            .map(Nat)
            .map_err(|_| NatConvertError)
    }
}

// ---------------------------------------------------------------------------
// Narrowing conversions to primitives
// ---------------------------------------------------------------------------

macro_rules! impl_try_from_nat {
    ($($t:ty),*) => {
        $(
            impl TryFrom<&Nat> for $t {
                type Error = NatConvertError;

                fn try_from(n: &Nat) -> Result<Self, Self::Error> {
                    <$t>::try_from(&n.0).map_err(|_| NatConvertError)
                }
            }
        )*
    };
}

impl_try_from_nat!(u64, u128, usize);

// ---------------------------------------------------------------------------
// Operator macros
// ---------------------------------------------------------------------------

macro_rules! impl_binop {
    ($trait:ident, $method:ident, $inner_method:ident) => {
        // val op val
        impl $trait for Nat {
            type Output = Nat;
            fn $method(self, rhs: Nat) -> Nat {
                Nat($inner_method(self.0, rhs.0))
            }
        }
        // val op &ref
        impl $trait<&Nat> for Nat {
            type Output = Nat;
            fn $method(self, rhs: &Nat) -> Nat {
                Nat($inner_method(self.0, &rhs.0))
            }
        }
        // &ref op val
        impl $trait<Nat> for &Nat {
            type Output = Nat;
            fn $method(self, rhs: Nat) -> Nat {
                Nat($inner_method(&self.0, rhs.0))
            }
        }
        // &ref op &ref
        impl $trait for &Nat {
            type Output = Nat;
            fn $method(self, rhs: &Nat) -> Nat {
                Nat($inner_method(&self.0, &rhs.0))
            }
        }
    };
}

macro_rules! impl_binop_assign {
    ($trait:ident, $method:ident, $op_trait:ident, $op_method:ident) => {
        impl $trait for Nat {
            fn $method(&mut self, rhs: Nat) {
                self.0.$method(rhs.0);
            }
        }
        impl $trait<&Nat> for Nat {
            fn $method(&mut self, rhs: &Nat) {
                self.0.$method(&rhs.0);
            }
        }
    };
}

// Helper functions to wrap BigUint ops (needed for the macro).
fn nat_add<A: Add<B, Output = BigUint>, B>(a: A, b: B) -> BigUint {
    a + b
}
fn nat_mul<A: Mul<B, Output = BigUint>, B>(a: A, b: B) -> BigUint {
    a * b
}
fn nat_div<A: Div<B, Output = BigUint>, B>(a: A, b: B) -> BigUint {
    a / b
}
fn nat_rem<A: Rem<B, Output = BigUint>, B>(a: A, b: B) -> BigUint {
    a % b
}

impl_binop!(Add, add, nat_add);
impl_binop!(Mul, mul, nat_mul);
impl_binop!(Div, div, nat_div);
impl_binop!(Rem, rem, nat_rem);

impl_binop_assign!(AddAssign, add_assign, Add, add);
impl_binop_assign!(MulAssign, mul_assign, Mul, mul);
impl_binop_assign!(DivAssign, div_assign, Div, div);
impl_binop_assign!(RemAssign, rem_assign, Rem, rem);

// Saturating subtraction — hand-implemented since it's non-standard.

impl Sub for Nat {
    type Output = Nat;
    fn sub(self, rhs: Nat) -> Nat {
        if self.0 >= rhs.0 {
            Nat(self.0 - rhs.0)
        } else {
            Nat::zero()
        }
    }
}

impl Sub<&Nat> for Nat {
    type Output = Nat;
    fn sub(self, rhs: &Nat) -> Nat {
        if self.0 >= rhs.0 {
            Nat(self.0 - &rhs.0)
        } else {
            Nat::zero()
        }
    }
}

impl Sub<Nat> for &Nat {
    type Output = Nat;
    fn sub(self, rhs: Nat) -> Nat {
        if self.0 >= rhs.0 {
            Nat(&self.0 - rhs.0)
        } else {
            Nat::zero()
        }
    }
}

impl Sub for &Nat {
    type Output = Nat;
    fn sub(self, rhs: &Nat) -> Nat {
        if self.0 >= rhs.0 {
            Nat(&self.0 - &rhs.0)
        } else {
            Nat::zero()
        }
    }
}

impl SubAssign for Nat {
    fn sub_assign(&mut self, rhs: Nat) {
        if self.0 >= rhs.0 {
            self.0 -= rhs.0;
        } else {
            self.0 = BigUint::zero();
        }
    }
}

impl SubAssign<&Nat> for Nat {
    fn sub_assign(&mut self, rhs: &Nat) {
        if self.0 >= rhs.0 {
            self.0 -= &rhs.0;
        } else {
            self.0 = BigUint::zero();
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn construction() {
        assert!(Nat::zero().is_zero());
        assert!(Nat::one().is_one());
        assert_eq!(Nat::from(0u64), Nat::zero());
        assert_eq!(Nat::from(1u32), Nat::one());
    }

    #[test]
    fn arithmetic() {
        let a = Nat::from(10u64);
        let b = Nat::from(3u64);
        assert_eq!(&a + &b, Nat::from(13u64));
        assert_eq!(&a * &b, Nat::from(30u64));
        assert_eq!(&a / &b, Nat::from(3u64));
        assert_eq!(&a % &b, Nat::from(1u64));
    }

    #[test]
    fn saturating_sub() {
        let a = Nat::from(5u64);
        let b = Nat::from(8u64);
        assert_eq!(&a - &b, Nat::zero());
        assert_eq!(&b - &a, Nat::from(3u64));
    }

    #[test]
    fn checked_sub() {
        let a = Nat::from(5u64);
        let b = Nat::from(8u64);
        assert!(a.checked_sub(&b).is_none());
        assert_eq!(b.checked_sub(&a), Some(Nat::from(3u64)));
    }

    #[test]
    fn pow_gcd_lcm() {
        let a = Nat::from(2u64);
        assert_eq!(a.pow(10), Nat::from(1024u64));

        let x = Nat::from(12u64);
        let y = Nat::from(8u64);
        assert_eq!(x.gcd(&y), Nat::from(4u64));
        assert_eq!(x.lcm(&y), Nat::from(24u64));
    }

    #[test]
    fn div_rem() {
        let a = Nat::from(17u64);
        let b = Nat::from(5u64);
        let (q, r) = a.div_rem(&b);
        assert_eq!(q, Nat::from(3u64));
        assert_eq!(r, Nat::from(2u64));
    }

    #[test]
    fn from_str_roundtrip() {
        let n: Nat = "123456789012345678901234567890".parse().unwrap();
        assert_eq!(n.to_string(), "123456789012345678901234567890");
    }

    #[test]
    fn from_str_error() {
        assert!("-1".parse::<Nat>().is_err());
        assert!("abc".parse::<Nat>().is_err());
    }

    #[test]
    fn byte_encoding_roundtrip() {
        let n = Nat::from(0xDEAD_BEEFu64);
        assert_eq!(Nat::from_bytes_be(&n.to_bytes_be()), n);
        assert_eq!(Nat::from_bytes_le(&n.to_bytes_le()), n);
    }

    #[test]
    fn assign_ops() {
        let mut n = Nat::from(10u64);
        n += Nat::from(5u64);
        assert_eq!(n, Nat::from(15u64));
        n -= Nat::from(3u64);
        assert_eq!(n, Nat::from(12u64));
        n *= Nat::from(2u64);
        assert_eq!(n, Nat::from(24u64));
        n /= Nat::from(4u64);
        assert_eq!(n, Nat::from(6u64));
        n %= Nat::from(4u64);
        assert_eq!(n, Nat::from(2u64));
    }

    #[test]
    fn debug_format() {
        let n = Nat::from(42u64);
        assert_eq!(format!("{n:?}"), "Nat(42)");
    }
}
