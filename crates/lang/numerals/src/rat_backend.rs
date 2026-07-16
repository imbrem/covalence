//! A self-contained, kernel-free [`NumeralBackend`]: evaluate every rung down
//! to a [`Rat`] and decide `=`/`<`/`toRat` by exact rational comparison.
//!
//! This is the reference backend the default (non-`hol`) build ships. It has no
//! proof objects of interest (`type Thm = ()`), but it exercises the whole
//! `parse ⇒ build ⇒ relate` pipeline and pins the intended semantics the kernel
//! backends must agree with.

use covalence_types::{Decimal, Int, Nat, Rat};

use crate::lit::{FloatCert32, NumeralBackend};

/// Exact rational value of a finite IEEE-754 single (a dyadic rational). Any
/// non-finite input (`±∞`, `NaN`) maps to zero — there is no rational for it.
fn f32_to_rat(f: f32) -> Rat {
    if !f.is_finite() {
        return Rat::zero();
    }
    let bits = f.to_bits();
    let sign = if bits >> 31 == 1 { -1i64 } else { 1 };
    let exp = ((bits >> 23) & 0xff) as i64;
    let frac = (bits & 0x7f_ffff) as u64;
    // (mantissa, e) with value = sign * mantissa * 2^e.
    let (mantissa, e) = if exp == 0 {
        // Subnormal: 0.frac * 2^-126 = frac * 2^(-126-23).
        (frac, -149i64)
    } else {
        // Normal: (1.frac) * 2^(exp-127) = (2^23 + frac) * 2^(exp-127-23).
        ((1u64 << 23) | frac, exp - 150)
    };
    let num = Int::from(sign * mantissa as i64);
    let two = Int::from(2i64);
    if e >= 0 {
        let scale = int_pow(&two, e as u32);
        Rat::from(&num * &scale)
    } else {
        let denom = int_pow(&two, (-e) as u32);
        Rat::new(num, denom).expect("2^k is nonzero")
    }
}

/// `base^exp` for an [`Int`] base by repeated squaring (small helper — the
/// crate does not pull in a bignum pow directly).
fn int_pow(base: &Int, exp: u32) -> Int {
    let mut acc = Int::from(1i64);
    let mut b = base.clone();
    let mut e = exp;
    while e > 0 {
        if e & 1 == 1 {
            acc = &acc * &b;
        }
        b = &b * &b;
        e >>= 1;
    }
    acc
}

/// A value built by [`RatBackend`]: exactly the rational it denotes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RatValue(pub Rat);

/// The kernel-free reference backend: builds rationals, proves by comparison.
#[derive(Clone, Copy, Debug, Default)]
pub struct RatBackend;

impl NumeralBackend for RatBackend {
    type Repr = RatValue;
    type Thm = ();

    fn nat(&self, value: &Nat) -> RatValue {
        RatValue(Rat::from(Int::from(value.clone())))
    }
    fn int(&self, value: &Int) -> RatValue {
        RatValue(Rat::from(value.clone()))
    }
    fn decimal(&self, value: &Decimal) -> RatValue {
        RatValue(value.to_rat())
    }
    fn rat(&self, value: &Rat) -> RatValue {
        RatValue(value.clone())
    }
    fn f32_bits(&self, bits: u32) -> RatValue {
        // Exact value of the IEEE-754 single as a dyadic rational
        // `mantissa * 2^exp`, decomposed with `f32::to_bits`. Non-finite maps
        // to zero (there is no rational for it).
        RatValue(f32_to_rat(f32::from_bits(bits)))
    }

    fn prove_eq(&self, a: &RatValue, b: &RatValue) -> Option<()> {
        (a.0 == b.0).then_some(())
    }
    fn prove_lt(&self, a: &RatValue, b: &RatValue) -> Option<()> {
        (a.0 < b.0).then_some(())
    }
    fn prove_to_rat(&self, a: &RatValue, r: &RatValue) -> Option<()> {
        (a.0 == r.0).then_some(())
    }
    fn ground_f32(&self, value: &Decimal) -> FloatCert32<()> {
        // Round the exact decimal to the nearest single and report the bits
        // (no enclosure proof at this tier).
        let r = value.to_rat();
        let num = i128::try_from(&r.numer()).ok();
        let den = i128::try_from(&r.denom()).ok();
        match (num, den) {
            (Some(n), Some(d)) if d != 0 => {
                FloatCert32::Bits(((n as f64 / d as f64) as f32).to_bits())
            }
            _ => FloatCert32::Unproven,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Lit, LiteralGrammar, NumeralGrammar, Style, lower};

    fn parse(s: &str) -> Lit {
        NumeralGrammar.parse(s.as_bytes()).unwrap().0
    }

    #[test]
    fn ladder_tags() {
        assert!(matches!(parse("2748"), Lit::Nat { .. }));
        assert!(matches!(parse("0xABC"), Lit::Nat { .. }));
        assert!(matches!(parse("-42"), Lit::Int { .. }));
        assert!(matches!(parse("3/4"), Lit::Rat(_)));
        assert!(matches!(parse("1.5"), Lit::Decimal(_)));
        assert!(matches!(parse("1.5e3"), Lit::Decimal(_)));
    }

    #[test]
    fn mixed_base_equal_via_backend() {
        let g = NumeralGrammar;
        let b = RatBackend;
        let (hex, _) = lower(&g, &b, b"0xABC").unwrap();
        let (dec, _) = lower(&g, &b, b"2748").unwrap();
        assert!(b.prove_eq(&hex, &dec).is_some());
        assert!(b.prove_lt(&dec, &b.nat(&Nat::from(9999u32))).is_some());
    }

    #[test]
    fn decimal_to_rat() {
        let b = RatBackend;
        let d = b.decimal(&Decimal::from_parts(Int::zero(), &[7, 5], 0)); // 0.75
        let r = b.rat(&Rat::new(Int::from(3i64), Int::from(4i64)).unwrap());
        assert!(b.prove_to_rat(&d, &r).is_some());
    }

    #[test]
    fn deparse_round_trip() {
        let g = NumeralGrammar;
        for s in ["2748", "0xabc", "-42", "3/4", "1.5"] {
            let (lit, _) = g.parse(s.as_bytes()).unwrap();
            let printed = g.deparse(&lit, Style::Native);
            let (lit2, _) = g.parse(&printed).unwrap();
            assert_eq!(lit, lit2, "round-trip failed for {s}");
        }
    }
}
