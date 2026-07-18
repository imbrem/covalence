//! WASM float **value sorts** (`F32`/`F64`) and their arithmetic ops.
//!
//! Bare `f32`/`f64` cannot be expression leaves: `NaN != NaN` breaks reflexivity
//! (and any structural comparison). [`F32`]/[`F64`] store the **raw bits** and
//! compare bitwise, so they are ordinary [`Eq`] leaf sorts — distinct NaN payloads
//! and `±0.0` stay distinct, and canonicalization happens *only* after arithmetic
//! ([`F32::add`] et al.), matching WASM.
//!
//! The `F32Add`/…/`F64Div` ops are [`CanonRule`]s — the **gated** computation seam
//! (reduce `App<F32Add, Val(a, b)>` to `Val(a.add(b))` only where the language admits
//! the op). This is the same seam the planned `Evaluate` trait will generalize to
//! whole expression trees and to equality-decision; see source-local TODO markers.

use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};

use crate::lang::CanonRule;
use crate::op::Op;

// ---- Float wrappers: bitwise equality with canonical NaN ----

macro_rules! float_wrapper {
    ($(#[$m:meta])* $name:ident, $f:ty, $bits:ty) => {
        $(#[$m])*
        #[derive(Clone, Copy)]
        pub struct $name($bits);

        // `add`/`sub`/`mul`/`div` are named WASM ops (canonicalizing NaN results),
        // deliberately NOT the std arithmetic traits — impl'ing `std::ops::Add`
        // would silently hide the canonicalization semantics.
        #[allow(clippy::should_implement_trait)]
        impl $name {
            /// Wrap a float by its **raw bits** — no canonicalization. Storing bits
            /// (not a live float) is robust against any platform re-canonicalizing a
            /// NaN when the value is moved, so a NaN *payload* is preserved exactly;
            /// distinct payloads are distinct leaves.
            pub fn new(x: $f) -> Self {
                $name(x.to_bits())
            }
            /// Wrap raw bits directly (e.g. a specific NaN payload).
            pub fn from_bits(b: $bits) -> Self {
                $name(b)
            }
            /// The wrapped float (decoded from bits).
            pub fn get(self) -> $f {
                <$f>::from_bits(self.0)
            }
            /// The raw bits.
            pub fn to_bits(self) -> $bits {
                self.0
            }
            /// **The sole NaN-canonicalization point.** A WASM *arithmetic* NaN
            /// result collapses to the one canonical NaN; anything else keeps its
            /// exact bits. Used only by the arithmetic ops below.
            fn canon(x: $f) -> Self {
                $name(if x.is_nan() { <$f>::NAN.to_bits() } else { x.to_bits() })
            }
            /// WASM-semantics addition (canonicalizes an arithmetic NaN result).
            pub fn add(self, o: Self) -> Self {
                Self::canon(self.get() + o.get())
            }
            /// WASM-semantics subtraction.
            pub fn sub(self, o: Self) -> Self {
                Self::canon(self.get() - o.get())
            }
            /// WASM-semantics multiplication.
            pub fn mul(self, o: Self) -> Self {
                Self::canon(self.get() * o.get())
            }
            /// WASM-semantics division.
            pub fn div(self, o: Self) -> Self {
                Self::canon(self.get() / o.get())
            }

            /// The sign bit as a mask (`0x8000_0000` for `f32`, etc.).
            const SIGN: $bits = (1 as $bits) << (<$bits>::BITS - 1);

            /// WASM-semantics square root (canonicalizes an arithmetic NaN result,
            /// e.g. `sqrt(-1)`).
            pub fn sqrt(self) -> Self {
                Self::canon(self.get().sqrt())
            }
            /// WASM `min` (`fmin`): NaN if either operand is NaN (canonical);
            /// otherwise the smaller, with `min(+0, -0) = -0`.
            pub fn min(self, o: Self) -> Self {
                let (a, b) = (self.get(), o.get());
                if a.is_nan() || b.is_nan() {
                    Self::canon(<$f>::NAN)
                } else if a == b {
                    // equal value (incl. ±0): the more-negative sign wins ⇒ OR of bits.
                    Self::from_bits(self.0 | o.0)
                } else if a < b {
                    self
                } else {
                    o
                }
            }
            /// WASM `max` (`fmax`): NaN if either operand is NaN (canonical);
            /// otherwise the larger, with `max(+0, -0) = +0`.
            pub fn max(self, o: Self) -> Self {
                let (a, b) = (self.get(), o.get());
                if a.is_nan() || b.is_nan() {
                    Self::canon(<$f>::NAN)
                } else if a == b {
                    // equal value (incl. ±0): the positive sign wins ⇒ AND of bits.
                    Self::from_bits(self.0 & o.0)
                } else if a > b {
                    self
                } else {
                    o
                }
            }
            /// WASM `abs` (`fabs`): clear the sign bit. A pure bit op — NaN payloads
            /// are preserved (no canonicalization), matching WASM.
            pub fn abs(self) -> Self {
                Self::from_bits(self.0 & !Self::SIGN)
            }
            /// WASM `neg`: flip the sign bit. A pure bit op — NaN payloads preserved.
            pub fn neg(self) -> Self {
                Self::from_bits(self.0 ^ Self::SIGN)
            }
            /// WASM `copysign`: this value's magnitude with `o`'s sign. A pure bit op
            /// — NaN payloads preserved.
            pub fn copysign(self, o: Self) -> Self {
                Self::from_bits((self.0 & !Self::SIGN) | (o.0 & Self::SIGN))
            }
            /// WASM `ceil` (round toward +∞; canonicalizes an arithmetic NaN result).
            pub fn ceil(self) -> Self {
                Self::canon(self.get().ceil())
            }
            /// WASM `floor` (round toward −∞).
            pub fn floor(self) -> Self {
                Self::canon(self.get().floor())
            }
            /// WASM `trunc` (round toward zero).
            pub fn trunc(self) -> Self {
                Self::canon(self.get().trunc())
            }
            /// WASM `nearest` (round to nearest, ties to even).
            pub fn nearest(self) -> Self {
                Self::canon(self.get().round_ties_even())
            }

            // Comparisons return `bool` with IEEE 754 ordering (Rust's float
            // comparison operators already implement it): `NaN` compares unordered
            // (false everywhere except `ne`), and `+0 == -0`. These match WASM
            // `eq`/`ne`/`lt`/`gt`/`le`/`ge` exactly.
            /// WASM `eq` (`+0 == -0`, `NaN` never equal).
            pub fn eq(self, o: Self) -> bool {
                self.get() == o.get()
            }
            /// WASM `ne` (true when unordered).
            pub fn ne(self, o: Self) -> bool {
                self.get() != o.get()
            }
            /// WASM `lt`.
            pub fn lt(self, o: Self) -> bool {
                self.get() < o.get()
            }
            /// WASM `gt`.
            pub fn gt(self, o: Self) -> bool {
                self.get() > o.get()
            }
            /// WASM `le`.
            pub fn le(self, o: Self) -> bool {
                self.get() <= o.get()
            }
            /// WASM `ge`.
            pub fn ge(self, o: Self) -> bool {
                self.get() >= o.get()
            }
        }
        // Equality/order/hash are **bitwise** (on `self.0`) — total, reflexive, and
        // decidable over bit patterns, so `$name` is a valid `Eq` leaf sort.
        impl PartialEq for $name {
            fn eq(&self, o: &Self) -> bool {
                self.0 == o.0
            }
        }
        impl Eq for $name {}
        impl PartialOrd for $name {
            fn partial_cmp(&self, o: &Self) -> Option<Ordering> {
                Some(self.cmp(o))
            }
        }
        impl Ord for $name {
            fn cmp(&self, o: &Self) -> Ordering {
                self.0.cmp(&o.0)
            }
        }
        impl Hash for $name {
            fn hash<H: Hasher>(&self, s: &mut H) {
                self.0.hash(s);
            }
        }
        impl fmt::Debug for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(f, "{}({})", stringify!($name), self.get())
            }
        }
    };
}

float_wrapper!(
    /// A 32-bit float stored as **raw bits** with bitwise equality — a valid sort
    /// leaf (unlike bare `f32`, whose `NaN != NaN` breaks `refl`). NaN payloads and
    /// `±0.0` are distinct; canonicalization happens only in arithmetic ([`F32::add`]
    /// et al.), matching WASM.
    F32, f32, u32
);
float_wrapper!(
    /// A 64-bit float stored as raw bits with bitwise equality. NaN payloads and
    /// `±0.0` are distinct; canonicalization happens only in arithmetic.
    F64, f64, u64
);

// Cross-width conversions (`In`/`Out` differ, so they live outside the per-width
// `float_wrapper!` macro), routed through the single `canon` NaN point.
impl F32 {
    /// WASM `f64.promote_f32`: widen to `f64` (canonicalizes an arithmetic NaN).
    pub fn promote(self) -> F64 {
        F64::canon(f64::from(self.get()))
    }
}
impl F64 {
    /// WASM `f32.demote_f64`: narrow to `f32`, rounding (canonicalizes an
    /// arithmetic NaN).
    pub fn demote(self) -> F32 {
        F32::canon(self.get() as f32)
    }
}

// ---- Gated float arithmetic ops (WASM semantics; reduced via `canon`) ----

/// A float arithmetic op that is also its own [`CanonRule`]: `App<Self, Val(a, b)>`
/// canonically equals `Val(a.$m(b))`, sound by literal denotation, gated on the
/// op's `TypeId`.
macro_rules! float_op {
    ($(#[$m:meta])* $op:ident, $flt:ty, $method:ident) => {
        $(#[$m])*
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
        pub struct $op;
        impl Op for $op {
            type In = ($flt, $flt);
            type Out = $flt;
        }
        impl CanonRule for $op {
            fn eval(&self, arg: &($flt, $flt)) -> Option<$flt> {
                // Bind owned `Copy` values so the *inherent* WASM op resolves for
                // `min`/`max` (which would otherwise pick `Ord::min`/`Ord::max` on
                // the `&$flt` receiver).
                let (a, b) = *arg;
                Some(a.$method(b))
            }
        }
    };
}

float_op!(/// `F32` addition op (WASM canonical-NaN semantics).
    F32Add, F32, add);
float_op!(/// `F32` subtraction op.
    F32Sub, F32, sub);
float_op!(/// `F32` multiplication op.
    F32Mul, F32, mul);
float_op!(/// `F32` division op.
    F32Div, F32, div);
float_op!(/// `F64` addition op.
    F64Add, F64, add);
float_op!(/// `F64` subtraction op.
    F64Sub, F64, sub);
float_op!(/// `F64` multiplication op.
    F64Mul, F64, mul);
float_op!(/// `F64` division op.
    F64Div, F64, div);

float_op!(/// `F32` `min` op (`fmin`; canonical NaN, `min(+0, -0) = -0`).
    F32Min, F32, min);
float_op!(/// `F32` `max` op (`fmax`; canonical NaN, `max(+0, -0) = +0`).
    F32Max, F32, max);
float_op!(/// `F32` `copysign` op.
    F32Copysign, F32, copysign);
float_op!(/// `F64` `min` op.
    F64Min, F64, min);
float_op!(/// `F64` `max` op.
    F64Max, F64, max);
float_op!(/// `F64` `copysign` op.
    F64Copysign, F64, copysign);

// ---- Unary float→float ops (`sqrt`/`abs`/`neg`/rounding) ----

/// A unary float op that is its own [`CanonRule`]: `App<Self, Val(a)>` canonically
/// equals `Val(a.$method())`.
macro_rules! float_unop {
    ($(#[$m:meta])* $op:ident, $flt:ty, $method:ident) => {
        $(#[$m])*
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
        pub struct $op;
        impl Op for $op {
            type In = $flt;
            type Out = $flt;
        }
        impl CanonRule for $op {
            fn eval(&self, a: &$flt) -> Option<$flt> {
                Some(a.$method())
            }
        }
    };
}

float_unop!(/// `F32` `sqrt` op (canonical NaN).
    F32Sqrt, F32, sqrt);
float_unop!(/// `F32` `abs` op (bit op — NaN payload preserved).
    F32Abs, F32, abs);
float_unop!(/// `F32` `neg` op (bit op — NaN payload preserved).
    F32Neg, F32, neg);
float_unop!(/// `F32` `ceil` op.
    F32Ceil, F32, ceil);
float_unop!(/// `F32` `floor` op.
    F32Floor, F32, floor);
float_unop!(/// `F32` `trunc` op.
    F32Trunc, F32, trunc);
float_unop!(/// `F32` `nearest` op (round to nearest, ties to even).
    F32Nearest, F32, nearest);
float_unop!(/// `F64` `sqrt` op.
    F64Sqrt, F64, sqrt);
float_unop!(/// `F64` `abs` op.
    F64Abs, F64, abs);
float_unop!(/// `F64` `neg` op.
    F64Neg, F64, neg);
float_unop!(/// `F64` `ceil` op.
    F64Ceil, F64, ceil);
float_unop!(/// `F64` `floor` op.
    F64Floor, F64, floor);
float_unop!(/// `F64` `trunc` op.
    F64Trunc, F64, trunc);
float_unop!(/// `F64` `nearest` op.
    F64Nearest, F64, nearest);

// ---- Float comparison ops (`Out = bool`, IEEE 754 ordering) ----

/// A float comparison op (`Out = bool`) that is its own [`CanonRule`].
macro_rules! float_cmp {
    ($(#[$m:meta])* $op:ident, $flt:ty, $method:ident) => {
        $(#[$m])*
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
        pub struct $op;
        impl Op for $op {
            type In = ($flt, $flt);
            type Out = bool;
        }
        impl CanonRule for $op {
            fn eval(&self, arg: &($flt, $flt)) -> Option<bool> {
                // Bind owned `Copy` values so the *inherent* WASM comparison method
                // resolves (not the structural `PartialEq`/`PartialOrd` trait method,
                // which a `&$flt` receiver would prefer).
                let (a, b) = *arg;
                Some(a.$method(b))
            }
        }
    };
}

float_cmp!(/// `F32` `eq` op (`+0 == -0`, `NaN` never equal).
    F32Eq, F32, eq);
float_cmp!(/// `F32` `ne` op (true when unordered).
    F32Ne, F32, ne);
float_cmp!(/// `F32` `lt` op.
    F32Lt, F32, lt);
float_cmp!(/// `F32` `gt` op.
    F32Gt, F32, gt);
float_cmp!(/// `F32` `le` op.
    F32Le, F32, le);
float_cmp!(/// `F32` `ge` op.
    F32Ge, F32, ge);
float_cmp!(/// `F64` `eq` op.
    F64Eq, F64, eq);
float_cmp!(/// `F64` `ne` op.
    F64Ne, F64, ne);
float_cmp!(/// `F64` `lt` op.
    F64Lt, F64, lt);
float_cmp!(/// `F64` `gt` op.
    F64Gt, F64, gt);
float_cmp!(/// `F64` `le` op.
    F64Le, F64, le);
float_cmp!(/// `F64` `ge` op.
    F64Ge, F64, ge);

// ---- Conversions: promote/demote, int↔float, reinterpret ----

/// A unary conversion op whose `In`/`Out` sorts may differ, given by an explicit
/// body. Its own [`CanonRule`]: `App<Self, Val(a)>` canonically equals
/// `Val($body)`. Every float-producing body routes through `F32/F64::canon` (or is
/// a raw bit move), keeping the single NaN-canonicalization point; int-producing
/// bodies use Rust's saturating float→int `as` cast (= WASM `trunc_sat`).
macro_rules! float_cvt {
    ($(#[$m:meta])* $op:ident, $in:ty => $out:ty, |$v:pat_param| $body:expr) => {
        $(#[$m])*
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
        pub struct $op;
        impl Op for $op {
            type In = $in;
            type Out = $out;
        }
        impl CanonRule for $op {
            fn eval(&self, $v: &$in) -> Option<$out> {
                Some($body)
            }
        }
    };
}

float_cvt!(/// WASM `f64.promote_f32`.
    F64PromoteF32, F32 => F64, |v| v.promote());
float_cvt!(/// WASM `f32.demote_f64`.
    F32DemoteF64, F64 => F32, |v| v.demote());

float_cvt!(/// WASM `f32.reinterpret_i32` (raw bits `i32`→`f32`; NaN bits preserved).
    F32ReinterpretI32, i32 => F32, |i| F32::from_bits(*i as u32));
float_cvt!(/// WASM `i32.reinterpret_f32` (raw bits `f32`→`i32`; NaN bits preserved).
    I32ReinterpretF32, F32 => i32, |v| v.to_bits() as i32);
float_cvt!(/// WASM `f64.reinterpret_i64`.
    F64ReinterpretI64, i64 => F64, |i| F64::from_bits(*i as u64));
float_cvt!(/// WASM `i64.reinterpret_f64`.
    I64ReinterpretF64, F64 => i64, |v| v.to_bits() as i64);

// float→int, saturating (WASM `trunc_sat`). Rust's float→int `as` cast saturates
// (NaN→0, out-of-range clamps to the type's min/max), matching `trunc_sat`.
float_cvt!(/// WASM `i32.trunc_sat_f32_s`.
    I32TruncSatF32, F32 => i32, |v| v.get() as i32);
float_cvt!(/// WASM `i32.trunc_sat_f32_u`.
    U32TruncSatF32, F32 => u32, |v| v.get() as u32);
float_cvt!(/// WASM `i64.trunc_sat_f32_s`.
    I64TruncSatF32, F32 => i64, |v| v.get() as i64);
float_cvt!(/// WASM `i64.trunc_sat_f32_u`.
    U64TruncSatF32, F32 => u64, |v| v.get() as u64);
float_cvt!(/// WASM `i32.trunc_sat_f64_s`.
    I32TruncSatF64, F64 => i32, |v| v.get() as i32);
float_cvt!(/// WASM `i32.trunc_sat_f64_u`.
    U32TruncSatF64, F64 => u32, |v| v.get() as u32);
float_cvt!(/// WASM `i64.trunc_sat_f64_s`.
    I64TruncSatF64, F64 => i64, |v| v.get() as i64);
float_cvt!(/// WASM `i64.trunc_sat_f64_u`.
    U64TruncSatF64, F64 => u64, |v| v.get() as u64);

// int→float (WASM `convert`; rounds to nearest-even, never produces NaN).
float_cvt!(/// WASM `f32.convert_i32_s`.
    F32ConvertI32, i32 => F32, |i| F32::new(*i as f32));
float_cvt!(/// WASM `f32.convert_i32_u`.
    F32ConvertU32, u32 => F32, |i| F32::new(*i as f32));
float_cvt!(/// WASM `f32.convert_i64_s`.
    F32ConvertI64, i64 => F32, |i| F32::new(*i as f32));
float_cvt!(/// WASM `f32.convert_i64_u`.
    F32ConvertU64, u64 => F32, |i| F32::new(*i as f32));
float_cvt!(/// WASM `f64.convert_i32_s`.
    F64ConvertI32, i32 => F64, |i| F64::new(f64::from(*i)));
float_cvt!(/// WASM `f64.convert_i32_u`.
    F64ConvertU32, u32 => F64, |i| F64::new(f64::from(*i)));
float_cvt!(/// WASM `f64.convert_i64_s`.
    F64ConvertI64, i64 => F64, |i| F64::new(*i as f64));
float_cvt!(/// WASM `f64.convert_i64_u`.
    F64ConvertU64, u64 => F64, |i| F64::new(*i as f64));

#[cfg(test)]
mod tests {
    use super::*;

    // The canonical NaN this profile collapses arithmetic NaNs to.
    fn canon_nan32() -> u32 {
        f32::NAN.to_bits()
    }
    fn canon_nan64() -> u64 {
        f64::NAN.to_bits()
    }

    #[test]
    fn arithmetic_canonicalizes_nan() {
        // sqrt of a negative is an arithmetic NaN ⇒ collapses to the canonical NaN.
        assert_eq!(F32::new(-1.0).sqrt().to_bits(), canon_nan32());
        assert_eq!(F64::new(-1.0).sqrt().to_bits(), canon_nan64());
        // 0/0 too (via div).
        assert_eq!(F32::new(0.0).div(F32::new(0.0)).to_bits(), canon_nan32());
    }

    #[test]
    fn abs_neg_copysign_preserve_nan_payload() {
        // A non-canonical NaN payload must survive abs/neg/copysign unchanged (they
        // are bit ops, NOT the canonicalization point).
        let payload = F32::from_bits(0x7fc0_1234); // a quiet NaN with a payload
        assert!(payload.get().is_nan());
        assert_eq!(payload.abs().to_bits(), 0x7fc0_1234 & 0x7fff_ffff);
        assert_eq!(payload.neg().to_bits(), 0x7fc0_1234 ^ 0x8000_0000);
        // copysign moves only the sign bit, leaving the payload intact.
        assert_eq!(
            payload.copysign(F32::new(-1.0)).to_bits(),
            0x7fc0_1234 | 0x8000_0000
        );
    }

    #[test]
    fn signed_zero() {
        // neg/abs on ±0.
        assert_eq!(F32::new(0.0).neg().to_bits(), F32::new(-0.0).to_bits());
        assert_eq!(F32::new(-0.0).abs().to_bits(), F32::new(0.0).to_bits());
        // min(+0, -0) = -0 ; max(+0, -0) = +0 (order-independent).
        assert_eq!(
            F32::new(0.0).min(F32::new(-0.0)).to_bits(),
            F32::new(-0.0).to_bits()
        );
        assert_eq!(
            F32::new(-0.0).min(F32::new(0.0)).to_bits(),
            F32::new(-0.0).to_bits()
        );
        assert_eq!(
            F32::new(0.0).max(F32::new(-0.0)).to_bits(),
            F32::new(0.0).to_bits()
        );
        // eq: +0 == -0.
        assert!(F32::new(0.0).eq(F32::new(-0.0)));
    }

    #[test]
    fn min_max_with_nan() {
        // Either operand NaN ⇒ canonical NaN, both orders (unlike Rust's f32::min).
        let n = F32::new(f32::NAN);
        assert_eq!(n.min(F32::new(1.0)).to_bits(), canon_nan32());
        assert_eq!(F32::new(1.0).min(n).to_bits(), canon_nan32());
        assert_eq!(n.max(F32::new(1.0)).to_bits(), canon_nan32());
        assert_eq!(F32::new(1.0).max(n).to_bits(), canon_nan32());
        // Ordinary values.
        assert_eq!(F32::new(1.0).min(F32::new(2.0)), F32::new(1.0));
        assert_eq!(F32::new(1.0).max(F32::new(2.0)), F32::new(2.0));
    }

    #[test]
    fn comparisons_ieee() {
        let n = F32::new(f32::NAN);
        // NaN is unordered: false everywhere except `ne`.
        assert!(!n.eq(n));
        assert!(n.ne(n));
        assert!(!n.lt(F32::new(0.0)));
        assert!(!n.gt(F32::new(0.0)));
        assert!(!n.le(F32::new(0.0)));
        assert!(!n.ge(F32::new(0.0)));
        assert!(F32::new(1.0).lt(F32::new(2.0)));
        assert!(F32::new(2.0).ge(F32::new(2.0)));
    }

    #[test]
    fn rounding() {
        // nearest ties-to-even: 0.5 → 0, 1.5 → 2, 2.5 → 2.
        assert_eq!(F64::new(0.5).nearest(), F64::new(0.0));
        assert_eq!(F64::new(1.5).nearest(), F64::new(2.0));
        assert_eq!(F64::new(2.5).nearest(), F64::new(2.0));
        assert_eq!(F32::new(1.4).ceil(), F32::new(2.0));
        assert_eq!(F32::new(1.6).floor(), F32::new(1.0));
        assert_eq!(F32::new(-1.6).trunc(), F32::new(-1.0));
    }

    #[test]
    fn trunc_sat_semantics() {
        // NaN → 0; +∞ → MAX; −∞/negative-for-unsigned → 0 / MIN.
        assert_eq!(I32TruncSatF32.eval(&F32::new(f32::NAN)), Some(0));
        assert_eq!(
            I32TruncSatF32.eval(&F32::new(f32::INFINITY)),
            Some(i32::MAX)
        );
        assert_eq!(
            I32TruncSatF32.eval(&F32::new(f32::NEG_INFINITY)),
            Some(i32::MIN)
        );
        assert_eq!(U32TruncSatF32.eval(&F32::new(-5.0)), Some(0));
        assert_eq!(U32TruncSatF32.eval(&F32::new(1e30)), Some(u32::MAX));
        // Ordinary truncation toward zero.
        assert_eq!(I32TruncSatF64.eval(&F64::new(-3.9)), Some(-3));
        assert_eq!(U64TruncSatF64.eval(&F64::new(42.9)), Some(42));
    }

    #[test]
    fn promote_demote_reinterpret_convert() {
        // promote/demote round-trip a representable value; promote of NaN canonical.
        assert_eq!(F32::new(1.5).promote(), F64::new(1.5));
        assert_eq!(F64::new(1.5).demote(), F32::new(1.5));
        assert_eq!(F32::new(f32::NAN).promote().to_bits(), canon_nan64());
        // reinterpret is a raw bit move.
        assert_eq!(
            F32ReinterpretI32.eval(&(0x3f80_0000u32 as i32)),
            Some(F32::new(1.0))
        );
        assert_eq!(
            I32ReinterpretF32.eval(&F32::new(1.0)),
            Some(0x3f80_0000u32 as i32)
        );
        // convert rounds; never NaN.
        assert_eq!(F32ConvertI32.eval(&-2), Some(F32::new(-2.0)));
        assert_eq!(F64ConvertU64.eval(&5), Some(F64::new(5.0)));
    }
}
