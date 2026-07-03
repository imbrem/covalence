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
//! whole expression trees and to equality-decision; see SKELETONS.

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
            fn eval(&self, (a, b): &($flt, $flt)) -> $flt {
                a.$method(*b)
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
