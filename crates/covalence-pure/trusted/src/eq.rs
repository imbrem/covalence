//! Trusted **structural equality** — the base theory of `()`.
//!
//! [`StructuralEq`] is a **sealed** marker: a type whose `Eq` (and `Ord`/`Hash`/…)
//! is a *fully correct, total, decidable* equality — `a == b` **iff** `a` and `b`
//! are genuinely equal (BOTH directions). It is a strictly stronger, audited claim
//! than plain `Eq` (which the kernel trusts only in the `true` direction). It buys
//! [`decide`]: prove an equation *true or false*. Plain `Eq` buys only
//! [`semidecide`](crate::semidecide) (in [`eqn`](crate::eqn)): prove it true, or
//! error.
//!
//! Implemented only for audited base types. Floats are **not** included directly
//! (`NaN != NaN` breaks reflexivity) — use [`F32`]/[`F64`], which canonicalize NaN
//! and compare bitwise.

use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};

use covalence_types::Either;

use crate::eqn::{Eqn, of_eq_with};
use crate::expr::{App, False, True, Val};
use crate::lang::CanonRule;
use crate::op::Op;
use crate::prop::EqOp;

mod sealed {
    pub trait Sealed {}
}

/// A type whose equality is fully correct, total, and decidable (both directions).
/// **Sealed** — the audited set of base types below. Implies every derived operator
/// (`Ord`, `Hash`, …) agrees with this equality (used later, e.g. for `BTreeSet`).
pub trait StructuralEq: Eq + sealed::Sealed {}

/// The internalized-equality proposition `App<EqOp<S>, (Val a, Val b)>` at sort `S`.
pub type EqProp<S> = App<EqOp<S>, (Val<S>, Val<S>)>;

/// Decide an equality **true or false** (needs [`StructuralEq`]). Returns the bool
/// proposition `(a = b)` proved equal to `⊤` (`Left`) or to `⊥` (`Right`).
///
/// The **true** branch reuses the ungated
/// [`of_eq_with`](crate::of_eq_with)`+`[`internalize`](crate::Eqn::internalize) path
/// (one fewer bespoke mint). The **false** branch is the load-bearing one: it emits
/// `(a =_S b) = ⊥` even though the values genuinely differ, which cannot be a
/// `Val a = Val b` certificate — so it needs [`StructuralEq`] (both-direction trust)
/// and this reified-proposition form. It is the audited minting site for `decide`.
pub fn decide<S: StructuralEq, L>(
    a: S,
    b: S,
    lang: L,
) -> Either<Eqn<EqProp<S>, True, L>, Eqn<EqProp<S>, False, L>> {
    if a == b {
        // safe: `a == b` just held.
        Either::Left(of_eq_with(a, b, lang).unwrap().internalize())
    } else {
        let expr = App(EqOp::new(), (Val(a), Val(b)));
        Either::Right(Eqn::new(expr, False, lang))
    }
}

// ---- StructuralEq impls: audited base types ----

macro_rules! structural {
    ($($t:ty),+ $(,)?) => { $(
        impl sealed::Sealed for $t {}
        impl StructuralEq for $t {}
    )+ };
}

structural!(
    u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize, bool, char, String,
);
structural!(
    covalence_types::Nat,
    covalence_types::Int,
    covalence_types::Bits,
    covalence_types::Bytes,
);

impl<T: StructuralEq> sealed::Sealed for Vec<T> {}
impl<T: StructuralEq> StructuralEq for Vec<T> {}
impl<T: StructuralEq, const N: usize> sealed::Sealed for [T; N] {}
impl<T: StructuralEq, const N: usize> StructuralEq for [T; N] {}

// WASM component-model shapes.
impl<T: StructuralEq> sealed::Sealed for Option<T> {}
impl<T: StructuralEq> StructuralEq for Option<T> {}
impl<T: StructuralEq, E: StructuralEq> sealed::Sealed for Result<T, E> {}
impl<T: StructuralEq, E: StructuralEq> StructuralEq for Result<T, E> {}
impl<T: StructuralEq, U: StructuralEq> sealed::Sealed for Either<T, U> {}
impl<T: StructuralEq, U: StructuralEq> StructuralEq for Either<T, U> {}

macro_rules! tuple_structural {
    ($($T:ident),+) => {
        impl<$($T: StructuralEq),+> sealed::Sealed for ($($T,)+) {}
        impl<$($T: StructuralEq),+> StructuralEq for ($($T,)+) {}
    };
}
tuple_structural!(A, B);
tuple_structural!(A, B, C);
tuple_structural!(A, B, C, D);
tuple_structural!(A, B, C, D, E);
tuple_structural!(A, B, C, D, E, F);
tuple_structural!(A, B, C, D, E, F, G);
tuple_structural!(A, B, C, D, E, F, G, H);
tuple_structural!(A, B, C, D, E, F, G, H, I);
tuple_structural!(A, B, C, D, E, F, G, H, I, J);
tuple_structural!(A, B, C, D, E, F, G, H, I, J, K);
tuple_structural!(A, B, C, D, E, F, G, H, I, J, K, L);

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
        // decidable over bit patterns, so `$name` is a valid `StructuralEq` leaf.
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
        impl sealed::Sealed for $name {}
        impl StructuralEq for $name {}
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

// ---- Gated float arithmetic ops (WASM semantics; reuse `canon`, no new mint) ----

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
