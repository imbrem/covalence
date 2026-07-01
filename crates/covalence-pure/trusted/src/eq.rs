//! Trusted **structural equality** — the base theory of `()`.
//!
//! [`StructuralEq`] is a **sealed** marker: a type whose `Eq` (and `Ord`/`Hash`/…)
//! is a *fully correct, total, decidable* equality — `a == b` **iff** `a` and `b`
//! are genuinely equal (BOTH directions). It is a strictly stronger, audited claim
//! than plain `Eq` (which the kernel trusts only in the `true` direction). It buys
//! [`decide`]: prove an equation *true or false*. Plain `Eq` buys only
//! [`semidecide`]: prove it true, or error.
//!
//! Implemented only for audited base types. Floats are **not** included directly
//! (`NaN != NaN` breaks reflexivity) — use [`F32`]/[`F64`], which canonicalize NaN
//! and compare bitwise.

use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};

use covalence_types::Either;

use crate::eqn::{Eqn, Error};
use crate::expr::{App, Val};
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
pub fn decide<S: StructuralEq, L>(
    a: S,
    b: S,
    lang: L,
) -> Either<Eqn<EqProp<S>, crate::expr::True, L>, Eqn<EqProp<S>, crate::expr::False, L>> {
    let equal = a == b;
    let expr = App(EqOp::new(), (Val(a), Val(b)));
    if equal {
        Either::Left(Eqn::new(expr, crate::expr::True, lang))
    } else {
        Either::Right(Eqn::new(expr, crate::expr::False, lang))
    }
}

/// **Semi**-decide an equality (needs only [`Eq`]): prove `(a = b) = ⊤` when
/// `a == b`, else [`Error::Undecided`] (the `false` direction of `Eq` is untrusted).
pub fn semidecide<S: Eq, L>(
    a: S,
    b: S,
    lang: L,
) -> Result<Eqn<EqProp<S>, crate::expr::True, L>, Error> {
    let equal = a == b;
    let expr = App(EqOp::new(), (Val(a), Val(b)));
    if equal {
        Ok(Eqn::new(expr, crate::expr::True, lang))
    } else {
        Err(Error::Undecided)
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
        pub struct $name($f);

        impl $name {
            /// Wrap a float, **canonicalizing any NaN** to one bit pattern so that
            /// equality is total, reflexive, and decidable (bitwise). (Also
            /// distinguishes `+0.0` from `-0.0` — this is *structural* identity.)
            pub fn new(x: $f) -> Self {
                $name(if x.is_nan() { <$f>::NAN } else { x })
            }
            /// The wrapped (already-canonical) float.
            pub fn get(self) -> $f {
                self.0
            }
            fn bits(self) -> $bits {
                self.0.to_bits()
            }
        }
        impl PartialEq for $name {
            fn eq(&self, o: &Self) -> bool {
                self.bits() == o.bits()
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
                self.bits().cmp(&o.bits())
            }
        }
        impl Hash for $name {
            fn hash<H: Hasher>(&self, s: &mut H) {
                self.bits().hash(s);
            }
        }
        impl fmt::Debug for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(f, "{}({})", stringify!($name), self.0)
            }
        }
        impl sealed::Sealed for $name {}
        impl StructuralEq for $name {}
    };
}

float_wrapper!(
    /// A 32-bit float with **bitwise** equality and canonical NaN — a valid sort
    /// leaf (unlike bare `f32`, whose `NaN != NaN` breaks `refl`).
    F32, f32, u32
);
float_wrapper!(
    /// A 64-bit float with bitwise equality and canonical NaN.
    F64, f64, u64
);
