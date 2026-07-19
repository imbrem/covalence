//! Unary successor-tower backend for the logic-agnostic Nat API.
//!
//! [`UnaryNat`] is distinct from both the native-leaf
//! [`NativeHol`](super::hol::NativeHol) and logarithmic-depth
//! [`DoubleSuccNat`](super::DoubleSuccNat) backends. A literal `n` is
//! represented by exactly `n` applications of successor to the shared zero
//! term.
//!
//! This is an API and representation stress test, not complete leaf
//! elimination. It still shares native HOL carriers, the zero leaf, theory
//! operations, and already-proved representation-independent Peano laws. A
//! later leaf-elimination backend can replace those pieces without changing
//! consumers generic over the dependency-free Nat capabilities.
//!
//! @covalence-api-impl {"api":"A0002","name":"UnaryNat","representation":"linear-depth successor towers over a shared native zero leaf"}

use covalence_core::{Result, Term, Type};
use covalence_kernel_data::numeric::nat::NatSyntax;

use super::nat_backend_common::impl_native_nat_theory;
use crate::init::nat;

/// Nat terms whose literals are unary successor towers.
#[derive(Clone, Copy, Debug, Default)]
pub struct UnaryNat;

impl_native_nat_theory!(UnaryNat);

impl NatSyntax for UnaryNat {
    fn nat_type(&self) -> Type {
        Type::nat()
    }

    fn nat_zero(&self) -> Term {
        nat::zero()
    }

    fn nat_succ(&self, n: Term) -> Result<Term> {
        Ok(Term::app(nat::nat_succ(), n))
    }

    fn nat_literal(&self, n: u64) -> Term {
        (0..n).fold(nat::zero(), |term, _| Term::app(nat::nat_succ(), term))
    }
}
