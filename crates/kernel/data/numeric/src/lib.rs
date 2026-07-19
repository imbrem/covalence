//! Representation-independent exact and approximate numeric capabilities.
//!
//! This crate starts with Nat and Int. Decimal, rational, floating-point,
//! real-number, and enclosure capabilities will join the same hierarchy as
//! their API seams are consolidated.

pub mod int;
pub mod nat;

pub use int::{
    IntAdditiveLaws, IntArithmetic, IntDecidableEquality, IntLaws, IntMultiplicativeLaws,
    IntNormalization, IntOrder, IntOrderedRingLaws, IntSyntax,
};
pub use nat::{
    NatAdditiveLaws, NatArithmetic, NatEqDecision, NatFreeness, NatLaws, NatMultiplicativeLaws,
    NatNormalization, NatOrder, NatRecursionLaws, NatSyntax,
};
