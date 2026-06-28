//! Algebraic structures and their rewriting tactics: the ring/semiring
//! normalizers, the monoidal/category structure layer, and the AC
//! (associative-commutative) tactic they build on.
//!
//! These are the generic algebraic *machinery* — distinct from the catalogue
//! theories in [`crate::init`] (`init::monoid`, `init::cat`) that instantiate
//! them.

pub mod ac;
pub mod category;
pub mod monoidal;
pub mod ring;
pub mod semiring;
