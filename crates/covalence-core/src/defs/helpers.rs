//! Shared helpers for the catalogue submodules.
//!
//! The `close` / `quot` type constructors ([`TypeSpec::close`] /
//! [`TypeSpec::quot`]) live in `super::quotient`.

use crate::term::{Term, Type};

/// The "any" predicate `λ_:τ. T` for the carrier type τ. Used by
/// `TypeSpec::newtype` and every `def name args := ty` (no `where
/// pred`) catalogue entry.
pub(crate) fn any(carrier: &Type) -> Term {
    Term::abs(carrier.clone(), Term::bool_lit(true))
}
