//! `unit := { b : bool | b = T }` — the one-element type.
//!
//! `unit` is a **bool-subtype**: the carrier is `bool` and the
//! selector predicate `λb. b = T` keeps only the `T` inhabitant, so
//! the type is a genuine singleton. It used to be a kernel-primitive
//! `TypeKind::Unit`; it is now an ordinary derived `TypeSpec`, like
//! `int`/`bytes`. [`crate::Type::unit`] wraps the 0-ary
//! `TypeKind::Spec(unit_spec, [])` leaf.
//!
//! The singleton fact — *any* two inhabitants of `unit` are equal —
//! is not derived here; it is the kernel rule [`crate::Thm::unit_eq`].
//! The canonical inhabitant is `abs T` (see
//! [`super::helpers::unit_val`]).

use std::sync::LazyLock;

use crate::hol;
use crate::term::{Term, Type};

use super::canonical::Canonical;
use super::spec::TypeSpec;

/// `λb:bool. b = T` — the selector predicate carving `unit` out of
/// `bool`.
fn unit_predicate() -> Term {
    let b = Term::free("b", Type::bool());
    let eq = hol::hol_eq(b, Term::bool_lit(true));
    hol::pub_abs("b", Type::bool(), eq)
}

/// `unit := { b : bool | b = T }`. A bool-subtype with exactly one
/// inhabitant.
pub fn unit_spec() -> TypeSpec {
    static LAZY: LazyLock<TypeSpec> =
        LazyLock::new(|| TypeSpec::subtype(Canonical::Unit, Type::bool(), unit_predicate()));
    LAZY.clone()
}

/// Body of `unit.nil`: `abs T` — the abstraction of the witness
/// `T : bool` into `unit`.
fn unit_nil_body() -> Term {
    let abs = Term::spec_abs(unit_spec(), Vec::new());
    Term::app(abs, Term::bool_lit(true))
}

let_term! {
    /// `unit.nil : unit` — the canonical inhabitant of `unit`, `abs T`.
    /// By [`crate::Thm::unit_eq`] it equals every other element of
    /// `unit`, so it is *the* representative.
    unit_nil_spec, unit_nil, Canonical::UnitNil, unit_nil_body()
}
