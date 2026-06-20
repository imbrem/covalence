//! `unit := { b : bool | b = T }` — the one-element type.
//!
//! **Source of truth: [`core.cov`](super::cov).** `unit` is the
//! `(#subtype unit bool (#lam (b bool) (#eq b T)))` directive and
//! `unit.nil` is `(#def unit.nil (#abs unit () T))`; the accessors below
//! are thin lookups into [`super::cov::core_env`].
//!
//! `unit` is a **bool-subtype**: the carrier is `bool` and the selector
//! predicate `λb. b = T` keeps only the `T` inhabitant, so the type is a
//! genuine singleton. It used to be a kernel-primitive `TypeKind::Unit`;
//! it is now an ordinary derived `TypeSpec`, like `int`/`bytes`.
//! [`crate::Type::unit`] wraps the 0-ary `TypeKind::Spec(unit_spec, [])`
//! leaf.
//!
//! The singleton fact — *any* two inhabitants of `unit` are equal —
//! is not derived here; it is the kernel rule [`crate::Thm::unit_eq`].
//! The canonical inhabitant is `abs T` (see
//! [`super::helpers::unit_val`]).

use crate::term::Term;

use super::cov::core_env;
use super::spec::{TermSpec, TypeSpec};

/// `unit := { b : bool | b = T }`. A bool-subtype with exactly one
/// inhabitant. Sourced from the `(#subtype unit …)` directive in
/// `core.cov`.
pub fn unit_spec() -> TypeSpec {
    core_env()
        .type_spec("unit")
        .expect("core.cov must define `unit`")
        .clone()
}

/// `unit.nil : unit` ≡ `abs T` — the canonical inhabitant of `unit`.
/// By [`crate::Thm::unit_eq`] it equals every other element of `unit`,
/// so it is *the* representative.
pub fn unit_nil_spec() -> TermSpec {
    core_env()
        .term_spec("unit.nil")
        .expect("core.cov must define `unit.nil`")
        .clone()
}

/// `unit.nil : unit` — `abs T`.
pub fn unit_nil() -> Term {
    Term::term_spec(unit_nil_spec(), vec![])
}
