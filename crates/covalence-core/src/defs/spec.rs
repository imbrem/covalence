//! `TypeSpec<S>` and `TermSpec<S>` — symbol-tagged definitions of
//! the kernel's derived types and term constants.
//!
//! Both structures pair a [`Symbol`] (the name) with an optional
//! `Type` and an optional `Term`. The *meaning* of the four
//! representable shapes is:
//!
//! | Shape                         | English notation                  |
//! |-------------------------------|-----------------------------------|
//! | `ty = Some, tm = Some(λ_. T)` | `def name args := ty`             |
//! | `ty = Some, tm = Some(pred)`  | `def name args := ty where pred`  |
//! | `ty = Some, tm = Some(rel)`   | `def name args := { car } close rel` |
//! | `ty = None,  tm = Some(t)`    | `let name args := t`              |
//!
//! See `docs/type-hierarchy.md` for the full intended catalogue and
//! the semantic rationale for the `{ car } close rel` /
//! `car quot rel` shapes.
//!
//! These structs are **data only** — they don't yet appear inside
//! `TypeKind` or `TermKind`. That integration is a follow-up step;
//! for now the kernel keeps its existing primitive-type variants
//! and the `defs::*` catalogue lives parallel to them as a
//! semi-trusted vocabulary.

use crate::term::{Term, Type};

use super::symbol::Symbol;

/// A symbol-tagged type definition.
///
/// `TypeSpec<S>` describes a type former parameterised by `args`:
///
/// ```text
/// def name args := ty                    // tm = Some(λ_. T)
/// def name args := ty where pred         // tm = Some(pred)
/// def name args := { car } close pred    // tm = Some(pred), pred a rel
/// ```
///
/// Set membership for the type is `{x : ty | tm x ∨ x = ε tm}` —
/// well-defined for any `(ty, tm)` since the `ε` branch supplies a
/// garbage canonical inhabitant when `tm` is unsatisfiable.
#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct TypeSpec<S: Symbol> {
    /// The name of this type former. Pick from [`super::Canonical`]
    /// for kernel-shipped types or supply your own [`Symbol`]
    /// implementer.
    pub symbol: S,
    /// The carrier type (`car` in `{ car } close rel`, or the right-
    /// hand side in `def … := ty`). `None` for fully-erased specs.
    pub ty: Option<Type>,
    /// The predicate / relation defining the spec. `None` for
    /// fully-erased specs.
    pub tm: Option<Term>,
}

/// A symbol-tagged term definition.
///
/// `TermSpec<S>` describes a term former: an expression of type
/// `ty` whose value can be (computationally) replaced by `ε tm` —
/// the canonical witness chosen by Hilbert's epsilon at type
/// `ty`. `tm` is a predicate on `ty` selecting the chosen value;
/// `ty` is the type of the resulting term.
///
/// ```text
/// def name args := { tm : ty -> bool }   // ε tm at type ty
/// let name args := body                  // explicit, non-opaque
/// ```
#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct TermSpec<S: Symbol> {
    /// The name of this term former.
    pub symbol: S,
    /// The type of the resulting term. `None` for fully-erased
    /// specs.
    pub ty: Option<Type>,
    /// The selector predicate. `None` for fully-erased specs.
    pub tm: Option<Term>,
}
