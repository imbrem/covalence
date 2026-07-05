//! Core's term language (the type language lives in [`crate::ty`]).
//!
//! Locally-nameless: bound variables use de Bruijn indices, free
//! variables and constants carry their declared type. Meta-implication,
//! meta-universal, and meta-equality are first-class variants — not
//! built-in `Const` applications — so inference rules pattern-match
//! them directly.
//!
//! Submodules:
//!
//! - `fresh` — the private `FreshId` identity token (freshness for
//!   `new_type_definition`'s τ and `abs`/`rep` constants).
//! - `term` — the term language: `Term`, `TermKind`,
//!   `Def`, and the type-checker (`TypeEnv` + `type_of_in`).
//! - [`set`] — `TermSet`, the structurally-shared set of terms that
//!   [`crate::Ctx`] wraps.
//!
//! `term` and [`crate::ty`] are mutually recursive: a `Term` carries
//! `Type`s, and a `Type` (via `FreshTyCon`) carries a `FreshId`. The
//! `Type` / `TypeKind` names are re-exported here so
//! existing `crate::term::{Term, Type, …}` imports keep working.

pub mod cons;
mod fresh;
pub mod set;
mod spec;
#[allow(clippy::module_inception)]
mod term;

pub use cons::{Checked, HashCons, TermCons, TrustedCons};
pub use fresh::{FreshId, FreshLeaf, FreshTyLeaf};
pub use set::TermSet;
pub use spec::TermSpec;
pub use term::{Def, IntTag, SmallIntLiteral, Term, TermKind, TyError, Var};
pub(crate) use term::{TypeEnv, type_of_in};

// Re-export the type language so `crate::term::{Type, TypeKind}`
// continues to resolve (the canonical home is `crate::ty`).
pub use crate::ty::{Type, TypeKind};
