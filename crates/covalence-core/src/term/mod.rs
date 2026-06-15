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
//! - [`observer`] — the observer-pattern infrastructure: the
//!   `Observer` / `Hint` marker traits, the `ObsTrue` / `ObsImp` /
//!   `ObsEq` policy traits, and the type-erased `Object` handle.
//! - [`term`](self::term) — the term language: `Term`, `TermKind`,
//!   `Def`, and the type-checker (`TypeEnv` + `type_of_in`).
//! - [`set`] — `TermSet`, the structurally-shared set of terms that
//!   [`crate::Ctx`] wraps.
//!
//! `term` and [`crate::ty`] are mutually recursive: a `Term` carries
//! `Type`s, and a `Type` (via `TyConObs`) carries an `Object`. The
//! `Type` / `TypeKind` names are re-exported here so
//! existing `crate::term::{Term, Type, …}` imports keep working.

mod observer;
pub mod set;
mod spec;
mod term;

pub use observer::{Hint, Object, ObsEq, ObsImp, ObsTrue, Observer};
pub use set::TermSet;
pub use spec::TermSpec;
pub use term::{Def, IntTag, SmallIntLiteral, Term, TermKind};

// Re-export the type language so `crate::term::{Type, TypeKind}`
// continues to resolve (the canonical home is `crate::ty`).
pub use crate::ty::{Type, TypeKind};

pub(crate) use term::{TypeEnv, type_of_in};
