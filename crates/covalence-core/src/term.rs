//! Pure's term and type language.
//!
//! Locally-nameless: bound variables use de Bruijn indices, free
//! variables and constants carry their declared type. Meta-implication,
//! meta-universal, and meta-equality are first-class variants — not
//! built-in `Const` applications — so inference rules pattern-match
//! them directly.
//!
//! The module is split into three submodules along the natural
//! design boundary:
//!
//! - [`observers`] — the observer-pattern infrastructure: the
//!   `Observer` / `Hint` marker traits, the `ObsTrue` / `ObsImp` /
//!   `ObsEq` policy traits, and the type-erased `Object` handle.
//! - [`types`] — the type language: `Type`, `TypeKind`, the cached
//!   primitive types (`prop`, `bool`, `nat`, `int`, `bytes`, `unit`),
//!   and `BinderHint` (the α-transparent display label used by both
//!   binders and `TyConObs`).
//! - [`terms`] — the term language: `Term`, `TermKind`, `Def`,
//!   and the type-checker (`TypeEnv` + `type_of_in`).
//!
//! Everything is re-exported at the `crate::term` level, so existing
//! `use crate::term::{Term, Type, ...}` imports continue to work.

mod observers;
mod terms;
mod types;

pub use observers::{Hint, ObsEq, ObsImp, ObsTrue, Object, Observer};
pub use terms::{Def, Term, TermKind};
pub use types::{BinderHint, Type, TypeKind};

pub(crate) use terms::{TypeEnv, type_of_in};
