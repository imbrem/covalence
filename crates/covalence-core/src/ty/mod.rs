//! Pure's type language.
//!
//! Mutually recursive with [`crate::term`]: a [`Type`] (via
//! `TyConObs`) carries an `Object` from `term::observer`, and a `Term`
//! carries `Type`s.
//!
//! Submodules:
//!
//! - [`ty`](self::ty) — `Type`, `TypeKind`, the cached primitive types
//!   (`nat`, `bool`, `int`, `bytes`, `unit`), and `BinderHint` (the
//!   α-transparent display label shared with term binders).
//! - [`list`] — `TypeList`, the wrapper around an ordered list of
//!   type arguments used throughout `TypeKind` / `TermKind`.

mod list;
mod spec;
mod ty;

pub use list::TypeList;
pub use spec::TypeSpec;
pub use ty::{BinderHint, Type, TypeKind};
