//! Type-level data: `TypeDef` (the single enum with builtin + user variants)
//! and `TypeRef` (local or foreign-arena reference).

use crate::id::{ImportId, TypeId};
use crate::name::{TypeName, TypeVarId};

/// Reference to a type in the *current* arena's namespace.
///
/// `Local(id)` indexes the current arena's `types` table. `Foreign(import,
/// id)` indexes the `types` table of `arena.imports[import]`. To resolve a
/// chain of Foreign refs through multiple arenas, use
/// [`Arena::canonical_type`](crate::arena::Arena::canonical_type), which
/// returns the final `(Arc<Arena>, TypeId)` pair.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TypeRef {
    Local(TypeId),
    Foreign(ImportId, TypeId),
}

/// The kernel's type language.
///
/// `Bool`, `Bits`, and `Fun` are builtins — they're plain enum variants,
/// not entries in any user-facing namespace. `TVar` and `Tyapp` are the
/// only variants that read from the user-side namespace.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeDef {
    /// The builtin boolean type.
    Bool,
    /// The builtin bit-string type — replaces HOL Light's `ind` as the
    /// primitive infinite type.
    Bits,
    /// The function type `α → β`. Builtin.
    Fun(TypeRef, TypeRef),
    /// A polymorphic type variable, e.g. `'a`.
    TVar(TypeVarId),
    /// A user-declared type constructor applied to its arguments.
    Tyapp(TypeName, Vec<TypeRef>),
}
