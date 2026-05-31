//! Type-level data: `TypeDef` (the single enum with builtin + user variants)
//! and `TypeRef` (local or foreign-arena reference).

use std::sync::Arc;

use crate::arena::Arena;
use crate::id::TypeId;
use crate::name::{TypeName, TypeVarId};

/// Reference to a type, possibly in a foreign (imported) arena.
///
/// `Local(id)` resolves against the current arena's `types` table.
/// `Foreign(arena, id)` holds an `Arc<Arena>` for the source and an
/// index into its `types`. Two `TypeRef`s denote the same type when
/// their arena allocations are pointer-equal and their inner IDs
/// match (see architecture §2.2).
#[derive(Debug, Clone)]
pub enum TypeRef {
    Local(TypeId),
    Foreign(Arc<Arena>, TypeId),
}

impl PartialEq for TypeRef {
    /// Pointer equality on the arena, value equality on the id.
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (TypeRef::Local(a), TypeRef::Local(b)) => a == b,
            (TypeRef::Foreign(a_arc, a_id), TypeRef::Foreign(b_arc, b_id)) => {
                Arc::ptr_eq(a_arc, b_arc) && a_id == b_id
            }
            _ => false,
        }
    }
}

impl Eq for TypeRef {}

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
