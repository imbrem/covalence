//! Type-level data: `TypeDef` (the single enum with builtin + user variants)
//! and `TypeRef` (local or foreign-arena reference).

use crate::id::{ForeignTypeId, TypeId};
use crate::name::{TypeName, TypeVarId};

/// Reference to a type in the *current* arena's namespace.
///
/// A bit-packed u32. The top bit is the local/foreign discriminator:
/// - bit 31 = 0: **local**. Bottom 31 bits are a [`TypeId`].
/// - bit 31 = 1: **foreign**. Bottom 31 bits are a [`ForeignTypeId`]
///   into the current arena's `foreign_types` side table.
///
/// To resolve a chain of foreign refs through multiple arenas, use
/// [`Arena::canonical_type`](crate::arena::Arena::canonical_type).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TypeRef(u32);

const FOREIGN_BIT: u32 = 1 << 31;
const INDEX_MASK: u32 = !FOREIGN_BIT;

impl TypeRef {
    /// Build a local reference. Panics if `id.0 > 2^31 - 1`.
    pub fn local(id: TypeId) -> Self {
        debug_assert!(id.0 & FOREIGN_BIT == 0, "TypeId out of range for packed ref");
        Self(id.0 & INDEX_MASK)
    }

    /// Build a foreign reference. Allocated via
    /// [`Arena::foreign_type_ref`](crate::arena::Arena::foreign_type_ref).
    pub fn foreign(id: ForeignTypeId) -> Self {
        debug_assert!(id.0 & FOREIGN_BIT == 0, "ForeignTypeId out of range for packed ref");
        Self(id.0 | FOREIGN_BIT)
    }

    pub fn is_local(self) -> bool {
        self.0 & FOREIGN_BIT == 0
    }

    pub fn is_foreign(self) -> bool {
        !self.is_local()
    }

    pub fn as_local(self) -> Option<TypeId> {
        self.is_local().then_some(TypeId(self.0))
    }

    pub fn as_foreign(self) -> Option<ForeignTypeId> {
        self.is_foreign().then_some(ForeignTypeId(self.0 & INDEX_MASK))
    }

    pub fn to_raw(self) -> u32 {
        self.0
    }

    pub fn from_raw(raw: u32) -> Self {
        Self(raw)
    }
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
