//! Type-level data: `TypeDef` (the single enum with builtin + user variants)
//! and `TypeRef` (local or foreign-arena reference).

use crate::id::{ForeignTypeId, StrId, TyArgsId, TypeId};

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

/// Type information attached to a term at allocation time.
///
/// Locally-closed, well-typed terms get `Typed(t)`; the term's type
/// is `t` and the kernel intends to enforce it. Terms with dangling
/// de Bruijn indices get `Unbound(n)` — `n` is the count of dangling
/// indices, i.e. how many more binders need to wrap this term before
/// it's locally closed. Terms that are locally closed but whose type
/// can't be derived from the children's types (mismatched Comb,
/// missing typing rule, etc.) get `IllTyped` as a sentinel.
///
/// **Soundness note.** A term with `IllTyped` is perfectly allowed
/// to sit in the arena; `alloc_term` never rejects. Only when a
/// `Thm` is constructed does the kernel assert that *all* terms in
/// the relevant arena are well-typed (along with the proof itself).
/// Ill-typed terms cannot appear in a `Thm`'s Prop.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TypeInfo {
    Typed(TypeRef),
    Unbound(u32),
    IllTyped,
}

impl TypeInfo {
    /// True iff the term is locally closed — no dangling Bound.
    /// Includes the `Typed` and `IllTyped` cases.
    pub fn is_locally_closed(self) -> bool {
        !matches!(self, TypeInfo::Unbound(n) if n > 0)
    }

    /// True iff the term has a known type.
    pub fn is_typed(self) -> bool {
        matches!(self, TypeInfo::Typed(_))
    }

    /// Returns the term's type if known.
    pub fn as_type(self) -> Option<TypeRef> {
        if let TypeInfo::Typed(t) = self {
            Some(t)
        } else {
            None
        }
    }

    /// The dangling-bound count for an `Unbound` info; `0` for any
    /// closed info.
    pub fn unbound_depth(self) -> u32 {
        match self {
            TypeInfo::Unbound(n) => n,
            _ => 0,
        }
    }
}

/// The kernel's type language.
///
/// Every variant is `Copy`: variable-sized payloads (type-variable
/// names, Tyapp arg lists) live in arena interning tables and appear
/// here only as `StrId` / `TyArgsId`.
///
/// The primitive type cluster (`Bool`, `Bits`, `Bytes`, `Int`, `Nat`,
/// the fixed-width `uN`/`iN` types) plus `Fun` are kernel builtins —
/// no user-side namespace involved. `TVar(StrId)` and `Tyapp(StrId,
/// TyArgsId)` are the only variants that read from the user-side
/// namespace.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TypeDef {
    // -- builtin primitive types --
    Bool,
    Bits,
    Bytes,
    Int,
    Nat,
    U8,
    U16,
    U32,
    U64,
    I8,
    I16,
    I32,
    I64,
    // -- type formers --
    /// The function type `α → β`. Builtin.
    Fun(TypeRef, TypeRef),
    /// A polymorphic type variable, e.g. `'a` — name interned in
    /// `arena.strings`.
    TVar(StrId),
    /// A user-declared type constructor applied to its arguments.
    /// `name` is interned in `arena.strings`; `args` is a list in
    /// `arena.tyargs`.
    Tyapp(StrId, TyArgsId),
}
