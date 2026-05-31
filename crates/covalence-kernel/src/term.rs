//! Term-level data: `TermDef` (one enum with structural + builtin variants)
//! and `TermRef` (local or foreign-arena reference). Plus `BitsValue` for
//! bit-string literals.

use crate::id::{BitsId, ForeignTermId, TermId};
use crate::name::{ConstName, VarName};
use crate::ty::TypeRef;

/// Reference to a term in the *current* arena's namespace.
///
/// A bit-packed u32. The top bit is the local/foreign discriminator:
/// - bit 31 = 0: **local**. Bottom 31 bits are a [`TermId`] into the
///   current arena's `terms` table.
/// - bit 31 = 1: **foreign**. Bottom 31 bits are a [`ForeignTermId`]
///   into the current arena's `foreign_terms` side table, which holds
///   `(ImportId, TermId)` pairs.
///
/// Either flavour resolves through the arena. To chase canonical
/// chains across arenas, use
/// [`Arena::canonical_term`](crate::arena::Arena::canonical_term).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TermRef(u32);

const FOREIGN_BIT: u32 = 1 << 31;
const INDEX_MASK: u32 = !FOREIGN_BIT;

impl TermRef {
    /// Build a local reference. Panics if `id.0 > 2^31 - 1`.
    pub fn local(id: TermId) -> Self {
        debug_assert!(id.0 & FOREIGN_BIT == 0, "TermId out of range for packed ref");
        Self(id.0 & INDEX_MASK)
    }

    /// Build a foreign reference. Panics if `id.0 > 2^31 - 1`.
    /// Allocated via [`Arena::foreign_term_ref`](crate::arena::Arena::foreign_term_ref).
    pub fn foreign(id: ForeignTermId) -> Self {
        debug_assert!(id.0 & FOREIGN_BIT == 0, "ForeignTermId out of range for packed ref");
        Self(id.0 | FOREIGN_BIT)
    }

    /// True iff this is a local reference.
    pub fn is_local(self) -> bool {
        self.0 & FOREIGN_BIT == 0
    }

    /// True iff this is a foreign reference.
    pub fn is_foreign(self) -> bool {
        !self.is_local()
    }

    /// Returns the local `TermId` if this is a local reference.
    pub fn as_local(self) -> Option<TermId> {
        self.is_local().then_some(TermId(self.0))
    }

    /// Returns the foreign side-table index if this is a foreign reference.
    pub fn as_foreign(self) -> Option<ForeignTermId> {
        self.is_foreign().then_some(ForeignTermId(self.0 & INDEX_MASK))
    }

    /// The raw u32 representation (for serialisation / debugging).
    pub fn to_raw(self) -> u32 {
        self.0
    }

    /// Wrap a raw u32. The high bit must be the local/foreign tag set
    /// consistently with the foreign-table layout.
    pub fn from_raw(raw: u32) -> Self {
        Self(raw)
    }
}

/// A bit-string value as it appears inside `TermDef::Bits`.
///
/// `Inline` carries the bytes directly inside the TermDef (cheap, used
/// for short literals). `Indirect` points at the arena's bits side table
/// (used for longer strings to keep TermDef small).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BitsValue {
    Inline(Vec<u8>),
    Indirect(BitsId),
}

/// Threshold (in bytes) at which the arena promotes a `Bits` literal
/// from `Inline` to `Indirect`. Implementation detail; both forms are
/// logically equivalent.
pub const BITS_INLINE_MAX_BYTES: usize = 32;

/// The kernel's term language.
///
/// All term kinds — structural shapes *and* builtins — live in this one
/// enum. Inference rules pattern-match on it directly; there are no
/// "well-known" name-IDs to look up alongside.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TermDef {
    // --- structural ---
    /// de Bruijn-indexed bound variable.
    Bound(u32),
    /// Free variable, named, with a type.
    Free(VarName, TypeRef),
    /// User-declared HOL constant at a particular type instance.
    Const(ConstName, TypeRef),
    /// Application `f x`.
    Comb(TermRef, TermRef),
    /// Lambda abstraction. `VarName` is a display hint; binding is by
    /// de Bruijn index, so the name doesn't affect identity.
    Abs(VarName, TypeRef, TermRef),

    // --- builtins ---
    /// Boolean true.
    True,
    /// Boolean false.
    False,
    /// Polymorphic primitive equality. Equal-as-bool; built-in to avoid
    /// the bootstrap circularity of defining `=` via Hilbert choice.
    Eq(TermRef, TermRef),
    /// A bit-string value (the primitive infinite type).
    Bits(BitsValue),
}
