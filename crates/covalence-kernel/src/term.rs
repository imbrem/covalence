//! Term-level data: `TermDef` (one enum with structural + builtin variants)
//! and `TermRef` (local or foreign-arena reference).

use crate::id::{BitsId, BytesId, ForeignTermId, IntId, NatId, StrId, TermId};
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

    /// Build a foreign reference. Allocated via
    /// [`Arena::foreign_term_ref`](crate::arena::Arena::foreign_term_ref).
    pub fn foreign(id: ForeignTermId) -> Self {
        debug_assert!(id.0 & FOREIGN_BIT == 0, "ForeignTermId out of range for packed ref");
        Self(id.0 | FOREIGN_BIT)
    }

    pub fn is_local(self) -> bool {
        self.0 & FOREIGN_BIT == 0
    }

    pub fn is_foreign(self) -> bool {
        !self.is_local()
    }

    pub fn as_local(self) -> Option<TermId> {
        self.is_local().then_some(TermId(self.0))
    }

    pub fn as_foreign(self) -> Option<ForeignTermId> {
        self.is_foreign().then_some(ForeignTermId(self.0 & INDEX_MASK))
    }

    pub fn to_raw(self) -> u32 {
        self.0
    }

    pub fn from_raw(raw: u32) -> Self {
        Self(raw)
    }
}

/// The kernel's term language.
///
/// Every variant payload fits in two `u32`s; combined with the enum
/// discriminant the whole `TermDef` is 12 bytes — the (tag, lhs, rhs)
/// 3-u32 invariant. Variable-length payloads (names, byte strings,
/// big integers) sit in arena interning tables and appear here as
/// small ID newtypes.
///
/// Note: `Abs` carries **no name** field — display hints live in
/// `arena.abs_hints` (a side table) because they never affect
/// correctness. Free variables retain their names because the name is
/// part of the variable's identity.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TermDef {
    // -- structural --
    /// de Bruijn-indexed bound variable.
    Bound(u32),
    /// Free variable, named, with a type.
    Free(StrId, TypeRef),
    /// User-declared HOL constant at a particular type instance.
    Const(StrId, TypeRef),
    /// Application `f x`.
    Comb(TermRef, TermRef),
    /// Lambda abstraction. No name — display hints in
    /// [`arena.abs_hints`](crate::arena::Arena::abs_hint).
    Abs(TypeRef, TermRef),

    // -- truth + equality --
    True,
    False,
    /// Polymorphic primitive equality.
    Eq(TermRef, TermRef),

    // -- literals: fixed-width unsigned --
    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),

    // -- literals: fixed-width signed --
    I8(i8),
    I16(i16),
    I32(i32),
    I64(i64),

    // -- literals: arbitrary-precision --
    /// Arbitrary-precision int that fits in i64.
    IntInline(i64),
    /// Larger int — payload interned in `arena.ints`.
    IntStored(IntId),

    /// Arbitrary-precision nat that fits in u64.
    NatInline(u64),
    /// Larger nat — payload interned in `arena.nats`.
    NatStored(NatId),

    // -- literals: bit / byte strings --
    /// Bit string literal — payload in `arena.bits`.
    BitsStored(BitsId),
    /// Byte string literal — payload in `arena.bytes`.
    BytesStored(BytesId),
}
