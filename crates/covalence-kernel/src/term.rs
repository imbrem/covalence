//! Term-level data: `TermDef` (one enum with structural + builtin variants)
//! and `TermRef` (local or foreign-arena reference).

use crate::id::{BitsId, BytesId, ForeignTermId, IntId, NatId, StrId, TermId};
use crate::primop::{PrimOp1, PrimOp2};
use crate::ty::TypeRef;

/// Crate-internal newtype wrapping a `u64` as two `u32`s.
///
/// Storing 64-bit literal payloads as raw `u64` would force 8-byte
/// enum alignment, pushing `TermDef` past the 3-u32 invariant.
/// `Packed64` stores the same value as `[u32; 2]` — 4-byte aligned —
/// and exposes `from_u64` / `to_u64` / `from_i64` / `to_i64` for
/// conversion. The newtype is `pub(crate)` so external code cannot
/// construct or destructure it directly; use the smart constructors
/// (`TermDef::nat_inline`, `u64_literal`, …) and `arena.kind()` to
/// see the logical scalar.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Packed64(pub(crate) [u32; 2]);

impl Packed64 {
    pub(crate) const fn from_u64(v: u64) -> Self {
        Self([v as u32, (v >> 32) as u32])
    }

    pub(crate) const fn to_u64(self) -> u64 {
        (self.0[0] as u64) | ((self.0[1] as u64) << 32)
    }

    pub(crate) const fn from_i64(v: i64) -> Self {
        Self::from_u64(v as u64)
    }

    pub(crate) const fn to_i64(self) -> i64 {
        self.to_u64() as i64
    }
}

/// Public view of a term.
///
/// This is the stable API for inspecting terms. `TermDef` (the
/// internal storage) has one variant per primop — ~270 cases —
/// because the (tag, lhs, rhs) 3-u32 invariant requires the
/// discriminant to carry the op kind. `TermKind` folds the per-op
/// variants back into `Op1(PrimOp1, _)` and `Op2(PrimOp2, _, _)`,
/// and presents arbitrary-precision literals as full `Nat`/`Int`
/// values (the inline-vs-stored split is a TermDef-level
/// implementation detail).
///
/// Get one via [`Arena::kind`](crate::arena::Arena::kind). Not
/// `Copy` because materialising `Nat`/`Int` may allocate.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TermKind {
    // -- structural --
    Bound(u32),
    Free(StrId, TypeRef),
    Const(StrId, TypeRef),
    Comb(TermRef, TermRef),
    Abs(TypeRef, TermRef),

    // -- truth + equality --
    True,
    False,
    Eq(TermRef, TermRef),
    Ne(TermRef, TermRef),

    // -- quantifiers + choice --
    Forall(TermRef),
    Exists(TermRef),
    Eps(TypeRef, TermRef),

    // -- combinators --
    Id(TypeRef),
    Comp(TermRef, TermRef),
    Iter(TermRef, TermRef),
    Ite(TermRef, TermRef),
    LiftOp1(PrimOp1),
    LiftOp2(PrimOp2),

    // -- applied primops (folded from per-op TermDef variants) --
    Op1(PrimOp1, TermRef),
    Op2(PrimOp2, TermRef, TermRef),

    // -- literals: fixed-width --
    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
    I8(i8),
    I16(i16),
    I32(i32),
    I64(i64),
    // -- literals: arbitrary-precision (materialised regardless of
    //    whether the underlying TermDef variant was Inline or Stored) --
    Nat(covalence_types::Nat),
    Int(covalence_types::Int),
    // -- bit / byte string literals (also materialised; the "Stored"
    //    bit is a storage detail of TermDef, hidden here) --
    Bits(covalence_types::Bits),
    Bytes(bytes::Bytes),
}


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
/// Storage layout: 12 bytes total — the (tag, lhs, rhs) 3-u32
/// invariant. Applied primops use two variants — `Op1(PrimOp1,
/// TermRef)` and `Op2(PrimOp2, TermRef, TermRef)` — with the op
/// kind inlined as a `u8` in the payload. The earlier sketch of
/// one variant per primop (~270 variants) collapsed under its own
/// weight; the embedded-op layout is dramatically simpler and Rust
/// packs the discriminant into the alignment padding so the size
/// is the same.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TermDef {
    // -- structural --
    Bound(u32),
    Free(StrId, TypeRef),
    Const(StrId, TypeRef),
    Comb(TermRef, TermRef),
    Abs(TypeRef, TermRef),

    // -- truth + equality --
    True,
    False,
    Eq(TermRef, TermRef),
    Ne(TermRef, TermRef),

    // -- quantifiers and choice --
    Forall(TermRef),
    Exists(TermRef),
    Eps(TypeRef, TermRef),

    // -- combinators --
    Id(TypeRef),
    Comp(TermRef, TermRef),
    Iter(TermRef, TermRef),
    Ite(TermRef, TermRef),
    LiftOp1(PrimOp1),
    LiftOp2(PrimOp2),

    // -- applied primops (op kind inlined) --
    Op1(PrimOp1, TermRef),
    Op2(PrimOp2, TermRef, TermRef),

    // -- literals: fixed-width --
    //
    // The 64-bit variants carry a `Packed64` rather than a raw
    // `u64` / `i64`; this avoids 8-byte enum alignment.
    U8(u8),
    U16(u16),
    U32(u32),
    U64(Packed64),
    I8(i8),
    I16(i16),
    I32(i32),
    I64(Packed64),

    // -- literals: arbitrary-precision --
    IntInline(Packed64),
    IntStored(IntId),
    NatInline(Packed64),
    NatStored(NatId),

    // -- literals: bit / byte strings --
    BitsStored(BitsId),
    BytesStored(BytesId),
}

impl TermDef {
    /// Smart constructor for a `U64` literal.
    pub const fn u64_literal(v: u64) -> Self {
        TermDef::U64(Packed64::from_u64(v))
    }

    /// Smart constructor for an `I64` literal.
    pub const fn i64_literal(v: i64) -> Self {
        TermDef::I64(Packed64::from_i64(v))
    }

    /// Smart constructor for an inline `Nat`.
    pub const fn nat_inline(v: u64) -> Self {
        TermDef::NatInline(Packed64::from_u64(v))
    }

    /// Smart constructor for an inline `Int`.
    pub const fn int_inline(v: i64) -> Self {
        TermDef::IntInline(Packed64::from_i64(v))
    }

    /// If this is an applied unary primop, return `(op, child)`.
    pub fn as_op1(&self) -> Option<(PrimOp1, TermRef)> {
        if let TermDef::Op1(op, x) = self {
            Some((*op, *x))
        } else {
            None
        }
    }

    /// If this is an applied binary primop, return `(op, lhs, rhs)`.
    pub fn as_op2(&self) -> Option<(PrimOp2, TermRef, TermRef)> {
        if let TermDef::Op2(op, a, b) = self {
            Some((*op, *a, *b))
        } else {
            None
        }
    }

    /// The `TermRef` dependencies of this def (0, 1, or 2 children).
    /// Type-ref dependencies (e.g. `Abs(TypeRef, _)`, `Eps(TypeRef, _)`,
    /// `Id(TypeRef)`) are *not* term deps and are not reported here —
    /// they're part of the shape and must match exactly.
    pub fn deps(&self) -> Deps {
        use TermDef::*;
        match *self {
            Bound(_) | Free(..) | Const(..) | True | False | Id(_) | LiftOp1(_) | LiftOp2(_)
            | U8(_) | U16(_) | U32(_) | U64(_) | I8(_) | I16(_) | I32(_) | I64(_)
            | IntInline(_) | IntStored(_) | NatInline(_) | NatStored(_)
            | BitsStored(_) | BytesStored(_) => Deps::None,
            Forall(p) | Exists(p) | Op1(_, p) => Deps::One(p),
            Eps(_, p) | Abs(_, p) => Deps::One(p),
            Comb(a, b) | Eq(a, b) | Ne(a, b) | Comp(a, b) | Iter(a, b) | Ite(a, b)
            | Op2(_, a, b) => Deps::Two(a, b),
        }
    }

    /// Return a copy of this def with all `TermRef` deps replaced by
    /// `sentinel`. Useful as a shape key: two defs share a shape iff
    /// `a.with_zeroed_deps(s) == b.with_zeroed_deps(s)`.
    pub fn with_zeroed_deps(&self, sentinel: TermRef) -> TermDef {
        use TermDef::*;
        match *self {
            Forall(_) => Forall(sentinel),
            Exists(_) => Exists(sentinel),
            Op1(o, _) => Op1(o, sentinel),
            Eps(t, _) => Eps(t, sentinel),
            Abs(t, _) => Abs(t, sentinel),
            Comb(_, _) => Comb(sentinel, sentinel),
            Eq(_, _) => Eq(sentinel, sentinel),
            Ne(_, _) => Ne(sentinel, sentinel),
            Comp(_, _) => Comp(sentinel, sentinel),
            Iter(_, _) => Iter(sentinel, sentinel),
            Ite(_, _) => Ite(sentinel, sentinel),
            Op2(o, _, _) => Op2(o, sentinel, sentinel),
            other => other,
        }
    }
}

/// The `TermRef` dependencies of a [`TermDef`].
///
/// The kernel's term language has at most two `TermRef` children per
/// def; this enum makes that bound explicit so callers don't need a
/// per-variant match.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Deps {
    None,
    One(TermRef),
    Two(TermRef, TermRef),
}
