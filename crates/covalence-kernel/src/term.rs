//! Term-level data: [`TermDef`] (the structural term language),
//! [`TermKind`] (the stable inspection view), and [`TermRef`] (a
//! reference to a term — local to one arena or imported from
//! another).

use crate::id::{BytesId, ForeignTermId, IntId, NatId, StrId, TermId};
use crate::primop::{PrimOp1, PrimOp2};
use crate::ty::TypeRef;

/// Opaque storage cell for inline 64-bit literal payloads.
/// Constructable only inside the crate; external callers see logical
/// `u64` / `i64` values via [`TermKind`].
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

/// Stable, ergonomic view of a term. Get one via
/// [`Arena::kind`](crate::Arena::kind).
///
/// `TermKind` presents arbitrary-precision literals as full
/// [`Nat`](covalence_types::Nat) / [`Int`](covalence_types::Int)
/// values, hiding any storage split inside [`TermDef`]. Not `Copy`
/// because materialising arbitrary-precision literals may allocate.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TermKind {
    // -- structural --
    Bound(u32),
    Free(StrId, TypeRef),
    Const(StrId, TypeRef),
    Comb(TermRef, TermRef),
    Abs(TypeRef, TermRef),

    // -- truth + equality --
    Bool(bool),
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

    // -- literals: arbitrary-precision --
    Nat(covalence_types::Nat),
    Int(covalence_types::Int),
    // -- byte string literal --
    Bytes(bytes::Bytes),
}


/// Opaque reference to a term — local to the current arena or
/// imported from a foreign one. Construct via [`TermRef::local`] or
/// [`TermRef::foreign`]; pattern-match via `as_local` / `as_foreign`.
///
/// To chase canonical chains across arenas use
/// [`Arena::canonical_term`](crate::Arena::canonical_term).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TermRef(u32);

const FOREIGN_BIT: u32 = 1 << 31;
const INDEX_MASK: u32 = !FOREIGN_BIT;

impl TermRef {
    /// Build a reference to a term in the current arena.
    pub fn local(id: TermId) -> Self {
        debug_assert!(id.0 & FOREIGN_BIT == 0, "TermId out of range for packed ref");
        Self(id.0 & INDEX_MASK)
    }

    /// Build a reference to a term imported from a foreign arena.
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

    pub(crate) fn from_raw(raw: u32) -> Self {
        Self(raw)
    }
}

/// The kernel's term language — the structural form stored at each
/// allocated term. `Copy` and packed for size; for ergonomic
/// inspection prefer [`TermKind`] via
/// [`Arena::kind`](crate::Arena::kind).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TermDef {
    // -- structural --
    Bound(u32),
    Free(StrId, TypeRef),
    Const(StrId, TypeRef),
    Comb(TermRef, TermRef),
    Abs(TypeRef, TermRef),

    // -- truth + equality --
    Bool(bool),
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

    // -- literals: arbitrary-precision --
    IntInline(Packed64),
    IntStored(IntId),
    NatInline(Packed64),
    NatStored(NatId),

    // -- literals: byte string --
    BytesStored(BytesId),
}

impl TermDef {
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
            Bound(_) | Free(..) | Const(..) | Bool(_) | Id(_) | LiftOp1(_) | LiftOp2(_)
            | IntInline(_) | IntStored(_) | NatInline(_) | NatStored(_)
            | BytesStored(_) => Deps::None,
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
