//! Term-level data: [`TermDef`] (the structural term language),
//! [`TermKind`] (the stable inspection view), and [`TermRef`] (a
//! reference to a term — local to one arena or imported from
//! another).

use crate::id::{BytesId, ImportId, IntId, NatId, StrId, TermId};
use crate::primop::{PrimOp1, PrimOp2};
use crate::ty::TypeRef;

// `TermDef::Abs(TypeRef)` / `TermDef::Rep(TypeRef)` carry the subset
// TypeRef (`Subset(α, P)`) and represent the abstraction / projection
// functions of that subset type — `Abs : α → Subset` and `Rep :
// Subset → α`. The kernel-generated subset axioms (Phase G2) are
// asserted via UF-union against `Bool(true)` after they're built out
// of these two leaves.

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
    /// Lambda abstraction `λ(x : ty). body` (locally-nameless body).
    Lam(TypeRef, TermRef),

    // -- truth + equality --
    Bool(bool),
    Eq(TermRef, TermRef),

    // -- quantifiers + choice --
    Forall(TermRef),
    Exists(TermRef),
    Eps(TypeRef, TermRef),

    // -- subset operations (Phase G) --
    /// `Abs : α → Subset(α, P)` for the given subset TypeRef.
    Abs(TypeRef),
    /// `Rep : Subset(α, P) → α` for the given subset TypeRef.
    Rep(TypeRef),

    // -- applied primops --
    Op1(PrimOp1, TermRef),
    Op2(PrimOp2, TermRef, TermRef),

    // -- literals: arbitrary-precision --
    Nat(covalence_types::Nat),
    Int(covalence_types::Int),
    // -- byte string literal --
    Bytes(bytes::Bytes),
    // -- foreign reference (resolves into an imported arena) --
    Foreign(ImportId, TermId),
}


/// Opaque reference to a term in the current arena.
///
/// Every reference is a [`TermId`] — foreign-arena references appear
/// as [`TermDef::Foreign`] structural variants, not as a separate
/// kind of `TermRef`. To chase canonical chains across arenas use
/// [`Arena::canonical_term`](crate::Arena::canonical_term).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TermRef(u32);

impl TermRef {
    /// Build a reference to a term in the current arena.
    pub fn local(id: TermId) -> Self {
        Self(id.0)
    }

    /// The local [`TermId`] this ref points at.
    pub fn id(self) -> TermId {
        TermId(self.0)
    }

    /// Backwards-compatible alias for [`Self::id`]. Always succeeds
    /// now that there is no foreign-flag bit; returned as `Option`
    /// for source-compatibility with the legacy API.
    pub fn as_local(self) -> Option<TermId> {
        Some(TermId(self.0))
    }

    pub(crate) fn from_raw(raw: u32) -> Self {
        Self(raw)
    }

    /// Raw encoding (Phase H content hashing).
    pub(crate) fn raw(self) -> u32 {
        self.0
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
    /// Lambda binder `λ(_ : ty). body` (locally-nameless body).
    Lam(TypeRef, TermRef),

    // -- truth + equality --
    Bool(bool),
    Eq(TermRef, TermRef),

    // -- quantifiers and choice --
    Forall(TermRef),
    Exists(TermRef),
    Eps(TypeRef, TermRef),

    // -- subset operations (Phase G) --
    /// Subset abstraction function `α → Subset(α, P)`. The `TypeRef`
    /// must point at a [`crate::ty::TypeDef::Subset`] in the arena
    /// (enforced by the kernel-level type-check on the term).
    Abs(TypeRef),
    /// Subset projection function `Subset(α, P) → α`.
    Rep(TypeRef),

    // -- applied primops --
    Op1(PrimOp1, TermRef),
    Op2(PrimOp2, TermRef, TermRef),

    // -- literals: arbitrary-precision --
    IntInline(Packed64),
    IntStored(IntId),
    NatInline(Packed64),
    NatStored(NatId),

    // -- literals: byte string --
    BytesStored(BytesId),

    // -- foreign reference: a term in an imported arena. `Foreign(i,
    //    source_id)` points at `arena.imports[i]`'s term `source_id`.
    Foreign(ImportId, TermId),
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
    /// Type-ref dependencies (e.g. `Abs(TypeRef, _)`, `Eps(TypeRef, _)`)
    /// are *not* term deps and are not reported here — they're part of
    /// the shape and must match exactly.
    pub fn deps(&self) -> Deps {
        use TermDef::*;
        match *self {
            Bound(_) | Free(..) | Const(..) | Bool(_)
            | IntInline(_) | IntStored(_) | NatInline(_) | NatStored(_)
            | BytesStored(_) | Abs(_) | Rep(_) | Foreign(..) => Deps::None,
            Forall(p) | Exists(p) | Op1(_, p) => Deps::One(p),
            Eps(_, p) | Lam(_, p) => Deps::One(p),
            Comb(a, b) | Eq(a, b) | Op2(_, a, b) => Deps::Two(a, b),
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
            Lam(t, _) => Lam(t, sentinel),
            Comb(_, _) => Comb(sentinel, sentinel),
            Eq(_, _) => Eq(sentinel, sentinel),
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
