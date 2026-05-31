//! Term-level data: `TermDef` (one enum with structural + builtin variants)
//! and `TermRef` (local or foreign-arena reference).

use crate::id::{BitsId, BytesId, ForeignTermId, IntId, NatId, StrId, TermId};
use crate::primop::{PrimOp1, PrimOp2};
use crate::ty::TypeRef;

/// Public view of a term.
///
/// This is the stable API for inspecting terms. `TermDef` (the
/// internal storage) has one variant per primop — ~270 cases —
/// because the (tag, lhs, rhs) 3-u32 invariant requires the
/// discriminant to carry the op kind. `TermKind` folds the per-op
/// variants back into `Op1(PrimOp1, _)` and `Op2(PrimOp2, _, _)`
/// for ergonomic pattern matching.
///
/// Get one via [`Arena::kind`](crate::arena::Arena::kind).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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

    // -- literals --
    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
    I8(i8),
    I16(i16),
    I32(i32),
    I64(i64),
    IntInline(i64),
    IntStored(IntId),
    NatInline(u64),
    NatStored(NatId),
    BitsStored(BitsId),
    BytesStored(BytesId),
}

impl TermDef {
    /// Project a `TermDef` to its public-API view. The per-op
    /// variants fold into `Op1` / `Op2`; everything else maps
    /// one-to-one.
    pub fn to_kind(&self) -> TermKind {
        if let Some((op, x)) = self.as_op1() {
            return TermKind::Op1(op, x);
        }
        if let Some((op, a, b)) = self.as_op2() {
            return TermKind::Op2(op, a, b);
        }
        match *self {
            TermDef::Bound(i) => TermKind::Bound(i),
            TermDef::Free(n, t) => TermKind::Free(n, t),
            TermDef::Const(n, t) => TermKind::Const(n, t),
            TermDef::Comb(f, x) => TermKind::Comb(f, x),
            TermDef::Abs(t, b) => TermKind::Abs(t, b),
            TermDef::True => TermKind::True,
            TermDef::False => TermKind::False,
            TermDef::Eq(a, b) => TermKind::Eq(a, b),
            TermDef::Ne(a, b) => TermKind::Ne(a, b),
            TermDef::Forall(p) => TermKind::Forall(p),
            TermDef::Exists(p) => TermKind::Exists(p),
            TermDef::Eps(t, p) => TermKind::Eps(t, p),
            TermDef::Id(t) => TermKind::Id(t),
            TermDef::Comp(f, g) => TermKind::Comp(f, g),
            TermDef::Iter(n, f) => TermKind::Iter(n, f),
            TermDef::Ite(c, t) => TermKind::Ite(c, t),
            TermDef::LiftOp1(op) => TermKind::LiftOp1(op),
            TermDef::LiftOp2(op) => TermKind::LiftOp2(op),
            TermDef::U8(v) => TermKind::U8(v),
            TermDef::U16(v) => TermKind::U16(v),
            TermDef::U32(v) => TermKind::U32(v),
            TermDef::U64(v) => TermKind::U64(v),
            TermDef::I8(v) => TermKind::I8(v),
            TermDef::I16(v) => TermKind::I16(v),
            TermDef::I32(v) => TermKind::I32(v),
            TermDef::I64(v) => TermKind::I64(v),
            TermDef::IntInline(v) => TermKind::IntInline(v),
            TermDef::IntStored(v) => TermKind::IntStored(v),
            TermDef::NatInline(v) => TermKind::NatInline(v),
            TermDef::NatStored(v) => TermKind::NatStored(v),
            TermDef::BitsStored(v) => TermKind::BitsStored(v),
            TermDef::BytesStored(v) => TermKind::BytesStored(v),
            _ => unreachable!("per-op variant handled by as_op1/as_op2 above"),
        }
    }
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

/// Declares `TermDef` and impls accessor helpers — one variant per
/// `PrimOp1` / `PrimOp2` case, plus the structural / literal /
/// combinator variants written out explicitly.
///
/// Encoded as a single macro so the list of per-op variants lives in
/// exactly one place; accessors `as_op1` / `as_op2` /
/// `op1_child` / `op2_children` are generated to match the same list.
macro_rules! define_term_def {
    (
        op1: [$($op1:ident),* $(,)?],
        op2: [$($op2:ident),* $(,)?],
    ) => {
        /// The kernel's term language.
        ///
        /// Every variant payload fits in two `u32`s; combined with the
        /// enum discriminant the whole `TermDef` is 12 bytes — the (tag,
        /// lhs, rhs) 3-u32 invariant. Variable-length payloads live in
        /// arena interning tables; primop variants are one-per-op so
        /// the discriminant carries the op kind (no embedded `PrimOpN`
        /// byte).
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

            // -- literals: fixed-width --
            U8(u8), U16(u16), U32(u32), U64(u64),
            I8(i8), I16(i16), I32(i32), I64(i64),

            // -- literals: arbitrary-precision --
            IntInline(i64),
            IntStored(IntId),
            NatInline(u64),
            NatStored(NatId),

            // -- literals: bit / byte strings --
            BitsStored(BitsId),
            BytesStored(BytesId),

            // -- per-op variants: one for each PrimOp1 case --
            $( $op1(TermRef), )*

            // -- per-op variants: one for each PrimOp2 case --
            $( $op2(TermRef, TermRef), )*
        }

        impl TermDef {
            /// If this is an applied unary primop, return `(op, child)`.
            pub fn as_op1(&self) -> Option<(PrimOp1, TermRef)> {
                match self {
                    $( TermDef::$op1(x) => Some((PrimOp1::$op1, *x)), )*
                    _ => None,
                }
            }

            /// If this is an applied binary primop, return `(op, lhs, rhs)`.
            pub fn as_op2(&self) -> Option<(PrimOp2, TermRef, TermRef)> {
                match self {
                    $( TermDef::$op2(a, b) => Some((PrimOp2::$op2, *a, *b)), )*
                    _ => None,
                }
            }
        }
    };
}

define_term_def! {
    op1: [
        // booleans
        LogicalNot,
        // naturals
        NatSucc, NatPred, NatPopcount,
        // integers
        IntNeg, IntNot,
        // fixed-width unary clusters
        U8Not, U8Popcount, U8Clz, U8Ctz, U8Eqz,
        U16Not, U16Popcount, U16Clz, U16Ctz, U16Eqz,
        U32Not, U32Popcount, U32Clz, U32Ctz, U32Eqz,
        U64Not, U64Popcount, U64Clz, U64Ctz, U64Eqz,
        I8Not, I8Popcount, I8Clz, I8Ctz, I8Eqz,
        I16Not, I16Popcount, I16Clz, I16Ctz, I16Eqz,
        I32Not, I32Popcount, I32Clz, I32Ctz, I32Eqz,
        I64Not, I64Popcount, I64Clz, I64Ctz, I64Eqz,
        // bytes / bits
        BytesLen, BytesIsEmpty, BytesHead, BytesTail, BytesToBits,
        BitsLen, BitsIsEmpty, BitsToBytes,
        // casts
        NatToInt, IntToNat,
        NatToU8, NatToU16, NatToU32, NatToU64,
        U8ToNat, U16ToNat, U32ToNat, U64ToNat,
        IntToI8, IntToI16, IntToI32, IntToI64,
        I8ToInt, I16ToInt, I32ToInt, I64ToInt,
        U16ToU8, U32ToU8, U64ToU8,
        U8ToU16, U32ToU16, U64ToU16,
        U8ToU32, U16ToU32, U64ToU32,
        U8ToU64, U16ToU64, U32ToU64,
        I16ToI8, I32ToI8, I64ToI8,
        I8ToI16, I32ToI16, I64ToI16,
        I8ToI32, I16ToI32, I64ToI32,
        I8ToI64, I16ToI64, I32ToI64,
        U8ToI8, U16ToI16, U32ToI32, U64ToI64,
        I8ToU8, I16ToU16, I32ToU32, I64ToU64,
    ],
    op2: [
        // booleans
        LogicalAnd, LogicalOr, LogicalXor, LogicalNand, LogicalNor, LogicalImp,
        // naturals
        NatAdd, NatSub, NatMul, NatDiv, NatMod, NatPow,
        NatAnd, NatOr, NatXor, NatShl, NatShr,
        NatEq, NatLt, NatLe,
        // integers
        IntAdd, IntSub, IntMul, IntDiv, IntMod, IntPow,
        IntAnd, IntOr, IntXor, IntShl, IntShr,
        IntEq, IntLt, IntLe,
        // fixed-width binary
        U8Add, U8Sub, U8Mul, U8Div, U8Mod, U8Pow,
        U8And, U8Or, U8Xor, U8Shl, U8Shr, U8Rotl, U8Rotr,
        U8Eq, U8Lt, U8Le,
        U16Add, U16Sub, U16Mul, U16Div, U16Mod, U16Pow,
        U16And, U16Or, U16Xor, U16Shl, U16Shr, U16Rotl, U16Rotr,
        U16Eq, U16Lt, U16Le,
        U32Add, U32Sub, U32Mul, U32Div, U32Mod, U32Pow,
        U32And, U32Or, U32Xor, U32Shl, U32Shr, U32Rotl, U32Rotr,
        U32Eq, U32Lt, U32Le,
        U64Add, U64Sub, U64Mul, U64Div, U64Mod, U64Pow,
        U64And, U64Or, U64Xor, U64Shl, U64Shr, U64Rotl, U64Rotr,
        U64Eq, U64Lt, U64Le,
        I8Add, I8Sub, I8Mul, I8Div, I8Mod, I8Pow,
        I8And, I8Or, I8Xor, I8Shl, I8Shr, I8Rotl, I8Rotr,
        I8Eq, I8Lt, I8Le,
        I16Add, I16Sub, I16Mul, I16Div, I16Mod, I16Pow,
        I16And, I16Or, I16Xor, I16Shl, I16Shr, I16Rotl, I16Rotr,
        I16Eq, I16Lt, I16Le,
        I32Add, I32Sub, I32Mul, I32Div, I32Mod, I32Pow,
        I32And, I32Or, I32Xor, I32Shl, I32Shr, I32Rotl, I32Rotr,
        I32Eq, I32Lt, I32Le,
        I64Add, I64Sub, I64Mul, I64Div, I64Mod, I64Pow,
        I64And, I64Or, I64Xor, I64Shl, I64Shr, I64Rotl, I64Rotr,
        I64Eq, I64Lt, I64Le,
        // bytes / bits
        BytesConcat, BytesCons, BytesIndex, BytesEq,
        BitsConcat, BitsCons, BitsIndex, BitsEq,
    ],
}
