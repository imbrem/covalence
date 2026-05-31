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
            //
            // The 64-bit variants are stored as `[u32; 2]` (low, high
            // halves) rather than `u64` / `i64` directly — the latter
            // would force 8-byte enum alignment and push TermDef from
            // 12 bytes (3 u32s) to 16. Use the `*_value` accessors to
            // get the logical scalar back.
            U8(u8), U16(u16), U32(u32), U64([u32; 2]),
            I8(i8), I16(i16), I32(i32), I64([u32; 2]),

            // -- literals: arbitrary-precision --
            //
            // Same `[u32; 2]` packing applies to the inline forms.
            IntInline([u32; 2]),
            IntStored(IntId),
            NatInline([u32; 2]),
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
            /// Pack a `u64` value into the `[u32; 2]` payload used by
            /// the inline-u64 variants (`U64`, `NatInline`).
            pub const fn pack_u64(v: u64) -> [u32; 2] {
                [v as u32, (v >> 32) as u32]
            }

            /// Unpack a `[u32; 2]` back into a `u64`.
            pub const fn unpack_u64(packed: [u32; 2]) -> u64 {
                (packed[0] as u64) | ((packed[1] as u64) << 32)
            }

            /// Pack an `i64` value into a `[u32; 2]` payload.
            pub const fn pack_i64(v: i64) -> [u32; 2] {
                Self::pack_u64(v as u64)
            }

            /// Unpack a `[u32; 2]` back into an `i64`.
            pub const fn unpack_i64(packed: [u32; 2]) -> i64 {
                Self::unpack_u64(packed) as i64
            }

            /// Smart constructor for a `U64` literal — saves the
            /// caller from writing `TermDef::U64(TermDef::pack_u64(v))`.
            pub const fn u64_literal(v: u64) -> Self {
                TermDef::U64(Self::pack_u64(v))
            }

            /// Smart constructor for an `I64` literal.
            pub const fn i64_literal(v: i64) -> Self {
                TermDef::I64(Self::pack_i64(v))
            }

            /// Smart constructor for an inline `Nat`.
            pub const fn nat_inline(v: u64) -> Self {
                TermDef::NatInline(Self::pack_u64(v))
            }

            /// Smart constructor for an inline `Int`.
            pub const fn int_inline(v: i64) -> Self {
                TermDef::IntInline(Self::pack_i64(v))
            }

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
