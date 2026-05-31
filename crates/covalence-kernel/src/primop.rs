//! Primitive operations — `PrimOp1` (unary) and `PrimOp2` (binary).
//!
//! See [`docs/prover-primops.md`](../../../docs/prover-primops.md) for the
//! full catalog with type signatures, reduction semantics, and axioms.
//! This module is the canonical Rust list. New ops added here must be
//! mirrored in the primops doc.
//!
//! Both enums are `#[repr(u8)]` and `Copy`. Variant count fits in a u8
//! discriminant (currently <256 each), so embedding them in `TermDef`
//! variants like `LiftOp1(PrimOp1)` keeps payloads small.

/// Unary primitive operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[repr(u8)]
pub enum PrimOp1 {
    // -- booleans (§1) --
    LogicalNot,

    // -- naturals (§3) --
    NatSucc,
    NatPred,
    NatPopcount,

    // -- integers (§4) --
    IntNeg,
    IntNot,

    // -- fixed-width unary (§5): one cluster per type --
    U8Not, U8Popcount, U8Clz, U8Ctz, U8Eqz,
    U16Not, U16Popcount, U16Clz, U16Ctz, U16Eqz,
    U32Not, U32Popcount, U32Clz, U32Ctz, U32Eqz,
    U64Not, U64Popcount, U64Clz, U64Ctz, U64Eqz,
    I8Not, I8Popcount, I8Clz, I8Ctz, I8Eqz,
    I16Not, I16Popcount, I16Clz, I16Ctz, I16Eqz,
    I32Not, I32Popcount, I32Clz, I32Ctz, I32Eqz,
    I64Not, I64Popcount, I64Clz, I64Ctz, I64Eqz,

    // -- bytes (§7) --
    BytesLen,
    BytesIsEmpty,
    BytesHead,
    BytesTail,
    BytesToBits,

    // -- bits (§6) --
    BitsLen,
    BitsIsEmpty,
    BitsToBytes,

    // -- casts (§8) --
    NatToInt,
    IntToNat,
    // nat ↔ uN
    NatToU8,  NatToU16, NatToU32, NatToU64,
    U8ToNat,  U16ToNat, U32ToNat, U64ToNat,
    // int ↔ iN
    IntToI8,  IntToI16, IntToI32, IntToI64,
    I8ToInt,  I16ToInt, I32ToInt, I64ToInt,
    // uN ↔ uM (truncate / zero-extend)
    U16ToU8, U32ToU8, U64ToU8,
    U8ToU16, U32ToU16, U64ToU16,
    U8ToU32, U16ToU32, U64ToU32,
    U8ToU64, U16ToU64, U32ToU64,
    // iN ↔ iM (truncate / sign-extend)
    I16ToI8, I32ToI8, I64ToI8,
    I8ToI16, I32ToI16, I64ToI16,
    I8ToI32, I16ToI32, I64ToI32,
    I8ToI64, I16ToI64, I32ToI64,
    // sign reinterpretation
    U8ToI8, U16ToI16, U32ToI32, U64ToI64,
    I8ToU8, I16ToU16, I32ToU32, I64ToU64,
}

/// Binary primitive operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[repr(u8)]
pub enum PrimOp2 {
    // -- booleans (§1) --
    LogicalAnd,
    LogicalOr,
    LogicalXor,
    LogicalNand,
    LogicalNor,
    LogicalImp,

    // -- naturals (§3) --
    NatAdd, NatSub, NatMul, NatDiv, NatMod, NatPow,
    NatAnd, NatOr, NatXor, NatShl, NatShr,
    NatEq, NatLt, NatLe,

    // -- integers (§4) --
    IntAdd, IntSub, IntMul, IntDiv, IntMod, IntPow,
    IntAnd, IntOr, IntXor, IntShl, IntShr,
    IntEq, IntLt, IntLe,

    // -- fixed-width binary (§5) --
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

    // -- bytes (§7) --
    BytesConcat,
    BytesCons,
    BytesIndex,
    BytesEq,

    // -- bits (§6) --
    BitsConcat,
    BitsCons,
    BitsIndex,
    BitsEq,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn primops_are_copy_and_small() {
        fn assert_copy<T: Copy>() {}
        assert_copy::<PrimOp1>();
        assert_copy::<PrimOp2>();
        assert_eq!(std::mem::size_of::<PrimOp1>(), 1);
        assert_eq!(std::mem::size_of::<PrimOp2>(), 1);
    }

    #[test]
    fn primop1_variants_distinguishable() {
        // sanity: a few key variants distinct.
        assert_ne!(PrimOp1::LogicalNot, PrimOp1::NatSucc);
        assert_ne!(PrimOp1::U8Not, PrimOp1::U16Not);
        assert_ne!(PrimOp1::BytesLen, PrimOp1::BitsLen);
    }

    #[test]
    fn primop2_variants_distinguishable() {
        assert_ne!(PrimOp2::LogicalAnd, PrimOp2::NatAdd);
        assert_ne!(PrimOp2::U8Add, PrimOp2::U16Add);
        assert_ne!(PrimOp2::NatAdd, PrimOp2::IntAdd);
    }
}
