//! Primitive operations — `PrimOp1` (unary) and `PrimOp2` (binary).
//!
//! See [`docs/prover-primops.md`](../../../docs/prover-primops.md) for the
//! full catalog with type signatures, reduction semantics, and axioms.
//! This module is the canonical Rust list. New ops added here must be
//! mirrored in the primops doc.

use crate::ty::{BuiltinTy, TypeRef};

/// Convenience: convert a [`BuiltinTy`] into its [`TypeRef`].
const fn b(t: BuiltinTy) -> TypeRef {
    TypeRef::builtin(t)
}

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
    NatToU8,  NatToU16, NatToU32, NatToU64,
    U8ToNat,  U16ToNat, U32ToNat, U64ToNat,
    IntToI8,  IntToI16, IntToI32, IntToI64,
    I8ToInt,  I16ToInt, I32ToInt, I64ToInt,
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

impl PrimOp1 {
    /// Type signature `(input, output)` of this unary op.
    pub fn sig(self) -> (TypeRef, TypeRef) {
        use BuiltinTy::*;
        use PrimOp1::*;
        match self {
            LogicalNot => (b(Bool), b(Bool)),

            NatSucc | NatPred | NatPopcount => (b(Nat), b(Nat)),
            IntNeg | IntNot => (b(Int), b(Int)),

            U8Not | U8Popcount | U8Clz | U8Ctz => (b(U8), b(U8)),
            U8Eqz => (b(U8), b(Bool)),
            U16Not | U16Popcount | U16Clz | U16Ctz => (b(U16), b(U16)),
            U16Eqz => (b(U16), b(Bool)),
            U32Not | U32Popcount | U32Clz | U32Ctz => (b(U32), b(U32)),
            U32Eqz => (b(U32), b(Bool)),
            U64Not | U64Popcount | U64Clz | U64Ctz => (b(U64), b(U64)),
            U64Eqz => (b(U64), b(Bool)),
            I8Not | I8Popcount | I8Clz | I8Ctz => (b(I8), b(I8)),
            I8Eqz => (b(I8), b(Bool)),
            I16Not | I16Popcount | I16Clz | I16Ctz => (b(I16), b(I16)),
            I16Eqz => (b(I16), b(Bool)),
            I32Not | I32Popcount | I32Clz | I32Ctz => (b(I32), b(I32)),
            I32Eqz => (b(I32), b(Bool)),
            I64Not | I64Popcount | I64Clz | I64Ctz => (b(I64), b(I64)),
            I64Eqz => (b(I64), b(Bool)),

            BytesLen => (b(Bytes), b(Nat)),
            BytesIsEmpty => (b(Bytes), b(Bool)),
            BytesHead => (b(Bytes), b(U8)),
            BytesTail => (b(Bytes), b(Bytes)),
            BytesToBits => (b(Bytes), b(Bits)),
            BitsLen => (b(Bits), b(Nat)),
            BitsIsEmpty => (b(Bits), b(Bool)),
            BitsToBytes => (b(Bits), b(Bytes)),

            NatToInt => (b(Nat), b(Int)),
            IntToNat => (b(Int), b(Nat)),
            NatToU8 => (b(Nat), b(U8)),
            NatToU16 => (b(Nat), b(U16)),
            NatToU32 => (b(Nat), b(U32)),
            NatToU64 => (b(Nat), b(U64)),
            U8ToNat => (b(U8), b(Nat)),
            U16ToNat => (b(U16), b(Nat)),
            U32ToNat => (b(U32), b(Nat)),
            U64ToNat => (b(U64), b(Nat)),
            IntToI8 => (b(Int), b(I8)),
            IntToI16 => (b(Int), b(I16)),
            IntToI32 => (b(Int), b(I32)),
            IntToI64 => (b(Int), b(I64)),
            I8ToInt => (b(I8), b(Int)),
            I16ToInt => (b(I16), b(Int)),
            I32ToInt => (b(I32), b(Int)),
            I64ToInt => (b(I64), b(Int)),
            U16ToU8 => (b(U16), b(U8)),
            U32ToU8 => (b(U32), b(U8)),
            U64ToU8 => (b(U64), b(U8)),
            U8ToU16 => (b(U8), b(U16)),
            U32ToU16 => (b(U32), b(U16)),
            U64ToU16 => (b(U64), b(U16)),
            U8ToU32 => (b(U8), b(U32)),
            U16ToU32 => (b(U16), b(U32)),
            U64ToU32 => (b(U64), b(U32)),
            U8ToU64 => (b(U8), b(U64)),
            U16ToU64 => (b(U16), b(U64)),
            U32ToU64 => (b(U32), b(U64)),
            I16ToI8 => (b(I16), b(I8)),
            I32ToI8 => (b(I32), b(I8)),
            I64ToI8 => (b(I64), b(I8)),
            I8ToI16 => (b(I8), b(I16)),
            I32ToI16 => (b(I32), b(I16)),
            I64ToI16 => (b(I64), b(I16)),
            I8ToI32 => (b(I8), b(I32)),
            I16ToI32 => (b(I16), b(I32)),
            I64ToI32 => (b(I64), b(I32)),
            I8ToI64 => (b(I8), b(I64)),
            I16ToI64 => (b(I16), b(I64)),
            I32ToI64 => (b(I32), b(I64)),
            U8ToI8 => (b(U8), b(I8)),
            U16ToI16 => (b(U16), b(I16)),
            U32ToI32 => (b(U32), b(I32)),
            U64ToI64 => (b(U64), b(I64)),
            I8ToU8 => (b(I8), b(U8)),
            I16ToU16 => (b(I16), b(U16)),
            I32ToU32 => (b(I32), b(U32)),
            I64ToU64 => (b(I64), b(U64)),
        }
    }
}

impl PrimOp2 {
    /// Type signature `(arg1, arg2, output)` of this binary op.
    pub fn sig(self) -> (TypeRef, TypeRef, TypeRef) {
        use BuiltinTy::*;
        use PrimOp2::*;
        match self {
            LogicalAnd | LogicalOr | LogicalXor | LogicalNand | LogicalNor | LogicalImp => {
                (b(Bool), b(Bool), b(Bool))
            }

            NatAdd | NatSub | NatMul | NatDiv | NatMod | NatPow
            | NatAnd | NatOr | NatXor | NatShl | NatShr => (b(Nat), b(Nat), b(Nat)),
            NatEq | NatLt | NatLe => (b(Nat), b(Nat), b(Bool)),

            IntAdd | IntSub | IntMul | IntDiv | IntMod
            | IntAnd | IntOr | IntXor => (b(Int), b(Int), b(Int)),
            IntPow | IntShl | IntShr => (b(Int), b(Nat), b(Int)),
            IntEq | IntLt | IntLe => (b(Int), b(Int), b(Bool)),

            U8Add | U8Sub | U8Mul | U8Div | U8Mod
            | U8And | U8Or | U8Xor => (b(U8), b(U8), b(U8)),
            U8Pow | U8Shl | U8Shr | U8Rotl | U8Rotr => (b(U8), b(Nat), b(U8)),
            U8Eq | U8Lt | U8Le => (b(U8), b(U8), b(Bool)),

            U16Add | U16Sub | U16Mul | U16Div | U16Mod
            | U16And | U16Or | U16Xor => (b(U16), b(U16), b(U16)),
            U16Pow | U16Shl | U16Shr | U16Rotl | U16Rotr => (b(U16), b(Nat), b(U16)),
            U16Eq | U16Lt | U16Le => (b(U16), b(U16), b(Bool)),

            U32Add | U32Sub | U32Mul | U32Div | U32Mod
            | U32And | U32Or | U32Xor => (b(U32), b(U32), b(U32)),
            U32Pow | U32Shl | U32Shr | U32Rotl | U32Rotr => (b(U32), b(Nat), b(U32)),
            U32Eq | U32Lt | U32Le => (b(U32), b(U32), b(Bool)),

            U64Add | U64Sub | U64Mul | U64Div | U64Mod
            | U64And | U64Or | U64Xor => (b(U64), b(U64), b(U64)),
            U64Pow | U64Shl | U64Shr | U64Rotl | U64Rotr => (b(U64), b(Nat), b(U64)),
            U64Eq | U64Lt | U64Le => (b(U64), b(U64), b(Bool)),

            I8Add | I8Sub | I8Mul | I8Div | I8Mod
            | I8And | I8Or | I8Xor => (b(I8), b(I8), b(I8)),
            I8Pow | I8Shl | I8Shr | I8Rotl | I8Rotr => (b(I8), b(Nat), b(I8)),
            I8Eq | I8Lt | I8Le => (b(I8), b(I8), b(Bool)),

            I16Add | I16Sub | I16Mul | I16Div | I16Mod
            | I16And | I16Or | I16Xor => (b(I16), b(I16), b(I16)),
            I16Pow | I16Shl | I16Shr | I16Rotl | I16Rotr => (b(I16), b(Nat), b(I16)),
            I16Eq | I16Lt | I16Le => (b(I16), b(I16), b(Bool)),

            I32Add | I32Sub | I32Mul | I32Div | I32Mod
            | I32And | I32Or | I32Xor => (b(I32), b(I32), b(I32)),
            I32Pow | I32Shl | I32Shr | I32Rotl | I32Rotr => (b(I32), b(Nat), b(I32)),
            I32Eq | I32Lt | I32Le => (b(I32), b(I32), b(Bool)),

            I64Add | I64Sub | I64Mul | I64Div | I64Mod
            | I64And | I64Or | I64Xor => (b(I64), b(I64), b(I64)),
            I64Pow | I64Shl | I64Shr | I64Rotl | I64Rotr => (b(I64), b(Nat), b(I64)),
            I64Eq | I64Lt | I64Le => (b(I64), b(I64), b(Bool)),

            BytesConcat => (b(Bytes), b(Bytes), b(Bytes)),
            BytesCons => (b(U8), b(Bytes), b(Bytes)),
            BytesIndex => (b(Bytes), b(Nat), b(U8)),
            BytesEq => (b(Bytes), b(Bytes), b(Bool)),
            BitsConcat => (b(Bits), b(Bits), b(Bits)),
            BitsCons => (b(Bool), b(Bits), b(Bits)),
            BitsIndex => (b(Bits), b(Nat), b(Bool)),
            BitsEq => (b(Bits), b(Bits), b(Bool)),
        }
    }
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

    #[test]
    fn sample_signatures() {
        assert_eq!(PrimOp1::LogicalNot.sig(), (b(BuiltinTy::Bool), b(BuiltinTy::Bool)));
        assert_eq!(PrimOp1::U32Popcount.sig(), (b(BuiltinTy::U32), b(BuiltinTy::U32)));
        assert_eq!(PrimOp1::U64Eqz.sig(), (b(BuiltinTy::U64), b(BuiltinTy::Bool)));
        assert_eq!(
            PrimOp2::NatAdd.sig(),
            (b(BuiltinTy::Nat), b(BuiltinTy::Nat), b(BuiltinTy::Nat))
        );
        assert_eq!(
            PrimOp2::U32Shl.sig(),
            (b(BuiltinTy::U32), b(BuiltinTy::Nat), b(BuiltinTy::U32))
        );
    }
}
