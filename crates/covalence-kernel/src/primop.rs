//! Primitive operations — `PrimOp1` (unary) and `PrimOp2` (binary).
//!
//! See [`docs/prover-primops.md`](../../../docs/prover-primops.md) for the
//! full catalog with type signatures, reduction semantics, and axioms.
//! This module is the canonical Rust list. New ops added here must be
//! mirrored in the primops doc.
//!
//! Current MVP scope: booleans, naturals, integers, and bytes. Bit
//! strings and fixed-width integers (u8/…/i64) are intentionally
//! deferred — they'll come back once the kernel API has settled.

use crate::ty::{BuiltinTy, TypeRef};

/// Convenience: convert a [`BuiltinTy`] into its [`TypeRef`].
const fn b(t: BuiltinTy) -> TypeRef {
    TypeRef::builtin(t)
}

/// Unary primitive operations.
///
/// **Non-exhaustive.** Future kernel revisions can introduce new
/// primops; downstream `match`es must include a wildcard arm.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[repr(u8)]
#[non_exhaustive]
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

    // -- bytes (§7) --
    BytesLen,
    BytesIsEmpty,
    BytesTail,

    // -- casts (§8) --
    NatToInt,
    IntToNat,
}

/// Binary primitive operations.
///
/// **Non-exhaustive.** Future kernel revisions can introduce new
/// primops; downstream `match`es must include a wildcard arm.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[repr(u8)]
#[non_exhaustive]
pub enum PrimOp2 {
    // -- booleans (§1) --
    LogicalAnd,
    LogicalOr,
    LogicalXor,
    LogicalNand,
    LogicalNor,
    LogicalImp,

    // -- naturals (§3) --
    NatAdd,
    NatSub,
    NatMul,
    NatDiv,
    NatMod,
    NatPow,
    NatAnd,
    NatOr,
    NatXor,
    NatShl,
    NatShr,
    NatEq,
    NatLt,
    NatLe,

    // -- integers (§4) --
    IntAdd,
    IntSub,
    IntMul,
    IntDiv,
    IntMod,
    IntPow,
    IntAnd,
    IntOr,
    IntXor,
    IntShl,
    IntShr,
    IntEq,
    IntLt,
    IntLe,

    // -- bytes (§7) --
    BytesConcat,
    BytesEq,
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

            BytesLen => (b(Bytes), b(Nat)),
            BytesIsEmpty => (b(Bytes), b(Bool)),
            BytesTail => (b(Bytes), b(Bytes)),

            NatToInt => (b(Nat), b(Int)),
            IntToNat => (b(Int), b(Nat)),
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

            NatAdd | NatSub | NatMul | NatDiv | NatMod | NatPow | NatAnd | NatOr | NatXor
            | NatShl | NatShr => (b(Nat), b(Nat), b(Nat)),
            NatEq | NatLt | NatLe => (b(Nat), b(Nat), b(Bool)),

            IntAdd | IntSub | IntMul | IntDiv | IntMod | IntAnd | IntOr | IntXor => {
                (b(Int), b(Int), b(Int))
            }
            IntPow | IntShl | IntShr => (b(Int), b(Nat), b(Int)),
            IntEq | IntLt | IntLe => (b(Int), b(Int), b(Bool)),

            BytesConcat => (b(Bytes), b(Bytes), b(Bytes)),
            BytesEq => (b(Bytes), b(Bytes), b(Bool)),
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
        assert_ne!(PrimOp1::IntNeg, PrimOp1::NatPred);
        assert_ne!(PrimOp1::BytesLen, PrimOp1::BytesIsEmpty);
    }

    #[test]
    fn primop2_variants_distinguishable() {
        assert_ne!(PrimOp2::LogicalAnd, PrimOp2::NatAdd);
        assert_ne!(PrimOp2::NatAdd, PrimOp2::IntAdd);
        assert_ne!(PrimOp2::BytesConcat, PrimOp2::BytesEq);
    }

    #[test]
    fn sample_signatures() {
        assert_eq!(
            PrimOp1::LogicalNot.sig(),
            (b(BuiltinTy::Bool), b(BuiltinTy::Bool))
        );
        assert_eq!(
            PrimOp1::NatSucc.sig(),
            (b(BuiltinTy::Nat), b(BuiltinTy::Nat))
        );
        assert_eq!(
            PrimOp1::IntNeg.sig(),
            (b(BuiltinTy::Int), b(BuiltinTy::Int))
        );
        assert_eq!(
            PrimOp2::NatAdd.sig(),
            (b(BuiltinTy::Nat), b(BuiltinTy::Nat), b(BuiltinTy::Nat))
        );
        assert_eq!(
            PrimOp2::IntShl.sig(),
            (b(BuiltinTy::Int), b(BuiltinTy::Nat), b(BuiltinTy::Int))
        );
    }
}
