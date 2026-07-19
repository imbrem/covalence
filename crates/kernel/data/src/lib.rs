//! Representation-independent data and numeric capabilities.
//!
//! This crate owns data vocabulary, not concrete representations or theorem
//! authority. Backends may use host values, Native HOL terms, inductive
//! encodings, WASM resources, or other carriers. Supplied law traits are
//! distinct from syntax, observation, decision, and normalization.
//!
//! The minimal logic carriers and relational vocabulary remain in
//! `covalence-logic-api`. Domain APIs such as S-expressions, Lisp, JSON, K, and
//! WASM build on this crate rather than becoming part of it.

#![forbid(unsafe_code)]

pub mod morphism;
pub mod scalar;

pub use covalence_inductive as inductive;
pub use covalence_kernel_numeric as numeric;
pub use covalence_logic_api::Logic;

pub use covalence_kernel_numeric::{
    IntAdditiveLaws, IntArithmetic, IntDecidableEquality, IntLaws, IntMultiplicativeLaws,
    IntNormalization, IntOrder, IntOrderedRingLaws, IntSyntax, NatAdditiveLaws, NatArithmetic,
    NatEqDecision, NatFreeness, NatLaws, NatMultiplicativeLaws, NatNormalization, NatOrder,
    NatRecursionLaws, NatSyntax,
};
pub use morphism::nat_bytes::{
    CanonicalNatBytes, FixedWidthError, NatBackedBytes, NatByteList, NatByteListError, Radix256Nat,
};
pub use scalar::bits::{
    BitSyntax, BitsBytesPacking, BitsBytesPackingLaws, BitsConcatLaws, BitsConstruction,
    BitsNormalization, BitsObservation, BitsSyntax, BytePacking, FixedWidthBits,
    FixedWidthBitsLaws, IntraByteOrder, PartialByte,
};
pub use scalar::bytes::{
    ByteNatBridge, ByteNatBridgeLaws, ByteSyntax, BytesConcatLaws, BytesConstruction,
    BytesNormalization, BytesObservation, BytesObservationLaws, BytesSyntax, Endianness,
    FixedWidthNatBytesConditions, FixedWidthNatBytesEncoding, FixedWidthNatBytesEncodingLaws,
    MinimalNatBytesEncoding, MinimalNatBytesEncodingLaws, NatByteSequence, NatByteSequenceBridge,
    NatByteSequenceBridgeLaws, NatBytesEquivalenceLaws, NatBytesEquivalenceSyntax,
};
pub use scalar::text::{
    CharacterSequenceSyntax, CharacterSyntax, MalformedUtf8, MalformedUtf16, MalformedUtf16Kind,
    RawByte, StringConcatLaws, StringConstruction, StringObservation, StringSyntax,
    UnicodeNormalization, UnicodeNormalizationLaws, UnicodeNormalizationSyntax, UnicodeScalar,
    Utf8DecodingSyntax, Utf8EncoderSyntax, Utf8EncodingLaws, Utf16CodeUnit, Utf16DecodingSyntax,
    Utf16EncoderSyntax, Utf16EncodingLaws, decode_utf8, decode_utf16, encode_utf8, encode_utf16,
};
