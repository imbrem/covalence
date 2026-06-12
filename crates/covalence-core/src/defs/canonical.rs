//! The kernel's canonical symbol catalogue.
//!
//! [`Canonical`] is a non-exhaustive enum naming every type-spec or
//! term-spec the kernel ships out of the box. New variants land as
//! the derived-types catalogue grows (see `docs/type-hierarchy.md`).
//!
//! These symbols are **transparent**: structural equality on a
//! `TypeSpec` looks only at `ty` and `tm`. Two definitions sharing a
//! `Canonical` symbol but disagreeing on `ty` or `tm` are
//! structurally distinct — this is fine, the symbol is purely
//! display.

use super::symbol::{Opacity, Symbol};
use std::fmt;

/// Names for the kernel's derived-type / derived-term catalogue.
///
/// The `#[non_exhaustive]` attribute lets us add new variants
/// without breaking downstream `match` users.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Canonical {
    // ---- Relational/algebraic primitives ----
    /// `set 'a := 'a → bool`.
    Set,
    /// `rel 'a 'b := 'a → 'b → bool`.
    Rel,
    /// `preord 'a := rel 'a 'a where (trans, refl)`.
    Preord,
    /// `pord 'a := rel 'a 'a where (trans, refl, antisym)`.
    Pord,
    /// `per 'a := rel 'a 'a where (trans, sym)`.
    Per,
    /// `part 'a := rel 'a 'a where (trans, sym, refl)`.
    Part,

    // ---- Product / coproduct ----
    /// `coprod 'a 'b := rel 'a 'b where (\R. (∃a. R = λx _. x = a) ∨ (∃b. R = λ_ y. y = b))`.
    Coprod,
    /// `prod 'a 'b := rel 'a 'b where (\R. ∃a b. R = λx y. x = a ∧ y = b)`.
    Prod,

    // ---- Fixed-width unsigned integers ----
    /// `u1 := coprod unit unit` (bit).
    Bit,
    /// `u2 := coprod bit bit` (crumb).
    U2,
    /// `u4 := coprod u2 u2` (nybble).
    U4,
    /// `u8 := coprod u4 u4` (byte).
    U8,
    /// `u16 := coprod u8 u8`.
    U16,
    /// `u32 := coprod u16 u16` (word).
    U32,
    /// `u64 := coprod u32 u32` (dword).
    U64,
    /// `u128 := coprod u64 u64` (qword).
    U128,
    /// `u256 := coprod u128 u128` (yword).
    U256,
    /// `u512 := coprod u256 u256` (zword).
    U512,
    /// `bits := list bool`.
    Bits,
    /// `fin n := coprod (fin (n-1)) unit` (fixed-size finite type).
    Fin,

    // ---- Container types ----
    /// `option 'a := coprod 'a unit`.
    Option,
    /// `stream 'a := nat → 'a`.
    Stream,
    /// `list 'a := stream (option 'a) where (eventually-none)`.
    List,
    /// `result 'a 'b := coprod 'a 'b`.
    Result,

    // ---- Bytes / blobs ----
    /// `blob := list u8`.
    Blob,
    /// `bytesCat : bytes → bytes → bytes` — concatenation.
    BytesCat,
    /// `bytesConsNat : nat → bytes → bytes` — cons a nat (mod 256).
    BytesConsNat,
    /// `bytesLen : bytes → nat` — length.
    BytesLen,
    /// `bytesAt : bytes → nat → nat` — byte at index (0 if OOB).
    BytesAt,
    /// `bytesSlice : bytes → nat → nat → bytes` — saturating slice.
    BytesSlice,

    // ---- Signed integers and beyond ----
    /// `signed1 'a := prod bit 'a` (a or −a).
    Signed1,
    /// `signed2 'a := prod bit 'a` (a or −(a+1)) — two's-complement-ish.
    Signed2,

    // ---- Rationals / reals / floats ----
    /// `fieldOfFractions[mul, zero] 'a := prod 'a 'a quot (standard)`.
    FieldOfFractions,
    /// `rat := fieldOfFractions int`.
    Rat,
    /// `real := { rat } close ratLe` — Dedekind cuts.
    Real,
    /// `f32 := u32` (bitwise).
    F32,
    /// `f64 := u64` (bitwise).
    F64,

    // ---- Term-level: option constructors ----
    /// `none : option 'a`.
    None,
    /// `some : 'a → option 'a`.
    Some,

    // ---- Term-level: result constructors ----
    /// `ok : 'a → result 'a 'b` — successful result.
    Ok,
    /// `err : 'b → result 'a 'b` — error result.
    Err,

    // ---- Term-level: list operations ----
    /// `nil : list 'a`.
    Nil,
    /// `cons : 'a → list 'a → list 'a`.
    Cons,
    /// `head : list 'a → option 'a`.
    Head,
    /// `tail : list 'a → list 'a`.
    Tail,

    // ---- Term-level: nat arithmetic ----
    /// `natSucc : nat → nat` — the constructor `λn. n + 1`. Closed
    /// forms reduce via `builtins::reduce_spec`.
    NatSucc,
    /// `natPred : nat → nat` — saturating predecessor (`0 - 1 = 0`).
    NatPred,
    /// `natRec : 'a → (nat → 'a → 'a) → nat → 'a` — primitive recursor.
    /// Selector predicate: the standard `r z f 0 = z` and
    /// `r z f (S n) = f n (r z f n)` equations.
    NatRec,
    /// `iter : nat → ('a → 'a) → 'a → 'a` — apply `f` to `a` `n`
    /// times. Defined as `λn f a. natRec a (λ_. f) n`.
    Iter,
    /// `natAdd : nat → nat → nat`.
    NatAdd,
    /// `natMul : nat → nat → nat`.
    NatMul,
    /// `natSub : nat → nat → nat` (saturating at zero).
    NatSub,
    /// `natDiv : nat → nat → nat` (Euclidean, n/0 = 0).
    NatDiv,
    /// `natMod : nat → nat → nat` (Euclidean, n%0 = 0).
    NatMod,
    /// `natPow : nat → nat → nat`.
    NatPow,
    /// `natLe : nat → nat → bool`.
    NatLe,
    /// `natLt : nat → nat → bool`.
    NatLt,
    /// `natToInt : nat → int`.
    NatToInt,
    /// `natShl : nat → nat → nat` — left shift by `n` (i.e. `* 2^n`).
    NatShl,
    /// `natShr : nat → nat → nat` — right shift by `n` (i.e. `/ 2^n`,
    /// truncating toward zero).
    NatShr,
    /// `natBitAnd : nat → nat → nat` — bitwise AND.
    NatBitAnd,
    /// `natBitOr : nat → nat → nat` — bitwise OR.
    NatBitOr,
    /// `natBitXor : nat → nat → nat` — bitwise XOR.
    NatBitXor,
    /// `natToBytesLe : nat → blob` — minimal little-endian byte encoding.
    NatToBytesLe,
    /// `natToBytesBe : nat → blob` — minimal big-endian byte encoding.
    NatToBytesBe,
    /// `natFromBytesLe : blob → nat` — decode little-endian.
    NatFromBytesLe,
    /// `natFromBytesBe : blob → nat` — decode big-endian.
    NatFromBytesBe,

    // ---- Term-level: int arithmetic ----
    /// `intSucc : int → int` — `λz. z + 1`. Closed forms reduce via
    /// `builtins::reduce_spec`.
    IntSucc,
    /// `intPred : int → int` — `λz. z − 1`.
    IntPred,
    /// `intAdd : int → int → int`.
    IntAdd,
    /// `intMul : int → int → int`.
    IntMul,
    /// `intSub : int → int → int`.
    IntSub,
    /// `intDiv : int → int → int` (Euclidean, n/0 = 0).
    IntDiv,
    /// `intMod : int → int → int` (Euclidean, n%0 = 0).
    IntMod,
    /// `intNeg : int → int` (unary minus).
    IntNeg,
    /// `intAbs : int → nat`.
    IntAbs,
    /// `intSgn : int → int` (−1, 0, or 1).
    IntSgn,
    /// `intLe : int → int → bool`.
    IntLe,
    /// `intLt : int → int → bool`.
    IntLt,

    // ---- Term-level: list operations ----
    /// `listLength : list 'a → nat`.
    ListLength,
    /// `listCat : list 'a → list 'a → list 'a`.
    ListCat,
    /// `listMap : ('a → 'b) → list 'a → list 'b`.
    ListMap,
    /// `listFilter : ('a → bool) → list 'a → list 'a`.
    ListFilter,
    /// `listFoldr : ('a → 'b → 'b) → 'b → list 'a → 'b`.
    ListFoldr,
    /// `listFoldl : ('b → 'a → 'b) → 'b → list 'a → 'b`.
    ListFoldl,
    /// `listTake : nat → list 'a → list 'a`.
    ListTake,
    /// `listSkip : nat → list 'a → list 'a`.
    ListSkip,
    /// `listIndex : nat → list 'a → option 'a`.
    ListIndex,
    /// `listRepeat : nat → 'a → list 'a`.
    ListRepeat,
    /// `listFlatten : list (list 'a) → list 'a`.
    ListFlatten,

    // ---- Term-level: set operations ----
    /// `setUnion : set 'a → set 'a → set 'a`.
    SetUnion,
    /// `setIntersect : set 'a → set 'a → set 'a`.
    SetIntersect,
    /// `setDiff : set 'a → set 'a → set 'a`.
    SetDiff,
    /// `setSubset : set 'a → set 'a → bool`.
    SetSubset,
    /// `setCard : set 'a → nat`.
    SetCard,
    /// `listToSet : list 'a → set 'a`.
    ListToSet,
}

impl Canonical {
    /// Human-readable label used in `Display` output and S-exp
    /// serialisation.
    pub fn label(&self) -> &'static str {
        match self {
            Canonical::Set => "set",
            Canonical::Rel => "rel",
            Canonical::Preord => "preord",
            Canonical::Pord => "pord",
            Canonical::Per => "per",
            Canonical::Part => "part",
            Canonical::Coprod => "coprod",
            Canonical::Prod => "prod",
            Canonical::Bit => "bit",
            Canonical::U2 => "u2",
            Canonical::U4 => "u4",
            Canonical::U8 => "u8",
            Canonical::U16 => "u16",
            Canonical::U32 => "u32",
            Canonical::U64 => "u64",
            Canonical::U128 => "u128",
            Canonical::U256 => "u256",
            Canonical::U512 => "u512",
            Canonical::Bits => "bits",
            Canonical::Fin => "fin",
            Canonical::Option => "option",
            Canonical::Stream => "stream",
            Canonical::List => "list",
            Canonical::Result => "result",
            Canonical::Blob => "blob",
            Canonical::BytesCat => "bytesCat",
            Canonical::BytesConsNat => "bytesConsNat",
            Canonical::BytesLen => "bytesLen",
            Canonical::BytesAt => "bytesAt",
            Canonical::BytesSlice => "bytesSlice",
            Canonical::Signed1 => "signed1",
            Canonical::Signed2 => "signed2",
            Canonical::FieldOfFractions => "fieldOfFractions",
            Canonical::Rat => "rat",
            Canonical::Real => "real",
            Canonical::F32 => "f32",
            Canonical::F64 => "f64",
            Canonical::None => "none",
            Canonical::Some => "some",
            Canonical::Ok => "ok",
            Canonical::Err => "err",
            Canonical::Nil => "nil",
            Canonical::Cons => "cons",
            Canonical::Head => "head",
            Canonical::Tail => "tail",
            Canonical::NatSucc => "natSucc",
            Canonical::NatPred => "natPred",
            Canonical::NatRec => "natRec",
            Canonical::Iter => "iter",
            Canonical::NatAdd => "natAdd",
            Canonical::NatMul => "natMul",
            Canonical::NatSub => "natSub",
            Canonical::NatDiv => "natDiv",
            Canonical::NatMod => "natMod",
            Canonical::NatPow => "natPow",
            Canonical::NatLe => "natLe",
            Canonical::NatLt => "natLt",
            Canonical::NatToInt => "natToInt",
            Canonical::NatShl => "natShl",
            Canonical::NatShr => "natShr",
            Canonical::NatBitAnd => "natBitAnd",
            Canonical::NatBitOr => "natBitOr",
            Canonical::NatBitXor => "natBitXor",
            Canonical::NatToBytesLe => "natToBytesLe",
            Canonical::NatToBytesBe => "natToBytesBe",
            Canonical::NatFromBytesLe => "natFromBytesLe",
            Canonical::NatFromBytesBe => "natFromBytesBe",
            Canonical::IntSucc => "intSucc",
            Canonical::IntPred => "intPred",
            Canonical::IntAdd => "intAdd",
            Canonical::IntMul => "intMul",
            Canonical::IntSub => "intSub",
            Canonical::IntDiv => "intDiv",
            Canonical::IntMod => "intMod",
            Canonical::IntNeg => "intNeg",
            Canonical::IntAbs => "intAbs",
            Canonical::IntSgn => "intSgn",
            Canonical::IntLe => "intLe",
            Canonical::IntLt => "intLt",
            Canonical::ListLength => "listLength",
            Canonical::ListCat => "listCat",
            Canonical::ListMap => "listMap",
            Canonical::ListFilter => "listFilter",
            Canonical::ListFoldr => "listFoldr",
            Canonical::ListFoldl => "listFoldl",
            Canonical::ListTake => "listTake",
            Canonical::ListSkip => "listSkip",
            Canonical::ListIndex => "listIndex",
            Canonical::ListRepeat => "listRepeat",
            Canonical::ListFlatten => "listFlatten",
            Canonical::SetUnion => "setUnion",
            Canonical::SetIntersect => "setIntersect",
            Canonical::SetDiff => "setDiff",
            Canonical::SetSubset => "setSubset",
            Canonical::SetCard => "setCard",
            Canonical::ListToSet => "listToSet",
        }
    }
}

impl fmt::Display for Canonical {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.label())
    }
}

impl Symbol for Canonical {
    /// Canonical kernel symbols are *transparent*: the symbol is a
    /// display label only; structural equality on a spec depends on
    /// `ty` and `tm`. Two `Canonical` symbols with identical
    /// definitions are structurally interchangeable.
    fn opacity(&self) -> Opacity {
        Opacity::Transparent
    }
    fn label(&self) -> &str {
        Canonical::label(self)
    }
}
