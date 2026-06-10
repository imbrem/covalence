//! The kernel's canonical symbol catalogue.
//!
//! [`Canonical`] is a non-exhaustive enum naming every type-spec or
//! term-spec the kernel ships out of the box. New variants land as
//! the derived-types catalogue grows (see `docs/type-hierarchy.md`).
//!
//! These symbols are **transparent**: structural equality on a
//! `TypeSpec<Canonical>` looks only at `ty` and `tm`. Two
//! definitions sharing a `Canonical` symbol but disagreeing on `ty`
//! or `tm` are structurally distinct — this is fine, the symbol is
//! purely display.

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

    // ---- Term-level: nat arithmetic ----
    /// `natAdd : nat → nat → nat`.
    NatAdd,
    /// `natMul : nat → nat → nat`.
    NatMul,
    /// `natSub : nat → nat → nat` (saturating at zero).
    NatSub,
    /// `natLe : nat → nat → bool`.
    NatLe,
    /// `natLt : nat → nat → bool`.
    NatLt,

    // ---- Term-level: int arithmetic ----
    /// `intAdd : int → int → int`.
    IntAdd,
    /// `intMul : int → int → int`.
    IntMul,
    /// `intSub : int → int → int`.
    IntSub,
    /// `intLe : int → int → bool`.
    IntLe,
    /// `intLt : int → int → bool`.
    IntLt,
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
            Canonical::Signed1 => "signed1",
            Canonical::Signed2 => "signed2",
            Canonical::FieldOfFractions => "fieldOfFractions",
            Canonical::Rat => "rat",
            Canonical::Real => "real",
            Canonical::F32 => "f32",
            Canonical::F64 => "f64",
            Canonical::NatAdd => "natAdd",
            Canonical::NatMul => "natMul",
            Canonical::NatSub => "natSub",
            Canonical::NatLe => "natLe",
            Canonical::NatLt => "natLt",
            Canonical::IntAdd => "intAdd",
            Canonical::IntMul => "intMul",
            Canonical::IntSub => "intSub",
            Canonical::IntLe => "intLe",
            Canonical::IntLt => "intLt",
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
    const OPACITY: Opacity = Opacity::Transparent;
}
