//! Fixed-width integer builtins: the WebAssembly-style `u8`…`u64` /
//! `s8`…`s64` families (arithmetic, bitwise, shifts, comparisons, casts,
//! nat/int conversions).
//!
//! The value sorts are the native Rust integer types (`u8`…`u64`,
//! `i8`…`i64` — the kernel's `sN` tags); [`FwRepr`] abstracts the eight of
//! them. Every body transcribes `covalence-core`'s
//! `builtins.rs::reduce_int_op` semantics exactly, computed the same way —
//! in 128-bit space (`value_u`/`value_s`) and re-encoded by truncation
//! ([`FwRepr::from_bits`], the `store` step):
//!
//! - arithmetic wraps mod `2^width`;
//! - signed/unsigned `div`/`rem`/`shr`/comparisons read the *type's*
//!   signedness;
//! - `x / 0 = 0` and `x rem 0 = x` (FORCED: `Div`/`Rem` have let-style
//!   catalogue bodies through `int.div`/`int.mod` / `nat.div`/`nat.mod`,
//!   so these are the bodies' values at `y = 0` — see `builtins.rs`);
//! - shift amounts are taken mod width (of the *unsigned* bit value of the
//!   right operand);
//! - `zext` zero-extends the source's unsigned bit value, `sext`
//!   sign-extends the source's two's-complement value (regardless of the
//!   source *type*'s signedness — the cast grid covers all 8×8 pairs);
//!   both then wrap into the destination width.

use std::marker::PhantomData;

use covalence_pure::{CanonRule, Op};
use covalence_types::{Int, Nat};

use crate::NamedRule;

// ============================================================================
// The eight representations
// ============================================================================

/// A fixed-width integer representation — one of `u8`…`u64` / `i8`…`i64`.
/// `value_u`/`value_s`/`from_bits` mirror `builtins.rs`'s
/// `value_u`/`value_s`/`store` on the tag/payload encoding: `value_u` is the
/// zero-extended bit pattern, `value_s` the sign-extended (two's-complement)
/// value, `from_bits` truncation to width (re-interpreted per the type).
pub trait FwRepr: Copy + Eq + Ord + std::fmt::Debug + std::hash::Hash + Default + 'static {
    /// Bit width (8/16/32/64).
    const WIDTH: u32;
    /// Whether the type reads its bits as two's complement.
    const SIGNED: bool;
    /// The kernel tag label (`"u8"`, …, `"s64"` — note `sN`, not `iN`).
    const LABEL: &'static str;
    /// The unsigned value of the bits (zero-extended into 128-bit space).
    fn value_u(self) -> u128;
    /// The two's-complement value of the bits (sign-extended), regardless
    /// of `SIGNED` — used by `sext` from unsigned sources too.
    fn value_s(self) -> i128;
    /// Truncate low bits to `WIDTH` and reinterpret per the type — the
    /// `store` step.
    fn from_bits(low: u128) -> Self;
}

macro_rules! fw_repr {
    ($t:ty, $ut:ty, $st:ty, $w:literal, $signed:literal, $label:literal) => {
        impl FwRepr for $t {
            const WIDTH: u32 = $w;
            const SIGNED: bool = $signed;
            const LABEL: &'static str = $label;
            fn value_u(self) -> u128 {
                (self as $ut) as u128
            }
            fn value_s(self) -> i128 {
                (self as $st) as i128
            }
            fn from_bits(low: u128) -> Self {
                low as $t
            }
        }
    };
}

fw_repr!(u8, u8, i8, 8, false, "u8");
fw_repr!(u16, u16, i16, 16, false, "u16");
fw_repr!(u32, u32, i32, 32, false, "u32");
fw_repr!(u64, u64, i64, 64, false, "u64");
fw_repr!(i8, u8, i8, 8, true, "s8");
fw_repr!(i16, u16, i16, 16, true, "s16");
fw_repr!(i32, u32, i32, 32, true, "s32");
fw_repr!(i64, u64, i64, 64, true, "s64");

// ============================================================================
// Shared arithmetic (transcribed from builtins.rs::int_binop / int_unary)
// ============================================================================

/// Low-`width`-bits mask — transcribes `builtins.rs::width_mask`.
fn width_mask(width: u32) -> u128 {
    if width >= 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    }
}

/// Shift amount: the right operand's unsigned bit value mod width.
fn fw_shift_amount<T: FwRepr>(b: T) -> u32 {
    (b.value_u() % T::WIDTH as u128) as u32
}

/// Truncating division; `x / 0 = 0` (FORCED — see the module docs).
/// TCB: keep the explicit `= 0` branch mirroring the signed/`Rem` arms
/// rather than restructuring into `checked_div` (matches `builtins.rs`).
#[allow(clippy::manual_checked_ops)]
fn fw_div<T: FwRepr>(a: T, b: T) -> T {
    if T::SIGNED {
        let bv = b.value_s();
        if bv == 0 {
            T::from_bits(0)
        } else {
            T::from_bits(a.value_s().wrapping_div(bv) as u128)
        }
    } else {
        let bu = b.value_u();
        if bu == 0 {
            T::from_bits(0)
        } else {
            T::from_bits(a.value_u() / bu)
        }
    }
}

/// Truncating remainder (dividend's sign); `x rem 0 = x` (FORCED).
#[allow(clippy::manual_checked_ops)]
fn fw_rem<T: FwRepr>(a: T, b: T) -> T {
    if T::SIGNED {
        let bv = b.value_s();
        if bv == 0 {
            a
        } else {
            T::from_bits(a.value_s().wrapping_rem(bv) as u128)
        }
    } else {
        let bu = b.value_u();
        if bu == 0 {
            a
        } else {
            T::from_bits(a.value_u() % bu)
        }
    }
}

/// Low `width` bits of a `Nat`, via its little-endian byte encoding —
/// transcribes `builtins.rs::nat_low_bits`.
fn nat_low_bits(n: &Nat, width: u32) -> u128 {
    let bytes = n.to_bytes_le();
    let nbytes = width.div_ceil(8) as usize;
    let mut acc: u128 = 0;
    for i in 0..nbytes {
        if let Some(&b) = bytes.get(i) {
            acc |= (b as u128) << (8 * i);
        }
    }
    acc & width_mask(width)
}

// ============================================================================
// Op ZST macros
// ============================================================================

/// A binary fixed-width op `T → T → $out`, generic over the representation.
macro_rules! fw_op2 {
    (
        $(#[$doc:meta])*
        $name:ident($frag:literal): ($a:ident, $b:ident) => $out:ty,
        $body:expr
    ) => {
        $(#[$doc])*
        #[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
        pub struct $name<T>(PhantomData<T>);

        impl<T> $name<T> {
            /// The op value (a ZST).
            pub const fn new() -> Self {
                Self(PhantomData)
            }
        }

        impl<T: FwRepr> Op for $name<T> {
            type In = (T, T);
            type Out = $out;
        }

        impl<T: FwRepr> CanonRule for $name<T> {
            fn eval(&self, &($a, $b): &Self::In) -> Self::Out {
                $body
            }
        }

        impl<T: FwRepr> NamedRule for $name<T> {
            fn name() -> String {
                format!("{}.{}", T::LABEL, $frag)
            }
        }
    };
}

/// A unary fixed-width op `$in → $out`, generic over the representation.
macro_rules! fw_op1 {
    (
        $(#[$doc:meta])*
        $name:ident($frag:literal): |$a:ident : $in:ty| => $out:ty,
        $body:expr
    ) => {
        $(#[$doc])*
        #[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
        pub struct $name<T>(PhantomData<T>);

        impl<T> $name<T> {
            /// The op value (a ZST).
            pub const fn new() -> Self {
                Self(PhantomData)
            }
        }

        impl<T: FwRepr> Op for $name<T> {
            type In = $in;
            type Out = $out;
        }

        impl<T: FwRepr> CanonRule for $name<T> {
            fn eval(&self, $a: &Self::In) -> Self::Out {
                $body
            }
        }

        impl<T: FwRepr> NamedRule for $name<T> {
            fn name() -> String {
                format!("{}.{}", T::LABEL, $frag)
            }
        }
    };
}

// ---- binary arithmetic / bitwise ----

fw_op2! {
    /// `T.add` — wrapping addition mod `2^width`.
    FwAdd("add"): (a, b) => T,
    T::from_bits(a.value_u().wrapping_add(b.value_u()))
}
fw_op2! {
    /// `T.sub` — wrapping subtraction mod `2^width`.
    FwSub("sub"): (a, b) => T,
    T::from_bits(a.value_u().wrapping_sub(b.value_u()))
}
fw_op2! {
    /// `T.mul` — wrapping multiplication mod `2^width`.
    FwMul("mul"): (a, b) => T,
    T::from_bits(a.value_u().wrapping_mul(b.value_u()))
}
fw_op2! {
    /// `T.div` — truncating division; `x / 0 = 0` (FORCED).
    FwDiv("div"): (a, b) => T,
    fw_div(a, b)
}
fw_op2! {
    /// `T.rem` — truncating remainder (dividend's sign); `x rem 0 = x`
    /// (FORCED).
    FwRem("rem"): (a, b) => T,
    fw_rem(a, b)
}
fw_op2! {
    /// `T.and` — bitwise and.
    FwAnd("and"): (a, b) => T,
    T::from_bits(a.value_u() & b.value_u())
}
fw_op2! {
    /// `T.or` — bitwise or.
    FwOr("or"): (a, b) => T,
    T::from_bits(a.value_u() | b.value_u())
}
fw_op2! {
    /// `T.xor` — bitwise xor.
    FwXor("xor"): (a, b) => T,
    T::from_bits(a.value_u() ^ b.value_u())
}
fw_op2! {
    /// `T.shl` — left shift by the right operand's bit value mod width.
    FwShl("shl"): (a, b) => T,
    T::from_bits(a.value_u() << fw_shift_amount(b))
}
fw_op2! {
    /// `T.shr` — right shift by the right operand's bit value mod width;
    /// arithmetic for `sN`, logical for `uN`.
    FwShr("shr"): (a, b) => T,
    {
        let s = fw_shift_amount(b);
        if T::SIGNED {
            T::from_bits((a.value_s() >> s) as u128)
        } else {
            T::from_bits(a.value_u() >> s)
        }
    }
}

// ---- comparisons (signedness from the type) ----

fw_op2! {
    /// `T.lt`.
    FwLt("lt"): (a, b) => bool,
    if T::SIGNED { a.value_s() < b.value_s() } else { a.value_u() < b.value_u() }
}
fw_op2! {
    /// `T.le`.
    FwLe("le"): (a, b) => bool,
    if T::SIGNED { a.value_s() <= b.value_s() } else { a.value_u() <= b.value_u() }
}
fw_op2! {
    /// `T.gt`.
    FwGt("gt"): (a, b) => bool,
    if T::SIGNED { a.value_s() > b.value_s() } else { a.value_u() > b.value_u() }
}
fw_op2! {
    /// `T.ge`.
    FwGe("ge"): (a, b) => bool,
    if T::SIGNED { a.value_s() >= b.value_s() } else { a.value_u() >= b.value_u() }
}

// ---- unary ----

fw_op1! {
    /// `T.neg` — two's-complement negation (wrapping).
    FwNeg("neg"): |a: T| => T,
    T::from_bits(0u128.wrapping_sub(a.value_u()))
}
fw_op1! {
    /// `T.not` — bitwise complement.
    FwNot("not"): |a: T| => T,
    T::from_bits(!a.value_u())
}

// ---- nat / int conversions ----

fw_op1! {
    /// `T.toNat` — the unsigned value of the bits.
    FwToNat("toNat"): |a: T| => Nat,
    Nat::from(a.value_u())
}
fw_op1! {
    /// `T.toInt` — the value of the bits (signed for `sN`).
    FwToInt("toInt"): |a: T| => Int,
    if T::SIGNED { Int::from(a.value_s()) } else { Int::from(a.value_u()) }
}
fw_op1! {
    /// `T.fromNat` — wrap a nat into `T` (mod `2^width`).
    FwFromNat("fromNat"): |n: Nat| => T,
    T::from_bits(nat_low_bits(n, T::WIDTH))
}
fw_op1! {
    /// `T.fromInt` — wrap an int into `T` (two's complement).
    FwFromInt("fromInt"): |z: Int| => T,
    {
        let w = T::WIDTH;
        let mag_low = nat_low_bits(&z.abs(), w);
        let low = if z.is_negative() {
            (width_mask(w) + 1).wrapping_sub(mag_low) & width_mask(w)
        } else {
            mag_low
        };
        T::from_bits(low)
    }
}

// ---- the 8×8 cast grid ----

/// `src.zext.dst` — zero-extend the source's unsigned bit value, then wrap
/// to the destination width. Doubles as `wrap` when the destination is
/// narrower.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Zext<S, D>(PhantomData<(S, D)>);

impl<S, D> Zext<S, D> {
    /// The op value (a ZST).
    pub const fn new() -> Self {
        Self(PhantomData)
    }
}

impl<S: FwRepr, D: FwRepr> Op for Zext<S, D> {
    type In = S;
    type Out = D;
}

impl<S: FwRepr, D: FwRepr> CanonRule for Zext<S, D> {
    fn eval(&self, a: &S) -> D {
        D::from_bits(a.value_u())
    }
}

impl<S: FwRepr, D: FwRepr> NamedRule for Zext<S, D> {
    fn name() -> String {
        format!("{}.zext.{}", S::LABEL, D::LABEL)
    }
}

/// `src.sext.dst` — sign-extend the source's two's-complement bit value
/// (regardless of the source *type*'s signedness), then wrap to the
/// destination width.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Sext<S, D>(PhantomData<(S, D)>);

impl<S, D> Sext<S, D> {
    /// The op value (a ZST).
    pub const fn new() -> Self {
        Self(PhantomData)
    }
}

impl<S: FwRepr, D: FwRepr> Op for Sext<S, D> {
    type In = S;
    type Out = D;
}

impl<S: FwRepr, D: FwRepr> CanonRule for Sext<S, D> {
    fn eval(&self, a: &S) -> D {
        D::from_bits(a.value_s() as u128)
    }
}

impl<S: FwRepr, D: FwRepr> NamedRule for Sext<S, D> {
    fn name() -> String {
        format!("{}.sext.{}", S::LABEL, D::LABEL)
    }
}
