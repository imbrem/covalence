//! Bit strings and fixed-width unsigned integers.
//!
//! ⚠️ **TODO-level definitions** (broadly-correct shapes, not
//! finalized — see the `defs` module docs).
//!
//! `bits := list bool` is the type of variable-length bit strings (a
//! list of booleans). Every fixed-width type is then a **subtype** of
//! `bits` carved out by a length predicate:
//!
//! ```text
//! bit (u1) := { v : bits | length v = 1 }
//! u2       := { v : bits | length v = 2 }
//! u4       := { v : bits | length v = 4 }
//! u8       := { v : bits | length v = 8 }
//! …    u512 := { v : bits | length v = 512 }
//! ```
//!
//! so `uN` is exactly the bit strings of length `N` (`2^N` values).
//! Rather than a product chain (`u{2n} := prod u{n} u{n}`), which would
//! duplicate the bit-string structure at every width, the structure
//! lives once in `list` and each width is just a length restriction.

use std::sync::LazyLock;

use crate::hol;
use crate::term::{Term, Type};

use super::canonical::Canonical;
use super::list::{list, list_length};
use super::spec::TypeSpec;

/// `bits := list bool` — variable-length bit strings. A newtype over
/// `list bool`; the list structure lives in `list`, not duplicated
/// here. Cross between `bits` and `list bool` via the `abs`/`rep`
/// bridge ([`Term::spec_abs`] / [`Term::spec_rep`]).
pub fn bits_spec() -> TypeSpec {
    static LAZY: LazyLock<TypeSpec> = LazyLock::new(|| {
        let carrier = list(Type::bool());
        TypeSpec::newtype(Canonical::Bits, carrier)
    });
    LAZY.clone()
}
pub fn bits_ty() -> Type {
    static LAZY: LazyLock<Type> = LazyLock::new(|| Type::spec(bits_spec(), vec![]));
    LAZY.clone()
}

/// Body of `bits.len`: `λv:bits. list.length (rep v)` — the
/// bit-string length, computed on the underlying `list bool`.
fn bits_len_body() -> Term {
    let v = Term::free("v", bits_ty());
    let rep_v = Term::app(Term::spec_rep(bits_spec(), Vec::new()), v);
    let len = Term::app(list_length(Type::bool()), rep_v);
    hol::pub_abs("v", bits_ty(), len)
}

let_term! {
    /// `bits.len : bits → nat` ≡ `λv. list.length (rep v)` — the number
    /// of bits in a bit string, via the underlying `list bool`.
    bits_len_spec, bits_len, Canonical::BitsLen, bits_len_body()
}

/// `λv:bits. bits.len v = width` — the selector predicate carving the
/// width-`width` bitvectors out of `bits`.
fn width_predicate(width: u64) -> Term {
    let v = Term::free("v", bits_ty());
    let len = Term::app(bits_len(), v);
    let eq = hol::hol_eq(len, Term::nat_lit(width));
    hol::pub_abs("v", bits_ty(), eq)
}

/// `uN := { v : bits | length v = width }` — a fresh symbol for the
/// fixed-width bitvectors, a subtype of `bits` restricted to length
/// `width`. Reuses `bits`' (and hence `list`'s) structure rather than
/// re-stating it.
fn fixed_width_spec(symbol: Canonical, width: u64) -> TypeSpec {
    TypeSpec::subtype(symbol, bits_ty(), width_predicate(width))
}

macro_rules! width {
    ($spec_fn:ident, $type_fn:ident, $canon:expr, $width:expr) => {
        pub fn $spec_fn() -> TypeSpec {
            static LAZY: LazyLock<TypeSpec> = LazyLock::new(|| fixed_width_spec($canon, $width));
            LAZY.clone()
        }
        pub fn $type_fn() -> Type {
            static LAZY: LazyLock<Type> = LazyLock::new(|| Type::spec($spec_fn(), vec![]));
            LAZY.clone()
        }
    };
}

width!(bit_spec, bit_ty, Canonical::Bit, 1);
width!(u2_spec, u2_ty, Canonical::U2, 2);
width!(u4_spec, u4_ty, Canonical::U4, 4);
width!(u8_spec, u8_ty, Canonical::U8, 8);
width!(u16_spec, u16_ty, Canonical::U16, 16);
width!(u32_spec, u32_ty, Canonical::U32, 32);
width!(u64_spec, u64_ty, Canonical::U64, 64);
width!(u128_spec, u128_ty, Canonical::U128, 128);
width!(u256_spec, u256_ty, Canonical::U256, 256);
width!(u512_spec, u512_ty, Canonical::U512, 512);

/// `sN := uN` — a signed fixed-width integer as a thin newtype over
/// the unsigned `uN` of the same width. Same bit representation
/// (`uN`'s carrier), distinct type; the signed *interpretation* of
/// those bits is an operation concern, not a representational one.
/// Matches the WebAssembly component model's signed integers.
fn signed_width_spec(symbol: Canonical, unsigned: Type) -> TypeSpec {
    TypeSpec::newtype(symbol, unsigned)
}

macro_rules! signed_width {
    ($spec_fn:ident, $type_fn:ident, $canon:expr, $unsigned_ty:ident) => {
        pub fn $spec_fn() -> TypeSpec {
            static LAZY: LazyLock<TypeSpec> =
                LazyLock::new(|| signed_width_spec($canon, $unsigned_ty()));
            LAZY.clone()
        }
        pub fn $type_fn() -> Type {
            static LAZY: LazyLock<Type> = LazyLock::new(|| Type::spec($spec_fn(), vec![]));
            LAZY.clone()
        }
    };
}

signed_width!(s1_spec, s1_ty, Canonical::S1, bit_ty);
signed_width!(s2_spec, s2_ty, Canonical::S2, u2_ty);
signed_width!(s4_spec, s4_ty, Canonical::S4, u4_ty);
signed_width!(s8_spec, s8_ty, Canonical::S8, u8_ty);
signed_width!(s16_spec, s16_ty, Canonical::S16, u16_ty);
signed_width!(s32_spec, s32_ty, Canonical::S32, u32_ty);
signed_width!(s64_spec, s64_ty, Canonical::S64, u64_ty);
signed_width!(s128_spec, s128_ty, Canonical::S128, u128_ty);
signed_width!(s256_spec, s256_ty, Canonical::S256, u256_ty);
signed_width!(s512_spec, s512_ty, Canonical::S512, u512_ty);
