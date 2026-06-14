//! Fixed-width unsigned integers: `u1 (bit)` … `u512`.
//!
//! ⚠️ **TODO-level definitions** (broadly-correct shapes, not
//! finalized — see the `defs` module docs).
//!
//! `bit (u1) := coprod unit unit` has two values. Each wider type is
//! the **product** of two copies of the previous one:
//!
//! ```text
//! u2  := prod bit bit    (2² = 4 values)
//! u4  := prod u2  u2     (4² = 16)
//! u8  := prod u4  u4     (16² = 256)
//! …    u512 := prod u256 u256
//! ```
//!
//! so `u{2n}` has `2^{2n}` values. (These were *coproducts* before,
//! which was wrong: `coprod u4 u4` has only `16 + 16 = 32` values —
//! that's a `u5`, not a `u8`. Products multiply; coproducts add.)

use std::sync::LazyLock;

use crate::term::Type;

use super::canonical::Canonical;
use super::coprod::coprod;
use super::prod::prod;
use super::spec::TypeSpec;

/// `u1 (bit) := coprod unit unit` — the two-element type. (A *sum*:
/// `1 + 1 = 2`.) A fresh symbol whose carrier is `coprod unit unit`;
/// the structure lives in `coprod`, not duplicated here.
pub fn bit_spec() -> TypeSpec {
    static LAZY: LazyLock<TypeSpec> = LazyLock::new(|| {
        let carrier = coprod(Type::unit(), Type::unit());
        TypeSpec::newtype(Canonical::Bit, carrier)
    });
    LAZY.clone()
}
pub fn bit_ty() -> Type {
    static LAZY: LazyLock<Type> = LazyLock::new(|| Type::spec(bit_spec(), vec![]));
    LAZY.clone()
}

/// `u{2n} := prod u{n} u{n}` — a fresh symbol whose carrier is the
/// *product* `prod prev prev` (`|prev|²` values). Reuses `prod`'s
/// structure rather than re-stating it.
fn fixed_width_spec(symbol: Canonical, prev: Type) -> TypeSpec {
    let carrier = prod(prev.clone(), prev);
    TypeSpec::newtype(symbol, carrier)
}

macro_rules! width {
    ($spec_fn:ident, $type_fn:ident, $canon:expr, $prev_fn:ident) => {
        pub fn $spec_fn() -> TypeSpec {
            static LAZY: LazyLock<TypeSpec> =
                LazyLock::new(|| fixed_width_spec($canon, $prev_fn()));
            LAZY.clone()
        }
        pub fn $type_fn() -> Type {
            static LAZY: LazyLock<Type> = LazyLock::new(|| Type::spec($spec_fn(), vec![]));
            LAZY.clone()
        }
    };
}

width!(u2_spec, u2_ty, Canonical::U2, bit_ty);
width!(u4_spec, u4_ty, Canonical::U4, u2_ty);
width!(u8_spec, u8_ty, Canonical::U8, u4_ty);
width!(u16_spec, u16_ty, Canonical::U16, u8_ty);
width!(u32_spec, u32_ty, Canonical::U32, u16_ty);
width!(u64_spec, u64_ty, Canonical::U64, u32_ty);
width!(u128_spec, u128_ty, Canonical::U128, u64_ty);
width!(u256_spec, u256_ty, Canonical::U256, u128_ty);
width!(u512_spec, u512_ty, Canonical::U512, u256_ty);
