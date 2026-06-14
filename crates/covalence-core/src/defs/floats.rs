//! `f32 := u32`, `f64 := u64` — bitwise aliases for IEEE 754 floats.

use std::sync::LazyLock;

use crate::term::Type;

use super::bits::{u32_ty, u64_ty};
use super::canonical::Canonical;
use super::spec::TypeSpec;

/// `f32 := u32` — bitwise.
pub fn f32_spec() -> TypeSpec {
    static LAZY: LazyLock<TypeSpec> = LazyLock::new(|| TypeSpec::newtype(Canonical::F32, u32_ty()));
    LAZY.clone()
}
pub fn f32_ty() -> Type {
    static LAZY: LazyLock<Type> = LazyLock::new(|| Type::spec(f32_spec(), vec![]));
    LAZY.clone()
}

/// `f64 := u64`.
pub fn f64_spec() -> TypeSpec {
    static LAZY: LazyLock<TypeSpec> = LazyLock::new(|| TypeSpec::newtype(Canonical::F64, u64_ty()));
    LAZY.clone()
}
pub fn f64_ty() -> Type {
    static LAZY: LazyLock<Type> = LazyLock::new(|| Type::spec(f64_spec(), vec![]));
    LAZY.clone()
}
