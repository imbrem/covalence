//! `f32 := u32`, `f64 := u64` — bitwise aliases for IEEE 754 floats.

use std::sync::LazyLock;

use crate::term::Type;

use super::canonical::Canonical;
use super::coprod::{u32_spec, u64_spec};
use super::spec::TypeSpec;

/// `f32 := u32` — bitwise.
pub fn f32_spec() -> TypeSpec {
    static LAZY: LazyLock<TypeSpec> = LazyLock::new(|| {
        let u = u32_spec();
        let carrier = u.ty().cloned().expect("u32 has carrier");
        let tm = u.tm().cloned().expect("u32 has tm");
        TypeSpec::new(Canonical::F32, Some(carrier), Some(tm))
    });
    LAZY.clone()
}
pub fn f32_ty() -> Type {
    static LAZY: LazyLock<Type> = LazyLock::new(|| Type::spec(f32_spec(), vec![]));
    LAZY.clone()
}

/// `f64 := u64`.
pub fn f64_spec() -> TypeSpec {
    static LAZY: LazyLock<TypeSpec> = LazyLock::new(|| {
        let u = u64_spec();
        let carrier = u.ty().cloned().expect("u64 has carrier");
        let tm = u.tm().cloned().expect("u64 has tm");
        TypeSpec::new(Canonical::F64, Some(carrier), Some(tm))
    });
    LAZY.clone()
}
pub fn f64_ty() -> Type {
    static LAZY: LazyLock<Type> = LazyLock::new(|| Type::spec(f64_spec(), vec![]));
    LAZY.clone()
}
