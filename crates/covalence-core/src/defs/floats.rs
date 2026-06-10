//! `f32 := u32`, `f64 := u64` — bitwise aliases for IEEE 754 floats.

use std::sync::LazyLock;

use crate::term::Type;

use super::canonical::Canonical;
use super::spec::{TypeSpec, TypeSpecHandle};
use super::coprod::{u32_spec, u64_spec};

static F32_LAZY: LazyLock<TypeSpecHandle> = LazyLock::new(|| {
    let u = u32_spec();
    let carrier = u.as_spec().ty.clone().expect("u32 has carrier");
    let tm = u.as_spec().tm.clone().expect("u32 has tm");
    TypeSpecHandle::new(TypeSpec {
        symbol: Canonical::F32,
        ty: Some(carrier),
        tm: Some(tm),
    })
});

static F64_LAZY: LazyLock<TypeSpecHandle> = LazyLock::new(|| {
    let u = u64_spec();
    let carrier = u.as_spec().ty.clone().expect("u64 has carrier");
    let tm = u.as_spec().tm.clone().expect("u64 has tm");
    TypeSpecHandle::new(TypeSpec {
        symbol: Canonical::F64,
        ty: Some(carrier),
        tm: Some(tm),
    })
});

/// `f32 := u32` — bitwise.
pub fn f32_spec() -> TypeSpecHandle {
    F32_LAZY.clone()
}
pub fn f32_ty() -> Type {
    Type::spec(f32_spec(), vec![])
}
/// `f64 := u64`.
pub fn f64_spec() -> TypeSpecHandle {
    F64_LAZY.clone()
}
pub fn f64_ty() -> Type {
    Type::spec(f64_spec(), vec![])
}
