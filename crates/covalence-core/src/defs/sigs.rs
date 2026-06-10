//! Common function-type signatures, cached as lazy statics so spec
//! constructors don't reallocate the same shape on every call.
//!
//! The kernel-side `Type` does NOT hash-cons or content-hash its
//! allocations — each `Type::fun(a, b)` call mints a fresh `Arc`. The
//! lazy statics here are how we share a single allocation for the
//! handful of signatures the catalogue reuses across many specs
//! (`nat → nat → nat`, `int → int → bool`, etc.). Cloning a `Type` is
//! a refcount bump on the cached `Arc`, so widely-shared shapes
//! become genuinely cheap.

#![allow(dead_code)] // Some sigs are kept for parity / future use.

use std::sync::LazyLock;

use crate::term::Type;

/// `nat → nat`.
pub fn nat_to_nat() -> Type {
    static LAZY: LazyLock<Type> = LazyLock::new(|| Type::fun(Type::nat(), Type::nat()));
    LAZY.clone()
}

/// `nat → nat → nat` — binary nat operation.
pub fn nat_nat_to_nat() -> Type {
    static LAZY: LazyLock<Type> =
        LazyLock::new(|| Type::fun(Type::nat(), Type::fun(Type::nat(), Type::nat())));
    LAZY.clone()
}

/// `nat → nat → bool` — nat comparison.
pub fn nat_nat_to_bool() -> Type {
    static LAZY: LazyLock<Type> =
        LazyLock::new(|| Type::fun(Type::nat(), Type::fun(Type::nat(), Type::bool())));
    LAZY.clone()
}

/// `nat → int` — coercion.
pub fn nat_to_int() -> Type {
    static LAZY: LazyLock<Type> = LazyLock::new(|| Type::fun(Type::nat(), Type::int()));
    LAZY.clone()
}

/// `nat → bool` — predicate on nat.
pub fn nat_to_bool() -> Type {
    static LAZY: LazyLock<Type> = LazyLock::new(|| Type::fun(Type::nat(), Type::bool()));
    LAZY.clone()
}

/// `nat → bytes` — byte encoding.
pub fn nat_to_bytes() -> Type {
    static LAZY: LazyLock<Type> = LazyLock::new(|| Type::fun(Type::nat(), Type::bytes()));
    LAZY.clone()
}

/// `bytes → nat` — byte decoding / length.
pub fn bytes_to_nat() -> Type {
    static LAZY: LazyLock<Type> = LazyLock::new(|| Type::fun(Type::bytes(), Type::nat()));
    LAZY.clone()
}

/// `int → int`.
pub fn int_to_int() -> Type {
    static LAZY: LazyLock<Type> = LazyLock::new(|| Type::fun(Type::int(), Type::int()));
    LAZY.clone()
}

/// `int → int → int` — binary int operation.
pub fn int_int_to_int() -> Type {
    static LAZY: LazyLock<Type> =
        LazyLock::new(|| Type::fun(Type::int(), Type::fun(Type::int(), Type::int())));
    LAZY.clone()
}

/// `int → int → bool` — int comparison.
pub fn int_int_to_bool() -> Type {
    static LAZY: LazyLock<Type> =
        LazyLock::new(|| Type::fun(Type::int(), Type::fun(Type::int(), Type::bool())));
    LAZY.clone()
}

/// `int → nat` — abs.
pub fn int_to_nat() -> Type {
    static LAZY: LazyLock<Type> = LazyLock::new(|| Type::fun(Type::int(), Type::nat()));
    LAZY.clone()
}

/// `bool → bool` — unary bool.
pub fn bool_to_bool() -> Type {
    static LAZY: LazyLock<Type> = LazyLock::new(|| Type::fun(Type::bool(), Type::bool()));
    LAZY.clone()
}

/// `bool → bool → bool` — binary bool.
pub fn bool_bool_to_bool() -> Type {
    static LAZY: LazyLock<Type> =
        LazyLock::new(|| Type::fun(Type::bool(), Type::fun(Type::bool(), Type::bool())));
    LAZY.clone()
}
