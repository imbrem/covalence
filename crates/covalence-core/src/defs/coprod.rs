//! `coprod 'a 'b` + `result 'a 'b` alias + fixed-width unsigned chain.

use std::sync::LazyLock;

use crate::hol;
use crate::term::{Term, Type};

use super::canonical::Canonical;
use super::spec::{TypeSpec, TypeSpecHandle};

// ============================================================================
// coprod predicate
// ============================================================================

/// Build the coprod predicate at concrete carriers α, β.
pub(super) fn coprod_predicate_at(alpha: Type, beta: Type) -> Term {
    let rel_ty = Type::fun(alpha.clone(), Type::fun(beta.clone(), Type::bool()));
    let r = Term::free("R", rel_ty.clone());

    let p1 = {
        let a_free = Term::free("a", alpha.clone());
        let x_free = Term::free("x", alpha.clone());
        let inner = hol::hol_eq(x_free, a_free);
        let lam_y = hol::pub_abs("y", beta.clone(), inner);
        let lam_xy = hol::pub_abs("x", alpha.clone(), lam_y);
        let r_eq = hol::hol_eq(r.clone(), lam_xy);
        hol::hol_exists("a", alpha.clone(), r_eq)
    };
    let p2 = {
        let b_free = Term::free("b", beta.clone());
        let y_free = Term::free("y", beta.clone());
        let inner = hol::hol_eq(y_free, b_free);
        let lam_y = hol::pub_abs("y", beta.clone(), inner);
        let lam_xy = hol::pub_abs("x", alpha.clone(), lam_y);
        let r_eq = hol::hol_eq(r.clone(), lam_xy);
        hol::hol_exists("b", beta.clone(), r_eq)
    };

    let body = hol::hol_or(p1, p2);
    hol::pub_abs("R", rel_ty, body)
}

fn coprod_predicate() -> Term {
    coprod_predicate_at(Type::tfree("a"), Type::tfree("b"))
}

// ============================================================================
// coprod 'a 'b
// ============================================================================

static COPROD_LAZY: LazyLock<TypeSpecHandle> = LazyLock::new(|| {
    let alpha = Type::tfree("a");
    let beta = Type::tfree("b");
    let carrier = Type::fun(alpha, Type::fun(beta, Type::bool()));
    TypeSpecHandle::new(TypeSpec {
        symbol: Canonical::Coprod,
        ty: Some(carrier),
        tm: Some(coprod_predicate()),
    })
});

/// `coprod 'a 'b := rel 'a 'b where (...)` — disjoint union.
pub fn coprod_spec() -> TypeSpecHandle {
    COPROD_LAZY.clone()
}
pub fn coprod(alpha: Type, beta: Type) -> Type {
    Type::spec(coprod_spec(), vec![alpha, beta])
}

// ============================================================================
// result 'a 'b := coprod 'a 'b
// ============================================================================

static RESULT_LAZY: LazyLock<TypeSpecHandle> = LazyLock::new(|| {
    let alpha = Type::tfree("a");
    let beta = Type::tfree("b");
    let carrier = Type::fun(alpha.clone(), Type::fun(beta.clone(), Type::bool()));
    TypeSpecHandle::new(TypeSpec {
        symbol: Canonical::Result,
        ty: Some(carrier),
        tm: Some(coprod_predicate_at(alpha, beta)),
    })
});

/// `result 'a 'b := coprod 'a 'b` — WASM component-model result.
pub fn result_spec() -> TypeSpecHandle {
    RESULT_LAZY.clone()
}
pub fn result(alpha: Type, beta: Type) -> Type {
    Type::spec(result_spec(), vec![alpha, beta])
}

// ============================================================================
// Fixed-width unsigned chain: bit, u2, u4, ..., u512
// ============================================================================

fn fixed_width_spec(symbol: Canonical, prev: Type) -> TypeSpecHandle {
    let carrier = Type::fun(prev.clone(), Type::fun(prev.clone(), Type::bool()));
    TypeSpecHandle::new(TypeSpec {
        symbol,
        ty: Some(carrier),
        tm: Some(coprod_predicate_at(prev.clone(), prev)),
    })
}

static BIT_LAZY: LazyLock<TypeSpecHandle> =
    LazyLock::new(|| fixed_width_spec(Canonical::Bit, Type::unit()));

/// `u1 (bit) := coprod unit unit`.
pub fn bit_spec() -> TypeSpecHandle {
    BIT_LAZY.clone()
}
/// `bit` as a 0-ary Type.
pub fn bit_ty() -> Type {
    Type::spec(bit_spec(), vec![])
}

macro_rules! width {
    ($lazy:ident, $spec_fn:ident, $type_fn:ident, $canon:expr, $prev_fn:ident) => {
        static $lazy: LazyLock<TypeSpecHandle> =
            LazyLock::new(|| fixed_width_spec($canon, $prev_fn()));

        pub fn $spec_fn() -> TypeSpecHandle {
            $lazy.clone()
        }
        pub fn $type_fn() -> Type {
            Type::spec($spec_fn(), vec![])
        }
    };
}

width!(U2_LAZY, u2_spec, u2_ty, Canonical::U2, bit_ty);
width!(U4_LAZY, u4_spec, u4_ty, Canonical::U4, u2_ty);
width!(U8_LAZY, u8_spec, u8_ty, Canonical::U8, u4_ty);
width!(U16_LAZY, u16_spec, u16_ty, Canonical::U16, u8_ty);
width!(U32_LAZY, u32_spec, u32_ty, Canonical::U32, u16_ty);
width!(U64_LAZY, u64_spec, u64_ty, Canonical::U64, u32_ty);
width!(U128_LAZY, u128_spec, u128_ty, Canonical::U128, u64_ty);
width!(U256_LAZY, u256_spec, u256_ty, Canonical::U256, u128_ty);
width!(U512_LAZY, u512_spec, u512_ty, Canonical::U512, u256_ty);
