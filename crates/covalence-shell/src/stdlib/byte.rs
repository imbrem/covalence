//! Fixed-width unsigned integer types — `u8` / `u16` / `u32` / `u64`.
//!
//! Each is a HOL type representing nat values bounded by `2^N`.
//! For the MVP they're declared as polymorphic-name `tycon` types
//! with their bounds + arithmetic-mod-2^N axiomatized; future
//! versions can swap to proper typedef carve-outs of nat (the
//! actual `{ n : nat | n < 2^N }` subset).
//!
//! `u8` is the byte type; `bytes::cons_nat` mods inputs by 256.

use std::sync::LazyLock;

use covalence_hol::HolLightCtx;
use covalence_core::{Term, Thm, Type};

use crate::stdlib::nat;

fn ctx() -> HolLightCtx {
    HolLightCtx::new()
}

fn assume_hol(body: Term) -> Thm {
    let wrapped = ctx().mk_trueprop(body).expect("stdlib::byte: mk_trueprop");
    Thm::assume(wrapped).expect("stdlib::byte: assume")
}

// ============================================================================
// u8 (byte)
// ============================================================================

pub fn u8_ty() -> Type {
    Type::tycon("u8", vec![])
}

/// Alias for `u8_ty()` — the "byte" type.
pub fn byte_ty() -> Type {
    u8_ty()
}

/// `u8_of_nat : nat → u8` — mod 2^8 = 256.
pub fn u8_of_nat() -> Term {
    Term::const_("u8_of_nat", Type::fun(Type::nat(), u8_ty()))
}

/// `nat_of_u8 : u8 → nat` — embedding.
pub fn nat_of_u8() -> Term {
    Term::const_("nat_of_u8", Type::fun(u8_ty(), Type::nat()))
}

pub fn u8_lit(n: u8) -> Term {
    Term::app(u8_of_nat(), nat::lit(n as u32))
}

/// `⊢ ∀b:u8. nat_of_u8 b < 256`.
pub fn axiom_u8_bound() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| build_bound_axiom(u8_ty(), nat_of_u8(), 256u64));
    AX.clone()
}

/// `⊢ ∀b:u8. u8_of_nat (nat_of_u8 b) = b`.
pub fn axiom_u8_round_trip() -> Thm {
    static AX: LazyLock<Thm> =
        LazyLock::new(|| build_round_trip_axiom(u8_ty(), u8_of_nat(), nat_of_u8(), "b"));
    AX.clone()
}

/// `⊢ ∀n:nat. nat_of_u8 (u8_of_nat n) = n mod 256`.
pub fn axiom_u8_of_nat_mod() -> Thm {
    static AX: LazyLock<Thm> =
        LazyLock::new(|| build_of_nat_mod_axiom(u8_of_nat(), nat_of_u8(), 256u64));
    AX.clone()
}

// ============================================================================
// u16
// ============================================================================

pub fn u16_ty() -> Type {
    Type::tycon("u16", vec![])
}
pub fn u16_of_nat() -> Term {
    Term::const_("u16_of_nat", Type::fun(Type::nat(), u16_ty()))
}
pub fn nat_of_u16() -> Term {
    Term::const_("nat_of_u16", Type::fun(u16_ty(), Type::nat()))
}
pub fn u16_lit(n: u16) -> Term {
    Term::app(u16_of_nat(), nat::lit(n as u32))
}
pub fn axiom_u16_bound() -> Thm {
    static AX: LazyLock<Thm> =
        LazyLock::new(|| build_bound_axiom(u16_ty(), nat_of_u16(), 65536u64));
    AX.clone()
}
pub fn axiom_u16_round_trip() -> Thm {
    static AX: LazyLock<Thm> =
        LazyLock::new(|| build_round_trip_axiom(u16_ty(), u16_of_nat(), nat_of_u16(), "x"));
    AX.clone()
}
pub fn axiom_u16_of_nat_mod() -> Thm {
    static AX: LazyLock<Thm> =
        LazyLock::new(|| build_of_nat_mod_axiom(u16_of_nat(), nat_of_u16(), 65536u64));
    AX.clone()
}

// ============================================================================
// u32
// ============================================================================

pub fn u32_ty() -> Type {
    Type::tycon("u32", vec![])
}
pub fn u32_of_nat() -> Term {
    Term::const_("u32_of_nat", Type::fun(Type::nat(), u32_ty()))
}
pub fn nat_of_u32() -> Term {
    Term::const_("nat_of_u32", Type::fun(u32_ty(), Type::nat()))
}
pub fn u32_lit(n: u32) -> Term {
    Term::app(u32_of_nat(), nat::lit(n))
}
pub fn axiom_u32_bound() -> Thm {
    static AX: LazyLock<Thm> =
        LazyLock::new(|| build_bound_axiom(u32_ty(), nat_of_u32(), 1u64 << 32));
    AX.clone()
}
pub fn axiom_u32_round_trip() -> Thm {
    static AX: LazyLock<Thm> =
        LazyLock::new(|| build_round_trip_axiom(u32_ty(), u32_of_nat(), nat_of_u32(), "x"));
    AX.clone()
}
pub fn axiom_u32_of_nat_mod() -> Thm {
    static AX: LazyLock<Thm> =
        LazyLock::new(|| build_of_nat_mod_axiom(u32_of_nat(), nat_of_u32(), 1u64 << 32));
    AX.clone()
}

// ============================================================================
// u64
// ============================================================================

pub fn u64_ty() -> Type {
    Type::tycon("u64", vec![])
}
pub fn u64_of_nat() -> Term {
    Term::const_("u64_of_nat", Type::fun(Type::nat(), u64_ty()))
}
pub fn nat_of_u64() -> Term {
    Term::const_("nat_of_u64", Type::fun(u64_ty(), Type::nat()))
}
pub fn u64_lit(n: u64) -> Term {
    Term::app(u64_of_nat(), nat::lit(covalence_types::Nat::from_inner(n.into())))
}
pub fn axiom_u64_bound() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        // 2^64 doesn't fit in u64; use BigUint via Nat directly.
        build_bound_axiom_big(u64_ty(), nat_of_u64(), nat_two_pow(64))
    });
    AX.clone()
}
pub fn axiom_u64_round_trip() -> Thm {
    static AX: LazyLock<Thm> =
        LazyLock::new(|| build_round_trip_axiom(u64_ty(), u64_of_nat(), nat_of_u64(), "x"));
    AX.clone()
}
pub fn axiom_u64_of_nat_mod() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        build_of_nat_mod_axiom_big(u64_of_nat(), nat_of_u64(), nat_two_pow(64))
    });
    AX.clone()
}

// ============================================================================
// Helpers
// ============================================================================

fn nat_two_pow(exp: u32) -> covalence_types::Nat {
    let two = covalence_types::Nat::from_inner(2u32.into());
    covalence_types::Nat::from_inner(two.as_inner().pow(exp))
}

fn nat_lt(a: Term, b: Term) -> Term {
    // We don't have a primitive `<` yet; encode as `b - a ≠ 0 ∧ a ≠ b`
    // — actually, let's keep this simple and just use a postulated
    // `nat_lt : nat → nat → bool` constant.
    let lt = Term::const_(
        "nat_lt",
        Type::fun(
            Type::nat(),
            Type::fun(Type::nat(), HolLightCtx::new().bool_type()),
        ),
    );
    Term::app(Term::app(lt, a), b)
}

fn build_bound_axiom(t: Type, repr: Term, bound: u64) -> Thm {
    let ctx = ctx();
    let x = Term::free("x", t.clone());
    let lhs = Term::app(repr, x);
    let bound_term = nat::lit(covalence_types::Nat::from_inner(bound.into()));
    let lt = nat_lt(lhs, bound_term);
    let body = ctx.mk_forall("x", t, lt);
    assume_hol(body)
}

fn build_bound_axiom_big(t: Type, repr: Term, bound: covalence_types::Nat) -> Thm {
    let ctx = ctx();
    let x = Term::free("x", t.clone());
    let lhs = Term::app(repr, x);
    let bound_term = nat::lit(bound);
    let lt = nat_lt(lhs, bound_term);
    let body = ctx.mk_forall("x", t, lt);
    assume_hol(body)
}

fn build_round_trip_axiom(t: Type, of_nat: Term, repr: Term, varname: &str) -> Thm {
    let ctx = ctx();
    let x = Term::free(varname, t.clone());
    let inner = Term::app(repr, x.clone());
    let round = Term::app(of_nat, inner);
    let eq = ctx
        .mk_eq(round, x)
        .expect("build_round_trip_axiom: mk_eq");
    let body = ctx.mk_forall(varname, t, eq);
    assume_hol(body)
}

fn build_of_nat_mod_axiom(of_nat: Term, repr: Term, modulus: u64) -> Thm {
    let ctx = ctx();
    let n = Term::free("n", Type::nat());
    let injected = Term::app(of_nat, n.clone());
    let projected = Term::app(repr, injected);
    let mod_term = nat::lit(covalence_types::Nat::from_inner(modulus.into()));
    let rhs = nat::rem(n, mod_term);
    let eq = ctx
        .mk_eq(projected, rhs)
        .expect("build_of_nat_mod_axiom: mk_eq");
    let body = ctx.mk_forall("n", Type::nat(), eq);
    assume_hol(body)
}

fn build_of_nat_mod_axiom_big(of_nat: Term, repr: Term, modulus: covalence_types::Nat) -> Thm {
    let ctx = ctx();
    let n = Term::free("n", Type::nat());
    let injected = Term::app(of_nat, n.clone());
    let projected = Term::app(repr, injected);
    let mod_term = nat::lit(modulus);
    let rhs = nat::rem(n, mod_term);
    let eq = ctx
        .mk_eq(projected, rhs)
        .expect("build_of_nat_mod_axiom_big: mk_eq");
    let body = ctx.mk_forall("n", Type::nat(), eq);
    assume_hol(body)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn check(ax: Thm) {
        assert!(ax.concl().type_of().unwrap().is_prop());
    }

    #[test]
    fn u8_axioms_well_formed() {
        check(axiom_u8_bound());
        check(axiom_u8_round_trip());
        check(axiom_u8_of_nat_mod());
    }

    #[test]
    fn u16_axioms_well_formed() {
        check(axiom_u16_bound());
        check(axiom_u16_round_trip());
        check(axiom_u16_of_nat_mod());
    }

    #[test]
    fn u32_u64_axioms_well_formed() {
        check(axiom_u32_bound());
        check(axiom_u32_round_trip());
        check(axiom_u32_of_nat_mod());
        check(axiom_u64_bound());
        check(axiom_u64_round_trip());
        check(axiom_u64_of_nat_mod());
    }

    #[test]
    fn lit_types() {
        assert_eq!(u8_lit(42).type_of().unwrap(), u8_ty());
        assert_eq!(u16_lit(40000).type_of().unwrap(), u16_ty());
        assert_eq!(u32_lit(1_000_000).type_of().unwrap(), u32_ty());
        assert_eq!(u64_lit(u64::MAX).type_of().unwrap(), u64_ty());
    }
}
