//! Rational numbers `rat`.
//!
//! Declared as an opaque HOL type with the field axioms postulated
//! as `rat`'s *definitional* characterisation — the eight
//! commutative-field laws plus `mul_inv` collectively pin down the
//! operations up to isomorphism (the universal property of the
//! prime field of characteristic zero). A future refactor will
//! swap to a typedef carve-out of `int × int+` modulo
//! `(p, q) ∼ (p', q') ⟺ p·q' = p'·q`, at which point the field
//! laws become derived theorems; the consumer-facing
//! `axiom_*`/`LazyLock<Thm>` surface stays stable.
//!
//! The `int_to_rat` axioms (`axiom_int_to_rat_zero`,
//! `axiom_int_to_rat_add`) characterise the embedding morphism;
//! they will likewise become derivable once the quotient is
//! committed to.

use std::sync::LazyLock;

use crate::HolLightCtx;
use covalence_core::{Term, Thm, Type};

use crate::stdlib::int;

fn ctx() -> HolLightCtx {
    HolLightCtx::new()
}

fn assume_hol(body: Term) -> Thm {
    Thm::assume(body).expect("stdlib::rat: assume")
}

// ============================================================================
// Type
// ============================================================================

pub fn ty() -> Type {
    Type::tycon("rat", vec![])
}

// ============================================================================
// Constants (the ring operations as `Term::const_`s)
// ============================================================================

pub fn zero() -> Term {
    Term::const_("rat_zero", ty())
}
pub fn one() -> Term {
    Term::const_("rat_one", ty())
}
pub fn add_fn() -> Term {
    Term::const_("rat_add", Type::fun(ty(), Type::fun(ty(), ty())))
}
pub fn add(a: Term, b: Term) -> Term {
    Term::app(Term::app(add_fn(), a), b)
}
pub fn mul_fn() -> Term {
    Term::const_("rat_mul", Type::fun(ty(), Type::fun(ty(), ty())))
}
pub fn mul(a: Term, b: Term) -> Term {
    Term::app(Term::app(mul_fn(), a), b)
}
pub fn neg_fn() -> Term {
    Term::const_("rat_neg", Type::fun(ty(), ty()))
}
pub fn neg(a: Term) -> Term {
    Term::app(neg_fn(), a)
}
/// `rat_inv : rat → rat` — multiplicative inverse; `inv 0 = 0` by
/// convention (matching HOL Light's `/`).
pub fn inv_fn() -> Term {
    Term::const_("rat_inv", Type::fun(ty(), ty()))
}
pub fn inv(a: Term) -> Term {
    Term::app(inv_fn(), a)
}
pub fn int_to_rat_fn() -> Term {
    Term::const_("int_to_rat", Type::fun(Type::int(), ty()))
}
pub fn of_int(i: Term) -> Term {
    Term::app(int_to_rat_fn(), i)
}

// ============================================================================
// Field axioms
// ============================================================================

fn forall_two(builder: impl FnOnce(Term, Term, &HolLightCtx) -> Term) -> Thm {
    let ctx = ctx();
    let a = Term::free("a", ty());
    let b = Term::free("b", ty());
    let body = builder(a, b, &ctx);
    let inner = ctx.mk_forall("b", ty(), body);
    let outer = ctx.mk_forall("a", ty(), inner);
    assume_hol(outer)
}

fn forall_three(builder: impl FnOnce(Term, Term, Term, &HolLightCtx) -> Term) -> Thm {
    let ctx = ctx();
    let a = Term::free("a", ty());
    let b = Term::free("b", ty());
    let c = Term::free("c", ty());
    let body = builder(a, b, c, &ctx);
    let i1 = ctx.mk_forall("c", ty(), body);
    let i2 = ctx.mk_forall("b", ty(), i1);
    let outer = ctx.mk_forall("a", ty(), i2);
    assume_hol(outer)
}

/// `⊢ ∀a. a + 0 = a`.
pub fn axiom_add_zero_r() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let a = Term::free("a", ty());
        let eq = ctx
            .mk_eq(add(a.clone(), zero()), a)
            .expect("rat add_zero_r");
        let body = ctx.mk_forall("a", ty(), eq);
        assume_hol(body)
    });
    AX.clone()
}

pub fn axiom_add_comm() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        forall_two(|a, b, ctx| {
            ctx.mk_eq(add(a.clone(), b.clone()), add(b, a))
                .expect("rat add_comm")
        })
    });
    AX.clone()
}

pub fn axiom_add_assoc() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        forall_three(|a, b, c, ctx| {
            ctx.mk_eq(
                add(add(a.clone(), b.clone()), c.clone()),
                add(a, add(b, c)),
            )
            .expect("rat add_assoc")
        })
    });
    AX.clone()
}

pub fn axiom_add_neg_r() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let a = Term::free("a", ty());
        let eq = ctx
            .mk_eq(add(a.clone(), neg(a)), zero())
            .expect("rat add_neg_r");
        let body = ctx.mk_forall("a", ty(), eq);
        assume_hol(body)
    });
    AX.clone()
}

pub fn axiom_mul_one_r() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let a = Term::free("a", ty());
        let eq = ctx
            .mk_eq(mul(a.clone(), one()), a)
            .expect("rat mul_one_r");
        let body = ctx.mk_forall("a", ty(), eq);
        assume_hol(body)
    });
    AX.clone()
}

pub fn axiom_mul_comm() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        forall_two(|a, b, ctx| {
            ctx.mk_eq(mul(a.clone(), b.clone()), mul(b, a))
                .expect("rat mul_comm")
        })
    });
    AX.clone()
}

pub fn axiom_mul_assoc() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        forall_three(|a, b, c, ctx| {
            ctx.mk_eq(
                mul(mul(a.clone(), b.clone()), c.clone()),
                mul(a, mul(b, c)),
            )
            .expect("rat mul_assoc")
        })
    });
    AX.clone()
}

pub fn axiom_mul_distrib_l() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        forall_three(|a, b, c, ctx| {
            ctx.mk_eq(
                mul(a.clone(), add(b.clone(), c.clone())),
                add(mul(a.clone(), b), mul(a, c)),
            )
            .expect("rat mul_distrib_l")
        })
    });
    AX.clone()
}

/// `⊢ ∀a. ¬ (a = 0) ⟹ a * inv a = 1`.
pub fn axiom_mul_inv() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let a = Term::free("a", ty());
        let zero_eq = ctx
            .mk_eq(a.clone(), zero())
            .expect("rat mul_inv: zero_eq");
        let nonzero = ctx.mk_not(zero_eq);
        let prod_eq = ctx
            .mk_eq(mul(a.clone(), inv(a)), one())
            .expect("rat mul_inv: prod_eq");
        let imp = ctx.mk_imp(nonzero, prod_eq);
        let body = ctx.mk_forall("a", ty(), imp);
        assume_hol(body)
    });
    AX.clone()
}

/// `⊢ int_to_rat 0 = 0`.
pub fn axiom_int_to_rat_zero() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let eq = ctx
            .mk_eq(of_int(int::zero()), zero())
            .expect("axiom_int_to_rat_zero: mk_eq");
        assume_hol(eq)
    });
    AX.clone()
}

/// `⊢ ∀m n. int_to_rat (m + n) = int_to_rat m + int_to_rat n`.
pub fn axiom_int_to_rat_add() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let m = Term::free("m", Type::int());
        let n = Term::free("n", Type::int());
        let lhs = of_int(int::add(m.clone(), n.clone()));
        let rhs = add(of_int(m), of_int(n));
        let eq = ctx
            .mk_eq(lhs, rhs)
            .expect("axiom_int_to_rat_add: mk_eq");
        let inner = ctx.mk_forall("n", Type::int(), eq);
        let outer = ctx.mk_forall("m", Type::int(), inner);
        assume_hol(outer)
    });
    AX.clone()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ring_axioms_well_formed() {
        for ax in [
            axiom_add_zero_r(),
            axiom_add_comm(),
            axiom_add_assoc(),
            axiom_add_neg_r(),
            axiom_mul_one_r(),
            axiom_mul_comm(),
            axiom_mul_assoc(),
            axiom_mul_distrib_l(),
            axiom_mul_inv(),
            axiom_int_to_rat_zero(),
            axiom_int_to_rat_add(),
        ] {
            assert!(ax.concl().type_of().unwrap().is_formula());
        }
    }
}
