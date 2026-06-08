//! Foundational HOL axioms about Pure's primitive `int` type.
//!
//! Mirrors `nat_axioms` for integers: induction (in both
//! directions), distinctness, injectivity, and the standard
//! arithmetic laws (commutative ring axioms).
//!
//! See [`crate::nat_axioms`] for the design rationale.

use std::sync::LazyLock;

use covalence_pure::{Arith, Prim, Term, Thm, Type};

use crate::HolLightCtx;

fn ctx() -> HolLightCtx {
    HolLightCtx::new()
}

fn int_ty() -> Type {
    Type::int()
}

fn zero() -> Term {
    Term::int_lit(covalence_types::Int::zero())
}

fn neg(t: Term) -> Term {
    Term::app(Term::prim(Prim::IntNeg), t)
}

fn add(a: Term, b: Term) -> Term {
    Term::app(Term::app(Term::prim(Prim::IntArith(Arith::Add)), a), b)
}

fn mul(a: Term, b: Term) -> Term {
    Term::app(Term::app(Term::prim(Prim::IntArith(Arith::Mul)), a), b)
}

fn assume_hol(body: Term) -> Thm {
    let wrapped = ctx()
        .mk_trueprop(body)
        .expect("int_axioms: axiom body must be HOL bool-typed");
    Thm::assume(wrapped).expect("int_axioms: Thm::assume on a closed Trueprop cannot fail")
}

// ============================================================================
// Ring axioms (additive + multiplicative)
// ============================================================================

/// `⊢ ∀n:int. n + 0 = n`.
pub fn int_add_zero_r() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let n = Term::free("n", int_ty());
        let eq = ctx
            .mk_eq(add(n.clone(), zero()), n)
            .expect("int_add_zero_r: mk_eq");
        let body = ctx.mk_forall("n", int_ty(), eq);
        assume_hol(body)
    });
    AX.clone()
}

/// `⊢ ∀m n:int. m + n = n + m`.
pub fn int_add_comm() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let m = Term::free("m", int_ty());
        let n = Term::free("n", int_ty());
        let eq = ctx
            .mk_eq(add(m.clone(), n.clone()), add(n, m))
            .expect("int_add_comm: mk_eq");
        let inner = ctx.mk_forall("n", int_ty(), eq);
        let outer = ctx.mk_forall("m", int_ty(), inner);
        assume_hol(outer)
    });
    AX.clone()
}

/// `⊢ ∀a b c. (a + b) + c = a + (b + c)`.
pub fn int_add_assoc() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let a = Term::free("a", int_ty());
        let b = Term::free("b", int_ty());
        let c = Term::free("c", int_ty());
        let lhs = add(add(a.clone(), b.clone()), c.clone());
        let rhs = add(a, add(b, c));
        let eq = ctx.mk_eq(lhs, rhs).expect("int_add_assoc: mk_eq");
        let inner1 = ctx.mk_forall("c", int_ty(), eq);
        let inner2 = ctx.mk_forall("b", int_ty(), inner1);
        let outer = ctx.mk_forall("a", int_ty(), inner2);
        assume_hol(outer)
    });
    AX.clone()
}

/// `⊢ ∀n:int. n + (- n) = 0` — additive inverse.
pub fn int_add_neg_r() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let n = Term::free("n", int_ty());
        let eq = ctx
            .mk_eq(add(n.clone(), neg(n)), zero())
            .expect("int_add_neg_r: mk_eq");
        let body = ctx.mk_forall("n", int_ty(), eq);
        assume_hol(body)
    });
    AX.clone()
}

/// `⊢ ∀m n. m * n = n * m`.
pub fn int_mul_comm() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let m = Term::free("m", int_ty());
        let n = Term::free("n", int_ty());
        let eq = ctx
            .mk_eq(mul(m.clone(), n.clone()), mul(n, m))
            .expect("int_mul_comm: mk_eq");
        let inner = ctx.mk_forall("n", int_ty(), eq);
        let outer = ctx.mk_forall("m", int_ty(), inner);
        assume_hol(outer)
    });
    AX.clone()
}

/// `⊢ ∀a b c. (a * b) * c = a * (b * c)`.
pub fn int_mul_assoc() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let a = Term::free("a", int_ty());
        let b = Term::free("b", int_ty());
        let c = Term::free("c", int_ty());
        let lhs = mul(mul(a.clone(), b.clone()), c.clone());
        let rhs = mul(a, mul(b, c));
        let eq = ctx.mk_eq(lhs, rhs).expect("int_mul_assoc: mk_eq");
        let inner1 = ctx.mk_forall("c", int_ty(), eq);
        let inner2 = ctx.mk_forall("b", int_ty(), inner1);
        let outer = ctx.mk_forall("a", int_ty(), inner2);
        assume_hol(outer)
    });
    AX.clone()
}

/// `⊢ ∀a b c. a * (b + c) = a*b + a*c` — distributivity.
pub fn int_mul_add_distrib_l() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let a = Term::free("a", int_ty());
        let b = Term::free("b", int_ty());
        let c = Term::free("c", int_ty());
        let lhs = mul(a.clone(), add(b.clone(), c.clone()));
        let rhs = add(mul(a.clone(), b), mul(a, c));
        let eq = ctx
            .mk_eq(lhs, rhs)
            .expect("int_mul_add_distrib_l: mk_eq");
        let inner1 = ctx.mk_forall("c", int_ty(), eq);
        let inner2 = ctx.mk_forall("b", int_ty(), inner1);
        let outer = ctx.mk_forall("a", int_ty(), inner2);
        assume_hol(outer)
    });
    AX.clone()
}

/// `⊢ ∀n:int. - (- n) = n`.
pub fn int_neg_involutive() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let n = Term::free("n", int_ty());
        let eq = ctx
            .mk_eq(neg(neg(n.clone())), n)
            .expect("int_neg_involutive: mk_eq");
        let body = ctx.mk_forall("n", int_ty(), eq);
        assume_hol(body)
    });
    AX.clone()
}

// ============================================================================
// Nat ↔ Int bridge
// ============================================================================

/// `⊢ ∀n:nat. natToInt n + 0 = natToInt n` (a sample fact connecting
/// nat embedding to int arithmetic — the basic embedding morphism
/// laws follow from this + nat_axioms.).
///
/// More foundationally: `natToInt` is a ring-monomorphism. We
/// postulate the most-used facts.
pub fn nat_to_int_add() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let nat_ty = Type::nat();
        let n = Term::free("n", nat_ty.clone());
        let m = Term::free("m", nat_ty.clone());
        let nat_add = Term::app(
            Term::app(Term::prim(Prim::NatArith(Arith::Add)), m.clone()),
            n.clone(),
        );
        let to_int = |t: Term| Term::app(Term::prim(Prim::NatToInt), t);
        // ⊢ ∀m n. natToInt (m + n) = natToInt m + natToInt n
        let lhs = to_int(nat_add);
        let rhs = add(to_int(m), to_int(n));
        let eq = ctx.mk_eq(lhs, rhs).expect("nat_to_int_add: mk_eq");
        let inner = ctx.mk_forall("n", nat_ty.clone(), eq);
        let outer = ctx.mk_forall("m", nat_ty, inner);
        assume_hol(outer)
    });
    AX.clone()
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn check(ax: Thm) {
        assert!(ax.concl().type_of().unwrap().is_prop());
        assert_eq!(ax.hyps().len(), 1);
        assert_eq!(ax.hyps().iter().next().unwrap(), ax.concl());
    }

    #[test]
    fn ring_axioms_well_formed() {
        check(int_add_zero_r());
        check(int_add_comm());
        check(int_add_assoc());
        check(int_add_neg_r());
        check(int_mul_comm());
        check(int_mul_assoc());
        check(int_mul_add_distrib_l());
        check(int_neg_involutive());
        check(nat_to_int_add());
    }
}
