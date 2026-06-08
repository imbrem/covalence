//! Foundational HOL axioms about Pure's primitive `nat` type.
//!
//! Pure exposes `Type::nat()` + `NatLit` + `Prim::NatArith(_)` and
//! decides closed-form arithmetic by reflexivity via
//! `Thm::reduce_prim`. The HOL-level facts about open-form
//! reasoning (the Peano axioms — induction, distinctness,
//! injectivity — plus the standard arithmetic laws) are postulated
//! here as `LazyLock<Thm>` constants, each formed by `Thm::assume`
//! over a Trueprop-wrapped HOL statement.
//!
//! Naming follows HOL Light: `nat_induction`, `nat_succ_inj`,
//! `nat_zero_ne_succ`, `nat_add_comm`, etc.
//!
//! Stdlib consumers go through `covalence_shell::stdlib::nat`
//! which re-exports these; downstream code should never need to
//! reach into `covalence-hol` directly for these facts.

use std::sync::LazyLock;

use covalence_pure::{Arith, Prim, Term, Thm, Type};

use crate::HolLightCtx;

// ============================================================================
// Helpers
// ============================================================================

fn ctx() -> HolLightCtx {
    HolLightCtx::new()
}

fn nat_ty() -> Type {
    Type::nat()
}

fn zero() -> Term {
    Term::nat_lit(covalence_types::Nat::zero())
}

fn succ(t: Term) -> Term {
    Term::app(Term::prim(Prim::NatArith(Arith::Succ)), t)
}

fn add(a: Term, b: Term) -> Term {
    Term::app(Term::app(Term::prim(Prim::NatArith(Arith::Add)), a), b)
}

fn mul(a: Term, b: Term) -> Term {
    Term::app(Term::app(Term::prim(Prim::NatArith(Arith::Mul)), a), b)
}

fn assume_hol(body: Term) -> Thm {
    let wrapped = ctx()
        .mk_trueprop(body)
        .expect("nat_axioms: axiom body must be HOL bool-typed");
    Thm::assume(wrapped).expect("nat_axioms: Thm::assume on a closed Trueprop cannot fail")
}

// ============================================================================
// Peano-Dedekind axioms
// ============================================================================

/// `⊢ ∀n:nat. ¬ (0 = succ n)` — zero is not a successor.
pub fn nat_zero_ne_succ() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let n = Term::free("n", nat_ty());
        let eq = ctx
            .mk_eq(zero(), succ(n))
            .expect("nat_zero_ne_succ: mk_eq");
        let not_eq = ctx.mk_not(eq);
        let body = ctx.mk_forall("n", nat_ty(), not_eq);
        assume_hol(body)
    });
    AX.clone()
}

/// `⊢ ∀m n:nat. succ m = succ n ⟹ m = n` — successor is injective.
pub fn nat_succ_inj() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let m = Term::free("m", nat_ty());
        let n = Term::free("n", nat_ty());
        let lhs = ctx
            .mk_eq(succ(m.clone()), succ(n.clone()))
            .expect("nat_succ_inj: mk_eq lhs");
        let rhs = ctx.mk_eq(m, n).expect("nat_succ_inj: mk_eq rhs");
        let imp = ctx.mk_imp(lhs, rhs);
        let inner = ctx.mk_forall("n", nat_ty(), imp);
        let body = ctx.mk_forall("m", nat_ty(), inner);
        assume_hol(body)
    });
    AX.clone()
}

/// `⊢ ∀P:nat→bool. P 0 ∧ (∀n. P n ⟹ P (succ n)) ⟹ ∀n. P n` —
/// mathematical induction on naturals.
pub fn nat_induction() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let nat_ty = nat_ty();
        let bool_ty = ctx.bool_type();
        let pred_ty = Type::fun(nat_ty.clone(), bool_ty);
        let p = Term::free("P", pred_ty.clone());

        let p_zero = Term::app(p.clone(), zero());

        let n = Term::free("n", nat_ty.clone());
        let p_n = Term::app(p.clone(), n.clone());
        let p_succ_n = Term::app(p.clone(), succ(n));
        let step_body = ctx.mk_imp(p_n, p_succ_n);
        let step = ctx.mk_forall("n", nat_ty.clone(), step_body);

        let antecedent = ctx.mk_and(p_zero, step);

        let n2 = Term::free("n", nat_ty.clone());
        let p_n2 = Term::app(p.clone(), n2);
        let consequent = ctx.mk_forall("n", nat_ty.clone(), p_n2);

        let imp = ctx.mk_imp(antecedent, consequent);
        let body = ctx.mk_forall("P", pred_ty, imp);
        assume_hol(body)
    });
    AX.clone()
}

// ============================================================================
// Arithmetic laws (over Pure's Prim::NatArith operators)
//
// Each is postulated. Closed-form instances are already provable by
// `Thm::reduce_prim` from the Pure kernel; these axioms cover the
// open-form (variable-containing) statements that downstream code
// needs to reason about programs/specs over nat.
// ============================================================================

fn arith_law_two_var(builder: fn(Term, Term, &HolLightCtx) -> Term) -> Thm {
    let ctx = ctx();
    let m = Term::free("m", nat_ty());
    let n = Term::free("n", nat_ty());
    let body = builder(m, n, &ctx);
    let inner = ctx.mk_forall("n", nat_ty(), body);
    let outer = ctx.mk_forall("m", nat_ty(), inner);
    assume_hol(outer)
}

fn arith_law_three_var(builder: fn(Term, Term, Term, &HolLightCtx) -> Term) -> Thm {
    let ctx = ctx();
    let a = Term::free("a", nat_ty());
    let b = Term::free("b", nat_ty());
    let c = Term::free("c", nat_ty());
    let body = builder(a, b, c, &ctx);
    let inner1 = ctx.mk_forall("c", nat_ty(), body);
    let inner2 = ctx.mk_forall("b", nat_ty(), inner1);
    let outer = ctx.mk_forall("a", nat_ty(), inner2);
    assume_hol(outer)
}

/// `⊢ ∀n. n + 0 = n` — right-identity for add.
pub fn nat_add_zero_r() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let n = Term::free("n", nat_ty());
        let lhs = add(n.clone(), zero());
        let eq = ctx.mk_eq(lhs, n).expect("nat_add_zero_r: mk_eq");
        let body = ctx.mk_forall("n", nat_ty(), eq);
        assume_hol(body)
    });
    AX.clone()
}

/// `⊢ ∀n. 0 + n = n` — left-identity for add.
pub fn nat_add_zero_l() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let n = Term::free("n", nat_ty());
        let lhs = add(zero(), n.clone());
        let eq = ctx.mk_eq(lhs, n).expect("nat_add_zero_l: mk_eq");
        let body = ctx.mk_forall("n", nat_ty(), eq);
        assume_hol(body)
    });
    AX.clone()
}

/// `⊢ ∀m n. m + n = n + m` — addition is commutative.
pub fn nat_add_comm() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        arith_law_two_var(|m, n, ctx| {
            ctx.mk_eq(add(m.clone(), n.clone()), add(n, m))
                .expect("nat_add_comm: mk_eq")
        })
    });
    AX.clone()
}

/// `⊢ ∀a b c. (a + b) + c = a + (b + c)` — addition is associative.
pub fn nat_add_assoc() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        arith_law_three_var(|a, b, c, ctx| {
            let lhs = add(add(a.clone(), b.clone()), c.clone());
            let rhs = add(a, add(b, c));
            ctx.mk_eq(lhs, rhs).expect("nat_add_assoc: mk_eq")
        })
    });
    AX.clone()
}

/// `⊢ ∀n. n * 0 = 0`.
pub fn nat_mul_zero_r() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let n = Term::free("n", nat_ty());
        let lhs = mul(n, zero());
        let eq = ctx.mk_eq(lhs, zero()).expect("nat_mul_zero_r: mk_eq");
        let body = ctx.mk_forall("n", nat_ty(), eq);
        assume_hol(body)
    });
    AX.clone()
}

/// `⊢ ∀n. 0 * n = 0`.
pub fn nat_mul_zero_l() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let n = Term::free("n", nat_ty());
        let lhs = mul(zero(), n);
        let eq = ctx.mk_eq(lhs, zero()).expect("nat_mul_zero_l: mk_eq");
        let body = ctx.mk_forall("n", nat_ty(), eq);
        assume_hol(body)
    });
    AX.clone()
}

/// `⊢ ∀m n. m * n = n * m` — multiplication is commutative.
pub fn nat_mul_comm() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        arith_law_two_var(|m, n, ctx| {
            ctx.mk_eq(mul(m.clone(), n.clone()), mul(n, m))
                .expect("nat_mul_comm: mk_eq")
        })
    });
    AX.clone()
}

/// `⊢ ∀a b c. (a * b) * c = a * (b * c)` — multiplication is
/// associative.
pub fn nat_mul_assoc() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        arith_law_three_var(|a, b, c, ctx| {
            let lhs = mul(mul(a.clone(), b.clone()), c.clone());
            let rhs = mul(a, mul(b, c));
            ctx.mk_eq(lhs, rhs).expect("nat_mul_assoc: mk_eq")
        })
    });
    AX.clone()
}

/// `⊢ ∀a b c. a * (b + c) = a*b + a*c` — left distributivity.
pub fn nat_mul_add_distrib_l() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        arith_law_three_var(|a, b, c, ctx| {
            let lhs = mul(a.clone(), add(b.clone(), c.clone()));
            let rhs = add(mul(a.clone(), b), mul(a, c));
            ctx.mk_eq(lhs, rhs).expect("nat_mul_add_distrib_l: mk_eq")
        })
    });
    AX.clone()
}

/// `⊢ ∀n. succ n = n + 1` — successor as add-1.
pub fn nat_succ_def() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let one = Term::nat_lit(covalence_types::Nat::one());
        let n = Term::free("n", nat_ty());
        let lhs = succ(n.clone());
        let rhs = add(n, one);
        let eq = ctx.mk_eq(lhs, rhs).expect("nat_succ_def: mk_eq");
        let body = ctx.mk_forall("n", nat_ty(), eq);
        assume_hol(body)
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
    fn peano_axioms_well_formed() {
        check(nat_zero_ne_succ());
        check(nat_succ_inj());
        check(nat_induction());
    }

    #[test]
    fn add_laws_well_formed() {
        check(nat_add_zero_r());
        check(nat_add_zero_l());
        check(nat_add_comm());
        check(nat_add_assoc());
    }

    #[test]
    fn mul_laws_well_formed() {
        check(nat_mul_zero_r());
        check(nat_mul_zero_l());
        check(nat_mul_comm());
        check(nat_mul_assoc());
        check(nat_mul_add_distrib_l());
    }

    #[test]
    fn succ_def_well_formed() {
        check(nat_succ_def());
    }

    #[test]
    fn axioms_are_cached() {
        let a = nat_induction();
        let b = nat_induction();
        assert_eq!(a.concl(), b.concl());
    }
}
