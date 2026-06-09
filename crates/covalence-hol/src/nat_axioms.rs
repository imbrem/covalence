//! Foundational HOL definitions over Pure's primitive `nat` type.
//!
//! Pure exposes `Type::nat()` + `NatLit` + `Prim::NatArith(_)` and
//! decides closed-form arithmetic by reflexivity via
//! `Thm::reduce_prim`. The HOL-level reasoning machinery for
//! open-form terms is layered on top in two stages:
//!
//! 1. **Definitional axioms** ([`natrec_def_zero`], [`natrec_def_succ`],
//!    [`nat_add_def`], [`nat_mul_def`], [`nat_pred_zero`],
//!    [`nat_pred_succ`], [`nat_sub_def`]) — each is a single equation
//!    that *defines* an operation in terms of more primitive ones.
//!    These plus Peano are the only postulates this module exposes.
//! 2. **Peano axioms** ([`nat_zero_ne_succ`], [`nat_succ_inj`],
//!    [`nat_induction`]) — intrinsic to the `nat` *type*, not to any
//!    operation.
//!
//! Standard algebraic properties (`add_comm`, `add_assoc`, etc.) are
//! *derived theorems*. Today they are still postulated via
//! [`nat_add_comm`] etc. and tagged `TODO: prove from definitional
//! axioms` — those stubs are scheduled to be replaced by real proofs
//! using Peano induction. Consumers depend only on the surface
//! `LazyLock<Thm>` constants, so the swap is invisible.

use std::sync::LazyLock;

use covalence_core::{Arith, Prim, Term, Thm, Type};

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

fn succ_fn() -> Term {
    Term::prim(Prim::NatArith(Arith::Succ))
}

fn succ(t: Term) -> Term {
    Term::app(succ_fn(), t)
}

fn pred_fn() -> Term {
    Term::prim(Prim::NatArith(Arith::Pred))
}

fn pred(t: Term) -> Term {
    Term::app(pred_fn(), t)
}

fn add(a: Term, b: Term) -> Term {
    Term::app(Term::app(Term::prim(Prim::NatArith(Arith::Add)), a), b)
}

fn mul(a: Term, b: Term) -> Term {
    Term::app(Term::app(Term::prim(Prim::NatArith(Arith::Mul)), a), b)
}

fn sub(a: Term, b: Term) -> Term {
    Term::app(Term::app(Term::prim(Prim::NatArith(Arith::Sub)), a), b)
}

fn assume_hol(body: Term) -> Thm {
    let wrapped = ctx()
        .mk_trueprop(body)
        .expect("nat_axioms: axiom body must be HOL bool-typed");
    Thm::assume(wrapped).expect("nat_axioms: Thm::assume on a closed Trueprop cannot fail")
}

// ============================================================================
// Peano axioms — intrinsic to the type
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
// natrec — the primitive-recursion combinator
// ============================================================================

/// `natrec` as a polymorphic HOL constant at carrier α:
/// `natrec : α → (α → α) → nat → α`.
///
/// Iterates a step function `n` times starting from a base value.
/// Combined with [`natrec_def_zero`] and [`natrec_def_succ`] this
/// gives the standard primitive-recursion operator.
pub fn natrec_at(alpha: Type) -> Term {
    // natrec base step n
    // : α → (α → α) → nat → α
    let step_ty = Type::fun(alpha.clone(), alpha.clone());
    let nat = nat_ty();
    let ty = Type::fun(
        alpha.clone(),
        Type::fun(step_ty, Type::fun(nat, alpha)),
    );
    Term::const_("natrec", ty)
}

/// `natrec base step n` — fully applied at carrier α inferred from
/// `base`.
pub fn natrec_apply(base: Term, step: Term, n: Term) -> Term {
    let alpha = base.type_of().expect("natrec_apply: base typed");
    let nr = natrec_at(alpha);
    Term::app(Term::app(Term::app(nr, base), step), n)
}

/// `⊢ ∀base:α. ∀step:α→α. natrec base step 0 = base` —
/// the zero case of primitive recursion.
pub fn natrec_def_zero() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let alpha = Type::tfree("a");
        let step_ty = Type::fun(alpha.clone(), alpha.clone());
        let base = Term::free("base", alpha.clone());
        let step = Term::free("step", step_ty.clone());
        let lhs = natrec_apply(base.clone(), step.clone(), zero());
        let eq = ctx.mk_eq(lhs, base).expect("natrec_def_zero: mk_eq");
        let inner = ctx.mk_forall("step", step_ty, eq);
        let body = ctx.mk_forall("base", alpha, inner);
        assume_hol(body)
    });
    AX.clone()
}

/// `⊢ ∀base:α. ∀step:α→α. ∀n:nat. natrec base step (succ n) =
///                          step (natrec base step n)` —
/// the successor case of primitive recursion.
pub fn natrec_def_succ() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let alpha = Type::tfree("a");
        let step_ty = Type::fun(alpha.clone(), alpha.clone());
        let base = Term::free("base", alpha.clone());
        let step = Term::free("step", step_ty.clone());
        let n = Term::free("n", nat_ty());
        let lhs = natrec_apply(base.clone(), step.clone(), succ(n.clone()));
        let rhs_inner = natrec_apply(base.clone(), step.clone(), n.clone());
        let rhs = Term::app(step.clone(), rhs_inner);
        let eq = ctx.mk_eq(lhs, rhs).expect("natrec_def_succ: mk_eq");
        let inner1 = ctx.mk_forall("n", nat_ty(), eq);
        let inner2 = ctx.mk_forall("step", step_ty, inner1);
        let body = ctx.mk_forall("base", alpha, inner2);
        assume_hol(body)
    });
    AX.clone()
}

// ============================================================================
// Definitional axioms for the Pure arithmetic primitives
//
// Each operator's HOL meaning is fixed by a single equation in terms
// of more primitive ones. Closed literal arithmetic is *already*
// decided by `Thm::reduce_prim` at the Pure level; these axioms
// extend that to open forms and reduce all algebraic reasoning to
// `natrec` (or to `succ`/`pred`).
// ============================================================================

/// `⊢ ∀m n:nat. m + n = natrec m succ n` — addition is `n`-fold
/// successor starting from `m`.
pub fn nat_add_def() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let m = Term::free("m", nat_ty());
        let n = Term::free("n", nat_ty());
        let rhs = natrec_apply(m.clone(), succ_fn(), n.clone());
        let eq = ctx
            .mk_eq(add(m, n), rhs)
            .expect("nat_add_def: mk_eq");
        let inner = ctx.mk_forall("n", nat_ty(), eq);
        let body = ctx.mk_forall("m", nat_ty(), inner);
        assume_hol(body)
    });
    AX.clone()
}

/// `⊢ ∀m n:nat. m * n = natrec 0 (λx. x + m) n` — multiplication is
/// `n`-fold add-of-`m` starting from `0`.
pub fn nat_mul_def() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let m = Term::free("m", nat_ty());
        let n = Term::free("n", nat_ty());
        // step = λx:nat. x + m
        let x = Term::free("x", nat_ty());
        let step_body = add(x, m.clone());
        let step = Term::abs("x", nat_ty(), step_body);
        let rhs = natrec_apply(zero(), step, n.clone());
        let eq = ctx
            .mk_eq(mul(m, n), rhs)
            .expect("nat_mul_def: mk_eq");
        let inner = ctx.mk_forall("n", nat_ty(), eq);
        let body = ctx.mk_forall("m", nat_ty(), inner);
        assume_hol(body)
    });
    AX.clone()
}

/// `⊢ pred 0 = 0` — predecessor saturates at zero.
pub fn nat_pred_zero() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let eq = ctx
            .mk_eq(pred(zero()), zero())
            .expect("nat_pred_zero: mk_eq");
        assume_hol(eq)
    });
    AX.clone()
}

/// `⊢ ∀n:nat. pred (succ n) = n` — predecessor inverts successor.
pub fn nat_pred_succ() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let n = Term::free("n", nat_ty());
        let eq = ctx
            .mk_eq(pred(succ(n.clone())), n)
            .expect("nat_pred_succ: mk_eq");
        let body = ctx.mk_forall("n", nat_ty(), eq);
        assume_hol(body)
    });
    AX.clone()
}

/// `⊢ ∀m n:nat. m - n = natrec m pred n` — saturating subtraction
/// is `n`-fold predecessor starting from `m`.
pub fn nat_sub_def() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let m = Term::free("m", nat_ty());
        let n = Term::free("n", nat_ty());
        let rhs = natrec_apply(m.clone(), pred_fn(), n.clone());
        let eq = ctx
            .mk_eq(sub(m, n), rhs)
            .expect("nat_sub_def: mk_eq");
        let inner = ctx.mk_forall("n", nat_ty(), eq);
        let body = ctx.mk_forall("m", nat_ty(), inner);
        assume_hol(body)
    });
    AX.clone()
}

// ============================================================================
// Derived theorems — currently TODO-postulated.
//
// Each of these is a theorem that *can* be proved from the
// definitional axioms above plus `nat_induction`. They are exposed
// here so consumers don't break when the real proofs land; the
// underlying TCB will then shrink to just the definitional + Peano
// axioms.
// ============================================================================

/// `⊢ ∀n. n + 0 = n`.
///
/// TODO: prove from [`nat_add_def`] + [`natrec_def_zero`]; currently
/// postulated.
pub fn nat_add_zero_r() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let n = Term::free("n", nat_ty());
        let eq = ctx
            .mk_eq(add(n.clone(), zero()), n)
            .expect("nat_add_zero_r: mk_eq");
        let body = ctx.mk_forall("n", nat_ty(), eq);
        assume_hol(body)
    });
    AX.clone()
}

/// `⊢ ∀n. 0 + n = n`.
///
/// TODO: prove from [`nat_add_def`] + [`natrec_def_zero`] +
/// [`natrec_def_succ`] + [`nat_induction`]; currently postulated.
pub fn nat_add_zero_l() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let n = Term::free("n", nat_ty());
        let eq = ctx
            .mk_eq(add(zero(), n.clone()), n)
            .expect("nat_add_zero_l: mk_eq");
        let body = ctx.mk_forall("n", nat_ty(), eq);
        assume_hol(body)
    });
    AX.clone()
}

/// `⊢ ∀m n. m + succ n = succ (m + n)`.
///
/// TODO: prove from [`nat_add_def`] + [`natrec_def_succ`]; currently
/// postulated.
pub fn nat_add_succ_r() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let m = Term::free("m", nat_ty());
        let n = Term::free("n", nat_ty());
        let lhs = add(m.clone(), succ(n.clone()));
        let rhs = succ(add(m, n));
        let eq = ctx.mk_eq(lhs, rhs).expect("nat_add_succ_r: mk_eq");
        let inner = ctx.mk_forall("n", nat_ty(), eq);
        let body = ctx.mk_forall("m", nat_ty(), inner);
        assume_hol(body)
    });
    AX.clone()
}

/// `⊢ ∀m n. m + n = n + m` — addition is commutative.
///
/// TODO: prove by induction on `n` from the basic add lemmas;
/// currently postulated.
pub fn nat_add_comm() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let m = Term::free("m", nat_ty());
        let n = Term::free("n", nat_ty());
        let eq = ctx
            .mk_eq(add(m.clone(), n.clone()), add(n, m))
            .expect("nat_add_comm: mk_eq");
        let inner = ctx.mk_forall("n", nat_ty(), eq);
        let body = ctx.mk_forall("m", nat_ty(), inner);
        assume_hol(body)
    });
    AX.clone()
}

/// `⊢ ∀a b c. (a + b) + c = a + (b + c)` — addition is associative.
///
/// TODO: prove by induction on `c` from [`nat_add_def`] +
/// [`natrec_def_succ`]; currently postulated.
pub fn nat_add_assoc() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let a = Term::free("a", nat_ty());
        let b = Term::free("b", nat_ty());
        let c = Term::free("c", nat_ty());
        let lhs = add(add(a.clone(), b.clone()), c.clone());
        let rhs = add(a, add(b, c));
        let eq = ctx.mk_eq(lhs, rhs).expect("nat_add_assoc: mk_eq");
        let inner1 = ctx.mk_forall("c", nat_ty(), eq);
        let inner2 = ctx.mk_forall("b", nat_ty(), inner1);
        let body = ctx.mk_forall("a", nat_ty(), inner2);
        assume_hol(body)
    });
    AX.clone()
}

/// `⊢ ∀m. m * 0 = 0`.
///
/// TODO: prove from [`nat_mul_def`] + [`natrec_def_zero`]; currently
/// postulated.
pub fn nat_mul_zero_r() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let m = Term::free("m", nat_ty());
        let eq = ctx
            .mk_eq(mul(m, zero()), zero())
            .expect("nat_mul_zero_r: mk_eq");
        let body = ctx.mk_forall("m", nat_ty(), eq);
        assume_hol(body)
    });
    AX.clone()
}

/// `⊢ ∀n. 0 * n = 0`.
///
/// TODO: prove by induction on `n` from the basic mul lemmas;
/// currently postulated.
pub fn nat_mul_zero_l() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let n = Term::free("n", nat_ty());
        let eq = ctx
            .mk_eq(mul(zero(), n), zero())
            .expect("nat_mul_zero_l: mk_eq");
        let body = ctx.mk_forall("n", nat_ty(), eq);
        assume_hol(body)
    });
    AX.clone()
}

/// `⊢ ∀m n. m * (succ n) = m * n + m`.
///
/// TODO: prove from [`nat_mul_def`] + [`natrec_def_succ`] + β; currently
/// postulated.
pub fn nat_mul_succ_r() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let m = Term::free("m", nat_ty());
        let n = Term::free("n", nat_ty());
        let lhs = mul(m.clone(), succ(n.clone()));
        let rhs = add(mul(m.clone(), n), m);
        let eq = ctx.mk_eq(lhs, rhs).expect("nat_mul_succ_r: mk_eq");
        let inner = ctx.mk_forall("n", nat_ty(), eq);
        let body = ctx.mk_forall("m", nat_ty(), inner);
        assume_hol(body)
    });
    AX.clone()
}

/// `⊢ ∀m n. m * n = n * m` — multiplication is commutative.
///
/// TODO: prove from mul lemmas + add_comm via induction; currently
/// postulated.
pub fn nat_mul_comm() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let m = Term::free("m", nat_ty());
        let n = Term::free("n", nat_ty());
        let eq = ctx
            .mk_eq(mul(m.clone(), n.clone()), mul(n, m))
            .expect("nat_mul_comm: mk_eq");
        let inner = ctx.mk_forall("n", nat_ty(), eq);
        let body = ctx.mk_forall("m", nat_ty(), inner);
        assume_hol(body)
    });
    AX.clone()
}

/// `⊢ ∀a b c. (a * b) * c = a * (b * c)` — multiplication is
/// associative.
///
/// TODO: prove via induction; currently postulated.
pub fn nat_mul_assoc() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let a = Term::free("a", nat_ty());
        let b = Term::free("b", nat_ty());
        let c = Term::free("c", nat_ty());
        let lhs = mul(mul(a.clone(), b.clone()), c.clone());
        let rhs = mul(a, mul(b, c));
        let eq = ctx.mk_eq(lhs, rhs).expect("nat_mul_assoc: mk_eq");
        let inner1 = ctx.mk_forall("c", nat_ty(), eq);
        let inner2 = ctx.mk_forall("b", nat_ty(), inner1);
        let body = ctx.mk_forall("a", nat_ty(), inner2);
        assume_hol(body)
    });
    AX.clone()
}

/// `⊢ ∀a b c. a * (b + c) = a*b + a*c` — left distributivity.
///
/// TODO: prove by induction on `c`; currently postulated.
pub fn nat_mul_add_distrib_l() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let a = Term::free("a", nat_ty());
        let b = Term::free("b", nat_ty());
        let c = Term::free("c", nat_ty());
        let lhs = mul(a.clone(), add(b.clone(), c.clone()));
        let rhs = add(mul(a.clone(), b), mul(a, c));
        let eq = ctx
            .mk_eq(lhs, rhs)
            .expect("nat_mul_add_distrib_l: mk_eq");
        let inner1 = ctx.mk_forall("c", nat_ty(), eq);
        let inner2 = ctx.mk_forall("b", nat_ty(), inner1);
        let body = ctx.mk_forall("a", nat_ty(), inner2);
        assume_hol(body)
    });
    AX.clone()
}

/// `⊢ ∀n. succ n = n + 1`.
///
/// TODO: prove from [`nat_add_def`] + [`natrec_def_succ`] +
/// [`natrec_def_zero`]; currently postulated.
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
    fn natrec_def_well_formed() {
        check(natrec_def_zero());
        check(natrec_def_succ());
    }

    #[test]
    fn natrec_at_has_expected_type() {
        let nr = natrec_at(nat_ty());
        let step_ty = Type::fun(nat_ty(), nat_ty());
        let expected = Type::fun(
            nat_ty(),
            Type::fun(step_ty, Type::fun(nat_ty(), nat_ty())),
        );
        assert_eq!(nr.type_of().unwrap(), expected);
    }

    #[test]
    fn definitional_axioms_well_formed() {
        check(nat_add_def());
        check(nat_mul_def());
        check(nat_pred_zero());
        check(nat_pred_succ());
        check(nat_sub_def());
    }

    #[test]
    fn derived_postulates_well_formed() {
        check(nat_add_zero_r());
        check(nat_add_zero_l());
        check(nat_add_succ_r());
        check(nat_add_comm());
        check(nat_add_assoc());
        check(nat_mul_zero_r());
        check(nat_mul_zero_l());
        check(nat_mul_succ_r());
        check(nat_mul_comm());
        check(nat_mul_assoc());
        check(nat_mul_add_distrib_l());
        check(nat_succ_def());
    }

    #[test]
    fn axioms_are_cached() {
        let a = nat_induction();
        let b = nat_induction();
        assert_eq!(a.concl(), b.concl());
    }
}
