//! Foundational HOL definitions over the kernel's primitive `nat` type.
//!
//! `covalence-core` exposes [`Type::nat`] + the `Nat` literal
//! ([`Term::nat_lit`]) and decides *closed-form* arithmetic by
//! reflexivity via [`Thm::reduce_prim`] — the `nat_add`/`nat_mul`/…
//! [`covalence_core::defs`] specs reduce on literal arguments inside
//! the kernel. The HOL-level reasoning machinery for *open-form*
//! terms is layered on top here in two stages:
//!
//! 1. **Definitional axioms** ([`natrec_def_zero`], [`natrec_def_succ`],
//!    [`nat_add_def`], [`nat_mul_def`], [`nat_pred_zero`],
//!    [`nat_pred_succ`], [`nat_sub_def`]) — each is a single equation
//!    that *defines* an operation in terms of more primitive ones.
//!    These plus Peano are the only postulates this module exposes.
//! 2. **Peano axioms** ([`nat_zero_ne_succ`], [`nat_succ_inj`],
//!    [`nat_induction`]) — intrinsic to the `nat` *type*, not to any
//!    operation. [`nat_induction`] is now *derived* from the kernel's
//!    induction rule [`Thm::nat_induct`] (hyp-free); the other two are
//!    still postulated downstream (see below).
//!
//! Standard algebraic properties (`add_comm`, `add_assoc`, etc.) are
//! *derived theorems*. Today they are still postulated via
//! [`nat_add_comm`] etc. and tagged `TODO: prove from definitional
//! axioms` — those stubs are scheduled to be replaced by real proofs
//! using the induction rule [`Thm::nat_induct`].
//! Consumers depend only on the surface `LazyLock<Thm>` constants, so
//! the swap is invisible.

use std::sync::LazyLock;

use covalence_core::{defs, Term, Thm, Type};

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
    defs::nat_succ()
}

fn succ(t: Term) -> Term {
    Term::app(succ_fn(), t)
}

fn add(a: Term, b: Term) -> Term {
    Term::app(Term::app(defs::nat_add(), a), b)
}

fn mul(a: Term, b: Term) -> Term {
    Term::app(Term::app(defs::nat_mul(), a), b)
}

fn assume_hol(body: Term) -> Thm {
        Thm::assume(body).expect("nat_axioms: Thm::assume on a closed bool body cannot fail")
}

// ============================================================================
// Peano axioms — intrinsic to the type
// ============================================================================

/// `⊢ ∀P:nat→bool. P 0 ∧ (∀n. P n ⟹ P (succ n)) ⟹ ∀n. P n` —
/// the classic induction *axiom*, now **derived** (hyp-free) from the
/// kernel's induction *rule* [`Thm::nat_induct`]: assume the
/// conjunction, split it with `and_elim`, `all_elim` the step at a
/// fresh `n`, apply the rule, then discharge and generalise.
pub fn nat_induction() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let pred_ty = Type::fun(nat_ty(), Type::bool());
        let p = Term::free("P", pred_ty.clone());
        let n = Term::free("n", nat_ty());

        // antecedent: P 0 ∧ (∀n. P n ⟹ P (succ n))
        let p0 = Term::app(p.clone(), zero());
        let step_body = ctx.mk_imp(
            Term::app(p.clone(), n.clone()),
            Term::app(p.clone(), succ(n.clone())),
        );
        let step_all = ctx.mk_forall("n", nat_ty(), step_body);
        let ante = ctx.mk_and(p0, step_all);

        let h = Thm::assume(ante.clone()).expect("nat_induction: assume");
        let base = h.clone().and_elim_l().expect("nat_induction: and_elim_l");
        let step = h
            .and_elim_r()
            .expect("nat_induction: and_elim_r")
            .all_elim(n)
            .expect("nat_induction: all_elim step");

        Thm::nat_induct(base, step)
            .expect("nat_induction: nat_induct rule") // {ante} ⊢ ∀n. P n
            .imp_intro(&ante)
            .expect("nat_induction: imp_intro")
            .all_intro("P", pred_ty)
            .expect("nat_induction: all_intro P")
    });
    AX.clone()
}

/// `⊢ ∀n:nat. ¬(0 = succ n)` — zero is never a successor.
///
/// Postulated via `Thm::assume`. A future derivation goes through
/// [`Thm::nat_induct`]
/// with the predicate `P n = ¬(0 = succ n)`; the base case `¬(0 = 1)`
/// is already derived in [`crate::proofs::nat::nat_zero_ne_one`] from
/// `Thm::reduce_prim` on the closed literals.
pub fn nat_zero_ne_succ() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let n = Term::free("n", nat_ty());
        let eq = ctx
            .mk_eq(zero(), succ(n))
            .expect("nat_zero_ne_succ: mk_eq");
        let neg = ctx.mk_not(eq);
        let body = ctx.mk_forall("n", nat_ty(), neg);
        assume_hol(body)
    });
    AX.clone()
}

/// `⊢ ∀m n:nat. succ m = succ n ⟹ m = n` — successor is injective.
///
/// Postulated via `Thm::assume`. A future derivation applies `pred`
/// to both sides via `cong_app` and uses `pred (succ k) = k`
/// ([`nat_pred_succ`]) twice; it lands once the postulate-free
/// `nat_pred_*` proofs do.
pub fn nat_succ_inj() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let m = Term::free("m", nat_ty());
        let n = Term::free("n", nat_ty());
        let succ_eq = ctx
            .mk_eq(succ(m.clone()), succ(n.clone()))
            .expect("nat_succ_inj: mk_eq succ");
        let mn_eq = ctx
            .mk_eq(m.clone(), n.clone())
            .expect("nat_succ_inj: mk_eq mn");
        let imp = ctx.mk_imp(succ_eq, mn_eq);
        let inner = ctx.mk_forall("n", nat_ty(), imp);
        let body = ctx.mk_forall("m", nat_ty(), inner);
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

// The following five facts (`nat_add_def`, `nat_mul_def`,
// `nat_pred_zero`, `nat_pred_succ`, `nat_sub_def`) were previously
// kernel axioms exposed on `Thm::*`. They are now derivable from
// `Thm::nat_induct` + `Thm::define` (introducing `+`/`*`/`pred`/
// `-` from `natrec` is a `define` call; their defining equations are
// then automatic, and the recursion-step equations follow by
// induction). Until the WASM-proof rewrite lands those derivations,
// we postulate them downstream via the standard `Thm::assume(body)`
// pattern. Each Thm carries a self-hyp marking it as unproved.

/// `⊢ ∀m n:nat. m + n = natrec m succ n` — addition as `n`-fold
/// successor starting from `m`. Postulated via `Thm::assume`; the
/// resulting Thm has the body itself as a single hypothesis.
pub fn nat_add_def() -> Thm {
    let m = Term::free("m", nat_ty());
    let n = Term::free("n", nat_ty());
    let lhs = add(m.clone(), n.clone());
    let rhs = natrec_apply(m.clone(), succ_fn(), n.clone());
    let eq = ctx().mk_eq(lhs, rhs).expect("nat_add_def: mk_eq");
    let inner = ctx().mk_forall("n", nat_ty(), eq);
    let body = ctx().mk_forall("m", nat_ty(), inner);
    assume_hol(body)
}

/// `⊢ ∀m n:nat. m * n = natrec 0 (λx. x + m) n` — multiplication as
/// `n`-fold add-of-`m`. Postulated via `Thm::assume`.
pub fn nat_mul_def() -> Thm {
    let m = Term::free("m", nat_ty());
    let n = Term::free("n", nat_ty());
    let lhs = mul(m.clone(), n.clone());
    // step = λx:nat. x + m
    let x = Term::free("x", nat_ty());
    let step_body = add(x, m.clone());
    // Use the kernel `close`+`abs` path directly: defs/* uses this
    // same pattern. `HolLightCtx` doesn't expose `mk_abs` because
    // `Term::abs` is already the user-facing entry point.
    let step_closed = covalence_core::subst::close(&step_body, "x");
    let step = Term::abs("x", nat_ty(), step_closed);
    let rhs = natrec_apply(zero(), step, n.clone());
    let eq = ctx().mk_eq(lhs, rhs).expect("nat_mul_def: mk_eq");
    let inner = ctx().mk_forall("n", nat_ty(), eq);
    let body = ctx().mk_forall("m", nat_ty(), inner);
    assume_hol(body)
}

/// `⊢ pred 0 = 0` — predecessor saturates at zero. Postulated via
/// `Thm::assume`.
pub fn nat_pred_zero() -> Thm {
    let lhs = Term::app(defs::nat_pred(), zero());
    let body = ctx().mk_eq(lhs, zero()).expect("nat_pred_zero: mk_eq");
    assume_hol(body)
}

/// `⊢ ∀n:nat. pred (succ n) = n` — predecessor inverts successor.
/// Postulated via `Thm::assume`.
pub fn nat_pred_succ() -> Thm {
    let n = Term::free("n", nat_ty());
    let lhs = Term::app(defs::nat_pred(), succ(n.clone()));
    let eq = ctx().mk_eq(lhs, n).expect("nat_pred_succ: mk_eq");
    let body = ctx().mk_forall("n", nat_ty(), eq);
    assume_hol(body)
}

/// `⊢ ∀m n:nat. m - n = natrec m pred n` — saturating subtraction as
/// `n`-fold predecessor. Postulated via `Thm::assume`.
pub fn nat_sub_def() -> Thm {
    let m = Term::free("m", nat_ty());
    let n = Term::free("n", nat_ty());
    let lhs = Term::app(Term::app(defs::nat_sub(), m.clone()), n.clone());
    let rhs = natrec_apply(m.clone(), defs::nat_pred(), n.clone());
    let eq = ctx().mk_eq(lhs, rhs).expect("nat_sub_def: mk_eq");
    let inner = ctx().mk_forall("n", nat_ty(), eq);
    let body = ctx().mk_forall("m", nat_ty(), inner);
    assume_hol(body)
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

    /// Assume-style axiom: hyp = concl (one hypothesis, the axiom
    /// itself). The self-hyp pattern serves as the audit trail.
    fn check(ax: Thm) {
        assert!(ax.concl().type_of().unwrap().is_bool());
        assert_eq!(ax.hyps().len(), 1);
        assert_eq!(ax.hyps().iter().next().unwrap(), ax.concl());
    }

    /// Hyp-free theorem: empty hyps, `bool`-typed conclusion.
    fn check_kernel(ax: Thm) {
        let ty = ax.concl().type_of().unwrap();
        assert!(ty.is_bool(), "conclusion {ty} is not bool");
        assert!(ax.hyps().is_empty(), "expected no hyps");
    }

    #[test]
    fn peano_axioms_well_formed() {
        // `nat_induction` is now derived from the kernel rule
        // `Thm::nat_induct` — hyp-free.
        check_kernel(nat_induction());
        // `nat_zero_ne_succ` / `nat_succ_inj` are postulated via
        // `Thm::assume` until their induction-based derivations land;
        // each carries one self-hyp.
        check(nat_zero_ne_succ());
        check(nat_succ_inj());
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
        // Each fact has one self-hyp (`Thm::assume(body)` shape) —
        // they're postulated downstream until the WASM-proof rewrite
        // derives them from `nat_induction` + `define`. `check`
        // accepts a single hyp; `check_kernel` requires zero.
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
