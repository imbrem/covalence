//! Real numbers `real`.
//!
//! Declared as an opaque HOL type with ordered field + completeness
//! axioms postulated. A future version will swap to a typedef
//! carve-out via Dedekind cuts of rationals (a Dedekind cut is a
//! downward-closed proper subset of `rat` without a maximum, encoded
//! as `rat → bool`), but the postulated surface here is the same.
//!
//! Completeness ("every nonempty bounded-above set has a supremum")
//! is the distinguishing axiom that makes ℝ the unique complete
//! ordered field; without it we'd just have ℚ.

use std::sync::LazyLock;

use crate::HolLightCtx;
use covalence_core::{Term, Thm, Type};

use crate::init::rat;

fn ctx() -> HolLightCtx {
    HolLightCtx::new()
}

fn assume_hol(body: Term) -> Thm {
    Thm::assume(body).expect("init::real: assume")
}

pub fn ty() -> Type {
    Type::tycon("real", vec![])
}

pub fn zero() -> Term {
    Term::const_("real_zero", ty())
}
pub fn one() -> Term {
    Term::const_("real_one", ty())
}
pub fn add_fn() -> Term {
    Term::const_("real_add", Type::fun(ty(), Type::fun(ty(), ty())))
}
pub fn add(a: Term, b: Term) -> Term {
    Term::app(Term::app(add_fn(), a), b)
}
pub fn mul_fn() -> Term {
    Term::const_("real_mul", Type::fun(ty(), Type::fun(ty(), ty())))
}
pub fn mul(a: Term, b: Term) -> Term {
    Term::app(Term::app(mul_fn(), a), b)
}
pub fn neg_fn() -> Term {
    Term::const_("real_neg", Type::fun(ty(), ty()))
}
pub fn neg(a: Term) -> Term {
    Term::app(neg_fn(), a)
}
pub fn inv_fn() -> Term {
    Term::const_("real_inv", Type::fun(ty(), ty()))
}
pub fn inv(a: Term) -> Term {
    Term::app(inv_fn(), a)
}
pub fn lt_fn() -> Term {
    Term::const_(
        "real_lt",
        Type::fun(ty(), Type::fun(ty(), ctx().bool_type())),
    )
}
pub fn lt(a: Term, b: Term) -> Term {
    Term::app(Term::app(lt_fn(), a), b)
}
pub fn rat_to_real_fn() -> Term {
    Term::const_("rat_to_real", Type::fun(rat::ty(), ty()))
}
pub fn of_rat(q: Term) -> Term {
    Term::app(rat_to_real_fn(), q)
}

// ============================================================================
// Field + order + completeness axioms
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

pub fn axiom_add_zero_r() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let a = Term::free("a", ty());
        let eq = ctx
            .mk_eq(add(a.clone(), zero()), a)
            .expect("real add_zero_r");
        let body = ctx.mk_forall("a", ty(), eq);
        assume_hol(body)
    });
    AX.clone()
}

pub fn axiom_add_comm() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        forall_two(|a, b, ctx| {
            ctx.mk_eq(add(a.clone(), b.clone()), add(b, a))
                .expect("real add_comm")
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
            .expect("real add_assoc")
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
            .expect("real add_neg_r");
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
            .expect("real mul_one_r");
        let body = ctx.mk_forall("a", ty(), eq);
        assume_hol(body)
    });
    AX.clone()
}

pub fn axiom_mul_comm() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        forall_two(|a, b, ctx| {
            ctx.mk_eq(mul(a.clone(), b.clone()), mul(b, a))
                .expect("real mul_comm")
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
            .expect("real mul_assoc")
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
            .expect("real mul_distrib_l")
        })
    });
    AX.clone()
}

pub fn axiom_mul_inv() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let a = Term::free("a", ty());
        let zero_eq = ctx
            .mk_eq(a.clone(), zero())
            .expect("real mul_inv: zero_eq");
        let nonzero = ctx.mk_not(zero_eq);
        let prod_eq = ctx
            .mk_eq(mul(a.clone(), inv(a)), one())
            .expect("real mul_inv: prod_eq");
        let imp = ctx.mk_imp(nonzero, prod_eq);
        let body = ctx.mk_forall("a", ty(), imp);
        assume_hol(body)
    });
    AX.clone()
}

/// `⊢ ∀a b c. lt a b ∧ lt b c ⟹ lt a c` — strict order is
/// transitive.
pub fn axiom_lt_trans() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        forall_three(|a, b, c, ctx| {
            let ab = lt(a.clone(), b.clone());
            let bc = lt(b, c.clone());
            let ac = lt(a, c);
            let conj = ctx.mk_and(ab, bc);
            ctx.mk_imp(conj, ac)
        })
    });
    AX.clone()
}

/// `⊢ ∀a b. lt a b ⟹ ¬ lt b a` — strict order is asymmetric.
pub fn axiom_lt_asym() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        forall_two(|a, b, ctx| {
            let ab = lt(a.clone(), b.clone());
            let ba = lt(b, a);
            let not_ba = ctx.mk_not(ba);
            ctx.mk_imp(ab, not_ba)
        })
    });
    AX.clone()
}

/// `⊢ ∀a b. lt a b ∨ a = b ∨ lt b a` — trichotomy.
pub fn axiom_trichotomy() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        forall_two(|a, b, ctx| {
            let ab = lt(a.clone(), b.clone());
            let eq = ctx.mk_eq(a.clone(), b.clone()).expect("real trichotomy eq");
            let ba = lt(b, a);
            let or1 = ctx.mk_or(eq, ba);
            ctx.mk_or(ab, or1)
        })
    });
    AX.clone()
}

/// `⊢ ∀S:real→bool. (∃u. ∀x. S x ⟹ lt x u ∨ x = u) ∧ (∃x. S x) ⟹
///                 ∃sup. (∀x. S x ⟹ lt x sup ∨ x = sup) ∧
///                       (∀ub. (∀x. S x ⟹ lt x ub ∨ x = ub) ⟹ lt sup ub ∨ sup = ub)`
/// — least-upper-bound (Dedekind completeness).
///
/// Postulated as one giant statement; we package it compactly.
pub fn axiom_completeness() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let real_ty = ty();
        let bool_ty = ctx.bool_type();
        let set_ty = Type::fun(real_ty.clone(), bool_ty);
        let s = Term::free("S", set_ty.clone());

        let le = |x: Term, y: Term| -> Term {
            // x ≤ y ≡ lt x y ∨ x = y
            let lt_xy = lt(x.clone(), y.clone());
            let eq = ctx.mk_eq(x, y).expect("real completeness eq");
            ctx.mk_or(lt_xy, eq)
        };

        // Upper-bound predicate over set s
        let is_ub = |u: Term| -> Term {
            let x = Term::free("x", real_ty.clone());
            let s_x = Term::app(s.clone(), x.clone());
            let body = ctx.mk_imp(s_x, le(x, u));
            ctx.mk_forall("x", real_ty.clone(), body)
        };

        // ∃u. is_ub u
        let bounded = {
            let u = Term::free("u", real_ty.clone());
            let body = is_ub(u);
            ctx.mk_exists("u", real_ty.clone(), body)
        };

        // ∃x. S x
        let nonempty = {
            let x = Term::free("x", real_ty.clone());
            let s_x = Term::app(s.clone(), x);
            ctx.mk_exists("x", real_ty.clone(), s_x)
        };

        let antecedent = ctx.mk_and(bounded, nonempty);

        // ∃sup. is_ub sup ∧ ∀ub. is_ub ub ⟹ sup ≤ ub
        let consequent = {
            let sup = Term::free("sup", real_ty.clone());
            let sup_ub = is_ub(sup.clone());
            let least = {
                let ub = Term::free("ub", real_ty.clone());
                let body = ctx.mk_imp(is_ub(ub.clone()), le(sup.clone(), ub));
                ctx.mk_forall("ub", real_ty.clone(), body)
            };
            let body = ctx.mk_and(sup_ub, least);
            ctx.mk_exists("sup", real_ty.clone(), body)
        };

        let imp = ctx.mk_imp(antecedent, consequent);
        let outer = ctx.mk_forall("S", set_ty, imp);
        assume_hol(outer)
    });
    AX.clone()
}

/// `⊢ rat_to_real 0 = 0`.
pub fn axiom_rat_to_real_zero() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let eq = ctx
            .mk_eq(of_rat(rat::zero()), zero())
            .expect("real of_rat_zero: mk_eq");
        assume_hol(eq)
    });
    AX.clone()
}

/// `⊢ ∀p q. rat_to_real (p + q) = rat_to_real p + rat_to_real q`.
pub fn axiom_rat_to_real_add() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let p = Term::free("p", rat::ty());
        let q = Term::free("q", rat::ty());
        let lhs = of_rat(rat::add(p.clone(), q.clone()));
        let rhs = add(of_rat(p), of_rat(q));
        let eq = ctx
            .mk_eq(lhs, rhs)
            .expect("real of_rat_add: mk_eq");
        let inner = ctx.mk_forall("q", rat::ty(), eq);
        let outer = ctx.mk_forall("p", rat::ty(), inner);
        assume_hol(outer)
    });
    AX.clone()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn field_axioms_well_formed() {
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
        ] {
            assert!(ax.concl().type_of().unwrap().is_bool());
        }
    }

    #[test]
    fn order_axioms_well_formed() {
        for ax in [axiom_lt_trans(), axiom_lt_asym(), axiom_trichotomy()] {
            assert!(ax.concl().type_of().unwrap().is_bool());
        }
    }

    #[test]
    fn completeness_axiom_well_formed() {
        let ax = axiom_completeness();
        assert!(ax.concl().type_of().unwrap().is_bool());
    }

    #[test]
    fn embedding_axioms_well_formed() {
        for ax in [axiom_rat_to_real_zero(), axiom_rat_to_real_add()] {
            assert!(ax.concl().type_of().unwrap().is_bool());
        }
    }
}
