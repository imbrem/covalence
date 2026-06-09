//! Polymorphic `either 'a 'b` — `left x` or `right y`.
//!
//! Layered the same way as [`crate::stdlib::option`] /
//! [`crate::stdlib::list`]:
//! 1. Constructor distinctness / injectivity ([`axiom_left_inj`],
//!    [`axiom_right_inj`], [`axiom_left_ne_right`]).
//! 2. Case analysis ([`axiom_either_cases`]).
//! 3. Recursor [`either_rec_at`] / [`either_rec_apply`] with two
//!    defining equations ([`axiom_either_rec_left`],
//!    [`axiom_either_rec_right`]) — defines elimination into any
//!    target carrier γ.

use std::sync::LazyLock;

use crate::HolLightCtx;
use covalence_core::{Term, Thm, Type};

fn ctx() -> HolLightCtx {
    HolLightCtx::new()
}

fn assume_hol(body: Term) -> Thm {
    let wrapped = ctx().mk_trueprop(body).expect("stdlib::either: mk_trueprop");
    Thm::assume(wrapped).expect("stdlib::either: assume")
}

/// `either α β`.
pub fn ty(alpha: Type, beta: Type) -> Type {
    Type::tycon("either", vec![alpha, beta])
}

pub fn ty_generic() -> Type {
    ty(Type::tfree("a"), Type::tfree("b"))
}

/// `left : α → either α β`.
pub fn left_at(alpha: Type, beta: Type) -> Term {
    Term::const_(
        "left",
        Type::fun(alpha.clone(), ty(alpha, beta)),
    )
}

/// `right : β → either α β`.
pub fn right_at(alpha: Type, beta: Type) -> Term {
    Term::const_("right", Type::fun(beta.clone(), ty(alpha, beta)))
}

pub fn left_generic() -> Term {
    left_at(Type::tfree("a"), Type::tfree("b"))
}

pub fn right_generic() -> Term {
    right_at(Type::tfree("a"), Type::tfree("b"))
}

// ============================================================================
// Recursor
// ============================================================================

/// `either_rec : (α → γ) → (β → γ) → either α β → γ`.
///
/// The two arms eliminate the two constructors into any target γ.
pub fn either_rec_at(alpha: Type, beta: Type, gamma: Type) -> Term {
    let f_ty = Type::fun(alpha.clone(), gamma.clone());
    let g_ty = Type::fun(beta.clone(), gamma.clone());
    Term::const_(
        "either_rec",
        Type::fun(f_ty, Type::fun(g_ty, Type::fun(ty(alpha, beta), gamma))),
    )
}

/// `either_rec f g e` — types inferred from `f`'s domain (= α),
/// `g`'s domain (= β), and `f`'s codomain (= γ).
pub fn either_rec_apply(f: Term, g: Term, e: Term) -> Term {
    let f_ty = f.type_of().expect("either_rec_apply: f typed");
    let g_ty = g.type_of().expect("either_rec_apply: g typed");
    let (alpha, gamma) = match f_ty.kind() {
        covalence_core::TypeKind::Fun(a, c) => (a.clone(), c.clone()),
        _ => panic!("either_rec_apply: f must be α → γ"),
    };
    let beta = match g_ty.kind() {
        covalence_core::TypeKind::Fun(b, _) => b.clone(),
        _ => panic!("either_rec_apply: g must be β → γ"),
    };
    let rec = either_rec_at(alpha, beta, gamma);
    Term::app(Term::app(Term::app(rec, f), g), e)
}

/// `⊢ ∀f g x. either_rec f g (left x) = f x`.
pub fn axiom_either_rec_left() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let alpha = Type::tfree("a");
        let beta = Type::tfree("b");
        let gamma = Type::tfree("c");
        let f_ty = Type::fun(alpha.clone(), gamma.clone());
        let g_ty = Type::fun(beta.clone(), gamma.clone());
        let f = Term::free("f", f_ty.clone());
        let g = Term::free("g", g_ty.clone());
        let x = Term::free("x", alpha.clone());
        let lhs = either_rec_apply(
            f.clone(),
            g.clone(),
            Term::app(left_at(alpha.clone(), beta.clone()), x.clone()),
        );
        let rhs = Term::app(f, x);
        let eq = ctx.mk_eq(lhs, rhs).expect("axiom_either_rec_left: mk_eq");
        let i1 = ctx.mk_forall("x", alpha, eq);
        let i2 = ctx.mk_forall("g", g_ty, i1);
        let body = ctx.mk_forall("f", f_ty, i2);
        assume_hol(body)
    });
    AX.clone()
}

/// `⊢ ∀f g y. either_rec f g (right y) = g y`.
pub fn axiom_either_rec_right() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let alpha = Type::tfree("a");
        let beta = Type::tfree("b");
        let gamma = Type::tfree("c");
        let f_ty = Type::fun(alpha.clone(), gamma.clone());
        let g_ty = Type::fun(beta.clone(), gamma.clone());
        let f = Term::free("f", f_ty.clone());
        let g = Term::free("g", g_ty.clone());
        let y = Term::free("y", beta.clone());
        let lhs = either_rec_apply(
            f.clone(),
            g.clone(),
            Term::app(right_at(alpha.clone(), beta.clone()), y.clone()),
        );
        let rhs = Term::app(g, y);
        let eq = ctx.mk_eq(lhs, rhs).expect("axiom_either_rec_right: mk_eq");
        let i1 = ctx.mk_forall("y", beta, eq);
        let i2 = ctx.mk_forall("g", g_ty, i1);
        let body = ctx.mk_forall("f", f_ty, i2);
        assume_hol(body)
    });
    AX.clone()
}

/// `⊢ ∀x x'. left x = left x' ⟹ x = x'`.
pub fn axiom_left_inj() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let alpha = Type::tfree("a");
        let beta = Type::tfree("b");
        let x = Term::free("x", alpha.clone());
        let y = Term::free("y", alpha.clone());
        let lhs = ctx
            .mk_eq(
                Term::app(left_at(alpha.clone(), beta.clone()), x.clone()),
                Term::app(left_at(alpha.clone(), beta.clone()), y.clone()),
            )
            .expect("axiom_left_inj: lhs");
        let rhs = ctx.mk_eq(x, y).expect("axiom_left_inj: rhs");
        let imp = ctx.mk_imp(lhs, rhs);
        let inner = ctx.mk_forall("y", alpha.clone(), imp);
        let outer = ctx.mk_forall("x", alpha, inner);
        assume_hol(outer)
    });
    AX.clone()
}

/// `⊢ ∀x x'. right x = right x' ⟹ x = x'`.
pub fn axiom_right_inj() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let alpha = Type::tfree("a");
        let beta = Type::tfree("b");
        let x = Term::free("x", beta.clone());
        let y = Term::free("y", beta.clone());
        let lhs = ctx
            .mk_eq(
                Term::app(right_at(alpha.clone(), beta.clone()), x.clone()),
                Term::app(right_at(alpha.clone(), beta.clone()), y.clone()),
            )
            .expect("axiom_right_inj: lhs");
        let rhs = ctx.mk_eq(x, y).expect("axiom_right_inj: rhs");
        let imp = ctx.mk_imp(lhs, rhs);
        let inner = ctx.mk_forall("y", beta.clone(), imp);
        let outer = ctx.mk_forall("x", beta, inner);
        assume_hol(outer)
    });
    AX.clone()
}

/// `⊢ ∀x:α y:β. ¬ (left x = right y)`.
pub fn axiom_left_ne_right() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let alpha = Type::tfree("a");
        let beta = Type::tfree("b");
        let x = Term::free("x", alpha.clone());
        let y = Term::free("y", beta.clone());
        let eq = ctx
            .mk_eq(
                Term::app(left_at(alpha.clone(), beta.clone()), x),
                Term::app(right_at(alpha.clone(), beta.clone()), y),
            )
            .expect("axiom_left_ne_right: mk_eq");
        let not_eq = ctx.mk_not(eq);
        let inner = ctx.mk_forall("y", beta, not_eq);
        let outer = ctx.mk_forall("x", alpha, inner);
        assume_hol(outer)
    });
    AX.clone()
}

/// `⊢ ∀P. (∀x. P (left x)) ∧ (∀y. P (right y)) ⟹ ∀e. P e` — case analysis.
pub fn axiom_either_cases() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let alpha = Type::tfree("a");
        let beta = Type::tfree("b");
        let e_ty = ty(alpha.clone(), beta.clone());
        let pred_ty = Type::fun(e_ty.clone(), ctx.bool_type());
        let p = Term::free("P", pred_ty.clone());

        let x = Term::free("x", alpha.clone());
        let p_left_x = Term::app(
            p.clone(),
            Term::app(left_at(alpha.clone(), beta.clone()), x),
        );
        let left_branch = ctx.mk_forall("x", alpha.clone(), p_left_x);

        let y = Term::free("y", beta.clone());
        let p_right_y = Term::app(
            p.clone(),
            Term::app(right_at(alpha.clone(), beta.clone()), y),
        );
        let right_branch = ctx.mk_forall("y", beta.clone(), p_right_y);

        let antecedent = ctx.mk_and(left_branch, right_branch);

        let e = Term::free("e", e_ty.clone());
        let p_e = Term::app(p.clone(), e);
        let consequent = ctx.mk_forall("e", e_ty, p_e);

        let imp = ctx.mk_imp(antecedent, consequent);
        let body = ctx.mk_forall("P", pred_ty, imp);
        assume_hol(body)
    });
    AX.clone()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn types() {
        let e = ty(Type::nat(), Type::int());
        assert_eq!(e, Type::tycon("either", vec![Type::nat(), Type::int()]));
    }

    #[test]
    fn axioms_well_formed() {
        for ax in [
            axiom_left_inj(),
            axiom_right_inj(),
            axiom_left_ne_right(),
            axiom_either_cases(),
        ] {
            assert!(ax.concl().type_of().unwrap().is_prop());
        }
    }

    #[test]
    fn either_rec_at_has_function_type() {
        let r = either_rec_at(Type::nat(), Type::int(), Type::nat());
        let f_ty = Type::fun(Type::nat(), Type::nat());
        let g_ty = Type::fun(Type::int(), Type::nat());
        let expected = Type::fun(
            f_ty,
            Type::fun(g_ty, Type::fun(ty(Type::nat(), Type::int()), Type::nat())),
        );
        assert_eq!(r.type_of().unwrap(), expected);
    }

    #[test]
    fn rec_axioms_well_formed() {
        for ax in [axiom_either_rec_left(), axiom_either_rec_right()] {
            assert!(ax.concl().type_of().unwrap().is_prop());
        }
    }
}
