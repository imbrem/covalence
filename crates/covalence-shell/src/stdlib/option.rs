//! Polymorphic `option 'a` — `none` or `some x`.

use std::sync::LazyLock;

use covalence_hol::HolLightCtx;
use covalence_pure::{Term, Thm, Type};

fn ctx() -> HolLightCtx {
    HolLightCtx::new()
}

fn assume_hol(body: Term) -> Thm {
    let wrapped = ctx().mk_trueprop(body).expect("stdlib::option: mk_trueprop");
    Thm::assume(wrapped).expect("stdlib::option: assume")
}

/// `option α` — the polymorphic option type.
pub fn ty(alpha: Type) -> Type {
    Type::tycon("option", vec![alpha])
}

pub fn ty_generic() -> Type {
    ty(Type::tfree("a"))
}

/// `none : option α`.
pub fn none_at(alpha: Type) -> Term {
    Term::const_("none", ty(alpha))
}

pub fn none_generic() -> Term {
    none_at(Type::tfree("a"))
}

/// `some : α → option α`.
pub fn some_at(alpha: Type) -> Term {
    Term::const_("some", Type::fun(alpha.clone(), ty(alpha)))
}

pub fn some_generic() -> Term {
    some_at(Type::tfree("a"))
}

pub fn some(x: Term) -> Term {
    let alpha = x.type_of().expect("some: x typed");
    Term::app(some_at(alpha), x)
}

/// `is_some : option α → bool`.
pub fn is_some_at(alpha: Type) -> Term {
    Term::const_("is_some", Type::fun(ty(alpha), ctx().bool_type()))
}

/// `from_some : option α → α` — undefined on `none`; axiomatised on `some`.
pub fn from_some_at(alpha: Type) -> Term {
    Term::const_("from_some", Type::fun(ty(alpha.clone()), alpha))
}

// ============================================================================
// Axioms
// ============================================================================

/// `⊢ ∀x:'a. ∀y:'a. some x = some y ⟹ x = y`.
pub fn axiom_some_inj() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let alpha = Type::tfree("a");
        let x = Term::free("x", alpha.clone());
        let y = Term::free("y", alpha.clone());
        let lhs = ctx
            .mk_eq(
                Term::app(some_at(alpha.clone()), x.clone()),
                Term::app(some_at(alpha.clone()), y.clone()),
            )
            .expect("axiom_some_inj: lhs");
        let rhs = ctx.mk_eq(x, y).expect("axiom_some_inj: rhs");
        let imp = ctx.mk_imp(lhs, rhs);
        let inner = ctx.mk_forall("y", alpha.clone(), imp);
        let outer = ctx.mk_forall("x", alpha, inner);
        assume_hol(outer)
    });
    AX.clone()
}

/// `⊢ ∀x:'a. ¬ (none = some x)`.
pub fn axiom_none_ne_some() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let alpha = Type::tfree("a");
        let x = Term::free("x", alpha.clone());
        let eq = ctx
            .mk_eq(none_at(alpha.clone()), Term::app(some_at(alpha.clone()), x))
            .expect("axiom_none_ne_some: mk_eq");
        let not_eq = ctx.mk_not(eq);
        let body = ctx.mk_forall("x", alpha, not_eq);
        assume_hol(body)
    });
    AX.clone()
}

/// `⊢ ∀x. from_some (some x) = x`.
pub fn axiom_from_some_some() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let alpha = Type::tfree("a");
        let x = Term::free("x", alpha.clone());
        let lhs = Term::app(
            from_some_at(alpha.clone()),
            Term::app(some_at(alpha.clone()), x.clone()),
        );
        let eq = ctx.mk_eq(lhs, x).expect("axiom_from_some_some: mk_eq");
        let body = ctx.mk_forall("x", alpha, eq);
        assume_hol(body)
    });
    AX.clone()
}

/// `⊢ ∀P. P none ∧ (∀x. P (some x)) ⟹ ∀o. P o` — case analysis.
pub fn axiom_option_cases() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let alpha = Type::tfree("a");
        let opt_ty = ty(alpha.clone());
        let pred_ty = Type::fun(opt_ty.clone(), ctx.bool_type());
        let p = Term::free("P", pred_ty.clone());

        let p_none = Term::app(p.clone(), none_at(alpha.clone()));

        let x = Term::free("x", alpha.clone());
        let some_x = Term::app(some_at(alpha.clone()), x);
        let p_some_x = Term::app(p.clone(), some_x);
        let step = ctx.mk_forall("x", alpha.clone(), p_some_x);

        let antecedent = ctx.mk_and(p_none, step);

        let o = Term::free("o", opt_ty.clone());
        let p_o = Term::app(p.clone(), o);
        let consequent = ctx.mk_forall("o", opt_ty, p_o);

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
        let opt_nat = ty(Type::nat());
        assert_eq!(opt_nat, Type::tycon("option", vec![Type::nat()]));
        assert_eq!(none_at(Type::nat()).type_of().unwrap(), opt_nat);
    }

    #[test]
    fn axioms_well_formed() {
        for ax in [
            axiom_some_inj(),
            axiom_none_ne_some(),
            axiom_from_some_some(),
            axiom_option_cases(),
        ] {
            assert!(ax.concl().type_of().unwrap().is_prop());
        }
    }
}
