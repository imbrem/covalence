//! Function combinators — identity and composition.
//!
//! Both are polymorphic: `id : 'a → 'a` and
//! `compose : ('b → 'c) → ('a → 'b) → ('a → 'c)`.
//!
//! Both are declared as HOL constants with postulated defining
//! equations. Closed-form facts (`id (lit 5) = lit 5`) and
//! composition laws (`id ∘ f = f`, `compose_assoc`) are exposed
//! as `LazyLock<Thm>` axioms, instantiated polymorphically via
//! [`inst_tfree`] when downstream callers need them at a specific
//! type.

use std::sync::LazyLock;

use covalence_hol::HolLightCtx;
use covalence_pure::{Term, Thm, Type};

fn ctx() -> HolLightCtx {
    HolLightCtx::new()
}

fn assume_hol(body: Term) -> Thm {
    let wrapped = ctx()
        .mk_trueprop(body)
        .expect("stdlib::fun: axiom body must be HOL bool-typed");
    Thm::assume(wrapped).expect("stdlib::fun: assume on closed Trueprop cannot fail")
}

// ============================================================================
// Identity
// ============================================================================

/// `id` at a specific carrier type α — `Term::const_("id", α → α)`.
pub fn id_at(alpha: Type) -> Term {
    Term::const_("id", Type::fun(alpha.clone(), alpha))
}

/// `id` at the generic `'a` (instantiate via `inst_tfree`).
pub fn id_generic() -> Term {
    id_at(Type::tfree("a"))
}

/// Apply `id` to a term `x`. Type-inferred from `x`'s type.
pub fn id_app(x: Term) -> Term {
    let alpha = x.type_of().expect("stdlib::fun::id_app: x must be typed");
    Term::app(id_at(alpha), x)
}

/// `⊢ ∀x:'a. id x = x` — the defining equation of `id`.
pub fn axiom_id_def() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let alpha = Type::tfree("a");
        let x = Term::free("x", alpha.clone());
        let lhs = Term::app(id_at(alpha.clone()), x.clone());
        let eq = ctx.mk_eq(lhs, x).expect("axiom_id_def: mk_eq");
        let body = ctx.mk_forall("x", alpha, eq);
        assume_hol(body)
    });
    AX.clone()
}

/// Specialise the `id` defining equation at a specific α.
pub fn axiom_id_def_at(alpha: Type) -> Thm {
    axiom_id_def()
        .inst_tfree("a", alpha)
        .expect("axiom_id_def_at: inst_tfree on 'a")
}

// ============================================================================
// Composition
// ============================================================================

/// `compose` at carrier types `(α, β, γ)` — type `(β → γ) → (α → β) → (α → γ)`.
pub fn compose_at(alpha: Type, beta: Type, gamma: Type) -> Term {
    let ty = Type::fun(
        Type::fun(beta.clone(), gamma.clone()),
        Type::fun(Type::fun(alpha.clone(), beta), Type::fun(alpha, gamma)),
    );
    Term::const_("compose", ty)
}

/// `compose` at the generic `('a, 'b, 'c)`.
pub fn compose_generic() -> Term {
    compose_at(Type::tfree("a"), Type::tfree("b"), Type::tfree("c"))
}

/// `compose f g x` — fully applied. Types inferred from `f`'s type
/// (which must be `β → γ`).
pub fn compose_apply(f: Term, g: Term, x: Term) -> Term {
    let f_ty = f.type_of().expect("compose_apply: f typed");
    let g_ty = g.type_of().expect("compose_apply: g typed");
    let (beta, gamma) = match f_ty.kind() {
        covalence_pure::TypeKind::Fun(b, c) => (b.clone(), c.clone()),
        _ => panic!("compose_apply: f must be a function"),
    };
    let alpha = match g_ty.kind() {
        covalence_pure::TypeKind::Fun(a, _) => a.clone(),
        _ => panic!("compose_apply: g must be a function"),
    };
    let comp = compose_at(alpha, beta, gamma);
    Term::app(Term::app(Term::app(comp, f), g), x)
}

/// `⊢ ∀f:'b→'c. ∀g:'a→'b. ∀x:'a. compose f g x = f (g x)` — the
/// defining equation of `compose`.
pub fn axiom_compose_def() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let alpha = Type::tfree("a");
        let beta = Type::tfree("b");
        let gamma = Type::tfree("c");

        let f_ty = Type::fun(beta.clone(), gamma.clone());
        let g_ty = Type::fun(alpha.clone(), beta.clone());

        let f = Term::free("f", f_ty.clone());
        let g = Term::free("g", g_ty.clone());
        let x = Term::free("x", alpha.clone());

        let comp = compose_at(alpha.clone(), beta.clone(), gamma.clone());
        let lhs = Term::app(Term::app(Term::app(comp, f.clone()), g.clone()), x.clone());
        let rhs = Term::app(f, Term::app(g, x));
        let eq = ctx.mk_eq(lhs, rhs).expect("axiom_compose_def: mk_eq");
        let inner1 = ctx.mk_forall("x", alpha, eq);
        let inner2 = ctx.mk_forall("g", g_ty, inner1);
        let outer = ctx.mk_forall("f", f_ty, inner2);
        assume_hol(outer)
    });
    AX.clone()
}

/// `⊢ ∀f:'a→'b. compose id f = f` — left identity (id ∘ f = f at function level).
pub fn axiom_id_compose_l() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let alpha = Type::tfree("a");
        let beta = Type::tfree("b");
        let f_ty = Type::fun(alpha.clone(), beta.clone());
        let f = Term::free("f", f_ty.clone());

        let comp = compose_at(alpha.clone(), beta.clone(), beta.clone());
        let lhs = Term::app(Term::app(comp, id_at(beta)), f.clone());
        let eq = ctx.mk_eq(lhs, f).expect("axiom_id_compose_l: mk_eq");
        let body = ctx.mk_forall("f", f_ty, eq);
        assume_hol(body)
    });
    AX.clone()
}

/// `⊢ ∀f:'a→'b. compose f id = f` — right identity.
pub fn axiom_id_compose_r() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let alpha = Type::tfree("a");
        let beta = Type::tfree("b");
        let f_ty = Type::fun(alpha.clone(), beta.clone());
        let f = Term::free("f", f_ty.clone());

        let comp = compose_at(alpha.clone(), alpha.clone(), beta);
        let lhs = Term::app(Term::app(comp, f.clone()), id_at(alpha));
        let eq = ctx.mk_eq(lhs, f).expect("axiom_id_compose_r: mk_eq");
        let body = ctx.mk_forall("f", f_ty, eq);
        assume_hol(body)
    });
    AX.clone()
}

/// `⊢ ∀f g h. (f ∘ g) ∘ h = f ∘ (g ∘ h)` — associativity.
pub fn axiom_compose_assoc() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let alpha = Type::tfree("a"); // h : α → β
        let beta = Type::tfree("b"); // g : β → γ
        let gamma = Type::tfree("c"); // f : γ → δ
        let delta = Type::tfree("d");

        let h_ty = Type::fun(alpha.clone(), beta.clone());
        let g_ty = Type::fun(beta.clone(), gamma.clone());
        let f_ty = Type::fun(gamma.clone(), delta.clone());

        let h = Term::free("h", h_ty.clone());
        let g = Term::free("g", g_ty.clone());
        let f = Term::free("f", f_ty.clone());

        // (f ∘ g) ∘ h
        let comp_fg = compose_at(beta.clone(), gamma.clone(), delta.clone());
        let fg = Term::app(Term::app(comp_fg, f.clone()), g.clone());
        let comp_fg_h = compose_at(alpha.clone(), beta.clone(), delta.clone());
        let lhs = Term::app(Term::app(comp_fg_h, fg), h.clone());

        // f ∘ (g ∘ h)
        let comp_gh = compose_at(alpha.clone(), beta, gamma.clone());
        let gh = Term::app(Term::app(comp_gh, g), h);
        let comp_f_gh = compose_at(alpha.clone(), gamma, delta);
        let rhs = Term::app(Term::app(comp_f_gh, f), gh);

        let eq = ctx.mk_eq(lhs, rhs).expect("axiom_compose_assoc: mk_eq");
        let inner1 = ctx.mk_forall("h", h_ty, eq);
        let inner2 = ctx.mk_forall("g", g_ty, inner1);
        let outer = ctx.mk_forall("f", f_ty, inner2);
        assume_hol(outer)
    });
    AX.clone()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn check(ax: Thm) {
        assert!(ax.concl().type_of().unwrap().is_prop());
    }

    #[test]
    fn id_axioms_well_formed() {
        check(axiom_id_def());
        check(axiom_id_def_at(Type::nat()));
    }

    #[test]
    fn compose_axioms_well_formed() {
        check(axiom_compose_def());
        check(axiom_id_compose_l());
        check(axiom_id_compose_r());
        check(axiom_compose_assoc());
    }

    #[test]
    fn id_at_has_function_type() {
        let id_nat = id_at(Type::nat());
        assert_eq!(
            id_nat.type_of().unwrap(),
            Type::fun(Type::nat(), Type::nat())
        );
    }

    #[test]
    fn compose_at_has_correct_type() {
        let c = compose_at(Type::nat(), Type::int(), Type::nat());
        let ty = c.type_of().unwrap();
        assert_eq!(
            ty,
            Type::fun(
                Type::fun(Type::int(), Type::nat()),
                Type::fun(
                    Type::fun(Type::nat(), Type::int()),
                    Type::fun(Type::nat(), Type::nat())
                )
            )
        );
    }
}
