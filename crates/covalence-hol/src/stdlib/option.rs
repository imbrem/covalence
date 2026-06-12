//! Polymorphic `option 'a` — `none` or `some x`.
//!
//! Layered the same way as [`crate::stdlib::nat`]:
//! 1. **Distinctness / injectivity** of the constructors
//!    ([`axiom_none_ne_some`], [`axiom_some_inj`]).
//! 2. **Recursor** [`option_rec_at`] / [`option_rec_apply`] with
//!    its two defining equations ([`axiom_option_rec_none`],
//!    [`axiom_option_rec_some`]).
//! 3. **Operations** (`is_some`, `from_some`, `map`, `bind`) each
//!    fixed by a single definitional axiom in terms of
//!    `option_rec`.
//! 4. **Derived theorems** (`axiom_map_none`, `axiom_map_some`,
//!    `axiom_bind_none`, `axiom_bind_some`, `axiom_from_some_some`)
//!    — currently TODO-postulated, scheduled to be replaced by
//!    proofs from the definitional layer + [`axiom_option_cases`].

use std::sync::LazyLock;

use crate::HolLightCtx;
use covalence_core::{Term, Thm, Type};

fn ctx() -> HolLightCtx {
    HolLightCtx::new()
}

fn assume_hol(body: Term) -> Thm {
    Thm::assume(body).expect("stdlib::option: assume")
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
// Recursor
// ============================================================================

/// `option_rec : β → (α → β) → option α → β` at carriers (α, β).
pub fn option_rec_at(alpha: Type, beta: Type) -> Term {
    let step_ty = Type::fun(alpha.clone(), beta.clone());
    let ty = Type::fun(
        beta.clone(),
        Type::fun(step_ty, Type::fun(ty(alpha), beta)),
    );
    Term::const_("option_rec", ty)
}

/// `option_rec base step opt` — types inferred from `base` (the β) and `opt` (the option α).
pub fn option_rec_apply(base: Term, step: Term, opt: Term) -> Term {
    let beta = base.type_of().expect("option_rec_apply: base typed");
    let opt_ty = opt.type_of().expect("option_rec_apply: opt typed");
    let alpha = match opt_ty.kind() {
        covalence_core::TypeKind::Tycon(_, args) if args.len() == 1 => args[0].clone(),
        _ => panic!("option_rec_apply: opt must have type `option α`"),
    };
    let rec = option_rec_at(alpha, beta);
    Term::app(Term::app(Term::app(rec, base), step), opt)
}

// ============================================================================
// Constructor distinctness / injectivity
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

/// `⊢ ∀P. P none ∧ (∀x. P (some x)) ⟹ ∀o. P o` — case analysis.
/// This is option's induction principle (no recursive case to make
/// it an actual induction — option is non-recursive).
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

// ============================================================================
// Definitional axioms for option_rec
// ============================================================================

/// `⊢ ∀base step. option_rec base step none = base`.
pub fn axiom_option_rec_none() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let alpha = Type::tfree("a");
        let beta = Type::tfree("b");
        let step_ty = Type::fun(alpha.clone(), beta.clone());
        let base = Term::free("base", beta.clone());
        let step = Term::free("step", step_ty.clone());
        let lhs = option_rec_apply(base.clone(), step.clone(), none_at(alpha));
        let eq = ctx.mk_eq(lhs, base).expect("axiom_option_rec_none: mk_eq");
        let inner = ctx.mk_forall("step", step_ty, eq);
        let body = ctx.mk_forall("base", beta, inner);
        assume_hol(body)
    });
    AX.clone()
}

/// `⊢ ∀base step x. option_rec base step (some x) = step x`.
pub fn axiom_option_rec_some() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let alpha = Type::tfree("a");
        let beta = Type::tfree("b");
        let step_ty = Type::fun(alpha.clone(), beta.clone());
        let base = Term::free("base", beta.clone());
        let step = Term::free("step", step_ty.clone());
        let x = Term::free("x", alpha.clone());
        let lhs = option_rec_apply(
            base.clone(),
            step.clone(),
            Term::app(some_at(alpha.clone()), x.clone()),
        );
        let rhs = Term::app(step.clone(), x);
        let eq = ctx.mk_eq(lhs, rhs).expect("axiom_option_rec_some: mk_eq");
        let inner1 = ctx.mk_forall("x", alpha, eq);
        let inner2 = ctx.mk_forall("step", step_ty, inner1);
        let body = ctx.mk_forall("base", beta, inner2);
        assume_hol(body)
    });
    AX.clone()
}

// ============================================================================
// Operations
// ============================================================================

/// `map : ('a → 'b) → option 'a → option 'b`.
pub fn map_at(alpha: Type, beta: Type) -> Term {
    let f_ty = Type::fun(alpha.clone(), beta.clone());
    Term::const_(
        "option_map",
        Type::fun(f_ty, Type::fun(ty(alpha), ty(beta))),
    )
}

/// `bind : option 'a → ('a → option 'b) → option 'b` — monadic bind.
pub fn bind_at(alpha: Type, beta: Type) -> Term {
    let k_ty = Type::fun(alpha.clone(), ty(beta.clone()));
    Term::const_(
        "option_bind",
        Type::fun(ty(alpha), Type::fun(k_ty, ty(beta))),
    )
}

// ============================================================================
// Definitional axioms for the operations
// ============================================================================

/// `⊢ ∀f opt. map f opt = option_rec none (λx. some (f x)) opt` —
/// definitional axiom for `option_map`.
pub fn axiom_map_def() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let alpha = Type::tfree("a");
        let beta = Type::tfree("b");
        let f_ty = Type::fun(alpha.clone(), beta.clone());
        let f = Term::free("f", f_ty.clone());
        let opt = Term::free("opt", ty(alpha.clone()));

        let lhs = Term::app(Term::app(map_at(alpha.clone(), beta.clone()), f.clone()), opt.clone());

        // step = λx:α. some (f x) — produces option β
        let x = Term::free("x", alpha.clone());
        let f_x = Term::app(f.clone(), x);
        let some_fx = Term::app(some_at(beta.clone()), f_x);
        let step = Term::abs("x", alpha.clone(), some_fx);
        let rhs = option_rec_apply(none_at(beta.clone()), step, opt);

        let eq = ctx.mk_eq(lhs, rhs).expect("axiom_map_def: mk_eq");
        let inner = ctx.mk_forall("opt", ty(alpha), eq);
        let body = ctx.mk_forall("f", f_ty, inner);
        assume_hol(body)
    });
    AX.clone()
}

/// `⊢ ∀opt k. bind opt k = option_rec none k opt` — definitional
/// axiom for `option_bind`.
pub fn axiom_bind_def() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let alpha = Type::tfree("a");
        let beta = Type::tfree("b");
        let k_ty = Type::fun(alpha.clone(), ty(beta.clone()));
        let k = Term::free("k", k_ty.clone());
        let opt = Term::free("opt", ty(alpha.clone()));
        let lhs = Term::app(Term::app(bind_at(alpha.clone(), beta.clone()), opt.clone()), k.clone());
        let rhs = option_rec_apply(none_at(beta.clone()), k, opt);
        let eq = ctx.mk_eq(lhs, rhs).expect("axiom_bind_def: mk_eq");
        let inner = ctx.mk_forall("opt", ty(alpha), eq);
        let body = ctx.mk_forall("k", k_ty, inner);
        assume_hol(body)
    });
    AX.clone()
}

/// `⊢ ∀opt. is_some opt = option_rec false (λ_. true) opt` —
/// definitional axiom for `is_some`.
pub fn axiom_is_some_def() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let alpha = Type::tfree("a");
        let opt = Term::free("opt", ty(alpha.clone()));
        let lhs = Term::app(is_some_at(alpha.clone()), opt.clone());

        // step = λx:α. T — discards x and returns HOL true
        let step = Term::abs("x", alpha.clone(), ctx.t());

        let rhs = option_rec_apply(ctx.f(), step, opt);
        let eq = ctx.mk_eq(lhs, rhs).expect("axiom_is_some_def: mk_eq");
        let body = ctx.mk_forall("opt", ty(alpha), eq);
        assume_hol(body)
    });
    AX.clone()
}

// ============================================================================
// Derived theorems — TODO-postulated, scheduled for proof from the
// definitional layer + axiom_option_cases.
// ============================================================================

/// `⊢ ∀x. from_some (some x) = x`.
///
/// TODO: prove from a `from_some_def` once we commit to a `select`-
/// based definition; currently postulated.
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

/// `⊢ ∀f. map f none = none`.
///
/// TODO: prove from [`axiom_map_def`] + [`axiom_option_rec_none`]
/// + β; currently postulated.
pub fn axiom_map_none() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let alpha = Type::tfree("a");
        let beta = Type::tfree("b");
        let f_ty = Type::fun(alpha.clone(), beta.clone());
        let f = Term::free("f", f_ty.clone());
        let lhs = Term::app(
            Term::app(map_at(alpha.clone(), beta.clone()), f),
            none_at(alpha),
        );
        let eq = ctx
            .mk_eq(lhs, none_at(beta))
            .expect("axiom_map_none: mk_eq");
        let body = ctx.mk_forall("f", f_ty, eq);
        assume_hol(body)
    });
    AX.clone()
}

/// `⊢ ∀f x. map f (some x) = some (f x)`.
///
/// TODO: prove from [`axiom_map_def`] + [`axiom_option_rec_some`]
/// + β; currently postulated.
pub fn axiom_map_some() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let alpha = Type::tfree("a");
        let beta = Type::tfree("b");
        let f_ty = Type::fun(alpha.clone(), beta.clone());
        let f = Term::free("f", f_ty.clone());
        let x = Term::free("x", alpha.clone());
        let lhs = Term::app(
            Term::app(map_at(alpha.clone(), beta.clone()), f.clone()),
            Term::app(some_at(alpha.clone()), x.clone()),
        );
        let rhs = Term::app(some_at(beta), Term::app(f, x));
        let eq = ctx.mk_eq(lhs, rhs).expect("axiom_map_some: mk_eq");
        let inner = ctx.mk_forall("x", alpha, eq);
        let outer = ctx.mk_forall("f", f_ty, inner);
        assume_hol(outer)
    });
    AX.clone()
}

/// `⊢ ∀k. bind none k = none`.
///
/// TODO: prove from [`axiom_bind_def`] + [`axiom_option_rec_none`];
/// currently postulated.
pub fn axiom_bind_none() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let alpha = Type::tfree("a");
        let beta = Type::tfree("b");
        let k_ty = Type::fun(alpha.clone(), ty(beta.clone()));
        let k = Term::free("k", k_ty.clone());
        let lhs = Term::app(
            Term::app(bind_at(alpha.clone(), beta.clone()), none_at(alpha)),
            k,
        );
        let eq = ctx
            .mk_eq(lhs, none_at(beta))
            .expect("axiom_bind_none: mk_eq");
        let body = ctx.mk_forall("k", k_ty, eq);
        assume_hol(body)
    });
    AX.clone()
}

/// `⊢ ∀x k. bind (some x) k = k x`.
///
/// TODO: prove from [`axiom_bind_def`] + [`axiom_option_rec_some`];
/// currently postulated.
pub fn axiom_bind_some() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let alpha = Type::tfree("a");
        let beta = Type::tfree("b");
        let k_ty = Type::fun(alpha.clone(), ty(beta.clone()));
        let k = Term::free("k", k_ty.clone());
        let x = Term::free("x", alpha.clone());
        let lhs = Term::app(
            Term::app(
                bind_at(alpha.clone(), beta),
                Term::app(some_at(alpha.clone()), x.clone()),
            ),
            k.clone(),
        );
        let rhs = Term::app(k, x);
        let eq = ctx.mk_eq(lhs, rhs).expect("axiom_bind_some: mk_eq");
        let inner = ctx.mk_forall("k", k_ty, eq);
        let outer = ctx.mk_forall("x", alpha, inner);
        assume_hol(outer)
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
    fn option_rec_at_has_function_type() {
        let r = option_rec_at(Type::nat(), Type::int());
        let step_ty = Type::fun(Type::nat(), Type::int());
        let expected = Type::fun(
            Type::int(),
            Type::fun(step_ty, Type::fun(ty(Type::nat()), Type::int())),
        );
        assert_eq!(r.type_of().unwrap(), expected);
    }

    #[test]
    fn axioms_well_formed() {
        for ax in [
            axiom_some_inj(),
            axiom_none_ne_some(),
            axiom_from_some_some(),
            axiom_option_cases(),
            axiom_option_rec_none(),
            axiom_option_rec_some(),
        ] {
            assert!(ax.concl().type_of().unwrap().is_formula());
        }
    }

    #[test]
    fn definitional_op_axioms_well_formed() {
        for ax in [axiom_map_def(), axiom_bind_def(), axiom_is_some_def()] {
            assert!(ax.concl().type_of().unwrap().is_formula());
        }
    }

    #[test]
    fn monadic_axioms_well_formed() {
        for ax in [
            axiom_map_none(),
            axiom_map_some(),
            axiom_bind_none(),
            axiom_bind_some(),
        ] {
            assert!(ax.concl().type_of().unwrap().is_formula());
        }
    }
}
