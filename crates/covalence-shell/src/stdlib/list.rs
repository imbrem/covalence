//! Polymorphic lists.
//!
//! `list 'a` is exposed as a HOL type constructor (via Pure
//! `Type::tycon`); `nil`/`cons` are polymorphic constants. The
//! initial spec is axiomatic — induction principle plus the
//! standard cons/nil/head/tail equations — so consumers can reason
//! about lists without us having committed to a particular carrier.
//!
//! A later upgrade can swap to a proper typedef (e.g. carve from
//! `nat → option 'a` or from a bytes encoding) without changing
//! this surface API.

use std::sync::LazyLock;

use covalence_hol::HolLightCtx;
use covalence_pure::{Term, Thm, Type};

fn ctx() -> HolLightCtx {
    HolLightCtx::new()
}

fn assume_hol(body: Term) -> Thm {
    let wrapped = ctx().mk_trueprop(body).expect("stdlib::list: mk_trueprop");
    Thm::assume(wrapped).expect("stdlib::list: assume")
}

// ============================================================================
// Type
// ============================================================================

/// `list α` — the polymorphic list type at carrier α.
pub fn ty(alpha: Type) -> Type {
    Type::tycon("list", vec![alpha])
}

/// `list 'a` — the generic list type.
pub fn ty_generic() -> Type {
    ty(Type::tfree("a"))
}

// ============================================================================
// Constructors
// ============================================================================

/// `nil : list α`.
pub fn nil_at(alpha: Type) -> Term {
    Term::const_("nil", ty(alpha))
}

pub fn nil_generic() -> Term {
    nil_at(Type::tfree("a"))
}

/// `cons : α → list α → list α`.
pub fn cons_at(alpha: Type) -> Term {
    let list_a = ty(alpha.clone());
    Term::const_("cons", Type::fun(alpha, Type::fun(list_a.clone(), list_a)))
}

pub fn cons_generic() -> Term {
    cons_at(Type::tfree("a"))
}

/// `cons x xs` applied.
pub fn cons(x: Term, xs: Term) -> Term {
    let alpha = x.type_of().expect("cons: x typed");
    Term::app(Term::app(cons_at(alpha), x), xs)
}

// ============================================================================
// Destructors
// ============================================================================

/// `head : list α → α` — undefined on `nil`; axiomatised on `cons`.
pub fn head_at(alpha: Type) -> Term {
    Term::const_("head", Type::fun(ty(alpha.clone()), alpha))
}

/// `tail : list α → list α` — `tail nil = nil`; `tail (cons x xs) = xs`.
pub fn tail_at(alpha: Type) -> Term {
    let la = ty(alpha);
    Term::const_("tail", Type::fun(la.clone(), la))
}

/// `null : list α → bool` — `null nil = T`, `null (cons _ _) = F`.
pub fn null_at(alpha: Type) -> Term {
    Term::const_("null", Type::fun(ty(alpha), ctx().bool_type()))
}

// ============================================================================
// Axioms (Peano-style for lists)
// ============================================================================

/// `⊢ ∀x:'a. ∀xs:list 'a. head (cons x xs) = x`.
pub fn axiom_head_cons() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let alpha = Type::tfree("a");
        let x = Term::free("x", alpha.clone());
        let xs = Term::free("xs", ty(alpha.clone()));
        let consed = Term::app(Term::app(cons_at(alpha.clone()), x.clone()), xs.clone());
        let lhs = Term::app(head_at(alpha.clone()), consed);
        let eq = ctx.mk_eq(lhs, x).expect("axiom_head_cons: mk_eq");
        let inner = ctx.mk_forall("xs", ty(alpha.clone()), eq);
        let outer = ctx.mk_forall("x", alpha, inner);
        assume_hol(outer)
    });
    AX.clone()
}

/// `⊢ ∀x:'a. ∀xs:list 'a. tail (cons x xs) = xs`.
pub fn axiom_tail_cons() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let alpha = Type::tfree("a");
        let x = Term::free("x", alpha.clone());
        let xs = Term::free("xs", ty(alpha.clone()));
        let consed = Term::app(Term::app(cons_at(alpha.clone()), x.clone()), xs.clone());
        let lhs = Term::app(tail_at(alpha.clone()), consed);
        let eq = ctx.mk_eq(lhs, xs).expect("axiom_tail_cons: mk_eq");
        let inner = ctx.mk_forall("xs", ty(alpha.clone()), eq);
        let outer = ctx.mk_forall("x", alpha, inner);
        assume_hol(outer)
    });
    AX.clone()
}

/// `⊢ ∀x:'a. ∀xs:list 'a. ¬ (nil = cons x xs)`.
pub fn axiom_nil_ne_cons() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let alpha = Type::tfree("a");
        let x = Term::free("x", alpha.clone());
        let xs = Term::free("xs", ty(alpha.clone()));
        let consed = Term::app(Term::app(cons_at(alpha.clone()), x.clone()), xs.clone());
        let eq = ctx
            .mk_eq(nil_at(alpha.clone()), consed)
            .expect("axiom_nil_ne_cons: mk_eq");
        let not_eq = ctx.mk_not(eq);
        let inner = ctx.mk_forall("xs", ty(alpha.clone()), not_eq);
        let outer = ctx.mk_forall("x", alpha, inner);
        assume_hol(outer)
    });
    AX.clone()
}

/// `⊢ ∀x x' xs xs'. cons x xs = cons x' xs' ⟹ x = x' ∧ xs = xs'`.
pub fn axiom_cons_inj() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let alpha = Type::tfree("a");
        let la = ty(alpha.clone());
        let x = Term::free("x", alpha.clone());
        let y = Term::free("y", alpha.clone());
        let xs = Term::free("xs", la.clone());
        let ys = Term::free("ys", la.clone());

        let consed_l = Term::app(Term::app(cons_at(alpha.clone()), x.clone()), xs.clone());
        let consed_r = Term::app(Term::app(cons_at(alpha.clone()), y.clone()), ys.clone());

        let lhs = ctx
            .mk_eq(consed_l, consed_r)
            .expect("axiom_cons_inj: outer mk_eq");
        let x_eq_y = ctx.mk_eq(x, y).expect("axiom_cons_inj: x = y");
        let xs_eq_ys = ctx.mk_eq(xs, ys).expect("axiom_cons_inj: xs = ys");
        let conj = ctx.mk_and(x_eq_y, xs_eq_ys);

        let imp = ctx.mk_imp(lhs, conj);
        let i1 = ctx.mk_forall("ys", la.clone(), imp);
        let i2 = ctx.mk_forall("xs", la, i1);
        let i3 = ctx.mk_forall("y", alpha.clone(), i2);
        let outer = ctx.mk_forall("x", alpha, i3);
        assume_hol(outer)
    });
    AX.clone()
}

// ============================================================================
// Combinators (map / filter / foldr)
// ============================================================================

/// `map : ('a → 'b) → list 'a → list 'b`.
pub fn map_at(alpha: Type, beta: Type) -> Term {
    let la = ty(alpha.clone());
    let lb = ty(beta.clone());
    let f_ty = Type::fun(alpha, beta);
    Term::const_("list_map", Type::fun(f_ty, Type::fun(la, lb)))
}

/// `filter : ('a → bool) → list 'a → list 'a`.
pub fn filter_at(alpha: Type) -> Term {
    let la = ty(alpha.clone());
    let pred_ty = Type::fun(alpha, ctx().bool_type());
    Term::const_("list_filter", Type::fun(pred_ty, Type::fun(la.clone(), la)))
}

/// `foldr : ('a → 'b → 'b) → 'b → list 'a → 'b`.
pub fn foldr_at(alpha: Type, beta: Type) -> Term {
    let la = ty(alpha.clone());
    let f_ty = Type::fun(alpha, Type::fun(beta.clone(), beta.clone()));
    Term::const_(
        "list_foldr",
        Type::fun(f_ty, Type::fun(beta.clone(), Type::fun(la, beta))),
    )
}

/// `⊢ ∀f. map f nil = nil`.
pub fn axiom_map_nil() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let alpha = Type::tfree("a");
        let beta = Type::tfree("b");
        let f_ty = Type::fun(alpha.clone(), beta.clone());
        let f = Term::free("f", f_ty.clone());
        let lhs = Term::app(
            Term::app(map_at(alpha.clone(), beta.clone()), f),
            nil_at(alpha),
        );
        let eq = ctx.mk_eq(lhs, nil_at(beta)).expect("axiom_map_nil: mk_eq");
        let body = ctx.mk_forall("f", f_ty, eq);
        assume_hol(body)
    });
    AX.clone()
}

/// `⊢ ∀f x xs. map f (cons x xs) = cons (f x) (map f xs)`.
pub fn axiom_map_cons() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let alpha = Type::tfree("a");
        let beta = Type::tfree("b");
        let f_ty = Type::fun(alpha.clone(), beta.clone());
        let f = Term::free("f", f_ty.clone());
        let x = Term::free("x", alpha.clone());
        let xs = Term::free("xs", ty(alpha.clone()));
        let map_at_ab = map_at(alpha.clone(), beta.clone());
        let consed = Term::app(Term::app(cons_at(alpha.clone()), x.clone()), xs.clone());
        let lhs = Term::app(Term::app(map_at_ab.clone(), f.clone()), consed);
        let mapped_xs = Term::app(Term::app(map_at_ab, f.clone()), xs);
        let head = Term::app(f, x);
        let rhs = Term::app(Term::app(cons_at(beta), head), mapped_xs);
        let eq = ctx.mk_eq(lhs, rhs).expect("axiom_map_cons: mk_eq");
        let i1 = ctx.mk_forall("xs", ty(alpha.clone()), eq);
        let i2 = ctx.mk_forall("x", alpha, i1);
        let outer = ctx.mk_forall("f", f_ty, i2);
        assume_hol(outer)
    });
    AX.clone()
}

/// `⊢ ∀f z. foldr f z nil = z`.
pub fn axiom_foldr_nil() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let alpha = Type::tfree("a");
        let beta = Type::tfree("b");
        let f_ty = Type::fun(alpha.clone(), Type::fun(beta.clone(), beta.clone()));
        let f = Term::free("f", f_ty.clone());
        let z = Term::free("z", beta.clone());
        let lhs = Term::app(
            Term::app(
                Term::app(foldr_at(alpha.clone(), beta.clone()), f),
                z.clone(),
            ),
            nil_at(alpha),
        );
        let eq = ctx.mk_eq(lhs, z).expect("axiom_foldr_nil: mk_eq");
        let inner = ctx.mk_forall("z", beta, eq);
        let outer = ctx.mk_forall("f", f_ty, inner);
        assume_hol(outer)
    });
    AX.clone()
}

/// `⊢ ∀f z x xs. foldr f z (cons x xs) = f x (foldr f z xs)`.
pub fn axiom_foldr_cons() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let alpha = Type::tfree("a");
        let beta = Type::tfree("b");
        let f_ty = Type::fun(alpha.clone(), Type::fun(beta.clone(), beta.clone()));
        let f = Term::free("f", f_ty.clone());
        let z = Term::free("z", beta.clone());
        let x = Term::free("x", alpha.clone());
        let xs = Term::free("xs", ty(alpha.clone()));
        let foldr_ = foldr_at(alpha.clone(), beta.clone());
        let consed = Term::app(Term::app(cons_at(alpha.clone()), x.clone()), xs.clone());
        let lhs = Term::app(
            Term::app(Term::app(foldr_.clone(), f.clone()), z.clone()),
            consed,
        );
        let inner_fold = Term::app(Term::app(Term::app(foldr_, f.clone()), z.clone()), xs);
        let rhs = Term::app(Term::app(f, x), inner_fold);
        let eq = ctx.mk_eq(lhs, rhs).expect("axiom_foldr_cons: mk_eq");
        let i1 = ctx.mk_forall("xs", ty(alpha.clone()), eq);
        let i2 = ctx.mk_forall("x", alpha, i1);
        let i3 = ctx.mk_forall("z", beta, i2);
        let outer = ctx.mk_forall("f", f_ty, i3);
        assume_hol(outer)
    });
    AX.clone()
}

/// `⊢ ∀P. P nil ∧ (∀x xs. P xs ⟹ P (cons x xs)) ⟹ ∀xs. P xs`.
pub fn axiom_list_induction() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let alpha = Type::tfree("a");
        let la = ty(alpha.clone());
        let bool_ty = ctx.bool_type();
        let pred_ty = Type::fun(la.clone(), bool_ty);
        let p = Term::free("P", pred_ty.clone());

        // P nil
        let p_nil = Term::app(p.clone(), nil_at(alpha.clone()));

        // ∀x xs. P xs ⟹ P (cons x xs)
        let x = Term::free("x", alpha.clone());
        let xs = Term::free("xs", la.clone());
        let consed = Term::app(Term::app(cons_at(alpha.clone()), x.clone()), xs.clone());
        let p_xs = Term::app(p.clone(), xs);
        let p_consed = Term::app(p.clone(), consed);
        let step_body = ctx.mk_imp(p_xs, p_consed);
        let step_inner = ctx.mk_forall("xs", la.clone(), step_body);
        let step = ctx.mk_forall("x", alpha.clone(), step_inner);

        let antecedent = ctx.mk_and(p_nil, step);

        // ∀xs. P xs
        let xs2 = Term::free("xs", la.clone());
        let p_xs2 = Term::app(p.clone(), xs2);
        let consequent = ctx.mk_forall("xs", la, p_xs2);

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
    fn ty_constructors() {
        let nat_list = ty(Type::nat());
        assert_eq!(nat_list, Type::tycon("list", vec![Type::nat()]));
    }

    #[test]
    fn nil_cons_types() {
        let nil = nil_at(Type::nat());
        assert_eq!(nil.type_of().unwrap(), ty(Type::nat()));
        let c = cons_at(Type::nat());
        assert_eq!(
            c.type_of().unwrap(),
            Type::fun(Type::nat(), Type::fun(ty(Type::nat()), ty(Type::nat())))
        );
    }

    #[test]
    fn cons_apply_round_trips() {
        let one = Term::nat_lit(covalence_types::Nat::one());
        let two = Term::nat_lit(covalence_types::Nat::from_inner(2u32.into()));
        let xs = cons(one, cons(two, nil_at(Type::nat())));
        assert_eq!(xs.type_of().unwrap(), ty(Type::nat()));
    }

    #[test]
    fn axioms_well_formed() {
        for ax in [
            axiom_head_cons(),
            axiom_tail_cons(),
            axiom_nil_ne_cons(),
            axiom_cons_inj(),
            axiom_list_induction(),
        ] {
            assert!(ax.concl().type_of().unwrap().is_prop());
        }
    }

    #[test]
    fn combinator_axioms_well_formed() {
        for ax in [
            axiom_map_nil(),
            axiom_map_cons(),
            axiom_foldr_nil(),
            axiom_foldr_cons(),
        ] {
            assert!(ax.concl().type_of().unwrap().is_prop());
        }
    }
}
