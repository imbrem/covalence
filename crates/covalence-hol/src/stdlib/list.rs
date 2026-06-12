//! Polymorphic lists.
//!
//! Layered like [`crate::stdlib::nat`] and [`crate::stdlib::option`]:
//! 1. **Constructor distinctness / injectivity**
//!    ([`axiom_nil_ne_cons`], [`axiom_cons_inj`]).
//! 2. **Induction** ([`axiom_list_induction`]).
//! 3. **Recursor** [`list_rec_at`] / [`list_rec_apply`] with its two
//!    defining equations ([`axiom_list_rec_nil`],
//!    [`axiom_list_rec_cons`]).
//! 4. **Operations** (`head`, `tail`, `null`, `map`, `filter`,
//!    `foldr`) each fixed by a single definitional axiom in terms
//!    of `list_rec`. Partial destructors (`head`) are postulated on
//!    the `cons` case only.
//! 5. **Derived theorems** — currently TODO-postulated, scheduled
//!    for proof from the definitional layer + induction.

use std::sync::LazyLock;

use crate::HolLightCtx;
use covalence_core::{Term, Thm, Type};

fn ctx() -> HolLightCtx {
    HolLightCtx::new()
}

fn assume_hol(body: Term) -> Thm {
    Thm::assume(body).expect("stdlib::list: assume")
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
// Recursor
// ============================================================================

/// `list_rec : β → (α → list α → β → β) → list α → β` at carriers (α, β).
///
/// The step function receives the head element, the tail list, *and*
/// the recursive result on the tail — making this a full
/// "iterator-with-context" recursor.
pub fn list_rec_at(alpha: Type, beta: Type) -> Term {
    let la = ty(alpha.clone());
    // step : α → list α → β → β
    let step_ty = Type::fun(
        alpha.clone(),
        Type::fun(la.clone(), Type::fun(beta.clone(), beta.clone())),
    );
    let ty = Type::fun(beta.clone(), Type::fun(step_ty, Type::fun(la, beta)));
    Term::const_("list_rec", ty)
}

/// `list_rec base step xs` — types inferred from `base` and `xs`.
pub fn list_rec_apply(base: Term, step: Term, xs: Term) -> Term {
    let beta = base.type_of().expect("list_rec_apply: base typed");
    let xs_ty = xs.type_of().expect("list_rec_apply: xs typed");
    let alpha = match xs_ty.kind() {
        covalence_core::TypeKind::Tycon(_, args) if args.len() == 1 => args[0].clone(),
        _ => panic!("list_rec_apply: xs must have type `list α`"),
    };
    let rec = list_rec_at(alpha, beta);
    Term::app(Term::app(Term::app(rec, base), step), xs)
}

// ============================================================================
// Constructor distinctness / injectivity / induction
// ============================================================================

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

/// `⊢ ∀P. P nil ∧ (∀x xs. P xs ⟹ P (cons x xs)) ⟹ ∀xs. P xs`.
pub fn axiom_list_induction() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let alpha = Type::tfree("a");
        let la = ty(alpha.clone());
        let bool_ty = ctx.bool_type();
        let pred_ty = Type::fun(la.clone(), bool_ty);
        let p = Term::free("P", pred_ty.clone());

        let p_nil = Term::app(p.clone(), nil_at(alpha.clone()));

        let x = Term::free("x", alpha.clone());
        let xs = Term::free("xs", la.clone());
        let consed = Term::app(Term::app(cons_at(alpha.clone()), x.clone()), xs.clone());
        let p_xs = Term::app(p.clone(), xs);
        let p_consed = Term::app(p.clone(), consed);
        let step_body = ctx.mk_imp(p_xs, p_consed);
        let step_inner = ctx.mk_forall("xs", la.clone(), step_body);
        let step = ctx.mk_forall("x", alpha.clone(), step_inner);

        let antecedent = ctx.mk_and(p_nil, step);

        let xs2 = Term::free("xs", la.clone());
        let p_xs2 = Term::app(p.clone(), xs2);
        let consequent = ctx.mk_forall("xs", la, p_xs2);

        let imp = ctx.mk_imp(antecedent, consequent);
        let body = ctx.mk_forall("P", pred_ty, imp);
        assume_hol(body)
    });
    AX.clone()
}

// ============================================================================
// Definitional axioms for list_rec
// ============================================================================

/// `⊢ ∀base step. list_rec base step nil = base`.
pub fn axiom_list_rec_nil() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let alpha = Type::tfree("a");
        let beta = Type::tfree("b");
        let la = ty(alpha.clone());
        let step_ty = Type::fun(
            alpha.clone(),
            Type::fun(la, Type::fun(beta.clone(), beta.clone())),
        );
        let base = Term::free("base", beta.clone());
        let step = Term::free("step", step_ty.clone());
        let lhs = list_rec_apply(base.clone(), step.clone(), nil_at(alpha));
        let eq = ctx.mk_eq(lhs, base).expect("axiom_list_rec_nil: mk_eq");
        let inner = ctx.mk_forall("step", step_ty, eq);
        let body = ctx.mk_forall("base", beta, inner);
        assume_hol(body)
    });
    AX.clone()
}

/// `⊢ ∀base step x xs. list_rec base step (cons x xs) =
///                     step x xs (list_rec base step xs)`.
pub fn axiom_list_rec_cons() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let alpha = Type::tfree("a");
        let beta = Type::tfree("b");
        let la = ty(alpha.clone());
        let step_ty = Type::fun(
            alpha.clone(),
            Type::fun(la.clone(), Type::fun(beta.clone(), beta.clone())),
        );
        let base = Term::free("base", beta.clone());
        let step = Term::free("step", step_ty.clone());
        let x = Term::free("x", alpha.clone());
        let xs = Term::free("xs", la.clone());
        let consed = Term::app(Term::app(cons_at(alpha.clone()), x.clone()), xs.clone());
        let lhs = list_rec_apply(base.clone(), step.clone(), consed);
        let inner_rec = list_rec_apply(base.clone(), step.clone(), xs.clone());
        let rhs = Term::app(
            Term::app(Term::app(step.clone(), x), xs),
            inner_rec,
        );
        let eq = ctx.mk_eq(lhs, rhs).expect("axiom_list_rec_cons: mk_eq");
        let i1 = ctx.mk_forall("xs", la, eq);
        let i2 = ctx.mk_forall("x", alpha, i1);
        let i3 = ctx.mk_forall("step", step_ty, i2);
        let body = ctx.mk_forall("base", beta, i3);
        assume_hol(body)
    });
    AX.clone()
}

// ============================================================================
// Definitional axioms for operations
// ============================================================================

/// `⊢ ∀xs. tail xs = list_rec nil (λx xs' _. xs') xs` — definitional.
pub fn axiom_tail_def() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let alpha = Type::tfree("a");
        let la = ty(alpha.clone());
        let xs = Term::free("xs", la.clone());
        let lhs = Term::app(tail_at(alpha.clone()), xs.clone());

        // step = λx:α. λxs':list α. λr:list α. xs'
        let xs_inner = Term::free("xs", la.clone());
        // body returns xs_inner under the three binders; for the
        // outermost (x) and innermost (r) the binders capture
        // distinct fresh hints, leaving `xs_inner` free in the body
        // of the second binder — we use `Term::abs` left-to-right
        // so the closest binder is `r`. Build body = `xs_inner`,
        // then abs r, then abs xs_inner (this captures), then abs x.
        let body = Term::abs("r", la.clone(), xs_inner.clone());
        let step_inner = Term::abs("xs", la.clone(), body);
        let step = Term::abs("x", alpha.clone(), step_inner);

        let rhs = list_rec_apply(nil_at(alpha.clone()), step, xs);
        let eq = ctx.mk_eq(lhs, rhs).expect("axiom_tail_def: mk_eq");
        let body = ctx.mk_forall("xs", la, eq);
        assume_hol(body)
    });
    AX.clone()
}

/// `⊢ ∀xs. null xs = list_rec T (λx xs' _. F) xs` — definitional.
pub fn axiom_null_def() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let alpha = Type::tfree("a");
        let la = ty(alpha.clone());
        let bool_ty = ctx.bool_type();
        let xs = Term::free("xs", la.clone());
        let lhs = Term::app(null_at(alpha.clone()), xs.clone());
        // step = λx:α. λxs':list α. λr:bool. F
        let body = Term::abs("r", bool_ty.clone(), ctx.f());
        let step_inner = Term::abs("xs", la.clone(), body);
        let step = Term::abs("x", alpha.clone(), step_inner);
        let rhs = list_rec_apply(ctx.t(), step, xs);
        let eq = ctx.mk_eq(lhs, rhs).expect("axiom_null_def: mk_eq");
        let body = ctx.mk_forall("xs", la, eq);
        assume_hol(body)
    });
    AX.clone()
}

/// `⊢ ∀f xs. map f xs = list_rec nil (λx xs' acc. cons (f x) acc) xs`
/// — definitional axiom for `list_map`.
pub fn axiom_map_def() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let alpha = Type::tfree("a");
        let beta = Type::tfree("b");
        let la = ty(alpha.clone());
        let lb = ty(beta.clone());
        let f_ty = Type::fun(alpha.clone(), beta.clone());
        let f = Term::free("f", f_ty.clone());
        let xs = Term::free("xs", la.clone());
        let lhs = Term::app(Term::app(map_at(alpha.clone(), beta.clone()), f.clone()), xs.clone());

        // step = λx:α. λxs':list α. λacc:list β. cons (f x) acc
        // Build the body referring to free `f`, `x`, `acc`, then abs in correct order.
        let x = Term::free("x", alpha.clone());
        let acc = Term::free("acc", lb.clone());
        let f_x = Term::app(f.clone(), x.clone());
        let body = Term::app(Term::app(cons_at(beta.clone()), f_x), acc);
        // abs from innermost binder (acc) outward
        let body = Term::abs("acc", lb.clone(), body);
        let body = Term::abs("xs", la.clone(), body);
        let step = Term::abs("x", alpha.clone(), body);
        let _ = x;

        let rhs = list_rec_apply(nil_at(beta), step, xs);
        let eq = ctx.mk_eq(lhs, rhs).expect("axiom_map_def: mk_eq");
        let inner = ctx.mk_forall("xs", la, eq);
        let body = ctx.mk_forall("f", f_ty, inner);
        assume_hol(body)
    });
    AX.clone()
}

/// `⊢ ∀f z xs. foldr f z xs = list_rec z (λx xs' acc. f x acc) xs`
/// — definitional axiom for `list_foldr`.
pub fn axiom_foldr_def() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let alpha = Type::tfree("a");
        let beta = Type::tfree("b");
        let la = ty(alpha.clone());
        let f_ty = Type::fun(alpha.clone(), Type::fun(beta.clone(), beta.clone()));
        let f = Term::free("f", f_ty.clone());
        let z = Term::free("z", beta.clone());
        let xs = Term::free("xs", la.clone());
        let lhs = Term::app(
            Term::app(
                Term::app(foldr_at(alpha.clone(), beta.clone()), f.clone()),
                z.clone(),
            ),
            xs.clone(),
        );

        // step = λx:α. λxs':list α. λacc:β. f x acc
        let x = Term::free("x", alpha.clone());
        let acc = Term::free("acc", beta.clone());
        let body = Term::app(Term::app(f.clone(), x.clone()), acc);
        let body = Term::abs("acc", beta.clone(), body);
        let body = Term::abs("xs", la.clone(), body);
        let step = Term::abs("x", alpha.clone(), body);
        let _ = x;

        let rhs = list_rec_apply(z.clone(), step, xs);
        let eq = ctx.mk_eq(lhs, rhs).expect("axiom_foldr_def: mk_eq");
        let i1 = ctx.mk_forall("xs", la, eq);
        let i2 = ctx.mk_forall("z", beta, i1);
        let body = ctx.mk_forall("f", f_ty, i2);
        assume_hol(body)
    });
    AX.clone()
}

// ============================================================================
// Combinator constants
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

// ============================================================================
// Derived theorems — TODO-postulated, scheduled for proof.
// ============================================================================

/// `⊢ ∀x:'a. ∀xs:list 'a. head (cons x xs) = x`.
///
/// TODO: `head` is partial; a future refactor will define it via
/// `select` (Hilbert epsilon) + this equation becomes derivable.
/// Currently postulated.
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
///
/// TODO: prove from [`axiom_tail_def`] + [`axiom_list_rec_cons`] + β;
/// currently postulated.
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

/// `⊢ ∀f. map f nil = nil`.
///
/// TODO: prove from [`axiom_map_def`] + [`axiom_list_rec_nil`] + β;
/// currently postulated.
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
///
/// TODO: prove from [`axiom_map_def`] + [`axiom_list_rec_cons`] + β;
/// currently postulated.
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
///
/// TODO: prove from [`axiom_foldr_def`] + [`axiom_list_rec_nil`] + β;
/// currently postulated.
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
///
/// TODO: prove from [`axiom_foldr_def`] + [`axiom_list_rec_cons`] + β;
/// currently postulated.
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
    fn list_rec_at_has_function_type() {
        let r = list_rec_at(Type::nat(), Type::int());
        let la = ty(Type::nat());
        let step_ty = Type::fun(
            Type::nat(),
            Type::fun(la.clone(), Type::fun(Type::int(), Type::int())),
        );
        let expected = Type::fun(
            Type::int(),
            Type::fun(step_ty, Type::fun(la, Type::int())),
        );
        assert_eq!(r.type_of().unwrap(), expected);
    }

    #[test]
    fn distinctness_axioms_well_formed() {
        for ax in [axiom_nil_ne_cons(), axiom_cons_inj(), axiom_list_induction()] {
            assert!(ax.concl().type_of().unwrap().is_bool());
        }
    }

    #[test]
    fn definitional_axioms_well_formed() {
        for ax in [
            axiom_list_rec_nil(),
            axiom_list_rec_cons(),
            axiom_tail_def(),
            axiom_null_def(),
            axiom_map_def(),
            axiom_foldr_def(),
        ] {
            assert!(ax.concl().type_of().unwrap().is_bool());
        }
    }

    #[test]
    fn derived_postulates_well_formed() {
        for ax in [
            axiom_head_cons(),
            axiom_tail_cons(),
            axiom_map_nil(),
            axiom_map_cons(),
            axiom_foldr_nil(),
            axiom_foldr_cons(),
        ] {
            assert!(ax.concl().type_of().unwrap().is_bool());
        }
    }
}
