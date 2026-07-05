//! **The two-sorted denotation carrier + the standard `nat` interpretation**
//! for the deep PA-in-HOL embedding (Phase A4 + B2 of
//! `notes/vibes/peano-arithmetic-plan.md`).
//!
//! [`fol`](super::fol) reifies PA syntax *locally-nameless* as the AST
//! [`Fol`] (with the proven de Bruijn substitution) and as a
//! single-sorted Church carrier. For the **denotation** `⟦·⟧` we need PA
//! terms to land in HOL `nat` and PA formulas in HOL `bool` — two sorts — so
//! here we denote the AST *directly* into HOL by a Rust meta-function (the
//! same style as [`crate::init::prop`]'s `axiom_schema`/`p_*` builders, which
//! are Rust meta-functions producing encoded HOL terms).
//!
//! ## Denotation under an environment
//!
//! A PA term may mention free variables (`fvar k`) and, *inside quantifiers*,
//! bound variables (`bvar i`). We denote under
//!
//! - a **free-variable interpretation**: each `fvar k` becomes a **named HOL
//!   free variable** `pa.v{k} : nat` (the natural standard interpretation —
//!   PA free variables *are* HOL free variables). This is what lets the
//!   induction schema discharge to [`Thm::nat_induct`](covalence_core::Thm::nat_induct), whose induction
//!   variable must be a bare free variable.
//! - a **bound-variable context** — a Rust `Vec<Term>` of the HOL `nat` terms
//!   the enclosing binders introduced (innermost last), so `⟦bvar i⟧` is the
//!   `i`-th entry from the top.
//!
//! A quantifier `∀. φ` denotes to a real HOL `∀x:nat. ⟦φ⟧[x::ctx]`, binding a
//! fresh HOL free variable `x` and pushing it on the context (then closing it
//! into a HOL binder). Locally-nameless bound vars thus become genuine HOL
//! bound vars — the denotation *is* the standard interpretation into HOL
//! `nat` (the `PA(A) ⟹ HOL(A)` transport's target).
//!
//! Everything here builds HOL terms with the kernel's existing `nat`
//! operations; nothing is added to `covalence-core`.

use covalence_core::{Term, Type, defs};
use covalence_hol_eval::mk_nat;
use covalence_types::Nat;

use super::fol::Fol;
use crate::init::ext::TermExt;

fn nat() -> Type {
    Type::nat()
}

/// The HOL `nat` free variable a PA free atom `fvar k` interprets to: `pa.v{k}`.
pub fn fvar_hol_name(k: u64) -> String {
    format!("pa.v{k}")
}

/// The HOL free variable `pa.v{k} : nat` for the PA free atom `k`.
pub fn fvar_hol(k: u64) -> Term {
    Term::free(fvar_hol_name(k), nat())
}

/// `⟦t⟧` for a PA **term** `t`, under the bound-variable context `ctx`
/// (innermost binder last). Free atoms `fvar k` interpret to the named HOL
/// free variable `pa.v{k}`. Returns an HOL term of type `nat`.
pub fn denote_term(t: &Fol, ctx: &[Term]) -> Term {
    match t {
        Fol::BVar(i) => {
            // de Bruijn: index `i` counts binders outward from here, so it is
            // the `i`-th entry from the top of `ctx`.
            let n = ctx.len();
            let idx = *i as usize;
            assert!(idx < n, "denote_term: dangling BVar {i} (ctx depth {n})");
            ctx[n - 1 - idx].clone()
        }
        Fol::FVar(k) => fvar_hol(*k),
        Fol::Zero => mk_nat(Nat::zero()),
        Fol::Succ(a) => Term::app(defs::nat_succ(), denote_term(a, ctx)),
        Fol::Add(a, b) => Term::app(
            Term::app(defs::nat_add(), denote_term(a, ctx)),
            denote_term(b, ctx),
        ),
        Fol::Mul(a, b) => Term::app(
            Term::app(defs::nat_mul(), denote_term(a, ctx)),
            denote_term(b, ctx),
        ),
        // Formula nodes are not terms; reaching one is a malformed AST.
        _ => panic!("denote_term: formula node where a term was expected"),
    }
}

/// `⟦φ⟧` for a PA **formula** `φ`, under bound-var context `ctx`. Returns an
/// HOL term of type `bool`. Quantifiers denote to real HOL `∀`/`∃` over `nat`.
pub fn denote_form(phi: &Fol, ctx: &[Term]) -> Term {
    match phi {
        Fol::Eq(a, b) => Term::app(
            Term::app(Term::eq_op(nat()), denote_term(a, ctx)),
            denote_term(b, ctx),
        ),
        Fol::Neg(a) => denote_form(a, ctx).not().expect("denote ¬"),
        Fol::And(a, b) => denote_form(a, ctx)
            .and(denote_form(b, ctx))
            .expect("denote ∧"),
        Fol::Or(a, b) => denote_form(a, ctx)
            .or(denote_form(b, ctx))
            .expect("denote ∨"),
        Fol::Imp(a, b) => denote_form(a, ctx)
            .imp(denote_form(b, ctx))
            .expect("denote ⟹"),
        Fol::All(body) => quantify(body, ctx, true),
        Fol::Ex(body) => quantify(body, ctx, false),
        // Term nodes are not formulas.
        _ => panic!("denote_form: term node where a formula was expected"),
    }
}

/// Denote a quantifier body: introduce a fresh HOL `nat` variable, denote the
/// body with it pushed on the context, then bind it with HOL `∀`/`∃`.
fn quantify(body: &Fol, ctx: &[Term], is_all: bool) -> Term {
    let name = format!("__pa_x{}", ctx.len());
    let x = Term::free(&name, nat());
    let mut ctx2 = ctx.to_vec();
    ctx2.push(x.clone());
    let inner = denote_form(body, &ctx2);
    if is_all {
        inner.forall(&name, nat()).expect("denote ∀")
    } else {
        inner.exists(&name, nat()).expect("denote ∃")
    }
}

/// `⟦φ⟧` for a formula `φ` with no dangling `bvar` (free atoms allowed). The
/// common case for stating PA metatheorems.
pub fn denote_closed(phi: &Fol) -> Term {
    denote_form(phi, &[])
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::init::eq::beta_nf;

    fn norm(t: Term) -> Term {
        beta_nf(t).concl().as_eq().unwrap().1.clone()
    }

    /// A closed term denotes to the expected `nat` HOL term.
    #[test]
    fn denote_succ_zero() {
        let t = Fol::Succ(Box::new(Fol::Zero));
        let d = denote_term(&t, &[]);
        assert_eq!(d.type_of().unwrap(), nat());
        assert_eq!(d, Term::app(defs::nat_succ(), Term::nat_lit(Nat::zero())));
    }

    /// A free atom denotes to its named HOL free variable.
    #[test]
    fn denote_fvar_is_named_free() {
        let d = denote_term(&Fol::FVar(3), &[]);
        assert_eq!(d, Term::free("pa.v3", nat()));
    }

    /// An atomic formula denotes to a `bool`-typed HOL equation.
    #[test]
    fn denote_eq_is_bool() {
        let phi = Fol::Eq(Box::new(Fol::FVar(0)), Box::new(Fol::Zero));
        let d = denote_closed(&phi);
        assert_eq!(d.type_of().unwrap(), Type::bool());
    }

    /// A universally-quantified formula denotes to a real HOL `∀n:nat. …`.
    #[test]
    fn denote_forall_is_hol_forall() {
        // ∀x. x = x
        let phi = Fol::All(Box::new(Fol::Eq(
            Box::new(Fol::BVar(0)),
            Box::new(Fol::BVar(0)),
        )));
        let d = denote_closed(&phi);
        assert_eq!(d.type_of().unwrap(), Type::bool());
        // Its β-normal form is `∀x. x = x` = `all (λx. x = x)`.
        let x = Term::free("__pa_x0", nat());
        let expected = x
            .clone()
            .equals(x)
            .unwrap()
            .forall("__pa_x0", nat())
            .unwrap();
        assert_eq!(norm(d), norm(expected));
    }

    /// Nested quantifiers index the context correctly: `∀x. ∀y. x = y`
    /// denotes with the *outer* `x` reachable as `bvar 1` from the inner body.
    #[test]
    fn nested_quantifiers_index_context() {
        // ∀.∀. (bvar1 = bvar0)   i.e. ∀x.∀y. x = y
        let phi = Fol::All(Box::new(Fol::All(Box::new(Fol::Eq(
            Box::new(Fol::BVar(1)),
            Box::new(Fol::BVar(0)),
        )))));
        let d = denote_closed(&phi);
        let x = Term::free("__pa_x0", nat());
        let y = Term::free("__pa_x1", nat());
        let expected = x
            .clone()
            .equals(y)
            .unwrap()
            .forall("__pa_x1", nat())
            .unwrap()
            .forall("__pa_x0", nat())
            .unwrap();
        assert_eq!(norm(d), norm(expected));
    }
}
