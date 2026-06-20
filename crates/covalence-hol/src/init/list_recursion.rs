//! The **`list` inductive adapter** — `list α` as an [`Inductive`] for the
//! generic recursion engine ([`crate::init::inductive`]).
//!
//! `list α := stream (option α) where (finite ∧ contiguous)` is a derived
//! type, so its `Inductive` interface is supplied by *theorems*, not kernel
//! primitives:
//!
//! - **induction** — [`crate::init::list::list_induct`] (itself a genuine
//!   theorem, via a finiteness-bound `nat`-induction);
//! - **`cons` injectivity** — [`crate::init::list::cons_inj`];
//! - **`nil`/`cons` distinctness** — [`crate::init::list::nil_ne_cons`].
//!
//! This is the **lifting seam** the engine was designed for: where `nat`'s
//! adapter ([`crate::init::recursion`]) wraps kernel primitives
//! (`Thm::nat_induct` / `Thm::succ_inj`), `list`'s wraps *derived* theorems
//! — so the same `graph`/`existence`/`uniqueness`/`determinacy` machinery
//! runs unchanged, proving that genuine `list` structural recursion is
//! available.
//!
//! See `SKELETONS.md` for what rides on top (the `list_foldr` / `list_foldl`
//! catalogue equations — a *catamorphic* specialisation of the paramorphic
//! recursor the engine produces).

use covalence_core::{Error, Result, Term, Thm, Type};

use crate::init::ext::{TermExt, ThmExt};
use crate::init::inductive::{Arg, Constructor, Inductive, InductiveSig};
use crate::init::list::{cons_inj, list_induct, nil_ne_cons};

use covalence_core::defs::{cons, list, nil, option};

/// The element type `α` the adapter is specialised at.
fn elem() -> Type {
    Type::tfree("a")
}

/// `list α` at the adapter's element type.
fn list_ty() -> Type {
    list(elem())
}

/// The `list α` signature: `nil` (nullary) and `cons` (an element
/// parameter `x : α`, then one recursive argument `xs : list α` with image
/// `b`). Matches the `cons`-shaped constructor the engine's `graph` layer
/// already exercises (`Param` then `Rec`).
pub fn list_sig() -> &'static InductiveSig {
    static SIG: std::sync::LazyLock<InductiveSig> = std::sync::LazyLock::new(|| InductiveSig {
        ty: list(Type::tfree("a")),
        relation: "G",
        ctors: vec![
            Constructor::nullary(nil(Type::tfree("a"))),
            Constructor::new(
                cons(Type::tfree("a")),
                vec![
                    Arg::Param {
                        ty: Type::tfree("a"),
                        name: "x",
                    },
                    Arg::Rec {
                        name: "xs",
                        image: "b",
                    },
                ],
            ),
        ],
    });
    &SIG
}

/// `list`'s [`Inductive`] adapter, sourcing induction + freeness from the
/// derived theorems in [`crate::init::list`].
pub struct ListTheory;

impl Inductive for ListTheory {
    fn sig(&self) -> &InductiveSig {
        list_sig()
    }

    fn induct(&self, motive: &Term, cases: Vec<Thm>) -> Result<Thm> {
        // cases = [⊢ P nil, ⊢ P xs ⟹ P (cons x xs)] (applied form, the
        // step over fresh `x : α`, `xs : list α`). `list_induct` wants the
        // step ∀-closed.
        let [base, step]: [Thm; 2] = cases.try_into().map_err(|_| {
            Error::ConnectiveRule("list induct: expected 2 cases".into())
        })?;
        let cons_case = step
            .all_intro("xs", list_ty())?
            .all_intro("x", elem())?; // ⊢ ∀x xs. P xs ⟹ P (cons x xs)
        list_induct(&elem(), motive, base, cons_case)
    }

    fn injective(&self, i: usize, xs: &[Term], ys: &[Term]) -> Result<Thm> {
        // Only `cons` (constructor 1) is injective-relevant.
        match (i, xs, ys) {
            (1, [x, xtl], [y, ytl]) => cons_inj(&elem(), x, xtl, y, ytl),
            _ => Err(Error::ConnectiveRule(format!(
                "list injective: no injectivity for constructor {i}"
            ))),
        }
    }

    fn distinct(&self, i: usize, j: usize, xs: &[Term], ys: &[Term]) -> Result<Thm> {
        // `nil_ne_cons x xs : ⊢ ¬(nil = cons x xs)`; bridge to `(Cᵢ = Cⱼ) ⟹ F`.
        match (i, j, xs, ys) {
            (0, 1, [], [y, ytl]) => {
                let eq = nil(elem()).equals(cons_app(y, ytl)?)?;
                nil_ne_cons(&elem(), y, ytl)?
                    .not_elim(Thm::assume(eq.clone())?)?
                    .imp_intro(&eq)
            }
            (1, 0, [x, xtl], []) => {
                let eq = cons_app(x, xtl)?.equals(nil(elem()))?;
                nil_ne_cons(&elem(), x, xtl)?
                    .not_elim(Thm::assume(eq.clone())?.sym()?)?
                    .imp_intro(&eq)
            }
            _ => Err(Error::ConnectiveRule(format!(
                "list distinct: no rule for constructors {i}, {j}"
            ))),
        }
    }
}

/// `cons x xs`.
fn cons_app(x: &Term, xs: &Term) -> Result<Term> {
    cons(elem()).apply(x.clone())?.apply(xs.clone())
}

/// `option α` at the adapter's element type (unused export guard).
#[allow(dead_code)]
fn opt() -> Type {
    option(elem())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::init::eq::beta_reduce;
    use crate::init::inductive::{existence, recursor, uniqueness};
    use covalence_core::subst;

    /// The recursor result type `β` for the validation tests.
    fn beta() -> Type {
        Type::nat()
    }

    /// Step terms `[z, f]`: `z : β` (the `nil` image) and
    /// `f : α → list α → β → β` (the `cons` step).
    fn steps() -> [Term; 2] {
        let z = Term::free("z", beta());
        let f = Term::free(
            "f",
            Type::fun(
                elem(),
                Type::fun(list_ty(), Type::fun(beta(), beta())),
            ),
        );
        [z, f]
    }

    #[test]
    fn graph_total_runs_through_list_induct() {
        // The existence layer (`∀l. ∃a. Graph l a`) consumes `ListTheory`'s
        // `induct` (= the derived `list_induct`). If it goes through, the
        // engine accepts `list`.
        let thm = existence::graph_total(&ListTheory, &steps(), &beta()).unwrap();
        assert!(thm.hyps().is_empty(), "graph_total must be axiom-free");
    }

    #[test]
    fn graph_base_inversion_is_axiom_free() {
        // `nil` inversion from the freeness feeders (`distinct`).
        let thm = uniqueness::graph_inv(&ListTheory, &steps(), &beta(), 0).unwrap();
        assert!(thm.hyps().is_empty());
    }

    #[test]
    fn graph_det_runs_through_list_induct() {
        let thm = crate::init::inductive::determinacy::graph_det(&ListTheory, &steps(), &beta())
            .unwrap();
        assert!(thm.hyps().is_empty(), "determinacy must be axiom-free");
    }

    #[test]
    fn recursion_theorem_for_list_is_axiom_free() {
        // The paramorphic recursor predicate: `λr. (r z f nil = z) ∧
        // (∀x xs. r z f (cons x xs) = f x xs (r z f xs))`. Build it and run
        // the engine's `recursion_theorem`; a successful, hypothesis-free
        // `∃r. P_rec r` is genuine `list` structural recursion.
        let [z, f] = steps();
        let pred = paramorphic_pred(&z, &f);
        let rt = recursor::recursion_theorem(&ListTheory, &[z, f], &beta(), &pred).unwrap();
        assert!(rt.hyps().is_empty(), "∃r. P_rec r must be axiom-free");
        assert!(rt.concl().type_of().unwrap().is_bool());
    }

    /// `λr. ∀z f. (r z f nil = z) ∧ (∀x xs. r z f (cons x xs) = f x xs (r z
    /// f xs))` — the paramorphic recursor predicate the engine ∃-introduces
    /// over. The engine abstracts the step variables `z, f`, so the
    /// predicate must ∀-quantify them (the inner `recursor` applications
    /// stay un-reduced, matching the engine's per-constructor equations).
    fn paramorphic_pred(z: &Term, f: &Term) -> Term {
        let f_ty = f.type_of().unwrap();
        let rec_ty = Type::fun(beta(), Type::fun(f_ty.clone(), Type::fun(list_ty(), beta())));
        let r = Term::free("r", rec_ty.clone());
        let rzf = |t: Term| -> Term {
            Term::app(Term::app(Term::app(r.clone(), z.clone()), f.clone()), t)
        };
        // base: r z f nil = z.
        let base = rzf(nil(elem())).equals(z.clone()).unwrap();
        // step: ∀x xs. r z f (cons x xs) = f x xs (r z f xs).
        let x = Term::free("x", elem());
        let xs = Term::free("xs", list_ty());
        let consed = cons(elem()).apply(x.clone()).unwrap().apply(xs.clone()).unwrap();
        let lhs = rzf(consed);
        let rhs = Term::app(
            Term::app(Term::app(f.clone(), x.clone()), xs.clone()),
            rzf(xs.clone()),
        );
        let step = lhs
            .equals(rhs)
            .unwrap()
            .forall("xs", list_ty())
            .unwrap()
            .forall("x", elem())
            .unwrap();
        // ∀z f. base ∧ step.
        let body = base
            .and(step)
            .unwrap()
            .forall("f", f_ty)
            .unwrap()
            .forall("z", beta())
            .unwrap();
        let _ = beta_reduce; // (kept for parity with the nat module's helpers)
        Term::abs(rec_ty, subst::close(&body, "r"))
    }
}
