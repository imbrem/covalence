//! The **shallow** ring embedding: [`crate::semiring::Int`] over HOL `int`
//! extended to a [`Ring`].
//!
//! [`Int`] already implements [`Semiring`](crate::semiring::Semiring) in
//! [`crate::semiring::shallow`]; here we add the additive-inverse layer that
//! makes it a ring. Like the semiring axioms, [`add_neg`](Ring::add_neg) /
//! [`sub_def`](Ring::sub_def) forward to [`crate::init::int`] (postulated for
//! now; see `SKELETONS.md`), and `neg` / `sub` build the corresponding
//! `int` terms.

use covalence_core::{Term, Thm};

use crate::init::int;
use crate::ring::Ring;
use crate::semiring::Int;

impl Ring for Int {
    fn neg(&self, a: Term) -> Term {
        Term::app(int::int_neg(), a)
    }
    fn sub(&self, a: Term, b: Term) -> Term {
        Term::app(Term::app(int::int_sub(), a), b)
    }

    fn add_neg(&self) -> Thm {
        int::add_neg()
    }
    fn sub_def(&self) -> Thm {
        int::sub_def()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::semiring::Semiring;

    #[test]
    fn int_ring_axioms_rebuild_through_the_prop_layer() {
        let r = Int::new();
        let a = r.var("a");

        // add_neg: ∀a. a + (-a) = 0
        let add_neg_stmt = r.forall("a", r.eq(r.add(a.clone(), r.neg(a.clone())), r.zero()));
        assert_eq!(r.concl(&r.add_neg()), add_neg_stmt);

        // sub_def: ∀a b. a - b = a + (-b)
        let b = r.var("b");
        let sub_def_body = r.eq(r.sub(a.clone(), b.clone()), r.add(a.clone(), r.neg(b)));
        let sub_def_stmt = r.forall("a", r.forall("b", sub_def_body));
        assert_eq!(r.concl(&r.sub_def()), sub_def_stmt);

        // Postulated → each carries itself as a hypothesis (the audit trail).
        for ax in [r.add_neg(), r.sub_def()] {
            assert!(ax.hyps().iter().any(|h| h == ax.concl()));
        }
    }

    /// A generic ring routine — `⊢ a + (-a) = 0` specialised at the carrier's
    /// `1` — exercises [`Ring`] through its [`Semiring`] supertrait.
    fn one_plus_neg_one_is_zero<R: Ring>(r: &R) -> R::Proof
    where
        R::Error: std::fmt::Debug,
    {
        r.specialize(r.add_neg(), r.one())
            .expect("specialize add_neg")
    }

    #[test]
    fn generic_ring_routine_runs_against_int() {
        let r = Int::new();
        let p = one_plus_neg_one_is_zero(&r);
        let expected = r.eq(r.add(r.one(), r.neg(r.one())), r.zero());
        assert_eq!(r.concl(&p), expected);
    }
}
