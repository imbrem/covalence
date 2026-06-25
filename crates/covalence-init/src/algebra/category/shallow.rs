//! The **shallow** embedding of category reasoning into HOL: an object is
//! a HOL [`Type`], a morphism is a HOL `α → β` [`Term`], and a proof is a
//! HOL [`Thm`] equating two morphisms.
//!
//! [`Hol`] is the trivial implementation of [`Category`] — "trivial"
//! because point-free category reasoning is *just* HOL reasoning about
//! functions. Every law forwards to a genuine, hypothesis-free theorem in
//! [`init::cat`](crate::init::cat), so a shallow categorical proof is an
//! outright HOL theorem — nothing is postulated. The same `Hol` handle
//! also carries the coproduct's [`Monoidal`](crate::algebra::monoidal::Monoidal)
//! structure, implemented one layer up.

use covalence_core::{Result, Term, Thm, Type};

use crate::algebra::category::Category;
use crate::init::cat;

/// Shallow point-free-in-HOL: `Obj = Type`, `Hom = Term`, `Proof = Thm`.
/// Zero-sized. Implements [`Category`] here and
/// [`Monoidal`](crate::algebra::monoidal::Monoidal) in [`crate::algebra::monoidal`].
#[derive(Clone, Copy, Debug, Default)]
pub struct Hol;

impl Hol {
    /// Construct a handle. Free; no allocation.
    pub fn new() -> Self {
        Self
    }
}

impl Category for Hol {
    type Obj = Type;
    type Hom = Term;
    type Proof = Thm;
    type Error = covalence_core::Error;

    // ---- morphisms: category ----

    fn id(&self, a: Type) -> Term {
        cat::id(a)
    }

    fn comp(&self, g: Term, f: Term) -> Result<Term> {
        cat::comp(&g, &f)
    }

    fn concl(&self, proof: &Thm) -> (Term, Term) {
        let (l, r) = proof
            .concl()
            .as_eq()
            .expect("a categorical proof is an equation");
        (l.clone(), r.clone())
    }

    // ---- axioms: category laws ----

    fn id_left(&self, f: Term) -> Result<Thm> {
        cat::id_left(&f)
    }

    fn id_right(&self, f: Term) -> Result<Thm> {
        cat::id_right(&f)
    }

    fn assoc(&self, h: Term, g: Term, f: Term) -> Result<Thm> {
        cat::comp_assoc(&h, &g, &f)
    }

    // ---- inference rules ----

    fn refl(&self, f: Term) -> Result<Thm> {
        Thm::refl(f)
    }

    fn sym(&self, p: Thm) -> Result<Thm> {
        p.sym()
    }

    fn trans(&self, p: Thm, q: Thm) -> Result<Thm> {
        p.trans(q)
    }

    fn comp_cong(&self, g_eq: Thm, f_eq: Thm) -> Result<Thm> {
        cat::comp_cong(&g_eq, &f_eq)
    }
}
