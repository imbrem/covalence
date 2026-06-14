//! The **shallow** embedding of Peano arithmetic into HOL: a PA term is
//! the HOL `nat` term, a PA proof is a HOL [`Thm`] about `nat`.
//!
//! [`Hol`] is the trivial implementation of [`Peano`] — "trivial"
//! because PA reasoning is *just* HOL reasoning over `nat`: a PA term is
//! a `nat` term, a PA formula is a `bool`-typed term built from the HOL
//! connectives, and a PA proof is a HOL [`Thm`]. The axioms are the
//! proved theorems in [`crate::init::nat`]; the inference rules forward
//! straight to the kernel ([`induct`](Peano::induct) → `Thm::nat_induct`,
//! [`specialize`](Peano::specialize) → `Thm::all_elim`,
//! [`mp`](Peano::mp) → `Thm::imp_elim`).
//!
//! Every PA axiom is a genuine, hypothesis-free HOL theorem (the four
//! `add`/`mul` recursion equations discharged by the recursion theorem
//! in [`crate::init::recursion`]), so a shallow PA proof is an outright
//! HOL theorem.

use covalence_core::{Error, Result, Term, Thm, Type, defs};
use covalence_types::Nat;

use crate::HolLightCtx;
use crate::init::nat;
use crate::peano::Peano;

/// Shallow PA-in-HOL: `Term = nat` HOL term, `Proof = Thm`. Zero-sized.
#[derive(Clone, Copy, Debug, Default)]
pub struct Hol;

impl Hol {
    /// Construct a handle. Free; no allocation.
    pub fn new() -> Self {
        Self
    }
}

impl Peano for Hol {
    // Both a PA term and a PA formula are just HOL `Term`s (a formula is
    // a `bool`-typed one); a PA proof is a HOL `Thm`.
    type Term = Term;
    type Prop = Term;
    type Proof = Thm;
    type Error = Error;

    // ---- expression theory: term constructors ----

    fn var(&self, name: &str) -> Term {
        Term::free(name, Type::nat())
    }

    fn zero(&self) -> Term {
        Term::nat_lit(Nat::zero())
    }

    fn succ(&self, n: Term) -> Term {
        Term::app(defs::nat_succ(), n)
    }

    fn add(&self, a: Term, b: Term) -> Term {
        Term::app(Term::app(defs::nat_add(), a), b)
    }

    fn mul(&self, a: Term, b: Term) -> Term {
        Term::app(Term::app(defs::nat_mul(), a), b)
    }

    // ---- first-order logic: formula constructors (HOL connectives) ----

    fn eq(&self, a: Term, b: Term) -> Term {
        HolLightCtx::new().mk_eq(a, b).expect("eq: nat terms are well-typed")
    }
    fn not(&self, p: Term) -> Term {
        HolLightCtx::new().mk_not(p)
    }
    fn and(&self, p: Term, q: Term) -> Term {
        HolLightCtx::new().mk_and(p, q)
    }
    fn or(&self, p: Term, q: Term) -> Term {
        HolLightCtx::new().mk_or(p, q)
    }
    fn implies(&self, p: Term, q: Term) -> Term {
        HolLightCtx::new().mk_imp(p, q)
    }
    fn iff(&self, p: Term, q: Term) -> Term {
        HolLightCtx::new().mk_iff(p, q)
    }
    fn forall(&self, name: &str, body: Term) -> Term {
        HolLightCtx::new().mk_forall(name, Type::nat(), body)
    }
    fn exists(&self, name: &str, body: Term) -> Term {
        HolLightCtx::new().mk_exists(name, Type::nat(), body)
    }

    fn concl(&self, proof: &Thm) -> Term {
        proof.concl().clone()
    }

    // ---- axioms (the proved theorems in `init::nat`) ----

    fn zero_ne_succ(&self) -> Thm {
        nat::zero_ne_succ()
    }
    fn succ_inj(&self) -> Thm {
        nat::succ_inj()
    }
    fn add_base(&self) -> Thm {
        nat::add_base()
    }
    fn add_step(&self) -> Thm {
        nat::add_step()
    }
    fn mul_base(&self) -> Thm {
        nat::mul_base()
    }
    fn mul_step(&self) -> Thm {
        nat::mul_step()
    }

    // ---- inference rules (genuine kernel forwarding) ----

    fn induct(&self, base: Thm, step: Thm) -> Result<Thm> {
        Thm::nat_induct(base, step)
    }

    fn specialize(&self, univ: Thm, witness: Term) -> Result<Thm> {
        univ.all_elim(witness)
    }

    fn mp(&self, implication: Thm, antecedent: Thm) -> Result<Thm> {
        implication.imp_elim(antecedent)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn hol() -> Hol {
        Hol::new()
    }

    #[test]
    fn specialize_then_mp_derives_zero_eq_zero() {
        // From succ_inj: ∀m n. S m = S n ⟹ m = n.
        // Specialize m,n := 0, MP with ⊢ S 0 = S 0, get ⊢ 0 = 0.
        let h = hol();
        let p1 = h.specialize(h.succ_inj(), h.zero()).unwrap();
        let p2 = h.specialize(p1, h.zero()).unwrap();
        let refl = Thm::refl(h.succ(h.zero())).unwrap(); // ⊢ S 0 = S 0
        let q = h.mp(p2, refl).unwrap();

        let expected = {
            use crate::init::ext::TermExt;
            h.zero().equals(h.zero()).unwrap()
        };
        assert_eq!(q.concl(), &expected);
        // succ_inj is genuine, so this derivation is hypothesis-free.
        assert!(q.hyps().is_empty(), "derived from proved axioms only");
    }

    #[test]
    fn axiom_statements_rebuild_through_the_fol_layer() {
        // The `Prop` layer reconstructs each axiom's statement exactly —
        // i.e. `concl(axiom)` equals the formula built from `eq` /
        // connectives / quantifiers.
        let h = hol();

        // add_base: ∀m. 0 + m = m
        let m = h.var("m");
        let add_base_stmt = h.forall("m", h.eq(h.add(h.zero(), m.clone()), m));
        assert_eq!(h.concl(&h.add_base()), add_base_stmt);

        // succ_inj: ∀m n. (S m = S n) ⟹ (m = n)
        let (m, n) = (h.var("m"), h.var("n"));
        let body = h.implies(
            h.eq(h.succ(m.clone()), h.succ(n.clone())),
            h.eq(m, n),
        );
        let succ_inj_stmt = h.forall("m", h.forall("n", body));
        assert_eq!(h.concl(&h.succ_inj()), succ_inj_stmt);

        // zero_ne_succ: ∀n. ¬(0 = S n)
        let n = h.var("n");
        let zns_stmt = h.forall("n", h.not(h.eq(h.zero(), h.succ(n))));
        assert_eq!(h.concl(&h.zero_ne_succ()), zns_stmt);
    }

    #[test]
    fn fol_constructors_build_bool_formulas() {
        // Every formula constructor yields a `bool`-typed HOL term.
        let h = hol();
        let (a, b) = (h.var("a"), h.var("b"));
        let p = h.eq(a.clone(), b.clone());
        let q = h.eq(h.succ(a), b);
        for prop in [
            p.clone(),
            h.not(p.clone()),
            h.and(p.clone(), q.clone()),
            h.or(p.clone(), q.clone()),
            h.implies(p.clone(), q.clone()),
            h.iff(p.clone(), q.clone()),
            h.forall("a", p.clone()),
            h.exists("a", p),
        ] {
            assert!(prop.type_of().unwrap().is_bool());
        }
    }

    #[test]
    fn induction_is_genuine_and_axiom_free() {
        // Prove ⊢ ∀n. P n for the trivial motive P := λn. T.
        let h = hol();
        let t = Term::bool_lit(true);
        let p = Term::abs(Type::nat(), t.clone()); // λn. T

        let base = Thm::beta_conv(Term::app(p.clone(), h.zero()))
            .unwrap()
            .sym()
            .unwrap()
            .eq_mp(crate::init::logic::truth())
            .unwrap();

        let n = h.var("n");
        let p_n = Thm::beta_conv(Term::app(p.clone(), n.clone()))
            .unwrap()
            .sym()
            .unwrap()
            .eq_mp(crate::init::logic::truth())
            .unwrap();
        let p_succ_n = Thm::beta_conv(Term::app(p, h.succ(n)))
            .unwrap()
            .sym()
            .unwrap()
            .eq_mp(crate::init::logic::truth())
            .unwrap();
        let step = p_succ_n.imp_intro(p_n.concl()).unwrap();

        let all = h.induct(base, step).unwrap();
        assert!(all.hyps().is_empty(), "induction adds no PA postulates");
        let covalence_core::TermKind::App(_forall, lam) = all.concl().kind() else {
            panic!("expected a ∀ application");
        };
        assert!(lam.as_abs().map(|(ty, _)| ty == &Type::nat()).unwrap_or(false));
    }
}
