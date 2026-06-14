//! The **shallow** embedding of Peano arithmetic into HOL: a PA term
//! is the HOL `nat` term, a PA proof is a HOL [`Thm`] about `nat`.
//!
//! [`Hol`] is the trivial implementation of [`Peano`] — "trivial"
//! because PA reasoning is *just* HOL reasoning over `nat`. The
//! inference rules forward straight to the kernel
//! ([`induct`](Hol::induct) → `Thm::nat_induct`,
//! [`specialize`](Peano::specialize) → `Thm::all_elim`,
//! [`mp`](Peano::mp) → `Thm::imp_elim`).
//!
//! ## What is proved vs postulated
//!
//! - **Genuine** (hypothesis-free HOL theorems):
//!   - [`induct`](Peano::induct) — kernel primitive `Thm::nat_induct`.
//!   - [`succ_inj`](Peano::succ_inj) / [`zero_ne_succ`](Peano::zero_ne_succ)
//!     — the kernel freeness primitives `Thm::succ_inj` /
//!     `Thm::zero_ne_succ` (`succ` is now a primitive `TermKind::Succ`),
//!     generalised with `all_intro`.
//! - **Postulated** via [`Hol::axiom`] = `Thm::assume`: the four
//!   `add`/`mul` recursion equations. These hold definitionally but
//!   are not yet *derivable*, because `nat_add` / `nat_mul` unfold to
//!   `natRec`, whose computation equations are not yet available over
//!   variables. A PA proof using them comes out as `{axioms used} ⊢ φ`,
//!   the hypotheses naming exactly the postulates relied on.
//!
//! The intended route for the four remaining ones is **not** a new
//! kernel primitive: `natRec` exists *by `ε`* (it is the choice over
//! its recursion-uniqueness predicate), so once `ε`/choice is exposed
//! the recursion equations are **derivable by induction** — at which
//! point the `Hol::axiom` calls become real derivations with no API
//! change. Tracked in `SKELETONS.md`.

use covalence_core::{Error, Result, Term, Thm, Type, defs};
use covalence_types::Nat;

use crate::init::ext::TermExt;
use crate::peano::Peano;

/// Shallow PA-in-HOL: `Term = nat` HOL term, `Proof = Thm`. Zero-sized.
#[derive(Clone, Copy, Debug, Default)]
pub struct Hol;

impl Hol {
    /// Construct a handle. Free; no allocation.
    pub fn new() -> Self {
        Self
    }

    fn nat() -> Type {
        Type::nat()
    }

    /// Postulate a PA axiom: `{t} ⊢ t`. The self-hypothesis is the
    /// audit trail — every PA proof built on this axiom carries it,
    /// flagging the unproved leaf until the kernel can discharge it
    /// (see the [module docs](self)).
    fn axiom(t: Term) -> Thm {
        Thm::assume(t).expect("Hol::axiom: PA axiom must be a bool-typed term")
    }
}

impl Peano for Hol {
    type Term = Term;
    type Proof = Thm;
    type Error = Error;

    // ---- term constructors ----

    fn var(&self, name: &str) -> Term {
        Term::free(name, Self::nat())
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

    // ---- axioms (postulated; see module docs) ----

    fn zero_ne_succ(&self) -> Thm {
        // Genuine: the kernel freeness rule gives `⊢ ¬(0 = S n)` for
        // free `n`; generalise.
        Thm::zero_ne_succ(self.var("n"))
            .and_then(|t| t.all_intro("n", Self::nat()))
            .expect("zero_ne_succ: kernel freeness rule")
    }

    fn succ_inj(&self) -> Thm {
        // Genuine: `⊢ (S m = S n) ⟹ (m = n)` for free `m`, `n`;
        // generalise inner-first.
        Thm::succ_inj(self.var("m"), self.var("n"))
            .and_then(|t| t.all_intro("n", Self::nat()))
            .and_then(|t| t.all_intro("m", Self::nat()))
            .expect("succ_inj: kernel freeness rule")
    }

    fn add_base(&self) -> Thm {
        let m = self.var("m");
        let lhs = self.add(self.zero(), m.clone());
        let eq = lhs.equals(m).expect("add_base: 0 + m = m");
        let term = eq.forall("m", Self::nat()).expect("add_base: ∀m");
        Self::axiom(term)
    }

    fn add_step(&self) -> Thm {
        let n = self.var("n");
        let m = self.var("m");
        let lhs = self.add(self.succ(n.clone()), m.clone());
        let rhs = self.succ(self.add(n, m.clone()));
        let eq = lhs.equals(rhs).expect("add_step: S n + m = S (n + m)");
        let term = eq
            .forall("m", Self::nat())
            .and_then(|t| t.forall("n", Self::nat()))
            .expect("add_step: ∀n m");
        Self::axiom(term)
    }

    fn mul_base(&self) -> Thm {
        let m = self.var("m");
        let lhs = self.mul(self.zero(), m);
        let eq = lhs.equals(self.zero()).expect("mul_base: 0 * m = 0");
        let term = eq.forall("m", Self::nat()).expect("mul_base: ∀m");
        Self::axiom(term)
    }

    fn mul_step(&self) -> Thm {
        let n = self.var("n");
        let m = self.var("m");
        let lhs = self.mul(self.succ(n.clone()), m.clone());
        let rhs = self.add(m.clone(), self.mul(n, m));
        let eq = lhs.equals(rhs).expect("mul_step: S n * m = m + n * m");
        let term = eq
            .forall("m", Self::nat())
            .and_then(|t| t.forall("n", Self::nat()))
            .expect("mul_step: ∀n m");
        Self::axiom(term)
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
    fn all_axioms_are_well_typed() {
        let h = hol();
        for ax in [
            h.zero_ne_succ(),
            h.succ_inj(),
            h.add_base(),
            h.add_step(),
            h.mul_base(),
            h.mul_step(),
        ] {
            assert!(ax.concl().type_of().unwrap().is_bool());
        }
    }

    #[test]
    fn freeness_axioms_are_genuine() {
        // succ_inj / zero_ne_succ are real HOL theorems now — no hyps.
        let h = hol();
        assert!(h.succ_inj().hyps().is_empty(), "succ_inj is proved");
        assert!(h.zero_ne_succ().hyps().is_empty(), "zero_ne_succ is proved");
    }

    #[test]
    fn arithmetic_axioms_are_postulated() {
        // The add/mul equations carry themselves as hypotheses until ε
        // + induction discharge them.
        let h = hol();
        for ax in [h.add_base(), h.add_step(), h.mul_base(), h.mul_step()] {
            assert!(
                ax.hyps().iter().any(|hyp| hyp == ax.concl()),
                "a postulated axiom carries itself as a hypothesis"
            );
        }
    }

    #[test]
    fn add_base_has_the_expected_shape() {
        let h = hol();
        // ∀m. 0 + m = m  — peel ∀, β-instantiate at a fresh var, check.
        let inst = h
            .specialize(h.add_base(), h.var("k"))
            .expect("specialize add_base");
        let expected = h
            .add(h.zero(), h.var("k"))
            .equals(h.var("k"))
            .unwrap();
        assert_eq!(inst.concl(), &expected);
    }

    #[test]
    fn specialize_then_mp_derives_zero_eq_zero() {
        // From succ_inj: ∀m n. S m = S n ⟹ m = n.
        // Specialize m,n := 0, MP with ⊢ S 0 = S 0, get ⊢ 0 = 0.
        let h = hol();
        let p = h.succ_inj();
        let p1 = h.specialize(p, h.zero()).unwrap();
        let p2 = h.specialize(p1, h.zero()).unwrap();
        let refl = Thm::refl(h.succ(h.zero())).unwrap(); // ⊢ S 0 = S 0
        let q = h.mp(p2, refl).unwrap();

        let expected = h.zero().equals(h.zero()).unwrap();
        assert_eq!(q.concl(), &expected);
        // succ_inj is genuine, so this derivation is hypothesis-free.
        assert!(q.hyps().is_empty(), "derived from proved axioms only");
    }

    #[test]
    fn induction_is_genuine_and_axiom_free() {
        // Prove ⊢ ∀n. P n for the trivial motive P := λn. T, with no
        // postulate dependency — induction is a real kernel rule.
        let h = hol();
        let t = Term::bool_lit(true);
        let p = Term::abs(Type::nat(), t.clone()); // λn. T

        // base : ⊢ P 0   (in applied `P 0` shape)
        let base = Thm::beta_conv(Term::app(p.clone(), h.zero()))
            .unwrap()
            .sym()
            .unwrap()
            .eq_mp(crate::init::logic::truth())
            .unwrap();

        // step : ⊢ P n ⟹ P (S n)   (free n, ungeneralised)
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
        // ⊢ ∀n:nat. P n, and — crucially — no postulate hypotheses.
        assert!(all.hyps().is_empty(), "induction adds no PA postulates");
        let covalence_core::TermKind::App(_forall, lam) = all.concl().kind() else {
            panic!("expected a ∀ application");
        };
        assert!(lam.as_abs().map(|(ty, _)| ty == &Type::nat()).unwrap_or(false));
    }
}
