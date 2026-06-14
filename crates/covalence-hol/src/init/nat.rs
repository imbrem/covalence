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
//! - **Induction** is genuine: `Thm::nat_induct` is a kernel primitive,
//!   so [`Peano::induct`] mints a hypothesis-free theorem.
//! - **The six structural axioms** ([`zero_ne_succ`](Peano::zero_ne_succ),
//!   [`succ_inj`](Peano::succ_inj), the `add`/`mul` equations) are
//!   **postulated** via [`Hol::axiom`] = `Thm::assume`. The kernel
//!   reduces `succ`/`natRec` only on closed literals, and exposes
//!   neither `natRec`'s computation equations nor `nat`'s freeness over
//!   *variables*, so these are not yet derivable. A PA proof therefore
//!   comes out as `{axioms used} ⊢ φ`: the hypotheses name exactly the
//!   axioms relied on (the shallow embedding of PA-derivability).
//!
//! Discharging those hypotheses — proving each `⊢ axiom` as a real HOL
//! theorem — is the **soundness of PA in HOL** step, and needs new
//! kernel primitives (the `natRec` equations + `succ` injectivity /
//! `0 ≠ S n`). Tracked in `SKELETONS.md`; the trait/API does not change
//! when they land.

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
        let n = self.var("n");
        let eq = self
            .zero()
            .equals(self.succ(n))
            .expect("zero_ne_succ: 0 = S n");
        let body = eq.not().expect("zero_ne_succ: ¬");
        let term = body.forall("n", Self::nat()).expect("zero_ne_succ: ∀n");
        Self::axiom(term)
    }

    fn succ_inj(&self) -> Thm {
        let m = self.var("m");
        let n = self.var("n");
        let prem = self
            .succ(m.clone())
            .equals(self.succ(n.clone()))
            .expect("succ_inj: S m = S n");
        let concl = m.equals(n).expect("succ_inj: m = n");
        let imp = prem.imp(concl).expect("succ_inj: ⟹");
        let term = imp
            .forall("n", Self::nat())
            .and_then(|t| t.forall("m", Self::nat()))
            .expect("succ_inj: ∀m n");
        Self::axiom(term)
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
    fn axioms_are_well_typed_and_carry_their_postulate() {
        let h = hol();
        for ax in [
            h.zero_ne_succ(),
            h.succ_inj(),
            h.add_base(),
            h.add_step(),
            h.mul_base(),
            h.mul_step(),
        ] {
            // bool-typed conclusion …
            assert!(ax.concl().type_of().unwrap().is_bool());
            // … postulated: it appears as its own hypothesis.
            assert!(
                ax.hyps().iter().any(|h| h == ax.concl()),
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
        // The derivation depends only on the succ_inj postulate.
        assert!(q.hyps().iter().any(|hyp| hyp == h.succ_inj().concl()));
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
