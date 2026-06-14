//! A trait for reasoning in first-order **Peano arithmetic** (PA).
//!
//! [`Peano`] is the abstract interface of "doing a PA proof": the term
//! constructors (`0`, successor, `+`, `*`, variables), the PA axioms
//! (as proofs), and the inference rules (induction, ∀-elimination,
//! modus ponens). It is generic over *what a PA proof is* via the
//! associated [`Peano::Proof`] type — and that is the whole point.
//!
//! ## Two implementations, one API (the mirror principle)
//!
//! 1. **Shallow** — [`crate::init::nat::Hol`]: a PA term *is* the HOL
//!    `nat` term and a PA proof *is* a HOL [`Thm`](covalence_core::Thm)
//!    about `nat`. PA reasoning collapses to HOL reasoning. This is the
//!    "trivial" implementation — it exists today.
//! 2. **Deep** (future) — a syntactic `PaTerm` / `PaDerivation` AST.
//!    `Proof = PaDerivation`: the methods *build proof objects* you can
//!    serialise, hash, and transport, rather than HOL theorems.
//!
//! Because both implement the *same* trait, a generic routine written
//! against [`Peano`] runs against either. The bridge between them is a
//! **soundness** map `PaDerivation → Thm` — "every PA derivation
//! denotes a valid HOL theorem" — which is Covalence's first piece of
//! *symbolic metatheory*: PA as an object logic with HOL as the
//! metalogic (see `docs/VISION.md` §2).
//!
//! ## Status of the axioms (read this)
//!
//! In the shallow impl, **three** axioms are genuine hypothesis-free
//! HOL theorems: [`induct`](Peano::induct) (kernel `Thm::nat_induct`)
//! and the two freeness axioms [`succ_inj`](Peano::succ_inj) /
//! [`zero_ne_succ`](Peano::zero_ne_succ) (kernel `Thm::succ_inj` /
//! `Thm::zero_ne_succ`, since `succ` is now the primitive
//! `TermKind::Succ`). The remaining **four** — the `add`/`mul`
//! recursion equations — are still **postulated** (`Thm::assume`), so a
//! PA proof using them comes out as `{axioms used} ⊢ φ`, the honest
//! shallow embedding of *PA-derivability*.
//!
//! Discharging the four is the **soundness** step. It needs *no new
//! computation primitive*: `natRec` exists by `ε` (choice over its
//! recursion-uniqueness predicate), so once `ε`/choice is exposed its
//! equations follow by induction, and the `add`/`mul` axioms with them.
//! Recorded in `SKELETONS.md`; flipping them to proofs is a localized
//! change behind this same API.

/// Reasoning in first-order Peano arithmetic, generic over the proof
/// representation. See the [module docs](self).
pub trait Peano {
    /// The representation of PA terms (`nat`-sorted).
    type Term: Clone;
    /// The representation of a PA proof / derivation.
    type Proof: Clone;
    /// Failure type for the inference rules.
    type Error;

    // ---- term constructors ----

    /// A PA variable `name` (sort `nat`).
    fn var(&self, name: &str) -> Self::Term;
    /// The constant `0`.
    fn zero(&self) -> Self::Term;
    /// Successor `S n`.
    fn succ(&self, n: Self::Term) -> Self::Term;
    /// Addition `a + b`.
    fn add(&self, a: Self::Term, b: Self::Term) -> Self::Term;
    /// Multiplication `a * b`.
    fn mul(&self, a: Self::Term, b: Self::Term) -> Self::Term;

    // ---- the Peano axioms (as proofs) ----

    /// `∀n. ¬(0 = S n)` — zero is not a successor.
    fn zero_ne_succ(&self) -> Self::Proof;
    /// `∀m n. S m = S n ⟹ m = n` — successor is injective.
    fn succ_inj(&self) -> Self::Proof;
    /// `∀m. 0 + m = m` — addition's base equation (recursion on the
    /// left argument, matching `defs::nat_add`).
    fn add_base(&self) -> Self::Proof;
    /// `∀n m. S n + m = S (n + m)` — addition's step equation.
    fn add_step(&self) -> Self::Proof;
    /// `∀m. 0 * m = 0` — multiplication's base equation.
    fn mul_base(&self) -> Self::Proof;
    /// `∀n m. S n * m = m + n * m` — multiplication's step equation.
    fn mul_step(&self) -> Self::Proof;

    // ---- inference rules ----

    /// **Induction.** From a base proof `⊢ P 0` and a step proof
    /// `⊢ P n ⟹ P (S n)` (free `n`), conclude `⊢ ∀n. P n`. The motive
    /// `P` and the variable `n` are read from the shapes of `base` /
    /// `step` (as in `Thm::nat_induct`).
    fn induct(&self, base: Self::Proof, step: Self::Proof) -> Result<Self::Proof, Self::Error>;

    /// **∀-elimination.** From `⊢ ∀x. P x` and a witness `t`, conclude
    /// `⊢ P t`.
    fn specialize(
        &self,
        univ: Self::Proof,
        witness: Self::Term,
    ) -> Result<Self::Proof, Self::Error>;

    /// **Modus ponens.** From `⊢ p ⟹ q` and `⊢ p`, conclude `⊢ q`.
    fn mp(
        &self,
        implication: Self::Proof,
        antecedent: Self::Proof,
    ) -> Result<Self::Proof, Self::Error>;
}
