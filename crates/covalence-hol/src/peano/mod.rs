//! A trait for reasoning in first-order **Peano arithmetic** (PA).
//!
//! [`Peano`] is the abstract interface of "doing a PA proof". It is
//! generic over three representations, the associated types
//! [`Term`](Peano::Term) / [`Prop`](Peano::Prop) /
//! [`Proof`](Peano::Proof) — and that genericity is the whole point.
//!
//! ## Three layers: expression theory, first-order logic, proofs
//!
//! PA is **first-order logic over an arithmetic expression theory**, and
//! the trait keeps those layers visible:
//!
//! - **Expression theory** ([`Term`](Peano::Term)) — the `nat`-sorted
//!   term language: `0`, successor, `+`, `*`, variables.
//! - **First-order logic** ([`Prop`](Peano::Prop)) — formulas built from
//!   the one relation symbol `=` ([`eq`](Peano::eq)) by the connectives
//!   ([`not`](Peano::not) / [`and`](Peano::and) / [`or`](Peano::or) /
//!   [`implies`](Peano::implies) / [`iff`](Peano::iff)) and quantifiers
//!   ([`forall`](Peano::forall) / [`exists`](Peano::exists)) over term
//!   variables. This layer is *not* arithmetic-specific — it is the FOL
//!   scaffolding. Eventually it will be factored into a generic
//!   `FirstOrder<Expr>` framework that **wraps any expression theory in
//!   first-order logic**; PA is then `FirstOrder<arithmetic>` plus the
//!   six arithmetic axioms.
//! - **Proofs** ([`Proof`](Peano::Proof)) — the PA axioms (as proofs)
//!   and the inference rules; [`concl`](Peano::concl) reads back the
//!   `Prop` a proof establishes.
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
//! ## Status of the axioms
//!
//! In the shallow impl **every** PA axiom is now a genuine
//! hypothesis-free HOL theorem: induction and the freeness axioms via
//! kernel primitives, and the four `add`/`mul` recursion equations via
//! the recursion theorem ([`crate::init::recursion`], which discharged
//! the last postulate). So a shallow PA proof is an outright HOL
//! theorem — PA is sound in HOL with nothing assumed.

pub mod shallow;

pub use shallow::Hol;

/// Reasoning in first-order Peano arithmetic, generic over the proof
/// representation. See the [module docs](self).
pub trait Peano {
    /// PA terms — the `nat`-sorted *expression* language.
    type Term: Clone;
    /// PA propositions — the first-order *formulas* over terms.
    type Prop: Clone;
    /// A PA proof / derivation.
    type Proof: Clone;
    /// Failure type for the inference rules.
    type Error;

    // ---- expression theory: term constructors ----

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

    // ---- first-order logic: formula constructors ----

    /// The atomic formula `a = b` — PA's sole relation symbol.
    fn eq(&self, a: Self::Term, b: Self::Term) -> Self::Prop;
    /// Negation `¬p`.
    fn not(&self, p: Self::Prop) -> Self::Prop;
    /// Conjunction `p ∧ q`.
    fn and(&self, p: Self::Prop, q: Self::Prop) -> Self::Prop;
    /// Disjunction `p ∨ q`.
    fn or(&self, p: Self::Prop, q: Self::Prop) -> Self::Prop;
    /// Implication `p ⟹ q`.
    fn implies(&self, p: Self::Prop, q: Self::Prop) -> Self::Prop;
    /// Biconditional `p ⟺ q`.
    fn iff(&self, p: Self::Prop, q: Self::Prop) -> Self::Prop;
    /// Universal quantification `∀name. body`, binding the term variable
    /// `name` in `body`.
    fn forall(&self, name: &str, body: Self::Prop) -> Self::Prop;
    /// Existential quantification `∃name. body`.
    fn exists(&self, name: &str, body: Self::Prop) -> Self::Prop;

    /// The proposition a proof establishes (its conclusion).
    fn concl(&self, proof: &Self::Proof) -> Self::Prop;

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
