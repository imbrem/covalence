//! A trait for reasoning in a **commutative semiring** — the equational
//! theory of `(+, ·, 0, 1)` shared by `nat`, `int`, `rat`, `real`,
//! polynomials, … .
//!
//! [`Semiring`] is the abstract interface of "doing a commutative-semiring
//! proof", generic over its representations — the associated types
//! [`Term`](Semiring::Term) / [`Prop`](Semiring::Prop) /
//! [`Proof`](Semiring::Proof). It is the algebraic sibling of
//! [`crate::peano::Peano`]: where `Peano` is *first-order logic over an
//! arithmetic expression theory*, `Semiring` is the **purely equational**
//! theory of a carrier with two associative-commutative operations, one
//! distributing over the other.
//!
//! ## Two layers: term theory + equational reasoning
//!
//! - **Term theory** ([`Term`](Semiring::Term)) — the carrier-sorted term
//!   language: the constants `0` ([`zero`](Semiring::zero)) / `1`
//!   ([`one`](Semiring::one)), the operations `+` ([`add`](Semiring::add))
//!   / `·` ([`mul`](Semiring::mul)), and variables ([`var`](Semiring::var)).
//! - **Equational reasoning** ([`Proof`](Semiring::Proof)) — the semiring
//!   axioms (as proofs), the equational congruence/closure rules
//!   ([`refl`](Semiring::refl) / [`sym`](Semiring::sym) /
//!   [`trans`](Semiring::trans) / [`cong_add`](Semiring::cong_add) /
//!   [`cong_mul`](Semiring::cong_mul)) and the
//!   universal-instance machinery ([`specialize`](Semiring::specialize) /
//!   [`generalize`](Semiring::generalize)) for the `∀`-quantified axioms.
//!   [`concl`](Semiring::concl) reads back the [`Prop`](Semiring::Prop) — a
//!   single equation — a proof establishes.
//!
//! Unlike PA, a semiring needs no connective/quantifier natural-deduction
//! layer: every axiom is a universally-quantified equation and reasoning is
//! by congruence + instantiation. Carriers that *are* first-order theories
//! (e.g. the ordered ring of `int`) layer that structure elsewhere; the
//! [`Ring`](crate::ring::Ring) extension adds the additive-inverse axioms.
//!
//! ## The axioms (commutative semiring)
//!
//! - **Additive commutative monoid** — [`add_comm`](Semiring::add_comm) /
//!   [`add_assoc`](Semiring::add_assoc) /
//!   [`add_zero`](Semiring::add_zero) (`a + 0 = a`).
//! - **Multiplicative commutative monoid** —
//!   [`mul_comm`](Semiring::mul_comm) / [`mul_assoc`](Semiring::mul_assoc) /
//!   [`mul_one`](Semiring::mul_one) (`a · 1 = a`).
//! - **Distributivity & annihilation** — [`distrib`](Semiring::distrib)
//!   (`a · (b + c) = a · b + a · c`) and
//!   [`mul_zero`](Semiring::mul_zero) (`a · 0 = 0`).
//!
//! ## Embeddings (the mirror principle)
//!
//! 1. **`nat`** — [`shallow::Nat`]: every axiom is a genuine, hypothesis-free
//!    HOL theorem proved by induction in [`crate::init::nat`].
//! 2. **`int`** — [`shallow::Int`]: the axioms forward to
//!    [`crate::init::int`]; `int` additionally extends to a
//!    [`Ring`](crate::ring::Ring). They are *postulated* for now (the
//!    Grothendieck quotient derivation is pending — see `SKELETONS.md`), but
//!    the public surface does not change when the proofs land.
//!
//! Both implement the *same* trait, so a generic routine written against
//! [`Semiring`] runs against either carrier — and against the `rat` / `real`
//! / polynomial instances to come.

pub mod shallow;

pub use shallow::{Int, Nat};

/// Reasoning in a commutative semiring, generic over the proof
/// representation. See the [module docs](self).
pub trait Semiring {
    /// Carrier-sorted *expression* terms.
    type Term: Clone;
    /// Propositions — here, equations between terms.
    type Prop: Clone;
    /// A semiring proof / derivation.
    type Proof: Clone;
    /// Failure type for the inference rules.
    type Error;

    // ---- term theory: constructors ----

    /// A variable `name` of the carrier sort.
    fn var(&self, name: &str) -> Self::Term;
    /// The additive identity `0`.
    fn zero(&self) -> Self::Term;
    /// The multiplicative identity `1`.
    fn one(&self) -> Self::Term;
    /// Addition `a + b`.
    fn add(&self, a: Self::Term, b: Self::Term) -> Self::Term;
    /// Multiplication `a · b`.
    fn mul(&self, a: Self::Term, b: Self::Term) -> Self::Term;

    // ---- propositions ----

    /// The equation `a = b` — a semiring's sole atomic proposition.
    fn eq(&self, a: Self::Term, b: Self::Term) -> Self::Prop;
    /// Universal closure `∀name. body` over a carrier variable.
    fn forall(&self, name: &str, body: Self::Prop) -> Self::Prop;

    /// The proposition a proof establishes (its conclusion).
    fn concl(&self, proof: &Self::Proof) -> Self::Prop;

    // ---- the semiring axioms (as proofs) ----

    /// `⊢ ∀a b. a + b = b + a`.
    fn add_comm(&self) -> Self::Proof;
    /// `⊢ ∀a b c. (a + b) + c = a + (b + c)`.
    fn add_assoc(&self) -> Self::Proof;
    /// `⊢ ∀a. a + 0 = a` — additive identity.
    fn add_zero(&self) -> Self::Proof;
    /// `⊢ ∀a b. a · b = b · a`.
    fn mul_comm(&self) -> Self::Proof;
    /// `⊢ ∀a b c. (a · b) · c = a · (b · c)`.
    fn mul_assoc(&self) -> Self::Proof;
    /// `⊢ ∀a. a · 1 = a` — multiplicative identity.
    fn mul_one(&self) -> Self::Proof;
    /// `⊢ ∀a. a · 0 = 0` — annihilation.
    fn mul_zero(&self) -> Self::Proof;
    /// `⊢ ∀a b c. a · (b + c) = a · b + a · c` — distributivity.
    fn distrib(&self) -> Self::Proof;

    // ---- equational reasoning ----

    /// **Reflexivity.** `⊢ a = a`.
    fn refl(&self, a: Self::Term) -> Result<Self::Proof, Self::Error>;
    /// **Symmetry.** From `⊢ a = b`, conclude `⊢ b = a`.
    fn sym(&self, eq: Self::Proof) -> Result<Self::Proof, Self::Error>;
    /// **Transitivity.** From `⊢ a = b` and `⊢ b = c`, conclude `⊢ a = c`.
    fn trans(&self, ab: Self::Proof, bc: Self::Proof) -> Result<Self::Proof, Self::Error>;

    /// **`+`-congruence.** From `⊢ a₁ = a₂` and `⊢ b₁ = b₂`, conclude
    /// `⊢ a₁ + b₁ = a₂ + b₂`.
    fn cong_add(&self, a: Self::Proof, b: Self::Proof) -> Result<Self::Proof, Self::Error>;
    /// **`·`-congruence.** From `⊢ a₁ = a₂` and `⊢ b₁ = b₂`, conclude
    /// `⊢ a₁ · b₁ = a₂ · b₂`.
    fn cong_mul(&self, a: Self::Proof, b: Self::Proof) -> Result<Self::Proof, Self::Error>;

    /// **∀-elimination (specialize).** From `⊢ ∀x. P x` and a witness `t`,
    /// conclude `⊢ P t`.
    fn specialize(
        &self,
        univ: Self::Proof,
        witness: Self::Term,
    ) -> Result<Self::Proof, Self::Error>;

    /// **∀-introduction (generalize).** From `⊢ P` in which `var` is not
    /// free in any hypothesis, conclude `⊢ ∀var. P`.
    fn generalize(&self, proof: Self::Proof, var: &str) -> Result<Self::Proof, Self::Error>;
}
