//! The **category** layer — the foundational point-free vocabulary:
//! objects, morphisms, and *equations between morphisms*, with the
//! category laws and equational-logic rules.
//!
//! This module is deliberately kept *below* (and independent of) the
//! coproduct's symmetric-monoidal structure in
//! [`monoidal`](crate::monoidal). A plain category is all you need to
//! **state and prove that a diagram commutes** — compose morphisms, and
//! reason equationally about the composites — and it is the substrate the
//! diagrammatic calculi are built on:
//!
//! - [`diagram`] — **commutative diagrams**: objects are nodes,
//!   morphisms are edges, and a proof shows two parallel paths are equal.
//! - *string diagrams* (future) — the Poincaré-dual graphical calculus
//!   (morphisms are boxes, objects are wires). They live here, on the
//!   bare [`Category`] interface, rather than under
//!   [`monoidal`](crate::monoidal), so the representation is shared by
//!   every category model.
//!
//! ## Three layers
//!
//! - **Objects** ([`Obj`](Category::Obj)) — the "types".
//! - **Morphisms** ([`Hom`](Category::Hom)) — the "programs" `a → b`,
//!   built from [`id`](Category::id) and [`comp`](Category::comp).
//! - **Proofs** ([`Proof`](Category::Proof)) — equations between
//!   morphisms. The **axioms** are the category laws
//!   ([`id_left`](Category::id_left) / [`id_right`](Category::id_right) /
//!   [`assoc`](Category::assoc)); the **inference rules** are equational
//!   logic ([`refl`](Category::refl) / [`sym`](Category::sym) /
//!   [`trans`](Category::trans)) plus the composition congruence
//!   ([`comp_cong`](Category::comp_cong) — the *whiskering* rule that lets
//!   a known equation act inside a larger composite).
//!
//! ## Two implementations, one API (the mirror principle)
//!
//! 1. **Shallow** — [`Hol`]: an object *is* a HOL [`Type`], a morphism
//!    *is* a HOL `α → β` [`Term`], and a proof *is* a HOL
//!    [`Thm`](covalence_core::Thm) equating two morphisms. Every law
//!    forwards to a genuine, hypothesis-free theorem in
//!    [`init::cat`](crate::init::cat). This is the model that exists
//!    today, and it is *proved* (no postulates).
//! 2. **Deep** (future) — a syntactic derivation AST whose methods build
//!    transportable proof objects; the bridge to the shallow model is the
//!    soundness map "every derivation denotes a valid HOL theorem".
//!
//! [`Type`]: covalence_core::Type
//! [`Term`]: covalence_core::Term

pub mod diagram;
pub mod shallow;

pub use shallow::Hol;

/// A category whose morphism equations can be *proved*, generic over the
/// proof representation. The substrate the [`diagram`] API (and future
/// string-diagram calculi) is built on, and the super-trait of
/// [`Monoidal`](crate::monoidal::Monoidal). See the [module docs](self).
pub trait Category {
    /// Objects — the "types".
    type Obj: Clone;
    /// Morphisms — the "programs" `a → b`.
    type Hom: Clone;
    /// An equational proof between two morphisms.
    type Proof: Clone;
    /// Failure type for the (partial) constructors and rules.
    type Error;

    // ---- morphisms: the category vocabulary ----

    /// The identity `id_a : a → a`.
    fn id(&self, a: Self::Obj) -> Self::Hom;
    /// Composition `g ∘ f` (apply `f` then `g`).
    fn comp(&self, g: Self::Hom, f: Self::Hom) -> Result<Self::Hom, Self::Error>;

    /// The two sides `(lhs, rhs)` of the equation a proof establishes.
    fn concl(&self, proof: &Self::Proof) -> (Self::Hom, Self::Hom);

    // ---- axioms (as proofs): the category laws ----

    /// `⊢ id ∘ f = f`.
    fn id_left(&self, f: Self::Hom) -> Result<Self::Proof, Self::Error>;
    /// `⊢ f ∘ id = f`.
    fn id_right(&self, f: Self::Hom) -> Result<Self::Proof, Self::Error>;
    /// `⊢ (h ∘ g) ∘ f = h ∘ (g ∘ f)`.
    fn assoc(
        &self,
        h: Self::Hom,
        g: Self::Hom,
        f: Self::Hom,
    ) -> Result<Self::Proof, Self::Error>;

    // ---- inference rules: equational logic + congruence ----

    /// `⊢ f = f`.
    fn refl(&self, f: Self::Hom) -> Result<Self::Proof, Self::Error>;
    /// From `⊢ f = g` conclude `⊢ g = f`.
    fn sym(&self, p: Self::Proof) -> Result<Self::Proof, Self::Error>;
    /// From `⊢ f = g` and `⊢ g = h` conclude `⊢ f = h`.
    fn trans(&self, p: Self::Proof, q: Self::Proof) -> Result<Self::Proof, Self::Error>;
    /// From `⊢ g = g'` and `⊢ f = f'` conclude `⊢ g ∘ f = g' ∘ f'` — the
    /// **whiskering** congruence that lets a proof act on either side of a
    /// composite.
    fn comp_cong(
        &self,
        g_eq: Self::Proof,
        f_eq: Self::Proof,
    ) -> Result<Self::Proof, Self::Error>;
}
