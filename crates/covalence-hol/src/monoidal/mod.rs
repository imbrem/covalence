//! A trait for **pointless (point-free) programming** over the
//! coproduct's symmetric-monoidal structure.
//!
//! [`Monoidal`] is the abstract interface of "doing a categorical,
//! point-free proof" — generic over three representations, the
//! associated types [`Obj`](Monoidal::Obj) / [`Hom`](Monoidal::Hom) /
//! [`Proof`](Monoidal::Proof). It is the coproduct analogue of
//! [`Peano`](crate::peano::Peano): the same "one API, many models, with a
//! soundness map between them" shape (the mirror principle).
//!
//! ## Three layers: objects, morphisms, equational proofs
//!
//! Point-free programming is *equational reasoning about morphisms* in a
//! category, and the trait keeps those layers visible:
//!
//! - **Objects** ([`Obj`](Monoidal::Obj)) — the "types". They carry a
//!   symmetric-monoidal product [`oplus`](Monoidal::oplus) (`⊕`, the
//!   coproduct) used to type the structural morphisms.
//! - **Morphisms** ([`Hom`](Monoidal::Hom)) — the "programs". Built from
//!   the **category** vocabulary ([`id`](Monoidal::id),
//!   [`comp`](Monoidal::comp)) and the coproduct's **join morphisms**:
//!   the coprojections [`inl`](Monoidal::inl) / [`inr`](Monoidal::inr),
//!   the copairing [`copair`](Monoidal::copair) (`[f,g]`), the bifunctor
//!   [`bimap`](Monoidal::bimap) (`f ⊕ g`), the symmetry
//!   [`swap`](Monoidal::swap) (`σ`), and the codiagonal
//!   [`codiag`](Monoidal::codiag) (`∇ = [id,id]`).
//! - **Proofs** ([`Proof`](Monoidal::Proof)) — *equations between
//!   morphisms*. The **axioms** (as proofs) are the category laws
//!   ([`id_left`](Monoidal::id_left) / [`id_right`](Monoidal::id_right) /
//!   [`assoc`](Monoidal::assoc)) and the coproduct **universal property**
//!   ([`copair_inl`](Monoidal::copair_inl) /
//!   [`copair_inr`](Monoidal::copair_inr) — the β-laws — and
//!   [`fusion`](Monoidal::fusion) — the η/uniqueness law). The
//!   **inference rules** are the equational-logic ones
//!   ([`refl`](Monoidal::refl) / [`sym`](Monoidal::sym) /
//!   [`trans`](Monoidal::trans)) plus the structural congruences
//!   ([`comp_cong`](Monoidal::comp_cong) /
//!   [`copair_cong`](Monoidal::copair_cong)).
//!
//! These axioms suffice to *derive* the symmetric-monoidal coherence
//! facts — swap's involution and naturality, the associator, the
//! bifunctoriality of `⊕` — with no further appeal to HOL. The
//! [`derived`] module collects representative worked examples
//! ([`derived::swap_involution`], [`derived::copair_unique`]), which is
//! the point of exposing a "high-level API to prove things using just
//! this structure".
//!
//! ## Two implementations, one API (the mirror principle)
//!
//! 1. **Shallow** — [`Hol`]: an object *is* a HOL [`Type`], a morphism
//!    *is* a HOL `α → β` [`Term`], and a proof *is* a HOL
//!    [`Thm`](covalence_core::Thm) equating two such terms. The axioms
//!    forward to the genuine, hypothesis-free theorems in
//!    [`init::cat`](crate::init::cat) and
//!    [`init::coprod`](crate::init::coprod). This is the model that
//!    exists today, and every axiom in it is *proved* (no postulates).
//! 2. **Deep** (future) — a syntactic `PointFreeTerm` / derivation AST,
//!    so the methods *build transportable proof objects*. The bridge to
//!    the shallow model is the soundness map "every point-free derivation
//!    denotes a valid HOL theorem".
//!
//! [`Type`]: covalence_core::Type
//! [`Term`]: covalence_core::Term

pub mod derived;
pub mod shallow;

pub use shallow::Hol;

/// Point-free reasoning over the coproduct's symmetric-monoidal
/// structure, generic over the proof representation. See the
/// [module docs](self).
pub trait Monoidal {
    /// Objects — the "types".
    type Obj: Clone;
    /// Morphisms — the "programs" `a → b`.
    type Hom: Clone;
    /// An equational proof between two morphisms.
    type Proof: Clone;
    /// Failure type for the (partial) constructors and rules.
    type Error;

    // ---- objects ----

    /// The monoidal product `a ⊕ b` (the coproduct).
    fn oplus(&self, a: Self::Obj, b: Self::Obj) -> Self::Obj;

    // ---- morphisms: the category vocabulary ----

    /// The identity `id_a : a → a`.
    fn id(&self, a: Self::Obj) -> Self::Hom;
    /// Composition `g ∘ f` (apply `f` then `g`).
    fn comp(&self, g: Self::Hom, f: Self::Hom) -> Result<Self::Hom, Self::Error>;

    // ---- morphisms: the coproduct's join morphisms ----

    /// Left coprojection `inl : a → a ⊕ b`.
    fn inl(&self, a: Self::Obj, b: Self::Obj) -> Self::Hom;
    /// Right coprojection `inr : b → a ⊕ b`.
    fn inr(&self, a: Self::Obj, b: Self::Obj) -> Self::Hom;
    /// The copairing / **join** `[f, g] : a ⊕ b → c`, given `f : a → c`
    /// and `g : b → c`.
    fn copair(&self, f: Self::Hom, g: Self::Hom) -> Result<Self::Hom, Self::Error>;
    /// The bifunctor action `f ⊕ g : a ⊕ b → a' ⊕ b'`, given `f : a → a'`
    /// and `g : b → b'`.
    fn bimap(&self, f: Self::Hom, g: Self::Hom) -> Result<Self::Hom, Self::Error>;
    /// The symmetry `σ : a ⊕ b → b ⊕ a`.
    fn swap(&self, a: Self::Obj, b: Self::Obj) -> Result<Self::Hom, Self::Error>;
    /// The codiagonal / fold `∇ = [id, id] : a ⊕ a → a`.
    fn codiag(&self, a: Self::Obj) -> Result<Self::Hom, Self::Error>;

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

    // ---- axioms (as proofs): the coproduct universal property ----

    /// **β-left.** `⊢ [f, g] ∘ inl = f`.
    fn copair_inl(&self, f: Self::Hom, g: Self::Hom) -> Result<Self::Proof, Self::Error>;
    /// **β-right.** `⊢ [f, g] ∘ inr = g`.
    fn copair_inr(&self, f: Self::Hom, g: Self::Hom) -> Result<Self::Proof, Self::Error>;
    /// **η / fusion (uniqueness).** `⊢ m = [m ∘ inl, m ∘ inr]` for any
    /// `m : a ⊕ b → c`. The principle that a map out of a coproduct is
    /// determined by its two restrictions — the workhorse for *proving*
    /// point-free equations.
    fn fusion(&self, m: Self::Hom) -> Result<Self::Proof, Self::Error>;

    // ---- inference rules: equational logic + congruence ----

    /// `⊢ f = f`.
    fn refl(&self, f: Self::Hom) -> Result<Self::Proof, Self::Error>;
    /// From `⊢ f = g` conclude `⊢ g = f`.
    fn sym(&self, p: Self::Proof) -> Result<Self::Proof, Self::Error>;
    /// From `⊢ f = g` and `⊢ g = h` conclude `⊢ f = h`.
    fn trans(&self, p: Self::Proof, q: Self::Proof) -> Result<Self::Proof, Self::Error>;
    /// From `⊢ g = g'` and `⊢ f = f'` conclude `⊢ g ∘ f = g' ∘ f'`.
    fn comp_cong(
        &self,
        g_eq: Self::Proof,
        f_eq: Self::Proof,
    ) -> Result<Self::Proof, Self::Error>;
    /// From `⊢ f = f'` and `⊢ g = g'` conclude `⊢ [f, g] = [f', g']`.
    fn copair_cong(
        &self,
        f_eq: Self::Proof,
        g_eq: Self::Proof,
    ) -> Result<Self::Proof, Self::Error>;
}
