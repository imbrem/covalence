//! A trait for **pointless (point-free) programming** over the
//! coproduct's symmetric-monoidal structure.
//!
//! [`Monoidal`] is the abstract interface of "doing a categorical,
//! point-free proof" — generic over three representations, the
//! associated types [`Obj`](Category::Obj) / [`Hom`](Category::Hom) /
//! [`Proof`](Category::Proof) it inherits from its super-trait
//! [`Category`]. It is the coproduct analogue of
//! [`Peano`](crate::peano::Peano): the same "one API, many models, with a
//! soundness map between them" shape (the mirror principle).
//!
//! ## Layering: [`Category`] then [`Monoidal`]
//!
//! The plain **category** vocabulary — objects, morphisms,
//! `id`/`comp`, the category laws, and equational logic — lives in the
//! [`Category`] super-trait (its own [`category`](crate::category)
//! module), because the
//! [`diagram`](crate::category::diagram) API (commutative diagrams *of
//! functions*) needs exactly that and nothing about the coproduct.
//! [`Monoidal`] then adds the coproduct's symmetric-monoidal structure on
//! top.
//!
//! ## Three layers: objects, morphisms, equational proofs
//!
//! Point-free programming is *equational reasoning about morphisms* in a
//! category, and the trait keeps those layers visible:
//!
//! - **Objects** ([`Obj`](Category::Obj)) — the "types". They carry a
//!   symmetric-monoidal product [`oplus`](Monoidal::oplus) (`⊕`, the
//!   coproduct) used to type the structural morphisms.
//! - **Morphisms** ([`Hom`](Category::Hom)) — the "programs". Built from
//!   the **category** vocabulary ([`id`](Category::id),
//!   [`comp`](Category::comp)) and the coproduct's **join morphisms**:
//!   the coprojections [`inl`](Monoidal::inl) / [`inr`](Monoidal::inr),
//!   the copairing [`copair`](Monoidal::copair) (`[f,g]`), the bifunctor
//!   [`bimap`](Monoidal::bimap) (`f ⊕ g`), the symmetry
//!   [`swap`](Monoidal::swap) (`σ`), and the codiagonal
//!   [`codiag`](Monoidal::codiag) (`∇ = [id,id]`).
//! - **Proofs** ([`Proof`](Category::Proof)) — *equations between
//!   morphisms*. The **axioms** (as proofs) are the category laws
//!   ([`id_left`](Category::id_left) / [`id_right`](Category::id_right) /
//!   [`assoc`](Category::assoc)) and the coproduct **universal property**
//!   ([`copair_inl`](Monoidal::copair_inl) /
//!   [`copair_inr`](Monoidal::copair_inr) — the β-laws — and
//!   [`fusion`](Monoidal::fusion) — the η/uniqueness law). The
//!   **inference rules** are the equational-logic ones
//!   ([`refl`](Category::refl) / [`sym`](Category::sym) /
//!   [`trans`](Category::trans)) plus the structural congruences
//!   ([`comp_cong`](Category::comp_cong) /
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
//!    [`init::coprod`](mod@crate::init::coprod). This is the model that
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

pub use crate::category::{Category, Hol};

/// Point-free reasoning over the coproduct's symmetric-monoidal
/// structure, generic over the proof representation. Extends
/// [`Category`] with the coproduct's join morphisms and universal
/// property. See the [module docs](self).
pub trait Monoidal: Category {
    // ---- objects ----

    /// The monoidal product `a ⊕ b` (the coproduct).
    fn oplus(&self, a: Self::Obj, b: Self::Obj) -> Self::Obj;

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

    // ---- inference rules: coproduct congruence ----

    /// From `⊢ f = f'` and `⊢ g = g'` conclude `⊢ [f, g] = [f', g']`.
    fn copair_cong(
        &self,
        f_eq: Self::Proof,
        g_eq: Self::Proof,
    ) -> Result<Self::Proof, Self::Error>;
}
