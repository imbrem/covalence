//! The **two-tier logic abstraction**.
//!
//! - [`Logic`] (tier 1) is just the carrier: the types a bundle is stated
//!   over. A backend needs only this to *deliver* an
//!   [`InductiveTheory`](crate::InductiveTheory) — it builds its proofs
//!   with its own native machinery.
//! - [`LogicOps`] (tier 2) adds term construction and a minimal HOL-style
//!   rule surface, for code that must be *generic over the logic*: bundle
//!   conformance checks ([`crate::conformance`]), generic derivations, and
//!   consumer layers (e.g. an ACL2-style theory over an S-expression
//!   bundle).
//!
//! The shape follows the value-typed `Hol` trait that made
//! `covalence-init`'s inductive engine backend-generic within HOL:
//! value-typed immutable terms, `&self` methods, rules returning
//! `Result<Thm, Error>`. An arena-backed logic can still implement this
//! with cheap-clone id-typed terms.
//!
//! Deliberately **not** here: `define` / `new_type_definition` (introducing
//! named constants is backend-internal — the bundle hands back *terms*),
//! and the "hard" derived rules (β-normal form, ∃-intro/elim, rewriting) —
//! backends use their own; generic tier-2 code makes do with the primitive
//! set below.

use std::fmt::Debug;

// TODO(cov:inductive.logic-api-adapter, major): Adapt this compatibility surface to covalence-logic-api once its carrier traits stabilize.

/// Tier 1 — the carrier: what an [`InductiveTheory`](crate::InductiveTheory)
/// is stated over.
pub trait Logic {
    /// The logic's types.
    type Type: Clone + PartialEq + Debug;
    /// The logic's terms.
    type Term: Clone + PartialEq + Debug;
    /// The logic's theorems (an unforgeable certificate type).
    type Thm: Clone + Debug;
    /// The logic's native error.
    type Error: std::error::Error;
}

/// Tier 2 — construction + the minimal rule surface for generic machinery
/// built on top of bundles. A strict subset of a full HOL kernel surface.
pub trait LogicOps: Logic {
    // -- Types --

    /// The type of propositions.
    fn bool_ty(&self) -> Self::Type;
    /// The function type `a → b`.
    fn fun_ty(&self, a: Self::Type, b: Self::Type) -> Self::Type;

    // -- Term builders --

    /// A free variable `name : ty`.
    fn var(&self, name: &str, ty: Self::Type) -> Self::Term;
    /// Application `f x` (type-checked).
    fn app(&self, f: Self::Term, x: Self::Term) -> Result<Self::Term, Self::Error>;
    /// Abstraction `λ(name:ty). body`, closing free `name` in `body`.
    fn lam(&self, name: &str, ty: Self::Type, body: Self::Term) -> Self::Term;
    /// `a = b`.
    fn eq(&self, a: Self::Term, b: Self::Term) -> Result<Self::Term, Self::Error>;
    /// `a ⟹ b`.
    fn imp(&self, a: Self::Term, b: Self::Term) -> Result<Self::Term, Self::Error>;
    /// `a ∧ b`.
    fn and(&self, a: Self::Term, b: Self::Term) -> Result<Self::Term, Self::Error>;
    /// `∀(name:ty). body`, closing free `name`.
    fn forall(
        &self,
        name: &str,
        ty: Self::Type,
        body: Self::Term,
    ) -> Result<Self::Term, Self::Error>;
    /// `∃(name:ty). body`, closing free `name`.
    fn exists(
        &self,
        name: &str,
        ty: Self::Type,
        body: Self::Term,
    ) -> Result<Self::Term, Self::Error>;

    // -- Queries --

    /// The type of a term.
    fn type_of(&self, t: &Self::Term) -> Result<Self::Type, Self::Error>;
    /// Destruct an application `f x`.
    fn dest_app(&self, t: &Self::Term) -> Option<(Self::Term, Self::Term)>;
    /// Destruct an equation `a = b`.
    fn dest_eq(&self, t: &Self::Term) -> Option<(Self::Term, Self::Term)>;
    /// A theorem's conclusion.
    fn concl(&self, th: &Self::Thm) -> Self::Term;
    /// A theorem's hypotheses.
    fn hyps(&self, th: &Self::Thm) -> Vec<Self::Term>;

    // -- Rules --

    /// `ASSUME t`: `{t} ⊢ t`.
    fn assume(&self, t: Self::Term) -> Result<Self::Thm, Self::Error>;
    /// `REFL t`: `⊢ t = t`.
    fn refl(&self, t: Self::Term) -> Result<Self::Thm, Self::Error>;
    /// `⊢ a = b` → `⊢ b = a`.
    fn sym(&self, th: Self::Thm) -> Result<Self::Thm, Self::Error>;
    /// `⊢ a = b` + `⊢ b = c` → `⊢ a = c`.
    fn trans(&self, a: Self::Thm, b: Self::Thm) -> Result<Self::Thm, Self::Error>;
    /// `⊢ a = b` + `⊢ a` → `⊢ b` (EQ_MP).
    fn eq_mp(&self, eq: Self::Thm, p: Self::Thm) -> Result<Self::Thm, Self::Error>;
    /// `BETA ((λx.t) u)`: `⊢ (λx.t) u = t[u/x]` (single top redex).
    fn beta_conv(&self, redex: Self::Term) -> Result<Self::Thm, Self::Error>;
    /// `⊢ f = g` + `⊢ x = y` → `⊢ f x = g y` (MK_COMB).
    fn cong_app(&self, f: Self::Thm, x: Self::Thm) -> Result<Self::Thm, Self::Error>;
    /// Instantiate the free variable `name` by `t` in a theorem.
    fn inst(&self, th: Self::Thm, name: &str, t: Self::Term) -> Result<Self::Thm, Self::Error>;
    /// `Γ ⊢ p` → `Γ ⊢ ∀(name:ty). p` (GEN; `name` not free in `Γ`).
    fn all_intro(
        &self,
        th: Self::Thm,
        name: &str,
        ty: Self::Type,
    ) -> Result<Self::Thm, Self::Error>;
    /// `⊢ ∀x. p` → `⊢ p[t/x]` (SPEC).
    fn all_elim(&self, th: Self::Thm, t: Self::Term) -> Result<Self::Thm, Self::Error>;
    /// `Γ ⊢ q` → `Γ\{p} ⊢ p ⟹ q` (DISCH; `p` need not be in `Γ`).
    fn imp_intro(&self, th: Self::Thm, h: &Self::Term) -> Result<Self::Thm, Self::Error>;
    /// `⊢ p ⟹ q` + `⊢ p` → `⊢ q` (MP).
    fn imp_elim(&self, imp: Self::Thm, ante: Self::Thm) -> Result<Self::Thm, Self::Error>;
    /// `⊢ a` + `⊢ b` → `⊢ a ∧ b`.
    fn and_intro(&self, a: Self::Thm, b: Self::Thm) -> Result<Self::Thm, Self::Error>;
    /// `⊢ a ∧ b` → `⊢ a`.
    fn and_elim_l(&self, th: Self::Thm) -> Result<Self::Thm, Self::Error>;
    /// `⊢ a ∧ b` → `⊢ b`.
    fn and_elim_r(&self, th: Self::Thm) -> Result<Self::Thm, Self::Error>;
}

/// `⊢ body` (`= f arg` β-reduced) → `⊢ f arg` — single-top-redex β-expand,
/// generic over any [`LogicOps`].
pub fn beta_expand<L: LogicOps>(
    logic: &L,
    f: &L::Term,
    arg: L::Term,
    body: L::Thm,
) -> Result<L::Thm, L::Error> {
    let redex = logic.app(f.clone(), arg)?;
    let conv = logic.beta_conv(redex)?;
    logic.eq_mp(logic.sym(conv)?, body)
}

/// `⊢ f arg` → `⊢ body` — single-top-redex β-reduce of the conclusion,
/// generic over any [`LogicOps`].
pub fn beta_reduce<L: LogicOps>(logic: &L, th: L::Thm) -> Result<L::Thm, L::Error> {
    let conv = logic.beta_conv(logic.concl(&th))?;
    logic.eq_mp(conv, th)
}
