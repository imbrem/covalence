//! The [`Inductive`] trait — the engine's **only** view of an inductive
//! type's logical structure, and the seam that lets the same recursion
//! machinery serve both today's kernel-primitive `nat` and a future
//! HOL-internal one.
//!
//! ## Why a trait (the lifting story)
//!
//! The recursion engine never calls a kernel rule (`Thm::nat_induct`,
//! `Thm::succ_inj`, …) directly. It asks an `Inductive` for the facts it
//! needs — structural induction now, constructor freeness later. That
//! *dependency inversion* is deliberate:
//!
//! - **Today** `nat` is a kernel primitive: its `Inductive` impl wraps
//!   `Thm::nat_induct` (and, when freeness lands, `Thm::succ_inj` /
//!   `Thm::zero_ne_succ`).
//! - **Later** we may define `nat` *internally* from `ind` the standard
//!   HOL way (`0`/`SUC` carved out of an infinite type, `NUM_REP`), where
//!   induction and freeness are **derived theorems** rather than kernel
//!   rules. That presentation supplies the *same* `Inductive` interface,
//!   so it drives the *same* engine — `graph`/`existence`/… are reused
//!   verbatim, and the work to lift these proofs into internal HOL is just
//!   writing one new impl.
//!
//! Keeping every engine entry point generic over `I: Inductive` (never
//! over a concrete `nat`) is what keeps that door open; see
//! `SKELETONS.md` for the planned `nat`-from-`ind` construction.

use covalence_core::{Result, Term, Thm};

use super::sig::InductiveSig;

/// An inductive type, presented to the recursion engine as its signature
/// plus the structural facts the engine consumes.
///
/// Implementors supply the *proofs*; the engine supplies the *plumbing*
/// (the impredicative graph, totality, determinacy, ε-assembly). The
/// split is what makes the engine reusable across presentations of the
/// same type (kernel-primitive vs. HOL-internal — see the [module
/// docs](self)).
pub trait Inductive {
    /// The type's constructor signature.
    fn sig(&self) -> &InductiveSig;

    /// **Structural induction.** Given the induction `motive` (a predicate
    /// `λt. …` over the inductive type) and one `case` proof per
    /// constructor — in *applied* form, the case for `Cᵢ` being
    ///
    /// ```text
    ///   ⊢ (⋀ⱼ motive rⱼ) ⟹ motive (Cᵢ x⃗)
    /// ```
    ///
    /// over fresh argument variables `x⃗` (with `rⱼ` the recursive ones),
    /// degenerating to `⊢ motive (Cᵢ x⃗)` for a non-recursive constructor —
    /// conclude `⊢ ∀t. motive t`.
    ///
    /// `cases` are in constructor order and must match `self.sig().arity()`.
    fn induct(&self, motive: &Term, cases: Vec<Thm>) -> Result<Thm>;
}
