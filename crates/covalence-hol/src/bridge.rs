//! HOL ↔ Pure conversion utilities.
//!
//! `covalence-core` exposes four reflection axioms
//! ([`Thm::eq_reflection`], [`Thm::forall_reflection`],
//! [`Thm::imp_reflection`]) that pair each HOL-object-language
//! connective with its Pure meta counterpart. The functions in this
//! module package the standard application patterns of those axioms
//! into reusable helpers — `pure_eq_from_hol_eq`,
//! `hol_eq_from_pure_eq`, `lift_imp_to_hol`, … — so downstream
//! proofs (like [`crate::peano`]) don't have to re-derive them.
//!
//! Every helper here is a thin combinator over the kernel rules;
//! none of them add new axioms. A bug in this module cannot
//! produce a false `Thm` — at worst, you get a kernel error
//! propagated out of an `.expect(...)`.
//!
//! ## Note on "could these be proved instead of axiomatized?"
//!
//! In HOL Light proper, the reflection bridges are *theorems*: the
//! object-level connectives `∀`, `⟹`, `∧`, `∨`, `¬` are all defined
//! in terms of `=` (e.g., `∀ = λP. P = λx. T`,
//! `⟹ = λp q. (p ∧ q) = p`, …). Once `eq_reflection` is in hand,
//! every other bridge derives by unfolding.
//!
//! In our kernel, each HOL connective is a first-class `HolOp(_)`
//! primitive — we trade derivability for simpler reasoning about
//! the connectives' shape. The reflection axioms stay as
//! kernel facts. A future variant of the kernel could drop them
//! down into definitions; the surface of this module would
//! survive the migration.

use covalence_core::{Term, Thm, Type};

/// Convert `Γ ⊢ Trueprop (x = y)` (HOL equality at type `α`) into
/// `Γ ⊢ x ≡ y` (Pure meta-equality). Uses
/// [`Thm::eq_reflection`].
pub fn pure_eq_from_hol_eq(hol_eq_thm: Thm, alpha: Type, x: Term, y: Term) -> Thm {
    Thm::eq_reflection()
        .inst_tfree("a", alpha)
        .expect("pure_eq_from_hol_eq: inst_tfree")
        .all_elim(x)
        .expect("pure_eq_from_hol_eq: all_elim x")
        .all_elim(y)
        .expect("pure_eq_from_hol_eq: all_elim y")
        .eq_mp(hol_eq_thm)
        .expect("pure_eq_from_hol_eq: eq_mp")
}

/// Convert `Γ ⊢ x ≡ y` into `Γ ⊢ Trueprop (x = y)`. Uses
/// [`Thm::eq_reflection`] in reverse via `sym`.
pub fn hol_eq_from_pure_eq(pure_eq_thm: Thm, alpha: Type, x: Term, y: Term) -> Thm {
    Thm::eq_reflection()
        .inst_tfree("a", alpha)
        .expect("hol_eq_from_pure_eq: inst_tfree")
        .all_elim(x)
        .expect("hol_eq_from_pure_eq: all_elim x")
        .all_elim(y)
        .expect("hol_eq_from_pure_eq: all_elim y")
        .sym()
        .expect("hol_eq_from_pure_eq: sym")
        .eq_mp(pure_eq_thm)
        .expect("hol_eq_from_pure_eq: eq_mp")
}

/// Convert `Γ ⊢ Trueprop A ⟹ Trueprop B` (Pure meta-implication
/// over Trueprop-wrapped HOL atoms) into `Γ ⊢ Trueprop (A ⟹ B)`
/// (HOL implication under one Trueprop). Uses
/// [`Thm::imp_reflection`].
pub fn lift_imp_to_hol(pure_imp_thm: Thm, a: Term, b: Term) -> Thm {
    Thm::imp_reflection()
        .all_elim(a)
        .expect("lift_imp_to_hol: all_elim a")
        .all_elim(b)
        .expect("lift_imp_to_hol: all_elim b")
        .eq_mp(pure_imp_thm)
        .expect("lift_imp_to_hol: eq_mp")
}

/// Convert `Γ ⊢ Trueprop (A ⟹ B)` (HOL implication under one
/// Trueprop) into `Γ ⊢ Trueprop A ⟹ Trueprop B` (Pure meta-imp
/// over Trueprop atoms). Uses [`Thm::imp_reflection`] in reverse
/// via `sym`.
pub fn lower_imp_from_hol(hol_imp_thm: Thm, a: Term, b: Term) -> Thm {
    Thm::imp_reflection()
        .all_elim(a)
        .expect("lower_imp_from_hol: all_elim a")
        .all_elim(b)
        .expect("lower_imp_from_hol: all_elim b")
        .sym()
        .expect("lower_imp_from_hol: sym")
        .eq_mp(hol_imp_thm)
        .expect("lower_imp_from_hol: eq_mp")
}
