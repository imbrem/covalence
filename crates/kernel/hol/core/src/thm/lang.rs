//! The `covalence-pure` mint gate for [`Thm`](super::Thm).
//!
//! Every proven HOL sequent `Γ ⊢ φ` is carried as the SINGLE structured pure
//! proposition
//!
//! ```text
//! CoreProp = App<IsThm, (Val<Ctx>, Val<Term>)>
//! ```
//!
//! minted through the fine-grained rule catalogue in `super::rules` in the
//! language [`CoreLang`] (public via [`crate::seam`] since the toHOL slice —
//! the deliberate, one-module-to-audit widening of the core-on-pure seam).
//! `Ctx`/`Term` enter as [`Val`] leaves (O(1)
//! `Arc`-backed wraps — no deep clone, no re-inference), so `App<IsThm, (Val<Ctx>,
//! Val<Term>)>` is an `Expr<Ty = bool>` (the tuple sorts at `(Ctx, Term) =
//! IsThm::In`), satisfying the [`Rule::Concl`] / `Thm<L, P>` bound. It is a
//! STRUCTURED proposition (an [`Op`] over `Val` leaves), not an opaque blob — which
//! keeps the future native-HOL / `NatToHol` embedding seam open (see `SKELETONS.md`).
//!
//! ## Soundness rests on `admits()` ALONE
//!
//! [`CoreLang`] admits exactly the sound `Rule<CoreLang>` ZSTs in
//! `super::rules`, one per HOL inference step. Each rule's `decide` takes its
//! premises as unforgeable `pure::Thm`s and **derives** its conclusion (it never
//! accepts a caller-supplied conclusion), so every firing on any input yields a
//! true theorem. The obtainable set of `pure::Thm<CoreLang, IsThm(Γ,φ)>` therefore
//! contains only genuinely-derivable sequents — the admits-only milestone.
//!
//! Concretely:
//! - `pure::Thm` is unforgeable (private fields, `pub(crate)` `new`; the only mint
//!   for an `IsThm`-headed prop is [`covalence_pure::apply`] gated on an admitted
//!   rule's own `TypeId`).
//! - Novel downstream `impl Rule<CoreLang> for Evil` types are inert:
//!   `core_admits(TypeId::of::<Evil>())` is `false`, so `apply` returns
//!   `NotAdmitted` before `Evil::decide` runs.
//! - [`super::rules::core_admits`] and `super::rules::CORE_MANIFEST` are emitted
//!   from ONE source list by the `core_rules!` macro, so they cannot drift.
//!
//! The inner `pure::Thm` field on [`Thm`](super::Thm) is now **hygiene-only**: it
//! keeps `pure::Thm`/`CoreLang` out of the public signature and preserves
//! `Arc`-identity, but is no longer load-bearing for soundness. What still remains
//! trusted (unchanged, documented seams): the `builtins` evaluator inside
//! `reduce_prim`/`unfold_term_spec`.

use std::any::TypeId;

use covalence_pure::{App, Language, Manifest, Op, Val};

use crate::ctx::Ctx;
use crate::term::Term;

/// The kernel judgement operator: `IsThm(Γ, φ) : bool` — "the sequent `Γ ⊢ φ` is
/// a theorem". A ZST; writing it is inert. Only the admitted rules in
/// `super::rules` (via the [`covalence_pure::apply`] gate) ever conclude an
/// `IsThm`-headed proposition. `pub` (re-exported through [`crate::seam`]) so
/// untrusted drivers can state and transport `IsThm`-headed propositions —
/// writing the op proves nothing.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct IsThm;

impl Op for IsThm {
    type In = (Ctx, Term);
    type Out = bool;
}

/// The structured proposition carried by every [`Thm`](super::Thm): the sequent
/// `(hyps, concl)` under the `IsThm` judgement.
pub type CoreProp = App<IsThm, (Val<Ctx>, Val<Term>)>;

/// The core kernel's language: a stateless [`Copy`] ZST admitting EXACTLY the sound
/// rule catalogue in `super::rules`. Hypotheses live INSIDE the proposition (the
/// `Val<Ctx>` operand), not in the language value, so `union` is trivial.
///
/// Since the toHOL slice, `CoreLang` **extends
/// [`covalence_pure_eval::Builtins`]** — the deliberate opening of the
/// core-on-pure seam: canon-minted `Thm<Builtins, Eqn<…>>` facts (the
/// enumerable native-computation TCB) lift into `CoreLang` via
/// [`covalence_pure::Thm::lift`], and the certificate rules in
/// `super::rules` may call the same `CanonRule` evals natively inside
/// `decide`. `pub` (re-exported through [`crate::seam`]) so untrusted drivers
/// can apply the admitted toHOL rules; publishing the language value mints
/// nothing — every mint stays gated on `admits`.
#[derive(Clone, Copy, Debug, Default)]
pub struct CoreLang;

impl Language for CoreLang {
    fn admits(&self, rule: TypeId) -> bool {
        super::rules::core_admits(rule)
    }
    /// `CoreLang` directly extends exactly [`covalence_pure_eval::Builtins`]
    /// (`tree(Builtins) ⊆ tree(CoreLang)`) — mirrored by the parent entry in
    /// `super::rules::CORE_MANIFEST`, so the manifest stays canonical.
    fn extends(&self, parent: TypeId) -> bool {
        parent == TypeId::of::<covalence_pure_eval::Builtins>()
    }
    fn union(self, _other: Self) -> Option<Self> {
        Some(self)
    }
    const MANIFEST: Option<&'static Manifest> = Some(&super::rules::CORE_MANIFEST);
}
