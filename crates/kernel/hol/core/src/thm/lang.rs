//! The `covalence-pure` mint gate for [`Thm`](super::Thm).
//!
//! Every proven HOL sequent `Γ ⊢ φ` is carried as the SINGLE structured pure
//! proposition
//!
//! ```text
//! CoreProp = App<IsThm, (Val<Ctx>, Val<Term>)>
//! ```
//!
//! minted through the fine-grained rule catalogue in [`super::rules`] in the
//! crate-private language [`CoreLang`]. `Ctx`/`Term` enter as [`Val`] leaves (O(1)
//! `Arc`-backed wraps — no deep clone, no re-inference), so `App<IsThm, (Val<Ctx>,
//! Val<Term>)>` is an `Expr<Ty = bool>` (the tuple sorts at `(Ctx, Term) =
//! IsThm::In`), satisfying the [`Rule::Concl`] / `Thm<L, P>` bound. It is a
//! STRUCTURED proposition (an [`Op`] over `Val` leaves), not an opaque blob — which
//! keeps the future native-HOL / `NatToHol` embedding seam open (see `SKELETONS.md`).
//!
//! ## Soundness rests on `admits()` ALONE
//!
//! [`CoreLang`] admits exactly the ~43 sound `Rule<CoreLang>` ZSTs in
//! [`super::rules`], one per HOL inference step. Each rule's `decide` takes its
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
//! - [`super::rules::core_admits`] and [`super::rules::CORE_MANIFEST`] are emitted
//!   from ONE source list by the `core_rules!` macro, so they cannot drift.
//!
//! The inner `pure::Thm` field on [`Thm`](super::Thm) is now **hygiene-only**: it
//! keeps `pure::Thm`/`CoreLang` out of the public signature and preserves
//! `Arc`-identity, but is no longer load-bearing for soundness. What still remains
//! trusted (unchanged, documented seams): the `builtins` evaluator inside
//! `reduce_prim`/`unfold_term_spec`, and the observer parametric-ε model.

use std::any::TypeId;

use covalence_pure::{App, Language, Manifest, Op, Val};

use crate::ctx::Ctx;
use crate::term::Term;

/// The kernel judgement operator: `IsThm(Γ, φ) : bool` — "the sequent `Γ ⊢ φ` is
/// a theorem". A ZST; writing it is inert. Only the admitted rules in
/// [`super::rules`] (via the [`covalence_pure::apply`] gate) ever conclude an
/// `IsThm`-headed proposition.
#[derive(Clone, Copy, Debug)]
pub(crate) struct IsThm;

impl Op for IsThm {
    type In = (Ctx, Term);
    type Out = bool;
}

/// The structured proposition carried by every [`Thm`](super::Thm): the sequent
/// `(hyps, concl)` under the `IsThm` judgement.
pub(crate) type CoreProp = App<IsThm, (Val<Ctx>, Val<Term>)>;

/// The core kernel's language: a stateless [`Copy`] ZST admitting EXACTLY the sound
/// rule catalogue in [`super::rules`]. Hypotheses live INSIDE the proposition (the
/// `Val<Ctx>` operand), not in the language value, so `union`/`extends`/`lift` are
/// never exercised by core.
#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct CoreLang;

impl Language for CoreLang {
    fn admits(&self, rule: TypeId) -> bool {
        super::rules::core_admits(rule)
    }
    fn extends(&self, _parent: TypeId) -> bool {
        false
    }
    fn union(self, _other: Self) -> Option<Self> {
        Some(self)
    }
    const MANIFEST: Option<&'static Manifest> = Some(&super::rules::CORE_MANIFEST);
}
