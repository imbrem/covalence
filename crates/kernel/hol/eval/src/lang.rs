//! [`CoreEval`] — the **eval tier**: the language extending
//! [`CoreLang`](covalence_core::seam::CoreLang) with the computation-backed
//! certificate and toHOL rules hosted in this crate.
//!
//! ## The tiered-trust declaration
//!
//! Trust is tiered *by declaration* (decision D1/D2 in
//! `notes/vibes/handoff/defs-out-of-core.md`):
//!
//! - `Thm<CoreLang>` — the **pure-HOL tier**: only the sound HOL inference
//!   rules in `covalence-core` (no computation TCB beyond the base
//!   `Builtins` canon the core seam already opens).
//! - [`EvalThm`]` = Thm<CoreEval>` — the **eval tier**: everything the pure
//!   tier admits, plus the per-family computation certificates and the toHOL
//!   reification rules in [`crate::rules`].
//!
//! Because [`CoreEval::admits`] delegates inherited rules to
//! [`core_admits`](covalence_core::seam::core_admits), the HOL rule
//! constructors mint DIRECTLY at the eval tier — a driver sets its working
//! tier once and everything infers; `Thm<CoreLang>` stays available for
//! pure-tier unit tests, lifting low→high via
//! [`Thm::lift`](covalence_core::Thm::lift).
//!
//! ## Soundness rests on `admits()` alone
//!
//! Implementing [`HolTier`] confers no proving power (see `covalence-core`'s
//! `thm::lang`); what makes `CoreEval` a *sound* tier is that every rule it
//! admits — core's catalogue plus [`crate::rules::eval_admits`]'s — derives
//! only true conclusions on every input. The eval additions' soundness
//! arguments live on each rule (`Soundness:` docstrings in `crate::rules`);
//! their per-rule trust is exactly what "this crate stopped being zero-TCB"
//! means. The static [`EVAL_MANIFEST`](crate::rules::EVAL_MANIFEST) (golden:
//! `docs/deps/eval-manifest.txt`) pins the additions; its parent embeds
//! [`CORE_MANIFEST`](covalence_core::seam::CORE_MANIFEST), so the whole
//! `tree(CoreEval)` is readable from one static.

use std::any::TypeId;

use covalence_core::seam::{HolTier, core_admits};
use covalence_pure::{Language, Manifest};

/// The eval-tier language: a stateless [`Copy`] ZST admitting core's HOL rule
/// catalogue (inherited, delegated to `core_admits`) **plus** the
/// computation-backed rules in [`crate::rules`]. See the module docs for the
/// tier/trust story.
#[derive(Clone, Copy, Debug, Default)]
pub struct CoreEval;

/// The eval-tier kernel certificate: `Thm` at [`CoreEval`]. The working tier
/// of `covalence-init` and the reduction drivers in this crate.
pub type EvalThm = covalence_core::Thm<CoreEval>;

/// The eval-tier `new_type_definition` package: `TypeDef` at [`CoreEval`].
pub type EvalTypeDef = covalence_core::TypeDef<CoreEval>;

impl Language for CoreEval {
    /// Direct rules: the eval additions ([`crate::rules::eval_admits`]).
    /// Inherited rules: delegated to [`core_admits`] — so the HOL rules mint
    /// directly at this tier (the base `Builtins` canon ops stay
    /// apply-in-home + lift, exactly as under `CoreLang`).
    fn admits(&self, rule: TypeId) -> bool {
        crate::rules::eval_admits(rule) || core_admits(rule)
    }
    /// Direct parent: [`CoreLang`](covalence_core::seam::CoreLang) (mirrored
    /// by the parent entry in [`crate::rules::EVAL_MANIFEST`]). Transitive
    /// ancestor [`covalence_pure_eval::Builtins`] is also accepted, so
    /// canon-minted base facts lift here in one hop.
    fn extends(&self, parent: TypeId) -> bool {
        parent == TypeId::of::<covalence_core::seam::CoreLang>()
            || parent == TypeId::of::<covalence_pure_eval::Builtins>()
    }
    fn union(self, _other: Self) -> Option<Self> {
        Some(self)
    }
    const MANIFEST: Option<&'static Manifest> = Some(&crate::rules::EVAL_MANIFEST);
}

impl HolTier for CoreEval {}
