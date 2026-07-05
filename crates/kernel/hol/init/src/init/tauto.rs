//! The foundational propositional layer: `⊢ T` ([`truth`]) and the `tauto`
//! FFI tactic, loaded from `tauto.cov`.
//!
//! This module exists to **break a load-time cycle**. The propositional
//! deciders in [`crate::init::logic`] — [`tauto`](crate::init::logic::tauto),
//! [`prop_eq`](crate::init::logic::prop_eq),
//! [`simp`](crate::init::logic::simp) — all bottom out in `⊢ T`
//! (`eqt_intro` / `eqt_elim` discharge against it). If `truth` were defined in
//! `logic.cov` *and* `logic.cov` used the `prop-eq` rule (whose Rust impl calls
//! `truth()`), forcing `logic.cov`'s lazy static would re-enter itself.
//!
//! So `truth` (and the `tauto` FFI registration) live here, in a theory that
//! depends only on `core`. `logic.cov` `#import`s this and re-exports `truth` /
//! `tauto`, and is then free to use `prop-eq` for its own lemmas
//! (`and.assoc`, …). Everything the deciders need is **exported** from
//! `tauto.cov` for that re-export.

use covalence_hol_eval::EvalThm as Thm;

/// The `tauto` **inference** — a trivial-tautology decider usable in **both**
/// proof modes: as a `#by` tactic `(tauto)` closing the current goal, and as a
/// `#proof` rule `(tauto TERM)` proving `TERM`. Registered into the foundational
/// `tauto` env via `(#register-ffi-tactic tauto)`, then re-exported through
/// `logic`, so downstream theories that `(#open logic)` get both facets.
pub struct Tauto;

#[async_trait::async_trait]
impl crate::script::Tactic for Tauto {
    async fn apply(
        &self,
        s: &[covalence_sexp::SExpr],
        rest: &[covalence_sexp::SExpr],
        it: &mut crate::script::Interp,
    ) -> core::result::Result<Thm, crate::script::ScriptError> {
        if s.len() != 1 || !rest.is_empty() {
            return Err(crate::script::ScriptError::Syntax(
                "tauto: expected `(tauto)` as the closing tactic".into(),
            ));
        }
        Ok(crate::init::logic::tauto(it.goal())?)
    }

    async fn rule(
        &self,
        a: &[covalence_sexp::SExpr],
        c: &mut crate::script::CheckCtx<'_>,
    ) -> core::result::Result<Thm, crate::script::ScriptError> {
        if a.len() != 1 {
            return Err(crate::script::ScriptError::Syntax(
                "rule `tauto` expects 1 argument".into(),
            ));
        }
        Ok(crate::init::logic::tauto(&c.term(&a[0])?)?)
    }
}

crate::cov_theory! {
    /// The foundational `truth` / `tauto` layer loaded from `tauto.cov`.
    pub mod cov from "tauto.cov" {
        import "core" = crate::script::Env::core();
        ffi-tactic "tauto" = crate::init::tauto::Tauto;
        "truth" => pub fn truth;
    }
}

pub use cov::truth;
