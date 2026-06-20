//! The `smt` proof tactic — discharge the current `.cov` goal via an
//! Alethe refutation, checked through the kernel.
//!
//! [`smt_tactic`] builds an [`Arc<dyn Tactic>`](covalence_hol::script::Tactic)
//! from an [`SmtDischarger`]. A `.cov` script wires it in with the public FFI
//! seam:
//!
//! ```text
//! (#register-ffi-tactic smt)
//! (#thm g (#concl  …) (#by (smt)))
//! ```
//!
//! The host hands the closure through `script::run`'s `tactics` argument
//! (`|name| (name == "smt").then(|| smt_tactic(discharger.clone()))`). When
//! the goal is reached, the tactic reads it, runs [`SmtDischarger::discharge`]
//! (cached proof first, else the injected solver), and returns the kernel
//! theorem `⊢ goal`. Nothing is trusted — the Alethe proof is re-derived.

use std::sync::Arc;

use covalence_hol::script::{Interp, ScriptError, Tactic};
use covalence_sexp::SExpr;

use crate::discharge::SmtDischarger;

/// Build the `smt` tactic from a discharger.
///
/// The returned [`Tactic`] ignores its S-expression arguments (the call is
/// just `(smt)`), closes the focused goal, and must be the last step in its
/// `#by` block.
pub fn smt_tactic(discharger: Arc<SmtDischarger>) -> Arc<dyn Tactic> {
    Arc::new(
        move |s: &[SExpr], rest: &[SExpr], it: &mut Interp| -> Result<_, ScriptError> {
            if s.len() != 1 {
                return Err(ScriptError::Syntax(format!(
                    "smt: expected `(smt)` with no arguments, got {} elements",
                    s.len()
                )));
            }
            if !rest.is_empty() {
                return Err(ScriptError::Syntax(format!(
                    "smt: closes the goal, but {} more tactic(s) follow",
                    rest.len()
                )));
            }
            let goal = it.goal().clone();
            discharger
                .discharge(&goal)
                .map_err(|e| ScriptError::Syntax(format!("smt: {e}")))
        },
    )
}
