//! External-egglog driver (feature `external-egglog`).
//!
//! Bridges upstream egglog (`egglog = "2"`) into our bridge surface. The
//! public API of this module is deliberately upstream-type-free: callers
//! receive [`crate::TermDag`] / [`crate::ProofStore`] handles, never
//! `egglog::*` types. That keeps the dep tree from leaking into the rest
//! of the crate and lets us pin the API surface independently of
//! upstream's release cadence.
//!
//! Two responsibilities, mirroring the integration plan:
//!
//!   1. **Drive upstream egglog** to saturate a user program and
//!      materialise a proof DAG for a `(prove …)` target.
//!   2. **Convert** the resulting upstream proof DAG into our local
//!      [`crate::ProofStore`] mirror so the rest of the crate (the bridge
//!      trait, the driver, every catalogue entry) stays oblivious of
//!      upstream's types.
//!
//! **Scope note.** This module exists to pin down the *API surface* — the
//! function signatures, the module split, and the trust boundary with
//! upstream. The bodies are deliberately stubbed where the upstream
//! entry point is uncertain (egglog 2.0.0 doesn't yet publicise its
//! `proof` module — that lands in the next release) or where the kernel
//! rewrite will force a refactor anyway. The high-level public API
//! ([`run_program`], [`ingest_via_oracle`]) is what the rest of the
//! crate commits to.

use crate::bridge::EgglogBridge;
use crate::error::BridgeError;
use crate::ingest::ingest_proof_store;
use crate::proof::{ProofId, ProofStore, TermDag};

/// Run an egglog `source` program with upstream egglog, materialise the
/// proof DAG for its `(prove …)` target, convert it to our local types,
/// and ingest the result into `bridge` — producing the corresponding
/// [`Thm`](EgglogBridge::Thm) in our kernel.
///
/// This is the user-facing one-shot composing [`run_program`] and
/// [`ingest_proof_store`].
///
/// Caveat: the caller is currently responsible for declaring sorts and
/// constructors on `bridge` ahead of time — the upstream proof DAG
/// references terms by id, and we have no syntactic-declaration
/// extractor yet. The kernel-rewrite work will likely move declaration
/// synthesis into this driver too; see the matching open question in
/// the integration plan.
pub fn ingest_via_oracle<B: EgglogBridge>(
    bridge: &mut B,
    source: &str,
) -> Result<B::Thm, BridgeError> {
    let (dag, store, root) = run_program(source)?;
    ingest_proof_store(bridge, &store, &dag, root)
}

/// Parse `source`, run it through a fresh upstream `EGraph`, extract the
/// proof of its (single) `(prove …)` target, and convert the result to
/// our local types.
///
/// Returned [`TermDag`] / [`ProofStore`] are *ours* — upstream's types
/// never appear in this function's signature. Conversion happens inside.
///
/// Errors loudly if:
/// - the source is malformed at upstream's parser;
/// - the program falls outside upstream's proof-encodable fragment;
/// - the program has no `(prove …)` or more than one;
/// - the conversion hits a term shape we don't yet model
///   (primitives, containers).
pub fn run_program(source: &str) -> Result<(TermDag, ProofStore, ProofId), BridgeError> {
    let _ = source;
    todo!(
        "TODO: drive upstream `egglog::EGraph` — \
         construct, `parse_and_run_program(None, source)`, locate the \
         `(prove …)` step's proof, then walk it via the (currently \
         private) proof module. Upstream's `proof` module ships public \
         in the next release; until then we pin the signature so the \
         rest of the crate compiles against the eventual surface."
    )
}

/// Pre-flight check: does the program in `path` belong to the fragment
/// upstream egglog can produce a proof DAG for? Wraps
/// [`egglog::file_supports_proofs`].
///
/// Returns `Ok(())` for proof-supportable programs; otherwise
/// [`BridgeError::Malformed`].
///
/// File-shaped on purpose — egglog 2.0.0's public surface only checks
/// files, not source strings. A future release is expected to expose a
/// program/commands variant; when it ships we'll add a sibling
/// `file_supports_proofs_source(&str)` here and call it from
/// [`run_program`] before invoking the upstream EGraph.
pub fn file_supports_proofs(path: &std::path::Path) -> Result<(), BridgeError> {
    if egglog::file_supports_proofs(path) {
        Ok(())
    } else {
        Err(BridgeError::Malformed(format!(
            "program at `{}` is outside upstream's proof-encodable fragment",
            path.display()
        )))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Confirms the dep links and our surface uses only our types — i.e.
    /// `run_program`'s return is `(TermDag, ProofStore, ProofId)` with no
    /// upstream leakage.
    #[test]
    fn surface_uses_only_local_types() {
        fn _accepts_local(_d: &TermDag, _s: &ProofStore, _r: ProofId) {}
    }

    /// Confirms the upstream entry point our public API currently calls
    /// (`egglog::file_supports_proofs`) links and runs. We hand it a
    /// non-existent path — we don't care about the answer, just that the
    /// call doesn't panic.
    #[test]
    fn file_supports_proofs_runs() {
        let _ = file_supports_proofs(std::path::Path::new("/nonexistent"));
    }

    /// `run_program` is stubbed; surface tests that drive it should pass
    /// with `#[ignore]` until the body lands.
    #[test]
    #[should_panic(expected = "TODO")]
    fn run_program_is_stubbed() {
        let _ = run_program("(sort U)");
    }
}
