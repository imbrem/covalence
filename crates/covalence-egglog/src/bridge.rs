//! The stable `EgglogBridge` trait — the single boundary between egglog
//! proof-DAG ingestion and any backend (HOL kernel, null kernel, future
//! redesigns).
//!
//! The trait is intentionally **egglog-shaped**, not kernel-shaped: one
//! method per [`Justification`](crate::proof::Justification) variant plus a
//! small set of program-declaration verbs. Premise [`ProofId`]s are
//! pre-resolved by the driver into `Self::Thm` values; the bridge never sees
//! raw ids.
//!
//! Stage 0: only [`EgglogBridge::fiat`] is expected to succeed in concrete
//! impls. Every other justification variant has a default returning
//! [`BridgeError::NotImplemented`] so a partial impl still compiles and
//! produces loud, structured failure tagged with the justification name.

use std::collections::HashMap;

use covalence_types::Decision;

use crate::error::BridgeError;
use crate::proof::{ProofId, ProofStore, Proposition, TermDag, TermId};

/// High-level egglog ingestion API.
///
/// Implementations may stub any justification by returning
/// [`BridgeError::NotImplemented("<variant>")`]. The driver
/// ([`crate::ingest::ingest_proof_store`]) calls these methods once per
/// proof node, in dependency-first order.
pub trait EgglogBridge {
    /// Backend representation of a proven equality. `Clone` (not `Copy`)
    /// because the kernel's `Thm` is `Arc`-backed.
    type Thm: Clone + std::fmt::Debug;

    // -----------------------------------------------------------------
    // Program ingestion
    // -----------------------------------------------------------------

    /// `(sort Name)` — declare a user eqsort.
    fn declare_sort(&mut self, name: &str) -> Result<(), BridgeError>;

    /// `(constructor name (P₁ … Pₙ) R)` — declare a constructor / function
    /// symbol with parameter sorts `params` and result sort `result_sort`.
    ///
    /// `relation` and `function` desugar to this in the common case where
    /// only the signature is needed (no merge expression). Stage 0 ignores
    /// any `:merge` / `:cost` annotations.
    fn declare_constructor(
        &mut self,
        name: &str,
        params: &[&str],
        result_sort: &str,
    ) -> Result<(), BridgeError>;

    // -----------------------------------------------------------------
    // Pre-walk setup
    // -----------------------------------------------------------------

    /// Called once by the driver before the topological walk starts.
    ///
    /// Backends that need state set up *before* any
    /// [`Justification`](crate::proof::Justification) is dispatched (e.g.
    /// pushing every [`Justification::Fiat`](crate::proof::Justification::Fiat)
    /// equality onto a shared context so later `Trans` / `Sym` steps share
    /// the same proof environment) override this method.
    ///
    /// The default is a no-op.
    fn pre_walk(
        &mut self,
        store: &ProofStore,
        dag: &TermDag,
        root: ProofId,
    ) -> Result<(), BridgeError> {
        let _ = (store, dag, root);
        Ok(())
    }

    // -----------------------------------------------------------------
    // Justification handlers (one per `Justification` variant)
    // -----------------------------------------------------------------

    /// [`Justification::Fiat`](crate::proof::Justification::Fiat) — a
    /// top-level fact or a primitive reflexive equality.
    fn fiat(&mut self, prop: &Proposition, dag: &TermDag) -> Result<Self::Thm, BridgeError>;

    /// [`Justification::Rule`](crate::proof::Justification::Rule) — a
    /// user-declared rule fired under `substitution` with the given premise
    /// theorems.
    fn rule(
        &mut self,
        name: &str,
        prop: &Proposition,
        premise_thms: &[Self::Thm],
        substitution: &HashMap<String, TermId>,
        dag: &TermDag,
    ) -> Result<Self::Thm, BridgeError> {
        let _ = (prop, premise_thms, substitution, dag);
        Err(BridgeError::NotImplemented(format!("rule:{name}")))
    }

    /// [`Justification::MergeFn`](crate::proof::Justification::MergeFn) — a
    /// merge function on `function` reconciling an old and new row value.
    fn merge_fn(
        &mut self,
        function: &str,
        prop: &Proposition,
        old_thm: Self::Thm,
        new_thm: Self::Thm,
        dag: &TermDag,
    ) -> Result<Self::Thm, BridgeError> {
        let _ = (prop, old_thm, new_thm, dag);
        Err(BridgeError::NotImplemented(format!("merge_fn:{function}")))
    }

    /// [`Justification::Trans`](crate::proof::Justification::Trans) —
    /// `a = b ∧ b = c ⊢ a = c`.
    fn trans(
        &mut self,
        prop: &Proposition,
        ab: Self::Thm,
        bc: Self::Thm,
        dag: &TermDag,
    ) -> Result<Self::Thm, BridgeError> {
        let _ = (prop, ab, bc, dag);
        Err(BridgeError::NotImplemented("trans".into()))
    }

    /// [`Justification::Sym`](crate::proof::Justification::Sym) — `a = b ⊢ b = a`.
    fn sym(
        &mut self,
        prop: &Proposition,
        ab: Self::Thm,
        dag: &TermDag,
    ) -> Result<Self::Thm, BridgeError> {
        let _ = (prop, ab, dag);
        Err(BridgeError::NotImplemented("sym".into()))
    }

    /// [`Justification::Congr`](crate::proof::Justification::Congr) —
    /// extends `proof_thm` (concluding `t₁ = f(…, c_i, …)`) at child position
    /// `child_index` with `child_thm` (concluding `c_i = c'`) to prove
    /// `t₁ = f(…, c', …)`.
    fn congr(
        &mut self,
        prop: &Proposition,
        proof_thm: Self::Thm,
        child_index: usize,
        child_thm: Self::Thm,
        dag: &TermDag,
    ) -> Result<Self::Thm, BridgeError> {
        let _ = (prop, proof_thm, child_index, child_thm, dag);
        Err(BridgeError::NotImplemented("congr".into()))
    }

    // -----------------------------------------------------------------
    // Result
    // -----------------------------------------------------------------

    /// Final decision after the driver has finished. Egglog by itself
    /// decides equalities rather than sat/unsat, so this is `Unknown` by
    /// default and implementations may override if they pair the bridge
    /// with an external query semantics.
    fn decision(&self) -> Decision {
        Decision::Unknown
    }
}
