//! The egglog ingestion driver — kernel-agnostic.
//!
//! Walks a [`ProofStore`] from a root [`ProofId`] in dependency-first order,
//! calling into any [`EgglogBridge`]. The driver owns the `ProofId → Thm`
//! map; the bridge never resolves a [`ProofId`] itself — premises arrive
//! pre-resolved as `Self::Thm` handles.

use std::collections::HashMap;

use crate::bridge::EgglogBridge;
use crate::error::BridgeError;
use crate::proof::{
    Justification, Proof, ProofId, ProofStore, TermDag, topological_order,
};

/// Drive a bridge through the proof DAG rooted at `root`.
///
/// Returns the [`Thm`](EgglogBridge::Thm) for the root proof.
pub fn ingest_proof_store<B: EgglogBridge>(
    bridge: &mut B,
    store: &ProofStore,
    dag: &TermDag,
    root: ProofId,
) -> Result<B::Thm, BridgeError> {
    let mut thms: HashMap<ProofId, B::Thm> = HashMap::new();

    for id in topological_order(store, root) {
        let proof = store
            .get(id)
            .ok_or(BridgeError::UndefinedProof(id.0))?;
        let thm = dispatch(bridge, proof, &thms, dag)?;
        thms.insert(id, thm);
    }

    thms.get(&root)
        .cloned()
        .ok_or(BridgeError::UndefinedProof(root.0))
}

fn dispatch<B: EgglogBridge>(
    bridge: &mut B,
    proof: &Proof,
    thms: &HashMap<ProofId, B::Thm>,
    dag: &TermDag,
) -> Result<B::Thm, BridgeError> {
    let prop = &proof.proposition;
    match &proof.justification {
        Justification::Fiat => bridge.fiat(prop, dag),
        Justification::Rule {
            name,
            premise_proofs,
            substitution,
        } => {
            let prem = resolve_ids(thms, premise_proofs)?;
            bridge.rule(name, prop, &prem, substitution, dag)
        }
        Justification::MergeFn {
            function,
            old_proof,
            new_proof,
        } => {
            let old = resolve_one(thms, *old_proof)?;
            let new = resolve_one(thms, *new_proof)?;
            bridge.merge_fn(function, prop, old, new, dag)
        }
        Justification::Trans(a, b) => {
            let ab = resolve_one(thms, *a)?;
            let bc = resolve_one(thms, *b)?;
            bridge.trans(prop, ab, bc, dag)
        }
        Justification::Sym(a) => {
            let ab = resolve_one(thms, *a)?;
            bridge.sym(prop, ab, dag)
        }
        Justification::Congr {
            proof: proof_id,
            child_index,
            child_proof,
        } => {
            let proof_thm = resolve_one(thms, *proof_id)?;
            let child_thm = resolve_one(thms, *child_proof)?;
            bridge.congr(prop, proof_thm, *child_index, child_thm, dag)
        }
    }
}

fn resolve_one<T: Clone>(thms: &HashMap<ProofId, T>, id: ProofId) -> Result<T, BridgeError> {
    thms.get(&id)
        .cloned()
        .ok_or(BridgeError::UndefinedProof(id.0))
}

fn resolve_ids<T: Clone>(
    thms: &HashMap<ProofId, T>,
    ids: &[ProofId],
) -> Result<Vec<T>, BridgeError> {
    ids.iter().map(|id| resolve_one(thms, *id)).collect()
}
