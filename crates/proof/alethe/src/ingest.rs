//! The Alethe ingestion driver — kernel-agnostic.
//!
//! Walks an SMT-LIB problem and an Alethe proof, calling into any
//! [`AletheBridge`]. The driver owns the step-id → `Thm` map; the bridge
//! never sees raw step names for premises/discharge — only resolved theorem
//! handles.

use std::collections::HashMap;

use covalence_smt::{AletheCommand, AletheProof, SmtProblem};
use covalence_types::Decision;

use crate::bridge::AletheBridge;
use crate::error::BridgeError;

/// Drive a bridge through an SMT-LIB problem followed by its Alethe proof.
///
/// Returns the bridge's final [`Decision`].
pub fn ingest_alethe<B: AletheBridge>(
    bridge: &mut B,
    problem: &SmtProblem,
    proof: &AletheProof,
) -> Result<Decision, BridgeError> {
    ingest_problem(bridge, problem)?;
    ingest_proof(bridge, proof)?;
    Ok(bridge.decision())
}

/// Ingest just the problem portion (sorts, funs, assertions).
pub fn ingest_problem<B: AletheBridge>(
    bridge: &mut B,
    problem: &SmtProblem,
) -> Result<(), BridgeError> {
    if let Some(logic) = problem.logic() {
        bridge.set_logic(logic)?;
    }
    for sort in problem.sorts() {
        bridge.declare_sort(&sort.name, sort.arity)?;
    }
    for fun in problem.funs() {
        bridge.declare_fun(&fun.name, &fun.params, &fun.sort)?;
    }
    for assertion in problem.assertions() {
        bridge.assert(assertion)?;
    }
    Ok(())
}

/// Ingest just the proof portion, threading the step-id → Thm map.
pub fn ingest_proof<B: AletheBridge>(
    bridge: &mut B,
    proof: &AletheProof,
) -> Result<(), BridgeError> {
    let mut steps: HashMap<String, B::Thm> = HashMap::new();

    for cmd in proof.commands() {
        match cmd {
            AletheCommand::Assume { id, term } => {
                let thm = bridge.assume(id, term)?;
                steps.insert(id.clone(), thm);
            }
            AletheCommand::Step {
                id,
                clause,
                rule,
                premises,
                args,
                discharge,
            } => {
                let prem = resolve_ids(&steps, premises)?;
                let disc = resolve_ids(&steps, discharge)?;
                let thm = bridge.step(id, clause, rule, &prem, args, &disc)?;
                steps.insert(id.clone(), thm);
            }
            AletheCommand::Anchor { step, args } => {
                bridge.anchor(step, args)?;
            }
            AletheCommand::DefineFun {
                name,
                params,
                sort,
                body,
            } => {
                bridge.define_fun(name, params, sort, body)?;
            }
        }
    }
    Ok(())
}

fn resolve_ids<T: Clone>(
    steps: &HashMap<String, T>,
    ids: &[String],
) -> Result<Vec<T>, BridgeError> {
    ids.iter()
        .map(|id| {
            steps
                .get(id)
                .cloned()
                .ok_or_else(|| BridgeError::UndefinedStep(id.clone()))
        })
        .collect()
}
