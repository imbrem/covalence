use covalence_computation::theory::{Realization, Theory};
use covalence_core::{Result, Term, Type};
use covalence_hol_eval::{EvalThm as Thm, defs::list, mk_bool};
use covalence_kernel_data::BitsSyntax;

use super::{
    NativeTheoryError, NativeTransitionBundle, SuppliedLaw, ValidatedTransitionFacts,
    validate_transition_bundle,
};
use crate::init::inductive::hol::{Hol, NativeHol};

pub(crate) fn bit_list(bits: impl IntoIterator<Item = bool>) -> Result<Term> {
    NativeHol.bits_literal(&bits.into_iter().collect::<Vec<_>>())
}

/// Realize one concrete, serialized configuration and its next transition.
///
/// This deliberately describes only the supplied configuration. It is the
/// small checked base case from which a recursive syntax datatype and general
/// reduction relation can later be proved.
pub(crate) fn bounded_realization(
    initial: Term,
    next: Option<Term>,
) -> std::result::Result<Realization<Theory<NativeHol>, ValidatedTransitionFacts>, NativeTheoryError>
{
    let hol = NativeHol;
    let bits = list(Type::bool());
    let machine = initial.clone();

    let initialize = hol.lam(
        "__computation_machine",
        bits.clone(),
        hol.lam("__computation_input", bits.clone(), initial.clone()),
    );

    let before = hol.var("__computation_before", bits.clone());
    let after = hol.var("__computation_after", bits.clone());
    let step_body = match &next {
        Some(next) => hol.and(
            hol.eq(before.clone(), initial.clone())?,
            hol.eq(after.clone(), next.clone())?,
        )?,
        None => mk_bool(false),
    };
    let step = hol.lam(
        "__computation_machine",
        bits.clone(),
        hol.lam(
            "__computation_before",
            bits.clone(),
            hol.lam("__computation_after", bits.clone(), step_body),
        ),
    );

    let state = hol.var("__computation_state", bits.clone());
    let output = hol.lam(
        "__computation_machine",
        bits.clone(),
        hol.lam("__computation_state", bits.clone(), state.clone()),
    );
    let halts_body = if next.is_none() {
        hol.eq(state, initial.clone())?
    } else {
        mk_bool(false)
    };
    let halts = hol.lam(
        "__computation_machine",
        bits.clone(),
        hol.lam("__computation_state", bits.clone(), halts_body),
    );

    // The laws currently assert closedness of this concrete vocabulary. Their
    // propositions are kernel equations, and their proofs are kernel REFL;
    // no semantic reduction theorem is fabricated here.
    let closed = hol.eq(machine.clone(), machine.clone())?;
    let supplied = || -> Result<SuppliedLaw> {
        Ok(SuppliedLaw {
            proposition: closed.clone(),
            theorem: Thm::refl(machine.clone())?,
        })
    };
    let initialization_closed = supplied()?;
    let step_closed = supplied()?;
    let halting_output = supplied()?;
    let theory = Theory {
        machine_type: bits.clone(),
        input_type: bits.clone(),
        state_type: bits.clone(),
        output_type: bits,
        machine,
        initialize,
        step,
        output,
        halts,
    };
    let bundle = NativeTransitionBundle {
        theory,
        initialization_closed,
        step_closed,
        halting_output,
    };
    let (theory, facts) = validate_transition_bundle(bundle)?;
    Ok(Realization { theory, facts })
}
