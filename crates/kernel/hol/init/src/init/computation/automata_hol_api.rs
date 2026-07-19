//! Native bounded realization of the A0011 finite-automata theory.
//!
//! @covalence-api-impl {"api":"A0011","name":"BoundedDfaReplay","representation":"closed native HOL predicates for one DFA and one accepted word"}
//!
//! This module provides one complete theorem path. Host search returns a full
//! DFA trace as plain data. Replay recomputes the trace, validates the entire
//! closed HOL theory, and derives:
//!
//! ```text
//! ⊢ accepts encoded_machine encoded_word
//! ```
//!
//! The realization is intentionally bounded to that machine and word.
//! Universal `accepts iff reachable-final` laws remain a separate A0011
//! capability and are not inferred from this theorem.

use core::fmt;

use covalence_computation::{
    automata_api::{
        AutomataSearchWitness, FiniteAutomataReplay, FiniteAutomataTheory, RecognitionClaim,
    },
    finite::{Dfa, RunError},
    theory::TheoremArtifact,
};
use covalence_core::{Error, Term, Type};
use covalence_hol_eval::{
    defs::{cons, list, nil},
    mk_bool, mk_nat,
};
use covalence_types::Nat;

use super::automata::encode_dfa;
use crate::init::{
    ext::TermExt,
    inductive::hol::{Hol, NativeHol},
};

/// Complete deterministic run proposed by untrusted search.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DfaRunWitness {
    pub input: Vec<u64>,
    /// Initial state followed by one state per consumed symbol.
    pub states: Vec<usize>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DfaAcceptanceMetadata {
    pub input: Vec<u64>,
    pub states: Vec<usize>,
    pub transitions: usize,
}

pub type DfaAcceptanceCertificate = TheoremArtifact<NativeHol, DfaAcceptanceMetadata>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DfaReplayError {
    UnknownSymbol { input_offset: usize },
    NotAccepting,
    WrongClaim,
    WrongTransitionCount { advertised: u64, actual: usize },
    ForgedTrace,
    TheoryMismatch,
    TypeMismatch { field: &'static str },
    Kernel,
}

impl fmt::Display for DfaReplayError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}

impl std::error::Error for DfaReplayError {}

impl From<Error> for DfaReplayError {
    fn from(_: Error) -> Self {
        Self::Kernel
    }
}

/// Search for a complete accepting run. The returned value has no proof
/// authority until replayed.
pub fn search_dfa_acceptance(
    automaton: &Dfa<u64>,
    input: Vec<u64>,
) -> Result<AutomataSearchWitness<DfaRunWitness>, DfaReplayError> {
    let trace = automaton.run(&input).map_err(map_run_error)?;
    if !trace.accepted {
        return Err(DfaReplayError::NotAccepting);
    }
    Ok(AutomataSearchWitness {
        claim: RecognitionClaim::Accepts,
        transitions: input.len() as u64,
        candidate: DfaRunWitness {
            input,
            states: trace.states,
        },
    })
}

/// Closed native HOL realization for one accepted `(DFA, word)` pair.
pub fn bounded_dfa_theory(
    automaton: &Dfa<u64>,
    input: &[u64],
) -> Result<FiniteAutomataTheory<NativeHol>, DfaReplayError> {
    let trace = automaton.run(input).map_err(map_run_error)?;
    if !trace.accepted {
        return Err(DfaReplayError::NotAccepting);
    }

    let hol = NativeHol;
    let machine_type = list(Type::nat());
    let word_type = list(Type::nat());
    let configuration_type = list(Type::nat());
    let machine = encode_dfa(automaton);
    let word = nat_list_u64(input.iter().copied());
    let configurations = trace_configurations(input, &trace.states);

    let state_var = hol.var("__dfa_state", Type::nat());
    let word_var = hol.var("__dfa_word", word_type.clone());
    let configuration = hol.lam(
        "__dfa_state",
        Type::nat(),
        hol.lam(
            "__dfa_word",
            word_type.clone(),
            Term::app(Term::app(cons(Type::nat()), state_var), word_var),
        ),
    );

    let initial = ternary_predicate(
        "__dfa_machine",
        machine_type.clone(),
        "__dfa_word",
        word_type.clone(),
        "__dfa_configuration",
        configuration_type.clone(),
        |machine_var, word_var, configuration_var| {
            conjunction([
                machine_var.equals(machine.clone())?,
                word_var.equals(word.clone())?,
                configuration_var.equals(configurations[0].clone())?,
            ])
        },
    )?;

    let transition_edges: Vec<_> = configurations
        .windows(2)
        .map(|pair| (pair[0].clone(), pair[1].clone()))
        .collect();
    let transition = relation_predicate(
        "__dfa_transition",
        &machine,
        machine_type.clone(),
        configuration_type.clone(),
        &transition_edges,
    )?;

    let mut closure_edges = Vec::new();
    for start in 0..configurations.len() {
        for end in start..configurations.len() {
            closure_edges.push((configurations[start].clone(), configurations[end].clone()));
        }
    }
    let closure = relation_predicate(
        "__dfa_closure",
        &machine,
        machine_type.clone(),
        configuration_type.clone(),
        &closure_edges,
    )?;

    let reachable = ternary_predicate(
        "__dfa_reachable_machine",
        machine_type.clone(),
        "__dfa_reachable_word",
        word_type.clone(),
        "__dfa_reachable_configuration",
        configuration_type.clone(),
        |machine_var, word_var, configuration_var| {
            let choices = configurations
                .iter()
                .map(|candidate| configuration_var.clone().equals(candidate.clone()))
                .collect::<Result<Vec<_>, _>>()?;
            conjunction([
                machine_var.equals(machine.clone())?,
                word_var.equals(word.clone())?,
                disjunction(choices)?,
            ])
        },
    )?;

    let final_configuration = configurations
        .last()
        .expect("a DFA trace always includes its initial state")
        .clone();
    let accepting_configuration = binary_predicate(
        "__dfa_accepting_machine",
        machine_type.clone(),
        "__dfa_accepting_configuration",
        configuration_type.clone(),
        |machine_var, configuration_var| {
            conjunction([
                machine_var.equals(machine.clone())?,
                configuration_var.equals(final_configuration.clone())?,
            ])
        },
    )?;

    let accepts = binary_predicate(
        "__dfa_accepts_machine",
        machine_type.clone(),
        "__dfa_accepts_word",
        word_type.clone(),
        |machine_var, word_var| {
            conjunction([
                machine_var.equals(machine.clone())?,
                word_var.equals(word.clone())?,
            ])
        },
    )?;

    let theory = FiniteAutomataTheory {
        machine_type,
        symbol_type: Type::nat(),
        state_type: Type::nat(),
        word_type,
        configuration_type,
        machine,
        configuration,
        initial,
        transition,
        closure,
        reachable,
        accepting_configuration,
        accepts,
    };
    validate_theory(&theory)?;
    Ok(theory)
}

/// Replay backend for one validated plain-data DFA.
pub struct BoundedDfaReplay<'a> {
    pub automaton: &'a Dfa<u64>,
}

impl FiniteAutomataReplay<NativeHol, DfaRunWitness> for BoundedDfaReplay<'_> {
    type Certificate = DfaAcceptanceCertificate;
    type Error = DfaReplayError;

    fn replay(
        &self,
        logic: &NativeHol,
        theory: &FiniteAutomataTheory<NativeHol>,
        witness: &AutomataSearchWitness<DfaRunWitness>,
    ) -> Result<Self::Certificate, Self::Error> {
        if witness.claim != RecognitionClaim::Accepts {
            return Err(DfaReplayError::WrongClaim);
        }
        let expected = self
            .automaton
            .run(&witness.candidate.input)
            .map_err(map_run_error)?;
        if !expected.accepted {
            return Err(DfaReplayError::NotAccepting);
        }
        let transitions = witness.candidate.input.len();
        if witness.transitions != transitions as u64 {
            return Err(DfaReplayError::WrongTransitionCount {
                advertised: witness.transitions,
                actual: transitions,
            });
        }
        if witness.candidate.states != expected.states {
            return Err(DfaReplayError::ForgedTrace);
        }

        let expected_theory = bounded_dfa_theory(self.automaton, &witness.candidate.input)?;
        if !same_theory(theory, &expected_theory) {
            return Err(DfaReplayError::TheoryMismatch);
        }

        let word = nat_list_u64(witness.candidate.input.iter().copied());
        let proposition = logic.app(
            logic.app(theory.accepts.clone(), theory.machine.clone())?,
            word.clone(),
        )?;
        let normal_form =
            logic.and_intro(logic.refl(theory.machine.clone())?, logic.refl(word)?)?;
        let theorem = logic.eq_mp(logic.sym(logic.beta_nf(proposition)?)?, normal_form)?;
        Ok(TheoremArtifact {
            theorem,
            metadata: DfaAcceptanceMetadata {
                input: witness.candidate.input.clone(),
                states: expected.states,
                transitions,
            },
        })
    }
}

fn map_run_error(error: RunError) -> DfaReplayError {
    match error {
        RunError::UnknownSymbol { input_offset } => DfaReplayError::UnknownSymbol { input_offset },
    }
}

fn trace_configurations(input: &[u64], states: &[usize]) -> Vec<Term> {
    states
        .iter()
        .enumerate()
        .map(|(offset, state)| {
            let values = core::iter::once(*state as u64).chain(input[offset..].iter().copied());
            nat_list_u64(values)
        })
        .collect()
}

fn numeral(value: u64) -> Term {
    mk_nat(Nat::from(value))
}

fn nat_list_u64(values: impl IntoIterator<Item = u64>) -> Term {
    let mut values: Vec<_> = values.into_iter().collect();
    let mut result = nil(Type::nat());
    while let Some(value) = values.pop() {
        result = Term::app(Term::app(cons(Type::nat()), numeral(value)), result);
    }
    result
}

fn conjunction(terms: impl IntoIterator<Item = Term>) -> Result<Term, Error> {
    let mut terms: Vec<_> = terms.into_iter().collect();
    let Some(mut result) = terms.pop() else {
        return Ok(mk_bool(true));
    };
    while let Some(term) = terms.pop() {
        result = term.and(result)?;
    }
    Ok(result)
}

fn disjunction(mut terms: Vec<Term>) -> Result<Term, Error> {
    let Some(mut result) = terms.pop() else {
        return Ok(mk_bool(false));
    };
    while let Some(term) = terms.pop() {
        result = term.or(result)?;
    }
    Ok(result)
}

fn binary_predicate(
    left_name: &str,
    left_type: Type,
    right_name: &str,
    right_type: Type,
    body: impl FnOnce(Term, Term) -> Result<Term, Error>,
) -> Result<Term, Error> {
    let hol = NativeHol;
    let left = hol.var(left_name, left_type.clone());
    let right = hol.var(right_name, right_type.clone());
    Ok(hol.lam(
        left_name,
        left_type,
        hol.lam(right_name, right_type, body(left, right)?),
    ))
}

#[allow(clippy::too_many_arguments)]
fn ternary_predicate(
    first_name: &str,
    first_type: Type,
    second_name: &str,
    second_type: Type,
    third_name: &str,
    third_type: Type,
    body: impl FnOnce(Term, Term, Term) -> Result<Term, Error>,
) -> Result<Term, Error> {
    let hol = NativeHol;
    let first = hol.var(first_name, first_type.clone());
    let second = hol.var(second_name, second_type.clone());
    let third = hol.var(third_name, third_type.clone());
    Ok(hol.lam(
        first_name,
        first_type,
        hol.lam(
            second_name,
            second_type,
            hol.lam(third_name, third_type, body(first, second, third)?),
        ),
    ))
}

fn relation_predicate(
    prefix: &str,
    machine: &Term,
    machine_type: Type,
    configuration_type: Type,
    edges: &[(Term, Term)],
) -> Result<Term, Error> {
    ternary_predicate(
        &format!("{prefix}_machine"),
        machine_type,
        &format!("{prefix}_before"),
        configuration_type.clone(),
        &format!("{prefix}_after"),
        configuration_type,
        |machine_var, before, after| {
            let choices = edges
                .iter()
                .map(|(expected_before, expected_after)| {
                    conjunction([
                        before.clone().equals(expected_before.clone())?,
                        after.clone().equals(expected_after.clone())?,
                    ])
                })
                .collect::<Result<Vec<_>, Error>>()?;
            conjunction([machine_var.equals(machine.clone())?, disjunction(choices)?])
        },
    )
}

fn validate_theory(theory: &FiniteAutomataTheory<NativeHol>) -> Result<(), DfaReplayError> {
    let bool_type = Type::bool();
    let arrow = Type::fun;
    let checks = [
        (
            "machine",
            theory.machine.clone(),
            theory.machine_type.clone(),
        ),
        (
            "configuration",
            theory.configuration.clone(),
            arrow(
                theory.state_type.clone(),
                arrow(theory.word_type.clone(), theory.configuration_type.clone()),
            ),
        ),
        (
            "initial",
            theory.initial.clone(),
            arrow(
                theory.machine_type.clone(),
                arrow(
                    theory.word_type.clone(),
                    arrow(theory.configuration_type.clone(), bool_type.clone()),
                ),
            ),
        ),
        (
            "transition",
            theory.transition.clone(),
            arrow(
                theory.machine_type.clone(),
                arrow(
                    theory.configuration_type.clone(),
                    arrow(theory.configuration_type.clone(), bool_type.clone()),
                ),
            ),
        ),
        (
            "closure",
            theory.closure.clone(),
            arrow(
                theory.machine_type.clone(),
                arrow(
                    theory.configuration_type.clone(),
                    arrow(theory.configuration_type.clone(), bool_type.clone()),
                ),
            ),
        ),
        (
            "reachable",
            theory.reachable.clone(),
            arrow(
                theory.machine_type.clone(),
                arrow(
                    theory.word_type.clone(),
                    arrow(theory.configuration_type.clone(), bool_type.clone()),
                ),
            ),
        ),
        (
            "accepting_configuration",
            theory.accepting_configuration.clone(),
            arrow(
                theory.machine_type.clone(),
                arrow(theory.configuration_type.clone(), bool_type.clone()),
            ),
        ),
        (
            "accepts",
            theory.accepts.clone(),
            arrow(
                theory.machine_type.clone(),
                arrow(theory.word_type.clone(), bool_type),
            ),
        ),
    ];
    for (field, term, expected) in checks {
        if term.type_of().map_err(|_| DfaReplayError::Kernel)? != expected {
            return Err(DfaReplayError::TypeMismatch { field });
        }
    }
    Ok(())
}

fn same_theory(
    left: &FiniteAutomataTheory<NativeHol>,
    right: &FiniteAutomataTheory<NativeHol>,
) -> bool {
    left.machine_type == right.machine_type
        && left.symbol_type == right.symbol_type
        && left.state_type == right.state_type
        && left.word_type == right.word_type
        && left.configuration_type == right.configuration_type
        && left.machine == right.machine
        && left.configuration == right.configuration
        && left.initial == right.initial
        && left.transition == right.transition
        && left.closure == right.closure
        && left.reachable == right.reachable
        && left.accepting_configuration == right.accepting_configuration
        && left.accepts == right.accepts
}

#[cfg(test)]
mod tests {
    use covalence_computation::{automata_api::FiniteAutomataReplay, theory::TheoremCertificate};

    use super::*;

    fn parity_dfa() -> Dfa<u64> {
        Dfa::new(vec![0, 1], 0, vec![0], vec![vec![0, 1], vec![1, 0]]).unwrap()
    }

    #[test]
    fn accepted_trace_replays_to_the_native_accepts_proposition() {
        let automaton = parity_dfa();
        let input = vec![1, 0, 1];
        let witness = search_dfa_acceptance(&automaton, input.clone()).unwrap();
        let theory = bounded_dfa_theory(&automaton, &input).unwrap();
        let certificate = BoundedDfaReplay {
            automaton: &automaton,
        }
        .replay(&NativeHol, &theory, &witness)
        .unwrap();

        let word = nat_list_u64(input);
        let expected = NativeHol
            .app(
                NativeHol
                    .app(theory.accepts.clone(), theory.machine.clone())
                    .unwrap(),
                word,
            )
            .unwrap();
        assert_eq!(NativeHol.concl(certificate.theorem()), expected);
        assert!(NativeHol.hyps(certificate.theorem()).is_empty());
        assert_eq!(certificate.metadata.transitions, 3);
    }

    #[test]
    fn forged_middle_state_is_rejected() {
        let automaton = parity_dfa();
        let input = vec![1, 0, 1];
        let mut witness = search_dfa_acceptance(&automaton, input.clone()).unwrap();
        witness.candidate.states[1] = 0;
        let theory = bounded_dfa_theory(&automaton, &input).unwrap();
        assert!(matches!(
            BoundedDfaReplay {
                automaton: &automaton
            }
            .replay(&NativeHol, &theory, &witness),
            Err(DfaReplayError::ForgedTrace)
        ));
    }

    #[test]
    fn forged_transition_count_is_rejected() {
        let automaton = parity_dfa();
        let input = vec![1, 0, 1];
        let mut witness = search_dfa_acceptance(&automaton, input.clone()).unwrap();
        witness.transitions = 2;
        let theory = bounded_dfa_theory(&automaton, &input).unwrap();
        assert!(matches!(
            BoundedDfaReplay {
                automaton: &automaton
            }
            .replay(&NativeHol, &theory, &witness),
            Err(DfaReplayError::WrongTransitionCount { .. })
        ));
    }

    #[test]
    fn substituted_acceptance_theory_is_rejected() {
        let automaton = parity_dfa();
        let input = vec![1, 0, 1];
        let witness = search_dfa_acceptance(&automaton, input.clone()).unwrap();
        let mut theory = bounded_dfa_theory(&automaton, &input).unwrap();
        theory.accepts = Term::free(
            "forged.accepts",
            Type::fun(
                theory.machine_type.clone(),
                Type::fun(theory.word_type.clone(), Type::bool()),
            ),
        );
        assert!(matches!(
            BoundedDfaReplay {
                automaton: &automaton
            }
            .replay(&NativeHol, &theory, &witness),
            Err(DfaReplayError::TheoryMismatch)
        ));
    }

    #[test]
    fn rejected_word_does_not_produce_an_acceptance_theory_or_witness() {
        let automaton = parity_dfa();
        let input = vec![1];
        assert!(matches!(
            search_dfa_acceptance(&automaton, input.clone()),
            Err(DfaReplayError::NotAccepting)
        ));
        assert!(matches!(
            bounded_dfa_theory(&automaton, &input),
            Err(DfaReplayError::NotAccepting)
        ));
    }
}
