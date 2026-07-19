//! Native-HOL terms and checked trace replay for deterministic Turing machines.
//!
//! The executable machine is untrusted search machinery. Replay checks every
//! transition, then asks the HOL kernel for closed equalities over the
//! canonical `list nat` representation. These equalities are deliberately
//! narrower than a theorem about the object-language `step` predicate.

use covalence_computation::theory::Theory;
use covalence_computation::turing::{Configuration, Machine, Step};
use covalence_core::{Term, Type};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::defs::{cons, list, nil};
use covalence_types::Nat;

use super::super::inductive::hol::{Hol, NativeHol};

#[derive(Clone, Copy, Debug, Default)]
pub struct Backend;

#[derive(Clone, Debug)]
pub struct CheckedTransition {
    pub before: Term,
    pub after: Term,
    /// `⊢ [before; after] = [before; after]`, minted only after replay.
    pub theorem: Thm,
}

#[derive(Clone, Debug)]
pub struct ReplayCertificate {
    /// One closed theorem and its exact representation metadata per step.
    pub checked_states: Vec<CheckedTransition>,
    /// Closed canonical-representation theorem for the final halting state.
    pub final_state: Thm,
    pub transitions: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReplayError {
    InvalidMachine,
    EmptyTrace,
    WrongInitialState,
    InvalidTransition { index: usize },
    Stuck { index: usize },
    NotHalted,
    Kernel,
}

impl Backend {
    /// The concrete vocabulary uses `list nat` for serialized machines,
    /// inputs, configurations, and outputs.
    pub fn theory(machine: &Machine<u64, u64>) -> Theory<NativeHol> {
        let data = list(Type::nat());
        Theory {
            machine_type: data.clone(),
            input_type: data.clone(),
            state_type: data.clone(),
            output_type: data.clone(),
            machine: encode_machine(machine),
            initialize: Term::free(
                "turing.initialize",
                Type::fun(data.clone(), Type::fun(data.clone(), data.clone())),
            ),
            step: Term::free(
                "turing.step",
                Type::fun(
                    data.clone(),
                    Type::fun(data.clone(), Type::fun(data.clone(), Type::bool())),
                ),
            ),
            output: Term::free(
                "turing.output",
                Type::fun(data.clone(), Type::fun(data.clone(), data.clone())),
            ),
            halts: Term::free(
                "turing.halts",
                Type::fun(data.clone(), Type::fun(data, Type::bool())),
            ),
        }
    }

    pub fn replay(
        machine: &Machine<u64, u64>,
        input: &[u64],
        trace: &[Configuration<u64, u64>],
    ) -> Result<ReplayCertificate, ReplayError> {
        machine
            .validate()
            .map_err(|_| ReplayError::InvalidMachine)?;
        let Some(first) = trace.first() else {
            return Err(ReplayError::EmptyTrace);
        };
        if first != &machine.initial_configuration(input.iter().copied()) {
            return Err(ReplayError::WrongInitialState);
        }

        let hol = NativeHol;
        let mut checked_states = Vec::with_capacity(trace.len().saturating_sub(1));
        for (index, pair) in trace.windows(2).enumerate() {
            let mut expected = pair[0].clone();
            match machine.step(&mut expected) {
                Step::Advanced | Step::Halted if expected == pair[1] => {}
                Step::Advanced | Step::Halted => {
                    return Err(ReplayError::InvalidTransition { index });
                }
                Step::Stuck => return Err(ReplayError::Stuck { index }),
            }
            let before = encode_configuration(&pair[0]);
            let after = encode_configuration(&pair[1]);
            let theorem = hol
                .refl(encode_pair(&pair[0], &pair[1]))
                .map_err(|_| ReplayError::Kernel)?;
            checked_states.push(CheckedTransition {
                before,
                after,
                theorem,
            });
        }
        let last = trace.last().expect("nonempty trace checked above");
        if !machine.halting.contains(&last.state) {
            return Err(ReplayError::NotHalted);
        }
        let final_term = encode_configuration(last);
        let final_state = hol.refl(final_term).map_err(|_| ReplayError::Kernel)?;
        Ok(ReplayCertificate {
            checked_states,
            final_state,
            transitions: trace.len() - 1,
        })
    }
}

fn numeral(value: u64) -> Term {
    covalence_hol_eval::mk_nat(Nat::from_inner(value.into()))
}

fn nat_list(values: impl IntoIterator<Item = u64>) -> Term {
    let mut values: Vec<_> = values.into_iter().collect();
    let mut term = nil(Type::nat());
    while let Some(value) = values.pop() {
        term = Term::app(Term::app(cons(Type::nat()), numeral(value)), term);
    }
    term
}

pub fn encode_configuration(configuration: &Configuration<u64, u64>) -> Term {
    let mut words = vec![configuration.state, configuration.left.len() as u64];
    words.extend(configuration.left.iter().copied());
    words.push(configuration.head);
    words.push(configuration.right.len() as u64);
    words.extend(configuration.right.iter().copied());
    nat_list(words)
}

pub fn encode_machine(machine: &Machine<u64, u64>) -> Term {
    let mut words = vec![machine.initial, machine.blank, machine.halting.len() as u64];
    words.extend(machine.halting.iter().copied());
    words.push(machine.transitions.len() as u64);
    for transition in &machine.transitions {
        words.extend([
            transition.state,
            transition.read,
            transition.write,
            u64::from(matches!(
                transition.direction,
                covalence_computation::turing::Direction::Right
            )),
            transition.next,
        ]);
    }
    nat_list(words)
}

fn encode_pair(before: &Configuration<u64, u64>, after: &Configuration<u64, u64>) -> Term {
    let state_type = list(Type::nat());
    Term::app(
        Term::app(cons(state_type.clone()), encode_configuration(before)),
        Term::app(
            Term::app(cons(state_type.clone()), encode_configuration(after)),
            nil(state_type),
        ),
    )
}

// TODO(cov:computation.turing-hol-step-definition, major): Define turing.step
// inside HOL and lift replayed concrete transitions to the object-language
// step predicate.
// TODO(cov:computation.turing-universal-equivalence, major): Prove the native
// Turing theory mutually simulates the SKI, BLC, and Minsky theories.

#[cfg(test)]
mod tests {
    use covalence_computation::turing::{Direction, Transition};

    use super::*;

    #[test]
    fn replay_returns_only_closed_kernel_theorems() {
        let machine = Machine {
            initial: 0,
            halting: vec![1],
            blank: 0,
            transitions: vec![Transition {
                state: 0,
                read: 0,
                write: 1,
                direction: Direction::Right,
                next: 1,
            }],
        };
        let first = machine.initial_configuration([]);
        let mut last = first.clone();
        assert_eq!(machine.step(&mut last), Step::Halted);
        let certificate = Backend::replay(&machine, &[], &[first, last]).unwrap();
        assert_eq!(certificate.transitions, 1);
        assert!(NativeHol.hyps(&certificate.final_state).is_empty());
        assert!(
            NativeHol
                .dest_eq(&NativeHol.concl(&certificate.final_state))
                .is_some()
        );
    }

    #[test]
    fn replay_rejects_a_forged_state() {
        let machine = Machine {
            initial: 0,
            halting: vec![1],
            blank: 0,
            transitions: vec![],
        };
        let first = machine.initial_configuration([]);
        let forged = Configuration {
            state: 1,
            ..first.clone()
        };
        assert!(matches!(
            Backend::replay(&machine, &[], &[first, forged]),
            Err(ReplayError::Stuck { index: 0 })
        ));
    }
}
