//! Native-HOL terms and checked trace replay for Minsky machines.

use covalence_computation::minsky::{Configuration, Instruction, Machine, Step};
use covalence_computation::theory::Theory;
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
    pub theorem: Thm,
}

#[derive(Clone, Debug)]
pub struct ReplayCertificate {
    pub checked_states: Vec<CheckedTransition>,
    pub final_state: Thm,
    pub transitions: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReplayError {
    EmptyTrace,
    WrongInitialState,
    InvalidTransition { index: usize },
    Stuck { index: usize },
    NotHalted,
    Kernel,
}

impl Backend {
    pub fn theory(machine: &Machine) -> Theory<NativeHol> {
        let data = list(Type::nat());
        Theory {
            machine_type: data.clone(),
            input_type: data.clone(),
            state_type: data.clone(),
            output_type: data.clone(),
            machine: encode_machine(machine),
            initialize: Term::free(
                "minsky.initialize",
                Type::fun(data.clone(), Type::fun(data.clone(), data.clone())),
            ),
            step: Term::free(
                "minsky.step",
                Type::fun(
                    data.clone(),
                    Type::fun(data.clone(), Type::fun(data.clone(), Type::bool())),
                ),
            ),
            output: Term::free(
                "minsky.output",
                Type::fun(data.clone(), Type::fun(data.clone(), data.clone())),
            ),
            halts: Term::free(
                "minsky.halts",
                Type::fun(data.clone(), Type::fun(data, Type::bool())),
            ),
        }
    }

    pub fn replay(
        machine: &Machine,
        initial_registers: &[u64],
        trace: &[Configuration],
    ) -> Result<ReplayCertificate, ReplayError> {
        let Some(first) = trace.first() else {
            return Err(ReplayError::EmptyTrace);
        };
        if first != &machine.initial_configuration(initial_registers.to_vec()) {
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
                Step::Stuck(_) => return Err(ReplayError::Stuck { index }),
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
        if !matches!(machine.program.get(last.pc), Some(Instruction::Halt)) {
            return Err(ReplayError::NotHalted);
        }
        let final_state = hol
            .refl(encode_configuration(last))
            .map_err(|_| ReplayError::Kernel)?;
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

pub fn encode_configuration(configuration: &Configuration) -> Term {
    let mut words = vec![
        configuration.pc as u64,
        configuration.registers.len() as u64,
    ];
    words.extend(configuration.registers.iter().copied());
    nat_list(words)
}

pub fn encode_machine(machine: &Machine) -> Term {
    let mut words = vec![machine.initial as u64, machine.program.len() as u64];
    for instruction in &machine.program {
        match *instruction {
            Instruction::Halt => words.push(0),
            Instruction::Increment { register, next } => {
                words.extend([1, register as u64, next as u64]);
            }
            Instruction::Decrement {
                register,
                if_positive,
                if_zero,
            } => {
                words.extend([2, register as u64, if_positive as u64, if_zero as u64]);
            }
        }
    }
    nat_list(words)
}

fn encode_pair(before: &Configuration, after: &Configuration) -> Term {
    let state_type = list(Type::nat());
    Term::app(
        Term::app(cons(state_type.clone()), encode_configuration(before)),
        Term::app(
            Term::app(cons(state_type.clone()), encode_configuration(after)),
            nil(state_type),
        ),
    )
}

// TODO(cov:computation.minsky-hol-step-definition, major): Define minsky.step
// inside HOL and lift replayed concrete transitions to the object-language
// step predicate.
// TODO(cov:computation.minsky-universal-equivalence, major): Prove the native
// Minsky theory mutually simulates the Turing, SKI, and BLC theories.

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn replay_checks_and_proves_a_halting_trace() {
        let machine = Machine {
            initial: 0,
            program: vec![
                Instruction::Increment {
                    register: 0,
                    next: 1,
                },
                Instruction::Halt,
            ],
        };
        let first = machine.initial_configuration(vec![2]);
        let mut last = first.clone();
        assert_eq!(machine.step(&mut last), Step::Halted);
        let certificate = Backend::replay(&machine, &[2], &[first, last]).unwrap();
        assert_eq!(certificate.transitions, 1);
        assert!(NativeHol.hyps(&certificate.final_state).is_empty());
    }

    #[test]
    fn replay_rejects_forged_registers() {
        let machine = Machine {
            initial: 0,
            program: vec![
                Instruction::Increment {
                    register: 0,
                    next: 1,
                },
                Instruction::Halt,
            ],
        };
        let first = machine.initial_configuration(vec![2]);
        let forged = Configuration {
            pc: 1,
            registers: vec![99],
        };
        assert!(matches!(
            Backend::replay(&machine, &[2], &[first, forged]),
            Err(ReplayError::InvalidTransition { index: 0 })
        ));
    }
}
