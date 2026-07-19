//! Deterministic small-step execution and fuel-bounded observation.

/// A deterministic transition system with an explicit halted observation.
pub trait TransitionSystem {
    /// Mutable machine configuration.
    type State;
    /// Observable result of halting.
    type Outcome;
    /// A rejected or undefined transition.
    type Error;

    /// Return the outcome exactly when `state` is halted.
    fn halted(&self, state: &Self::State) -> Result<Option<Self::Outcome>, Self::Error>;

    /// Advance a non-halted configuration by exactly one transition.
    ///
    /// Calling this on a halted state is permitted to return an error.
    fn transition(&self, state: Self::State) -> Result<Self::State, Self::Error>;
}

/// A transition system that can initialize configurations from programs and
/// inputs.
pub trait Machine: TransitionSystem {
    /// Static program or machine description.
    type Program;
    /// External input representation.
    type Input;

    /// Construct the initial configuration.
    fn initialize(
        &self,
        program: &Self::Program,
        input: &Self::Input,
    ) -> Result<Self::State, Self::Error>;
}

/// Result of running for at most a finite amount of fuel.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RunResult<S, O> {
    /// The initial or a later state was halted.
    Halted {
        outcome: O,
        /// Number of successful transitions performed.
        steps: u64,
    },
    /// Fuel ran out; `state` is the configuration after exactly `steps`
    /// transitions.
    OutOfFuel { state: S, steps: u64 },
}

/// A transition failure annotated with the number of preceding transitions.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExecutionError<E> {
    pub error: E,
    pub steps: u64,
}

/// Run a state for at most `fuel` transitions.
///
/// Halting is checked before fuel exhaustion, so an initially halted state
/// halts with zero fuel and a state reached by the final transition is reported
/// halted rather than out of fuel.
pub fn run<M: TransitionSystem>(
    machine: &M,
    state: M::State,
    fuel: u64,
) -> Result<RunResult<M::State, M::Outcome>, ExecutionError<M::Error>> {
    let mut state = state;
    let mut steps = 0;
    loop {
        match machine.halted(&state) {
            Ok(Some(outcome)) => return Ok(RunResult::Halted { outcome, steps }),
            Ok(None) if steps == fuel => return Ok(RunResult::OutOfFuel { state, steps }),
            Ok(None) => {}
            Err(error) => return Err(ExecutionError { error, steps }),
        }
        state = machine
            .transition(state)
            .map_err(|error| ExecutionError { error, steps })?;
        steps += 1;
    }
}

/// States observed during a fuel-bounded execution.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Trace<S, O> {
    /// Initial state followed by each post-transition state.
    pub states: Vec<S>,
    /// Number of transitions performed (`states.len() - 1`).
    pub steps: u64,
    /// Present exactly when the last state is halted.
    pub outcome: Option<O>,
}

/// Trace result, preserving the partial trace when execution fails.
pub type TraceResult<S, O, E> = Result<Trace<S, O>, (Trace<S, O>, ExecutionError<E>)>;

/// Run while retaining initial and post-transition configurations.
pub fn trace<M>(
    machine: &M,
    state: M::State,
    fuel: u64,
) -> TraceResult<M::State, M::Outcome, M::Error>
where
    M: TransitionSystem,
    M::State: Clone,
{
    let mut state = state;
    let mut states = vec![state.clone()];
    let mut steps = 0;
    loop {
        match machine.halted(&state) {
            Ok(Some(outcome)) => {
                return Ok(Trace {
                    states,
                    steps,
                    outcome: Some(outcome),
                });
            }
            Ok(None) if steps == fuel => {
                return Ok(Trace {
                    states,
                    steps,
                    outcome: None,
                });
            }
            Ok(None) => {}
            Err(error) => {
                let partial = Trace {
                    states,
                    steps,
                    outcome: None,
                };
                return Err((partial, ExecutionError { error, steps }));
            }
        }
        match machine.transition(state) {
            Ok(next) => {
                state = next;
                steps += 1;
                states.push(state.clone());
            }
            Err(error) => {
                let partial = Trace {
                    states,
                    steps,
                    outcome: None,
                };
                return Err((partial, ExecutionError { error, steps }));
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct Countdown;

    impl TransitionSystem for Countdown {
        type State = u8;
        type Outcome = &'static str;
        type Error = core::convert::Infallible;

        fn halted(&self, state: &u8) -> Result<Option<Self::Outcome>, Self::Error> {
            Ok((*state == 0).then_some("done"))
        }

        fn transition(&self, state: u8) -> Result<u8, Self::Error> {
            Ok(state - 1)
        }
    }

    #[test]
    fn zero_fuel_observes_an_initial_halt() {
        assert_eq!(
            run(&Countdown, 0, 0),
            Ok(RunResult::Halted {
                outcome: "done",
                steps: 0,
            })
        );
    }

    #[test]
    fn zero_fuel_does_not_advance_a_running_state() {
        assert_eq!(
            run(&Countdown, 2, 0),
            Ok(RunResult::OutOfFuel { state: 2, steps: 0 })
        );
    }

    #[test]
    fn final_fuel_step_can_halt() {
        assert_eq!(
            run(&Countdown, 2, 2),
            Ok(RunResult::Halted {
                outcome: "done",
                steps: 2,
            })
        );
    }

    #[test]
    fn trace_contains_each_configuration() {
        assert_eq!(
            trace(&Countdown, 2, 1),
            Ok(Trace {
                states: vec![2, 1],
                steps: 1,
                outcome: None,
            })
        );
    }
}
