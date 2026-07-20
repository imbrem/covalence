//! Explicit effect requests and resumptions for Lisp-family machines.
//!
//! Pure reduction may suspend with a request, but it never performs host I/O
//! or mutates host state. Handlers are separate capabilities, and their
//! request/response transcripts remain plain data until a proof backend
//! supplies an appropriate replay theorem.
//!
//! @covalence-api {"id":"A0025","title":"Lisp effect suspension and handling","status":"experimental","dependsOn":["A0022","A0023"]}

use core::fmt::{Debug, Display, Formatter};

use crate::{DeterministicStep, StepRelation};

/// A representation-independent effect request.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EffectRequest<O, I> {
    pub operation: O,
    pub input: I,
}

/// A machine continuation waiting for an effect response.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EffectSuspension<C, Q> {
    pub continuation: C,
    pub request: Q,
}

/// Observable state of an effectful machine.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EffectState<C, Q> {
    Running(C),
    Suspended(EffectSuspension<C, Q>),
    Returned(C),
}

/// One handled request retained as auditable, serializable data.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HandledEffect<Q, R> {
    pub request: Q,
    pub response: R,
}

/// WIT-shaped request construction.
pub trait EffectSyntax {
    type Operation: Clone;
    type Input: Clone;
    type Request: Clone;
    type Error;

    fn request(
        &self,
        operation: Self::Operation,
        input: Self::Input,
    ) -> Result<Self::Request, Self::Error>;
}

/// Language semantics for validating a response and resuming a continuation.
pub trait EffectResume {
    type Configuration: Clone;
    type Request: Clone;
    type Response: Clone;
    type Error;

    fn resume(
        &self,
        suspension: EffectSuspension<Self::Configuration, Self::Request>,
        response: Self::Response,
    ) -> Result<Self::Configuration, Self::Error>;
}

/// Proof-free external effect handler.
///
/// Implementations may perform I/O or mutate host state. Consequently this
/// capability carries no theorem authority.
pub trait EffectHandler<Q, R> {
    type Error;

    fn handle(&mut self, request: &Q) -> Result<R, Self::Error>;
}

/// Optional proof-producing validation of a handled effect.
pub trait EffectReplay<Q, R> {
    type Evidence;
    type Error;

    fn replay(&self, handled: &HandledEffect<Q, R>) -> Result<Self::Evidence, Self::Error>;
}

/// A completed proof-free handled execution.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HandledRun<C, Q, R> {
    pub returned: C,
    pub transcript: Vec<HandledEffect<Q, R>>,
    /// Initial state followed by every reduction or resumption result.
    pub states: Vec<EffectState<C, Q>>,
    /// Machine reductions plus handler resumptions.
    pub steps: usize,
}

/// A structurally checked handled run plus evidence for every external effect.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReplayedHandledRun<E> {
    pub effect_evidence: Vec<E>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HandledRunCheckError<M> {
    EmptyTrace,
    InitialStateMismatch,
    ReturnedStateMismatch,
    StepCountMismatch { recorded: usize, actual: usize },
    Machine(M),
    Stuck { index: usize },
    InvalidTransition { index: usize },
    MissingHandledEffect { index: usize },
    RequestMismatch { index: usize },
    ExtraHandledEffects { used: usize, recorded: usize },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EffectReplayError<E> {
    pub index: usize,
    pub error: E,
}

/// Failure from [`handle_to_completion`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EffectRunError<M, H> {
    Machine(M),
    Handler(H),
    Stuck,
    FuelExhausted { fuel: usize },
}

impl<M: Display, H: Display> Display for EffectRunError<M, H> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Machine(error) => write!(f, "effect machine failed: {error}"),
            Self::Handler(error) => write!(f, "effect handler failed: {error}"),
            Self::Stuck => f.write_str("effect machine stopped without returning or suspending"),
            Self::FuelExhausted { fuel } => {
                write!(f, "effectful execution exceeded its {fuel}-step bound")
            }
        }
    }
}

impl<M: Debug + Display, H: Debug + Display> core::error::Error for EffectRunError<M, H> {}

impl<M: Display> Display for HandledRunCheckError<M> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::EmptyTrace => f.write_str("handled run has no recorded states"),
            Self::InitialStateMismatch => {
                f.write_str("handled run does not begin at the claimed initial state")
            }
            Self::ReturnedStateMismatch => {
                f.write_str("handled run does not end at its claimed returned state")
            }
            Self::StepCountMismatch { recorded, actual } => write!(
                f,
                "handled run records {recorded} steps but contains {actual} transitions"
            ),
            Self::Machine(error) => write!(f, "handled-run replay failed: {error}"),
            Self::Stuck { index } => write!(f, "handled run is stuck at transition {index}"),
            Self::InvalidTransition { index } => {
                write!(f, "handled run has an invalid transition at {index}")
            }
            Self::MissingHandledEffect { index } => {
                write!(f, "handled run has no response for suspension {index}")
            }
            Self::RequestMismatch { index } => {
                write!(f, "handled response {index} names the wrong request")
            }
            Self::ExtraHandledEffects { used, recorded } => write!(
                f,
                "handled run uses {used} responses but records {recorded}"
            ),
        }
    }
}

impl<M: Debug + Display> core::error::Error for HandledRunCheckError<M> {}

impl<E: Display> Display for EffectReplayError<E> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "external effect {} failed validation: {}",
            self.index, self.error
        )
    }
}

impl<E: Debug + Display> core::error::Error for EffectReplayError<E> {}

/// Run a deterministic effect machine with a proof-free handler.
///
/// Each request/response pair is retained in order. The transcript has no
/// theorem authority; a proof-producing client must replay it through
/// [`EffectReplay`].
pub fn handle_to_completion<M, H, C, Q, R>(
    machine: &M,
    mut state: EffectState<C, Q>,
    handler: &mut H,
    fuel: usize,
) -> Result<HandledRun<C, Q, R>, EffectRunError<<M as StepRelation>::Error, H::Error>>
where
    C: Clone + PartialEq + Debug,
    Q: Clone + PartialEq + Debug,
    R: Clone,
    M: DeterministicStep<Configuration = EffectState<C, Q>>
        + EffectResume<
            Configuration = C,
            Request = Q,
            Response = R,
            Error = <M as StepRelation>::Error,
        >,
    H: EffectHandler<Q, R>,
{
    let mut transcript = Vec::new();
    let mut states = vec![state.clone()];
    let mut steps = 0;
    loop {
        if let EffectState::Returned(returned) = state {
            return Ok(HandledRun {
                returned,
                transcript,
                states,
                steps,
            });
        }
        if steps == fuel {
            return Err(EffectRunError::FuelExhausted { fuel });
        }
        state = match state {
            EffectState::Running(_) => machine
                .next(&state)
                .map_err(EffectRunError::Machine)?
                .ok_or(EffectRunError::Stuck)?,
            EffectState::Suspended(suspension) => {
                let request = suspension.request.clone();
                let response = handler.handle(&request).map_err(EffectRunError::Handler)?;
                let continuation = machine
                    .resume(suspension, response.clone())
                    .map_err(EffectRunError::Machine)?;
                transcript.push(HandledEffect { request, response });
                EffectState::Running(continuation)
            }
            EffectState::Returned(_) => unreachable!("returned above"),
        };
        steps += 1;
        states.push(state.clone());
    }
}

/// Independently replay every internal reduction and effect resumption.
///
/// This checks the operational trace but does not establish that an external
/// response was truthful. Use [`replay_handled_effects`] for that separate
/// authority boundary.
pub fn check_handled_run<M, C, Q, R>(
    machine: &M,
    initial: &EffectState<C, Q>,
    run: &HandledRun<C, Q, R>,
) -> Result<(), HandledRunCheckError<<M as StepRelation>::Error>>
where
    C: Clone + PartialEq + Debug,
    Q: Clone + PartialEq + Debug,
    R: Clone,
    M: DeterministicStep<Configuration = EffectState<C, Q>>
        + EffectResume<
            Configuration = C,
            Request = Q,
            Response = R,
            Error = <M as StepRelation>::Error,
        >,
{
    let Some(first) = run.states.first() else {
        return Err(HandledRunCheckError::EmptyTrace);
    };
    if first != initial {
        return Err(HandledRunCheckError::InitialStateMismatch);
    }
    if run.states.last() != Some(&EffectState::Returned(run.returned.clone())) {
        return Err(HandledRunCheckError::ReturnedStateMismatch);
    }
    let actual_steps = run.states.len() - 1;
    if run.steps != actual_steps {
        return Err(HandledRunCheckError::StepCountMismatch {
            recorded: run.steps,
            actual: actual_steps,
        });
    }

    let mut handled_index = 0;
    for (index, pair) in run.states.windows(2).enumerate() {
        let before = &pair[0];
        let after = &pair[1];
        let expected = match before {
            EffectState::Running(_) => machine
                .next(before)
                .map_err(HandledRunCheckError::Machine)?
                .ok_or(HandledRunCheckError::Stuck { index })?,
            EffectState::Suspended(suspension) => {
                let handled = run.transcript.get(handled_index).ok_or(
                    HandledRunCheckError::MissingHandledEffect {
                        index: handled_index,
                    },
                )?;
                if handled.request != suspension.request {
                    return Err(HandledRunCheckError::RequestMismatch {
                        index: handled_index,
                    });
                }
                handled_index += 1;
                EffectState::Running(
                    machine
                        .resume(suspension.clone(), handled.response.clone())
                        .map_err(HandledRunCheckError::Machine)?,
                )
            }
            EffectState::Returned(_) => {
                return Err(HandledRunCheckError::InvalidTransition { index });
            }
        };
        if &expected != after {
            return Err(HandledRunCheckError::InvalidTransition { index });
        }
    }
    if handled_index != run.transcript.len() {
        return Err(HandledRunCheckError::ExtraHandledEffects {
            used: handled_index,
            recorded: run.transcript.len(),
        });
    }
    Ok(())
}

/// Validate every external response through a proof-producing replay policy.
pub fn replay_handled_effects<C, Q, R, P>(
    run: &HandledRun<C, Q, R>,
    replay: &P,
) -> Result<ReplayedHandledRun<P::Evidence>, EffectReplayError<P::Error>>
where
    P: EffectReplay<Q, R>,
{
    let effect_evidence = run
        .transcript
        .iter()
        .enumerate()
        .map(|(index, handled)| {
            replay
                .replay(handled)
                .map_err(|error| EffectReplayError { index, error })
        })
        .collect::<Result<_, _>>()?;
    Ok(ReplayedHandledRun { effect_evidence })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Clone, Copy, Debug)]
    struct ToyMachine;

    impl StepRelation for ToyMachine {
        type Configuration = EffectState<u8, &'static str>;
        type Error = &'static str;

        fn successors(
            &self,
            state: &Self::Configuration,
        ) -> Result<Vec<Self::Configuration>, Self::Error> {
            Ok(self.next(state)?.into_iter().collect())
        }
    }

    impl DeterministicStep for ToyMachine {
        fn next(
            &self,
            state: &Self::Configuration,
        ) -> Result<Option<Self::Configuration>, Self::Error> {
            Ok(match state {
                EffectState::Running(0) => Some(EffectState::Suspended(EffectSuspension {
                    continuation: 1,
                    request: "read",
                })),
                EffectState::Running(1) => Some(EffectState::Returned(1)),
                EffectState::Running(_) | EffectState::Suspended(_) | EffectState::Returned(_) => {
                    None
                }
            })
        }
    }

    impl EffectResume for ToyMachine {
        type Configuration = u8;
        type Request = &'static str;
        type Response = u8;
        type Error = &'static str;

        fn resume(
            &self,
            suspension: EffectSuspension<Self::Configuration, Self::Request>,
            response: Self::Response,
        ) -> Result<Self::Configuration, Self::Error> {
            if suspension.request == "read" && response == 42 {
                Ok(suspension.continuation)
            } else {
                Err("invalid response")
            }
        }
    }

    struct Answer;

    impl EffectHandler<&'static str, u8> for Answer {
        type Error = &'static str;

        fn handle(&mut self, _request: &&'static str) -> Result<u8, Self::Error> {
            Ok(42)
        }
    }

    #[test]
    fn handled_runs_replay_and_reject_forged_traces() {
        let initial = EffectState::Running(0);
        let run = handle_to_completion(&ToyMachine, initial.clone(), &mut Answer, 4).unwrap();
        assert_eq!(run.steps, 3);
        assert_eq!(run.states.len(), 4);
        check_handled_run(&ToyMachine, &initial, &run).unwrap();

        let mut forged = run.clone();
        forged.steps += 1;
        assert_eq!(
            check_handled_run(&ToyMachine, &initial, &forged),
            Err(HandledRunCheckError::StepCountMismatch {
                recorded: 4,
                actual: 3
            })
        );

        let mut forged = run;
        forged.transcript[0].request = "write";
        assert_eq!(
            check_handled_run(&ToyMachine, &initial, &forged),
            Err(HandledRunCheckError::RequestMismatch { index: 0 })
        );
    }
}
