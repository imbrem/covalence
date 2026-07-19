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
    /// Machine reductions plus handler resumptions.
    pub steps: usize,
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
    let mut steps = 0;
    loop {
        if let EffectState::Returned(returned) = state {
            return Ok(HandledRun {
                returned,
                transcript,
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
    }
}
