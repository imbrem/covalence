//! Generic suspension and resumption for concatenative Lisp effects.

use core::fmt::{Debug, Display, Formatter};

use crate::{
    DeterministicStep, EffectResume, EffectState, EffectSuspension, StackInstructionLayer,
    StackInstructionView, StackMachine, StackPrimitiveSemantics, StackRuntime,
    StackRuntimeConfiguration, StackRuntimeMachineError, StepRelation, TerminalValue,
};

/// Language policy for turning stack effects into requests and responses.
///
/// Ownership of the operand stack crosses the capability boundary, keeping
/// the API compatible with a WIT `list<value>` representation.
pub trait StackEffectSemantics<R>
where
    R: StackRuntime,
    R::Syntax: StackInstructionView,
{
    type Request: Clone;
    type Response: Clone;
    type Error;

    fn suspend(
        &self,
        runtime: &R,
        effect: &<R::Syntax as StackInstructionView>::Effect,
        operands: Vec<R::Value>,
    ) -> Result<(Vec<R::Value>, Self::Request), Self::Error>;

    fn resume(
        &self,
        runtime: &R,
        request: &Self::Request,
        response: Self::Response,
        operands: Vec<R::Value>,
    ) -> Result<Vec<R::Value>, Self::Error>;
}

/// Failure from a generic effectful stack machine.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StackEffectMachineError<S, E> {
    Stack(S),
    Effect(E),
}

impl<S: Display, E: Display> Display for StackEffectMachineError<S, E> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Stack(error) => write!(f, "stack transition failed: {error}"),
            Self::Effect(error) => write!(f, "stack effect failed: {error}"),
        }
    }
}

impl<S: Debug + Display, E: Debug + Display> core::error::Error for StackEffectMachineError<S, E> {}

/// Effect state selected by a runtime and effect policy.
pub type StackEffectState<R, E> =
    EffectState<StackRuntimeConfiguration<R>, <E as StackEffectSemantics<R>>::Request>;

/// Error selected by a runtime, primitive dictionary, and effect policy.
pub type StackEffectRuntimeError<R, P, E> =
    StackEffectMachineError<StackRuntimeMachineError<R, P>, <E as StackEffectSemantics<R>>::Error>;

/// Generic effect runner over the pure [`StackMachine`].
#[derive(Clone, Debug)]
pub struct StackEffectMachine<R, P, E> {
    pure: StackMachine<R, P>,
    effects: E,
}

impl<R, P, E> StackEffectMachine<R, P, E> {
    pub fn new(runtime: R, primitives: P, effects: E) -> Self {
        Self {
            pure: StackMachine::new(runtime, primitives),
            effects,
        }
    }

    pub fn runtime(&self) -> &R {
        self.pure.runtime()
    }

    pub fn primitives(&self) -> &P {
        self.pure.primitives()
    }

    pub fn effects(&self) -> &E {
        &self.effects
    }
}

impl<R, P, E> StackEffectMachine<R, P, E>
where
    R: StackRuntime,
    R::Syntax: StackInstructionView,
    P: StackPrimitiveSemantics<R>,
    E: StackEffectSemantics<R>,
{
    pub fn initial(&self, code: R::Code) -> StackEffectState<R, E> {
        EffectState::Running(self.pure.initial(code))
    }

    pub fn next_effect(
        &self,
        state: &StackEffectState<R, E>,
    ) -> Result<Option<StackEffectState<R, E>>, StackEffectRuntimeError<R, P, E>> {
        match state {
            EffectState::Suspended(_) | EffectState::Returned(_) => Ok(None),
            EffectState::Running(configuration) => {
                if let Some((StackInstructionLayer::Effect(effect), mut continuation)) = self
                    .pure
                    .take_instruction(configuration)
                    .map_err(StackEffectMachineError::Stack)?
                {
                    let (operands, request) = self
                        .effects
                        .suspend(self.runtime(), &effect, continuation.operands)
                        .map_err(StackEffectMachineError::Effect)?;
                    continuation.operands = operands;
                    return Ok(Some(EffectState::Suspended(EffectSuspension {
                        continuation,
                        request,
                    })));
                }
                Ok(Some(
                    match self
                        .pure
                        .next_configuration(configuration)
                        .map_err(StackEffectMachineError::Stack)?
                    {
                        Some(next) => EffectState::Running(next),
                        None => EffectState::Returned(configuration.clone()),
                    },
                ))
            }
        }
    }
}

impl<R, P, E> StepRelation for StackEffectMachine<R, P, E>
where
    R: StackRuntime,
    R::Syntax: StackInstructionView,
    P: StackPrimitiveSemantics<R>,
    E: StackEffectSemantics<R>,
    R::Code: Debug + PartialEq,
    R::Value: Debug + PartialEq,
    R::Environment: Debug + PartialEq,
    E::Request: Debug + PartialEq,
{
    type Configuration = StackEffectState<R, E>;
    type Error = StackEffectRuntimeError<R, P, E>;

    fn successors(
        &self,
        state: &Self::Configuration,
    ) -> Result<Vec<Self::Configuration>, Self::Error> {
        Ok(self.next_effect(state)?.into_iter().collect())
    }
}

impl<R, P, E> DeterministicStep for StackEffectMachine<R, P, E>
where
    R: StackRuntime,
    R::Syntax: StackInstructionView,
    P: StackPrimitiveSemantics<R>,
    E: StackEffectSemantics<R>,
    R::Code: Debug + PartialEq,
    R::Value: Debug + PartialEq,
    R::Environment: Debug + PartialEq,
    E::Request: Debug + PartialEq,
{
    fn next(
        &self,
        state: &Self::Configuration,
    ) -> Result<Option<Self::Configuration>, Self::Error> {
        self.next_effect(state)
    }
}

impl<R, P, E> TerminalValue for StackEffectMachine<R, P, E>
where
    R: StackRuntime,
    R::Syntax: StackInstructionView,
    P: StackPrimitiveSemantics<R>,
    E: StackEffectSemantics<R>,
    R::Code: Debug + PartialEq,
    R::Value: Debug + PartialEq,
    R::Environment: Debug + PartialEq,
    E::Request: Debug + PartialEq,
{
    type Value = StackRuntimeConfiguration<R>;

    fn terminal_value(&self, state: &Self::Configuration) -> Option<Self::Value> {
        match state {
            EffectState::Returned(configuration) => Some(configuration.clone()),
            EffectState::Running(_) | EffectState::Suspended(_) => None,
        }
    }
}

impl<R, P, E> EffectResume for StackEffectMachine<R, P, E>
where
    R: StackRuntime,
    R::Syntax: StackInstructionView,
    P: StackPrimitiveSemantics<R>,
    E: StackEffectSemantics<R>,
    R::Code: Debug + PartialEq,
    R::Value: Debug + PartialEq,
    R::Environment: Debug + PartialEq,
    E::Request: Debug + PartialEq,
{
    type Configuration = StackRuntimeConfiguration<R>;
    type Request = E::Request;
    type Response = E::Response;
    type Error = StackEffectRuntimeError<R, P, E>;

    fn resume(
        &self,
        suspension: EffectSuspension<Self::Configuration, Self::Request>,
        response: Self::Response,
    ) -> Result<Self::Configuration, Self::Error> {
        let mut continuation = suspension.continuation;
        continuation.operands = self
            .effects
            .resume(
                self.runtime(),
                &suspension.request,
                response,
                continuation.operands,
            )
            .map_err(StackEffectMachineError::Effect)?;
        Ok(continuation)
    }
}
