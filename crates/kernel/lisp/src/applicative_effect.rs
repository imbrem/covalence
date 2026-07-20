//! Generic suspension and resumption for applicative Lisp primitives.

use core::fmt::Debug;

use crate::{
    CoreMachineError, DeterministicStep, EffectResume, EffectState, EffectSuspension,
    LispConfiguration, LispMachine, LispMachineError, LispRuntime, MachineControl,
    PrimitiveSemantics, StepRelation, TerminalValue,
};

/// Effect state selected by an applicative runtime and primitive dictionary.
pub type LispEffectState<R, P> = EffectState<
    LispConfiguration<R, P>,
    <P as PrimitiveSemantics<<R as LispRuntime>::Values>>::Request,
>;

/// Generic effect runner over a deterministic [`LispMachine`].
#[derive(Clone, Debug)]
pub struct LispEffectMachine<R, P> {
    pure: LispMachine<R, P>,
}

impl<R, P> LispEffectMachine<R, P> {
    pub fn new(pure: LispMachine<R, P>) -> Self {
        Self { pure }
    }

    pub fn pure(&self) -> &LispMachine<R, P> {
        &self.pure
    }

    pub fn runtime(&self) -> &R {
        self.pure.runtime()
    }

    pub fn primitives(&self) -> &P {
        self.pure.primitives()
    }
}

impl<R, P> LispEffectMachine<R, P>
where
    R: LispRuntime,
    R::Symbol: PartialEq,
    R::Expr: Debug + PartialEq,
    R::Value: Debug + PartialEq,
    R::Environment: Debug + PartialEq,
    R::Primitive: Debug + PartialEq,
    P: PrimitiveSemantics<R::Values>,
{
    fn suspended(
        configuration: LispConfiguration<R, P>,
    ) -> EffectState<LispConfiguration<R, P>, P::Request> {
        let MachineControl::Suspended(request) = &configuration.control else {
            return EffectState::Running(configuration);
        };
        EffectState::Suspended(EffectSuspension {
            continuation: configuration.clone(),
            request: request.clone(),
        })
    }

    pub fn next_effect(
        &self,
        state: &LispEffectState<R, P>,
    ) -> Result<Option<LispEffectState<R, P>>, LispMachineError<R, P>> {
        match state {
            EffectState::Suspended(_) | EffectState::Returned(_) => Ok(None),
            EffectState::Running(configuration) => {
                if matches!(configuration.control, MachineControl::Suspended(_)) {
                    return Ok(Some(Self::suspended(configuration.clone())));
                }
                match self.pure.next(configuration)? {
                    Some(next) => Ok(Some(Self::suspended(next))),
                    None if configuration.terminal_value().is_some() => {
                        Ok(Some(EffectState::Returned(configuration.clone())))
                    }
                    None => Ok(None),
                }
            }
        }
    }
}

impl<R, P> StepRelation for LispEffectMachine<R, P>
where
    R: LispRuntime,
    R::Symbol: PartialEq,
    R::Expr: Debug + PartialEq,
    R::Value: Debug + PartialEq,
    R::Environment: Debug + PartialEq,
    R::Primitive: Debug + PartialEq,
    P: PrimitiveSemantics<R::Values>,
{
    type Configuration = LispEffectState<R, P>;
    type Error = LispMachineError<R, P>;

    fn successors(
        &self,
        state: &Self::Configuration,
    ) -> Result<Vec<Self::Configuration>, Self::Error> {
        Ok(self.next_effect(state)?.into_iter().collect())
    }
}

impl<R, P> DeterministicStep for LispEffectMachine<R, P>
where
    R: LispRuntime,
    R::Symbol: PartialEq,
    R::Expr: Debug + PartialEq,
    R::Value: Debug + PartialEq,
    R::Environment: Debug + PartialEq,
    R::Primitive: Debug + PartialEq,
    P: PrimitiveSemantics<R::Values>,
{
    fn next(
        &self,
        state: &Self::Configuration,
    ) -> Result<Option<Self::Configuration>, Self::Error> {
        self.next_effect(state)
    }
}

impl<R, P> TerminalValue for LispEffectMachine<R, P>
where
    R: LispRuntime,
    R::Symbol: PartialEq,
    R::Expr: Debug + PartialEq,
    R::Value: Debug + PartialEq,
    R::Environment: Debug + PartialEq,
    R::Primitive: Debug + PartialEq,
    P: PrimitiveSemantics<R::Values>,
{
    type Value = R::Value;

    fn terminal_value(&self, state: &Self::Configuration) -> Option<Self::Value> {
        match state {
            EffectState::Returned(configuration) => configuration.terminal_value().cloned(),
            EffectState::Running(_) | EffectState::Suspended(_) => None,
        }
    }
}

impl<R, P> EffectResume for LispEffectMachine<R, P>
where
    R: LispRuntime,
    R::Symbol: PartialEq,
    R::Expr: Debug + PartialEq,
    R::Value: Debug + PartialEq,
    R::Environment: Debug + PartialEq,
    R::Primitive: Debug + PartialEq,
    P: PrimitiveSemantics<R::Values>,
{
    type Configuration = LispConfiguration<R, P>;
    type Request = P::Request;
    type Response = P::Response;
    type Error = LispMachineError<R, P>;

    fn resume(
        &self,
        suspension: EffectSuspension<Self::Configuration, Self::Request>,
        response: Self::Response,
    ) -> Result<Self::Configuration, Self::Error> {
        let mut continuation = suspension.continuation;
        let MachineControl::Suspended(stored) = &continuation.control else {
            return Err(CoreMachineError::InvalidEffectSuspension);
        };
        if stored != &suspension.request {
            return Err(CoreMachineError::InvalidEffectSuspension);
        }
        let value = self
            .primitives()
            .resume(self.runtime().values(), stored, response)
            .map_err(CoreMachineError::Primitive)?;
        continuation.control = MachineControl::Value(value);
        Ok(continuation)
    }
}
