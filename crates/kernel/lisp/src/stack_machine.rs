//! Generic pure evaluator for concatenative Lisp machines.

use core::fmt::{Debug, Display, Formatter};

use crate::{
    DeterministicStep, LispEnvironment, RuntimeBinding, StackClosure, StackClosureRecord,
    StackConfiguration, StackContinuation, StackInstructionLayer, StackInstructionView,
    StackMachineValue, StackPrimitiveSemantics, StackProgramSyntax, StackRuntime, StackValue,
    StackValueLayer, StepRelation,
};

/// Failure from the language-independent stack transition engine.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StackMachineError<S, F, P, R> {
    EmptyStack,
    Unbound(S),
    UnhandledEffect(F),
    Primitive(P),
    Runtime(R),
}

impl<S: Display, F: Debug, P: Display, R: Display> Display for StackMachineError<S, F, P, R> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::EmptyStack => f.write_str("stack machine operand stack is empty"),
            Self::Unbound(symbol) => write!(f, "unbound stack-language name `{symbol}`"),
            Self::UnhandledEffect(effect) => {
                write!(f, "pure stack machine cannot handle effect {effect:?}")
            }
            Self::Primitive(error) => write!(f, "stack primitive failed: {error}"),
            Self::Runtime(error) => write!(f, "stack runtime failed: {error}"),
        }
    }
}

impl<S: Debug + Display, F: Debug, P: Debug + Display, R: Debug + Display> core::error::Error
    for StackMachineError<S, F, P, R>
{
}

/// Configuration type selected by a [`StackRuntime`].
pub type StackRuntimeConfiguration<R> = StackConfiguration<
    <R as StackRuntime>::Code,
    <R as StackRuntime>::Value,
    <R as StackRuntime>::Environment,
>;

/// Pure concatenative evaluator over abstract representations and primitives.
#[derive(Clone, Debug)]
pub struct StackMachine<R, P> {
    runtime: R,
    primitives: P,
}

impl<R, P> StackMachine<R, P> {
    pub fn new(runtime: R, primitives: P) -> Self {
        Self {
            runtime,
            primitives,
        }
    }

    pub fn runtime(&self) -> &R {
        &self.runtime
    }

    pub fn primitives(&self) -> &P {
        &self.primitives
    }
}

impl<R, P> StackMachine<R, P>
where
    R: StackRuntime,
    R::Syntax: StackInstructionView,
    P: StackPrimitiveSemantics<R>,
{
    pub fn initial(&self, code: R::Code) -> StackRuntimeConfiguration<R> {
        StackConfiguration::new(code, self.runtime.environments().empty())
    }

    fn runtime_error(
        &self,
        error: R::Error,
    ) -> StackMachineError<R::Symbol, <R::Syntax as StackInstructionView>::Effect, P::Error, R::Error>
    {
        StackMachineError::Runtime(error)
    }

    pub fn next_configuration(
        &self,
        configuration: &StackRuntimeConfiguration<R>,
    ) -> Result<
        Option<StackRuntimeConfiguration<R>>,
        StackMachineError<
            R::Symbol,
            <R::Syntax as StackInstructionView>::Effect,
            P::Error,
            R::Error,
        >,
    > {
        let mut next = configuration.clone();
        let instructions = self
            .runtime
            .syntax()
            .instructions(&next.code)
            .map_err(|error| self.runtime_error(self.runtime.syntax_error(error)))?;
        if next.cursor == instructions.len() {
            let Some(caller) = next.continuations.pop() else {
                return Ok(None);
            };
            next.code = caller.code;
            next.cursor = caller.cursor;
            next.environment = caller.environment;
            return Ok(Some(next));
        }

        let instruction = self
            .runtime
            .syntax()
            .view_instruction(&instructions[next.cursor])
            .map_err(|error| self.runtime_error(self.runtime.syntax_error(error)))?;
        next.cursor += 1;
        match instruction {
            StackInstructionLayer::Literal(datum) | StackInstructionLayer::Quote(datum) => {
                let value = self
                    .runtime
                    .values()
                    .datum(datum)
                    .map_err(|error| self.runtime_error(self.runtime.value_error(error)))?;
                next.operands.push(value);
            }
            StackInstructionLayer::Closure(code) => {
                let closure = self
                    .runtime
                    .closures()
                    .close(StackClosureRecord {
                        code,
                        environment: next.environment.clone(),
                    })
                    .map_err(|error| self.runtime_error(self.runtime.closure_error(error)))?;
                let value = self
                    .runtime
                    .values()
                    .roll(StackValueLayer::Closure(closure))
                    .map_err(|error| self.runtime_error(self.runtime.value_error(error)))?;
                next.operands.push(value);
            }
            StackInstructionLayer::Bind(symbol) => {
                let value = next.operands.pop().ok_or(StackMachineError::EmptyStack)?;
                next.environment = self
                    .runtime
                    .environments()
                    .extend(&next.environment, vec![RuntimeBinding::new(symbol, value)])
                    .map_err(|error| self.runtime_error(self.runtime.environment_error(error)))?;
            }
            StackInstructionLayer::PushBinding(symbol) => {
                let value = self
                    .runtime
                    .environments()
                    .lookup(&next.environment, &symbol)
                    .map_err(|error| self.runtime_error(self.runtime.environment_error(error)))?
                    .ok_or_else(|| StackMachineError::Unbound(symbol.clone()))?;
                next.operands.push(value);
            }
            StackInstructionLayer::Resolve(symbol) => {
                let value = self
                    .runtime
                    .environments()
                    .lookup(&next.environment, &symbol)
                    .map_err(|error| self.runtime_error(self.runtime.environment_error(error)))?
                    .ok_or_else(|| StackMachineError::Unbound(symbol.clone()))?;
                match self
                    .runtime
                    .values()
                    .unroll(&value)
                    .map_err(|error| self.runtime_error(self.runtime.value_error(error)))?
                {
                    StackValueLayer::Datum(_) => next.operands.push(value),
                    StackValueLayer::Closure(closure) => {
                        let closure = self.runtime.closures().open(&closure).map_err(|error| {
                            self.runtime_error(self.runtime.closure_error(error))
                        })?;
                        next.continuations.push(StackContinuation {
                            code: next.code,
                            cursor: next.cursor,
                            environment: next.environment,
                        });
                        next.code = closure.code;
                        next.cursor = 0;
                        next.environment = closure.environment;
                    }
                }
            }
            StackInstructionLayer::Primitive(primitive) => {
                next.operands = self
                    .primitives
                    .apply(&self.runtime, &primitive, next.operands)
                    .map_err(StackMachineError::Primitive)?;
            }
            StackInstructionLayer::Effect(effect) => {
                return Err(StackMachineError::UnhandledEffect(effect));
            }
        }
        Ok(Some(next))
    }
}

impl<R, P> StepRelation for StackMachine<R, P>
where
    R: StackRuntime,
    R::Syntax: StackInstructionView,
    P: StackPrimitiveSemantics<R>,
    R::Code: Debug + PartialEq,
    R::Value: Debug + PartialEq,
    R::Environment: Debug + PartialEq,
{
    type Configuration = StackRuntimeConfiguration<R>;
    type Error = StackMachineError<
        R::Symbol,
        <R::Syntax as StackInstructionView>::Effect,
        P::Error,
        R::Error,
    >;

    fn successors(
        &self,
        configuration: &Self::Configuration,
    ) -> Result<Vec<Self::Configuration>, Self::Error> {
        Ok(self
            .next_configuration(configuration)?
            .into_iter()
            .collect())
    }
}

impl<R, P> DeterministicStep for StackMachine<R, P>
where
    R: StackRuntime,
    R::Syntax: StackInstructionView,
    P: StackPrimitiveSemantics<R>,
    R::Code: Debug + PartialEq,
    R::Value: Debug + PartialEq,
    R::Environment: Debug + PartialEq,
{
    fn next(
        &self,
        configuration: &Self::Configuration,
    ) -> Result<Option<Self::Configuration>, Self::Error> {
        self.next_configuration(configuration)
    }
}
