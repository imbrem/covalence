//! Scheme I/O policy over the backend-neutral applicative effect machine.
//!
//! The requests and responses are plain, representation-generic data. This
//! module does not perform I/O: a host, WASM component, or proof-producing
//! replay layer supplies a handler separately.

use covalence_kernel_lisp::{
    LispIoRequest, LispIoResponse, LispValue, PrimitiveOutcome, PrimitiveSemantics,
};

use crate::frontend::{
    CoreAtom, Primitive, PrimitiveError, PrimitiveExecutionError, StandardPrimitives,
};

/// Observable Scheme operations supported by the initial interactive policy.
pub type SchemeRequest<V> = LispIoRequest<V>;

/// A typed response prevents a write acknowledgement from being mistaken for
/// a value returned by `read`, and vice versa.
pub type SchemeResponse<V> = LispIoResponse<V>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SchemePrimitiveError<E> {
    Primitive(PrimitiveExecutionError<E>),
    InvalidResponse,
}

impl<E> From<PrimitiveExecutionError<E>> for SchemePrimitiveError<E> {
    fn from(error: PrimitiveExecutionError<E>) -> Self {
        Self::Primitive(error)
    }
}

impl<E> From<PrimitiveError> for SchemePrimitiveError<E> {
    fn from(error: PrimitiveError) -> Self {
        Self::Primitive(PrimitiveExecutionError::Language(error))
    }
}

/// Effectful Scheme dictionary layered over the shared pure primitives.
#[derive(Clone, Copy, Debug, Default)]
pub struct SchemePrimitives;

impl<V> PrimitiveSemantics<V> for SchemePrimitives
where
    V: LispValue<Atom = CoreAtom, Primitive = Primitive>,
    V::Value: core::fmt::Debug + PartialEq,
{
    type Request = SchemeRequest<V::Value>;
    type Response = SchemeResponse<V::Value>;
    type Error = SchemePrimitiveError<V::Error>;

    fn apply(
        &self,
        runtime: &V,
        primitive: &Primitive,
        arguments: Vec<V::Value>,
    ) -> Result<PrimitiveOutcome<V::Value, Self::Request>, Self::Error> {
        match primitive {
            Primitive::Read => {
                require_arity(&arguments, 0)?;
                Ok(PrimitiveOutcome::Request(LispIoRequest::Read))
            }
            Primitive::Write => {
                require_arity(&arguments, 1)?;
                Ok(PrimitiveOutcome::Request(LispIoRequest::Write(
                    arguments.into_iter().next().expect("arity checked"),
                )))
            }
            _ => match StandardPrimitives.apply(runtime, primitive, arguments)? {
                PrimitiveOutcome::Value(value) => Ok(PrimitiveOutcome::Value(value)),
                PrimitiveOutcome::Request(never) => match never {},
            },
        }
    }

    fn resume(
        &self,
        runtime: &V,
        request: &Self::Request,
        response: Self::Response,
    ) -> Result<V::Value, Self::Error> {
        match (request, response) {
            (LispIoRequest::Read, LispIoResponse::Value(value)) => Ok(value),
            (LispIoRequest::Write(_), LispIoResponse::Unit) => Ok(runtime.nil()),
            _ => Err(SchemePrimitiveError::InvalidResponse),
        }
    }

    fn truth(&self, runtime: &V, value: bool) -> Result<V::Value, Self::Error> {
        StandardPrimitives.truth(runtime, value).map_err(Into::into)
    }

    fn is_false(&self, runtime: &V, value: &V::Value) -> Result<bool, Self::Error> {
        StandardPrimitives
            .is_false(runtime, value)
            .map_err(Into::into)
    }
}

fn require_arity<V>(arguments: &[V], expected: usize) -> Result<(), PrimitiveError> {
    if arguments.len() == expected {
        Ok(())
    } else {
        Err(PrimitiveError::Arity {
            expected,
            actual: arguments.len(),
        })
    }
}

#[cfg(test)]
mod tests {
    use core::convert::Infallible;

    use covalence_kernel_lisp::{
        ArenaRuntime, EffectState, HostRuntime, LispEffectMachine, LispIo, LispIoHandler,
        LispMachine, LispRuntime, LispValue, MachineConfiguration, RuntimeValueView, Strategy,
        handle_to_completion,
    };
    use covalence_types::Int;

    use super::*;
    use crate::frontend::{Frontend, FrontendExpr, SurfaceDialect, initial_environment_for};

    struct Scripted<V> {
        read: Option<V>,
    }

    impl<V> LispIo<V> for Scripted<V> {
        type Error = Infallible;

        fn read(&mut self) -> Result<V, Self::Error> {
            Ok(self.read.take().expect("one scripted read value"))
        }

        fn write(&mut self, _value: &V) -> Result<(), Self::Error> {
            Ok(())
        }
    }

    fn expression() -> FrontendExpr {
        let form = crate::reader::read("(begin (write (quote hello)) (read))")
            .unwrap()
            .pop()
            .unwrap();
        Frontend::new(SurfaceDialect::Scheme).lower(&form).unwrap()
    }

    #[test]
    fn scheme_io_is_explicit_and_runtime_representation_independent() {
        let runtime = HostRuntime::<String, CoreAtom, Primitive>::default();
        let environment = initial_environment_for(
            runtime.values(),
            runtime.environments(),
            SurfaceDialect::Scheme,
        )
        .unwrap();
        let expected = runtime
            .values()
            .atom(CoreAtom::Integer(Int::from(42)))
            .unwrap();
        let machine = LispEffectMachine::new(LispMachine::with_runtime(
            runtime,
            SchemePrimitives,
            Strategy::STRICT_LEXICAL,
        ));
        let run = handle_to_completion(
            &machine,
            EffectState::Running(MachineConfiguration::with_environment(
                expression(),
                environment,
            )),
            &mut LispIoHandler {
                host: Scripted {
                    read: Some(expected.clone()),
                },
            },
            64,
        )
        .unwrap();
        assert_eq!(run.transcript.len(), 2);
        assert!(matches!(
            &run.transcript[0].request,
            LispIoRequest::Write(_)
        ));
        assert_eq!(run.returned.terminal_value(), Some(&expected));

        let runtime = ArenaRuntime::<String, CoreAtom, Primitive>::default();
        let environment = initial_environment_for(
            runtime.values(),
            runtime.environments(),
            SurfaceDialect::Scheme,
        )
        .unwrap();
        let expected = runtime
            .values()
            .atom(CoreAtom::Integer(Int::from(42)))
            .unwrap();
        let machine = LispEffectMachine::new(LispMachine::with_runtime(
            runtime,
            SchemePrimitives,
            Strategy::STRICT_LEXICAL,
        ));
        let run = handle_to_completion(
            &machine,
            EffectState::Running(MachineConfiguration::with_environment(
                expression(),
                environment,
            )),
            &mut LispIoHandler {
                host: Scripted {
                    read: Some(expected),
                },
            },
            64,
        )
        .unwrap();
        assert_eq!(run.transcript.len(), 2);
        let value = run.returned.terminal_value().expect("terminal value");
        assert_eq!(
            machine.runtime().values().view(value).unwrap(),
            RuntimeValueView::Atom(CoreAtom::Integer(Int::from(42)))
        );
    }

    #[test]
    fn scheme_resumption_rejects_the_wrong_response_shape() {
        let runtime = HostRuntime::<String, CoreAtom, Primitive>::default();
        assert_eq!(
            SchemePrimitives.resume(runtime.values(), &LispIoRequest::Read, LispIoResponse::Unit,),
            Err(SchemePrimitiveError::InvalidResponse)
        );
    }
}
