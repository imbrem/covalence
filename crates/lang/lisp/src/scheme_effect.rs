//! Scheme I/O policy over the backend-neutral applicative effect machine.
//!
//! The requests and responses are plain, representation-generic data. This
//! module does not perform I/O: a host, WASM component, or proof-producing
//! replay layer supplies a handler separately.

use core::fmt::{Debug, Display, Formatter};

use covalence_kernel_lisp::{
    EffectHandler, EffectReplay, EffectReplayError, EffectRunError, EffectState, HandledRun,
    HandledRunCheckError, LispConfiguration, LispEffectMachine, LispIoRequest, LispIoResponse,
    LispMachine, LispMachineError, LispRuntime, LispRuntimeSnapshot, LispValue,
    MachineConfiguration, PrimitiveOutcome, PrimitiveSemantics, ReplayedHandledRun, Strategy,
    check_handled_run, handle_to_completion, replay_handled_effects,
};
use covalence_sexp::SExpr;

use crate::frontend::{
    CoreAtom, FrontendExpr, LowerError, Primitive, PrimitiveError, PrimitiveExecutionError,
    RuntimeSession, RuntimeSessionError, StandardPrimitives, SurfaceDialect,
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

pub type SchemeSession<R> = RuntimeSession<R, SchemePrimitives>;
pub type SchemeMachineError<R> = LispMachineError<R, SchemePrimitives>;
pub type RuntimeSchemeEvaluation<R> =
    SchemeEvaluation<LispConfiguration<R, SchemePrimitives>, <R as LispRuntime>::Value>;

/// High-level result of one handled Scheme evaluation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SchemeEvaluation<C, V> {
    pub value: V,
    pub run: HandledRun<C, LispIoRequest<V>, LispIoResponse<V>>,
}

impl<C, V> SchemeEvaluation<C, V> {
    pub fn replay_effects<P>(
        &self,
        replay: &P,
    ) -> Result<ReplayedHandledRun<P::Evidence>, EffectReplayError<P::Error>>
    where
        P: EffectReplay<LispIoRequest<V>, LispIoResponse<V>>,
    {
        replay_handled_effects(&self.run, replay)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SchemeEvaluationError<M, H> {
    Lower(LowerError),
    Run(EffectRunError<M, H>),
    InvalidRun(HandledRunCheckError<M>),
    MissingValue,
}

impl<M: Display, H: Display> Display for SchemeEvaluationError<M, H> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Lower(error) => Display::fmt(error, f),
            Self::Run(error) => Display::fmt(error, f),
            Self::InvalidRun(error) => Display::fmt(error, f),
            Self::MissingValue => f.write_str("handled Scheme evaluation returned no value"),
        }
    }
}

impl<M, H> core::error::Error for SchemeEvaluationError<M, H>
where
    M: Debug + Display,
    H: Debug + Display,
{
}

impl<R> RuntimeSession<R, SchemePrimitives>
where
    R: LispRuntime<
            Symbol = String,
            Atom = CoreAtom,
            Datum = covalence_kernel_lisp::Datum<CoreAtom>,
            Primitive = Primitive,
            Expr = FrontendExpr,
        > + Clone,
    R: LispRuntimeSnapshot,
    R::Value: Debug + PartialEq,
    R::Environment: Debug + PartialEq,
{
    pub fn scheme(
        fuel: usize,
        runtime: R,
    ) -> Result<Self, RuntimeSessionError<R, SchemePrimitives>> {
        Self::with_runtime_and_primitives(SurfaceDialect::Scheme, fuel, runtime, SchemePrimitives)
    }

    pub fn evaluate_handled<H>(
        &self,
        form: &SExpr,
        handler: &mut H,
    ) -> Result<RuntimeSchemeEvaluation<R>, SchemeEvaluationError<SchemeMachineError<R>, H::Error>>
    where
        H: EffectHandler<LispIoRequest<R::Value>, LispIoResponse<R::Value>>,
    {
        let expression = self
            .frontend()
            .lower(form)
            .map_err(SchemeEvaluationError::Lower)?;
        self.evaluate_core_handled(&expression, handler)
    }

    pub fn evaluate_core_handled<H>(
        &self,
        expression: &FrontendExpr,
        handler: &mut H,
    ) -> Result<RuntimeSchemeEvaluation<R>, SchemeEvaluationError<SchemeMachineError<R>, H::Error>>
    where
        H: EffectHandler<LispIoRequest<R::Value>, LispIoResponse<R::Value>>,
    {
        let replay_machine = LispEffectMachine::new(LispMachine::with_runtime(
            self.runtime().replay_snapshot(),
            SchemePrimitives,
            Strategy::STRICT_LEXICAL,
        ));
        let machine = LispEffectMachine::new(self.machine().clone());
        let initial = EffectState::Running(MachineConfiguration::with_environment(
            expression.clone(),
            self.environment().clone(),
        ));
        let run = handle_to_completion(&machine, initial.clone(), handler, self.fuel())
            .map_err(SchemeEvaluationError::Run)?;
        check_handled_run(&replay_machine, &initial, &run)
            .map_err(SchemeEvaluationError::InvalidRun)?;
        let value = run
            .returned
            .terminal_value()
            .cloned()
            .ok_or(SchemeEvaluationError::MissingValue)?;
        Ok(SchemeEvaluation { value, run })
    }

    /// Evaluate a single non-recursive definition's right-hand side with an
    /// explicit handler, then extend the lexical session environment.
    pub fn define_handled<H>(
        &mut self,
        form: &SExpr,
        handler: &mut H,
    ) -> Result<
        Option<(String, RuntimeSchemeEvaluation<R>)>,
        DefineHandledError<
            RuntimeSessionError<R, SchemePrimitives>,
            SchemeEvaluationError<SchemeMachineError<R>, H::Error>,
        >,
    >
    where
        H: EffectHandler<LispIoRequest<R::Value>, LispIoResponse<R::Value>>,
    {
        let Some((name, expression)) = self
            .frontend()
            .definition(form)
            .map_err(|error| DefineHandledError::Evaluation(SchemeEvaluationError::Lower(error)))?
        else {
            return Ok(None);
        };
        let evaluation = self
            .evaluate_core_handled(&expression, handler)
            .map_err(DefineHandledError::Evaluation)?;
        self.bind_value(name.clone(), evaluation.value.clone())
            .map_err(DefineHandledError::Session)?;
        Ok(Some((name, evaluation)))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DefineHandledError<S, E> {
    Session(S),
    Evaluation(E),
}

impl<S: Display, E: Display> Display for DefineHandledError<S, E> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Session(error) => Display::fmt(error, f),
            Self::Evaluation(error) => Display::fmt(error, f),
        }
    }
}

impl<S, E> core::error::Error for DefineHandledError<S, E>
where
    S: Debug + Display,
    E: Debug + Display,
{
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
        ArenaRuntime, HostRuntime, LispIo, LispIoHandler, LispRuntime, LispValue, RuntimeValueView,
    };
    use covalence_types::Int;

    use super::*;
    struct Scripted<V> {
        read: Option<V>,
    }

    struct ShapeReplay {
        reject_reads: bool,
    }

    impl<V> EffectReplay<LispIoRequest<V>, LispIoResponse<V>> for ShapeReplay {
        type Evidence = &'static str;
        type Error = &'static str;

        fn replay(
            &self,
            handled: &covalence_kernel_lisp::HandledEffect<LispIoRequest<V>, LispIoResponse<V>>,
        ) -> Result<Self::Evidence, Self::Error> {
            match (&handled.request, &handled.response) {
                (LispIoRequest::Read, LispIoResponse::Value(_)) if self.reject_reads => {
                    Err("read response lacks external evidence")
                }
                (LispIoRequest::Read, LispIoResponse::Value(_)) => Ok("read"),
                (LispIoRequest::Write(_), LispIoResponse::Unit) => Ok("write"),
                _ => Err("response shape does not match request"),
            }
        }
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

    fn form(source: &str) -> SExpr {
        crate::reader::read(source).unwrap().pop().unwrap()
    }

    #[test]
    fn scheme_io_is_explicit_and_runtime_representation_independent() {
        let runtime = HostRuntime::<String, CoreAtom, Primitive>::default();
        let expected = runtime
            .values()
            .atom(CoreAtom::Integer(Int::from(42)))
            .unwrap();
        let session = SchemeSession::scheme(64, runtime).unwrap();
        let run = session
            .evaluate_handled(
                &form("(begin (write (quote hello)) (read))"),
                &mut LispIoHandler {
                    host: Scripted {
                        read: Some(expected.clone()),
                    },
                },
            )
            .unwrap();
        assert_eq!(run.run.transcript.len(), 2);
        assert!(matches!(
            &run.run.transcript[0].request,
            LispIoRequest::Write(_)
        ));
        assert_eq!(run.value, expected);
        assert_eq!(
            run.replay_effects(&ShapeReplay {
                reject_reads: false
            })
            .unwrap()
            .effect_evidence,
            vec!["write", "read"]
        );
        assert_eq!(
            run.replay_effects(&ShapeReplay { reject_reads: true })
                .unwrap_err(),
            EffectReplayError {
                index: 1,
                error: "read response lacks external evidence"
            }
        );

        let runtime = ArenaRuntime::<String, CoreAtom, Primitive>::default();
        let expected = runtime
            .values()
            .atom(CoreAtom::Integer(Int::from(42)))
            .unwrap();
        let session = SchemeSession::scheme(64, runtime).unwrap();
        let run = session
            .evaluate_handled(
                &form("(begin (write (quote hello)) (read))"),
                &mut LispIoHandler {
                    host: Scripted {
                        read: Some(expected),
                    },
                },
            )
            .unwrap();
        assert_eq!(run.run.transcript.len(), 2);
        assert_eq!(
            session.runtime().values().view(&run.value).unwrap(),
            RuntimeValueView::Atom(CoreAtom::Integer(Int::from(42)))
        );
    }

    #[test]
    fn handled_definitions_extend_the_stateful_scheme_environment() {
        let runtime = HostRuntime::<String, CoreAtom, Primitive>::default();
        let expected = runtime
            .values()
            .atom(CoreAtom::Integer(Int::from(42)))
            .unwrap();
        let mut session = SchemeSession::scheme(64, runtime).unwrap();
        let (name, definition) = session
            .define_handled(
                &form("(define answer (begin (write (quote loading)) (read)))"),
                &mut LispIoHandler {
                    host: Scripted {
                        read: Some(expected.clone()),
                    },
                },
            )
            .unwrap()
            .expect("definition");
        assert_eq!(name, "answer");
        assert_eq!(definition.value, expected);
        assert_eq!(definition.run.transcript.len(), 2);

        let evaluation = session
            .evaluate_handled(
                &form("answer"),
                &mut LispIoHandler {
                    host: Scripted { read: None },
                },
            )
            .unwrap();
        assert_eq!(evaluation.value, expected);
        assert!(evaluation.run.transcript.is_empty());
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
