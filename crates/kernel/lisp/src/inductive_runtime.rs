//! Runtime values realized through the shared `data/inductive` backend.
//!
//! This is the representation-stress backend for [`crate::runtime_value_fixpoint`].
//! Unlike the direct host enum and opaque arena, its values are generic tagged
//! inductive values. The evaluator-facing API is nevertheless exactly
//! [`crate::LispMachineValue`].

use core::convert::Infallible;
use core::fmt::{Display, Formatter};

use covalence_sexpr_api::{
    EncodingError, InductiveRepresentation, RawArgument, RawEncoding, RawInductive,
};

use crate::{
    ClosureRecord, CoreExpr, CoreSyntax, HostEnvironment, HostEnvironments, LispClosure,
    LispMachineValue, LispRuntime, LispRuntimeSnapshot, LispValue, Resource, ResourceArena,
    ResourceError, ResourceTable, RuntimeValueCase, RuntimeValueLayer, RuntimeValueParameter,
    RuntimeValueView, runtime_value_fixpoint,
};

/// External leaves of the runtime-value polynomial.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum RuntimeExternal<A, C, P> {
    Atom(A),
    Closure(C),
    Primitive(P),
}

/// Failure at the generic inductive runtime-value boundary.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InductiveRuntimeError {
    Encoding(EncodingError),
    MalformedValue,
}

impl From<EncodingError> for InductiveRuntimeError {
    fn from(error: EncodingError) -> Self {
        Self::Encoding(error)
    }
}

/// One runtime value in the generic tagged inductive representation.
pub type InductiveRuntimeValue<A, C, P> =
    RawInductive<RuntimeValueParameter, RuntimeExternal<A, C, P>>;

/// Realization of Lisp runtime values through `data/inductive`.
#[derive(Clone, Debug)]
pub struct InductiveRuntimeValues<A, C, P> {
    encoding: RawEncoding<RuntimeValueParameter, RuntimeExternal<A, C, P>>,
}

/// Resource kind for closures captured by [`InductiveRuntime`].
pub enum InductiveClosureKind {}

/// Opaque closure handle used by the complete inductive runtime bundle.
pub type InductiveClosure = Resource<InductiveClosureKind>;

/// Values of a complete inductive runtime.
pub type InductiveLispValue<A, P> = InductiveRuntimeValue<A, InductiveClosure, P>;

/// Persistent lexical environment of a complete inductive runtime.
pub type InductiveEnvironment<S, A, P> = HostEnvironment<S, InductiveLispValue<A, P>>;

type StoredClosure<S, A, P> = ClosureRecord<
    S,
    CoreExpr<S, covalence_sexpr_api::FreeSExpr<A>, P>,
    InductiveEnvironment<S, A, P>,
>;

/// Closure capability backed by a typed resource table.
#[derive(Clone, Debug)]
pub struct InductiveClosures<S, A, P> {
    closures: ResourceTable<InductiveClosureKind, StoredClosure<S, A, P>>,
}

impl<S, A, P> LispClosure for InductiveClosures<S, A, P>
where
    S: Clone,
    A: Clone,
    P: Clone,
{
    type Symbol = S;
    type Expr = CoreExpr<S, covalence_sexpr_api::FreeSExpr<A>, P>;
    type Environment = InductiveEnvironment<S, A, P>;
    type Closure = InductiveClosure;
    type Error = ResourceError;

    fn close(
        &self,
        record: ClosureRecord<Self::Symbol, Self::Expr, Self::Environment>,
    ) -> Result<Self::Closure, Self::Error> {
        Ok(self.closures.insert(record))
    }

    fn open(
        &self,
        closure: &Self::Closure,
    ) -> Result<ClosureRecord<Self::Symbol, Self::Expr, Self::Environment>, Self::Error> {
        self.closures.get_cloned(*closure)
    }
}

/// Coherent failure channel for [`InductiveRuntime`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InductiveLispRuntimeError {
    Value(InductiveRuntimeError),
    Resource(ResourceError),
}

impl Display for InductiveLispRuntimeError {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Value(error) => write!(f, "inductive Lisp value error: {error:?}"),
            Self::Resource(error) => Display::fmt(error, f),
        }
    }
}

impl core::error::Error for InductiveLispRuntimeError {}

/// Complete CEK runtime whose recursive values use `data/inductive`.
#[derive(Clone, Debug)]
pub struct InductiveRuntime<S, A, P> {
    data: covalence_sexpr_api::Free<A>,
    values: InductiveRuntimeValues<A, InductiveClosure, P>,
    expressions: CoreSyntax<S, A, P>,
    closures: InductiveClosures<S, A, P>,
    environments: HostEnvironments<S, InductiveLispValue<A, P>>,
}

impl<S, A, P> Default for InductiveRuntime<S, A, P> {
    fn default() -> Self {
        let arena = ResourceArena::new();
        Self {
            data: covalence_sexpr_api::Free::new(),
            values: InductiveRuntimeValues::new(),
            expressions: CoreSyntax::default(),
            closures: InductiveClosures {
                closures: arena.table("inductive Lisp closure"),
            },
            environments: HostEnvironments::default(),
        }
    }
}

impl<A, C, P> Default for InductiveRuntimeValues<A, C, P> {
    fn default() -> Self {
        Self {
            encoding: RawEncoding::from_inductive_fixpoint(runtime_value_fixpoint()),
        }
    }
}

impl<A, C, P> InductiveRuntimeValues<A, C, P> {
    pub fn new() -> Self {
        Self::default()
    }

    fn external(
        &self,
        case: RuntimeValueCase,
        sort: RuntimeValueParameter,
        value: RuntimeExternal<A, C, P>,
    ) -> Result<InductiveRuntimeValue<A, C, P>, InductiveRuntimeError>
    where
        A: Clone,
        C: Clone,
        P: Clone,
    {
        self.encoding
            .construct(
                case.index(),
                vec![RawArgument::External { sort, value }],
                (),
            )
            .map_err(Into::into)
    }
}

impl<A, C, P> LispValue for InductiveRuntimeValues<A, C, P>
where
    A: Clone + PartialEq,
    C: Clone + PartialEq,
    P: Clone + PartialEq,
{
    type Atom = A;
    type Primitive = P;
    type Value = InductiveRuntimeValue<A, C, P>;
    type Error = InductiveRuntimeError;

    fn atom(&self, atom: A) -> Result<Self::Value, Self::Error> {
        self.external(
            RuntimeValueCase::Atom,
            RuntimeValueParameter::Atom,
            RuntimeExternal::Atom(atom),
        )
    }

    fn nil(&self) -> Self::Value {
        self.encoding
            .construct(RuntimeValueCase::Nil.index(), vec![], ())
            .expect("the validated nil constructor has no arguments")
    }

    fn cons(&self, head: Self::Value, tail: Self::Value) -> Result<Self::Value, Self::Error> {
        self.encoding
            .construct(
                RuntimeValueCase::Cons.index(),
                vec![RawArgument::Recursive(head), RawArgument::Recursive(tail)],
                (),
            )
            .map_err(Into::into)
    }

    fn primitive(&self, primitive: P) -> Result<Self::Value, Self::Error> {
        self.external(
            RuntimeValueCase::Primitive,
            RuntimeValueParameter::Primitive,
            RuntimeExternal::Primitive(primitive),
        )
    }

    fn apply_list_procedure(&self) -> Self::Value {
        self.encoding
            .construct(RuntimeValueCase::ApplyListProcedure.index(), vec![], ())
            .expect("the validated apply-list constructor has no arguments")
    }

    fn view(
        &self,
        value: &Self::Value,
    ) -> Result<RuntimeValueView<A, P, Self::Value>, Self::Error> {
        let layer = self
            .encoding
            .view(value)
            .ok_or(InductiveRuntimeError::MalformedValue)?;
        match (
            RuntimeValueCase::from_index(layer.constructor),
            layer.arguments.as_slice(),
        ) {
            (
                n,
                [
                    RawArgument::External {
                        sort: RuntimeValueParameter::Atom,
                        value: RuntimeExternal::Atom(atom),
                    },
                ],
            ) if n == Some(RuntimeValueCase::Atom) => Ok(RuntimeValueView::Atom(atom.clone())),
            (Some(RuntimeValueCase::Nil), []) => Ok(RuntimeValueView::Nil),
            (
                Some(RuntimeValueCase::Cons),
                [RawArgument::Recursive(head), RawArgument::Recursive(tail)],
            ) => Ok(RuntimeValueView::Cons {
                head: head.clone(),
                tail: tail.clone(),
            }),
            (Some(RuntimeValueCase::Closure), [RawArgument::External { .. }]) => {
                Ok(RuntimeValueView::Closure)
            }
            (
                n,
                [
                    RawArgument::External {
                        sort: RuntimeValueParameter::Primitive,
                        value: RuntimeExternal::Primitive(primitive),
                    },
                ],
            ) if n == Some(RuntimeValueCase::Primitive) => {
                Ok(RuntimeValueView::Primitive(primitive.clone()))
            }
            (Some(RuntimeValueCase::ApplyListProcedure), []) => {
                Ok(RuntimeValueView::ApplyListProcedure)
            }
            _ => Err(InductiveRuntimeError::MalformedValue),
        }
    }

    fn equivalent(&self, left: &Self::Value, right: &Self::Value) -> Result<bool, Self::Error> {
        Ok(left == right)
    }
}

impl<A, C, P> LispMachineValue for InductiveRuntimeValues<A, C, P>
where
    A: Clone + PartialEq,
    C: Clone + PartialEq,
    P: Clone + PartialEq,
{
    type Closure = C;

    fn roll(
        &self,
        layer: RuntimeValueLayer<A, C, P, Self::Value>,
    ) -> Result<Self::Value, Self::Error> {
        match layer {
            RuntimeValueLayer::Atom(atom) => self.atom(atom),
            RuntimeValueLayer::Nil => Ok(self.nil()),
            RuntimeValueLayer::Cons { head, tail } => self.cons(head, tail),
            RuntimeValueLayer::Closure(closure) => self.external(
                RuntimeValueCase::Closure,
                RuntimeValueParameter::Closure,
                RuntimeExternal::Closure(closure),
            ),
            RuntimeValueLayer::Primitive(primitive) => self.primitive(primitive),
            RuntimeValueLayer::ApplyListProcedure => Ok(self.apply_list_procedure()),
        }
    }

    fn unroll(
        &self,
        value: &Self::Value,
    ) -> Result<RuntimeValueLayer<A, C, P, Self::Value>, Self::Error> {
        let layer = self
            .encoding
            .view(value)
            .ok_or(InductiveRuntimeError::MalformedValue)?;
        match (
            RuntimeValueCase::from_index(layer.constructor),
            layer.arguments.as_slice(),
        ) {
            (
                n,
                [
                    RawArgument::External {
                        sort: RuntimeValueParameter::Atom,
                        value: RuntimeExternal::Atom(atom),
                    },
                ],
            ) if n == Some(RuntimeValueCase::Atom) => Ok(RuntimeValueLayer::Atom(atom.clone())),
            (Some(RuntimeValueCase::Nil), []) => Ok(RuntimeValueLayer::Nil),
            (
                Some(RuntimeValueCase::Cons),
                [RawArgument::Recursive(head), RawArgument::Recursive(tail)],
            ) => Ok(RuntimeValueLayer::Cons {
                head: head.clone(),
                tail: tail.clone(),
            }),
            (
                n,
                [
                    RawArgument::External {
                        sort: RuntimeValueParameter::Closure,
                        value: RuntimeExternal::Closure(closure),
                    },
                ],
            ) if n == Some(RuntimeValueCase::Closure) => {
                Ok(RuntimeValueLayer::Closure(closure.clone()))
            }
            (
                n,
                [
                    RawArgument::External {
                        sort: RuntimeValueParameter::Primitive,
                        value: RuntimeExternal::Primitive(primitive),
                    },
                ],
            ) if n == Some(RuntimeValueCase::Primitive) => {
                Ok(RuntimeValueLayer::Primitive(primitive.clone()))
            }
            (Some(RuntimeValueCase::ApplyListProcedure), []) => {
                Ok(RuntimeValueLayer::ApplyListProcedure)
            }
            _ => Err(InductiveRuntimeError::MalformedValue),
        }
    }
}

impl<S, A, P> LispRuntime for InductiveRuntime<S, A, P>
where
    S: Clone + PartialEq,
    A: Clone + PartialEq,
    P: Clone + PartialEq,
{
    type Symbol = S;
    type Atom = A;
    type Datum = covalence_sexpr_api::FreeSExpr<A>;
    type Primitive = P;
    type Expr = CoreExpr<S, Self::Datum, P>;
    type Value = InductiveLispValue<A, P>;
    type Closure = InductiveClosure;
    type Environment = InductiveEnvironment<S, A, P>;
    type Error = InductiveLispRuntimeError;
    type Data = covalence_sexpr_api::Free<A>;
    type Values = InductiveRuntimeValues<A, InductiveClosure, P>;
    type Expressions = CoreSyntax<S, A, P>;
    type Closures = InductiveClosures<S, A, P>;
    type Environments = HostEnvironments<S, Self::Value>;

    fn values(&self) -> &Self::Values {
        &self.values
    }

    fn data(&self) -> &Self::Data {
        &self.data
    }

    fn expressions(&self) -> &Self::Expressions {
        &self.expressions
    }

    fn closures(&self) -> &Self::Closures {
        &self.closures
    }

    fn environments(&self) -> &Self::Environments {
        &self.environments
    }

    fn data_error(&self, error: Infallible) -> Self::Error {
        match error {}
    }

    fn value_error(&self, error: InductiveRuntimeError) -> Self::Error {
        InductiveLispRuntimeError::Value(error)
    }

    fn expression_error(&self, error: Infallible) -> Self::Error {
        match error {}
    }

    fn syntax_error(&self, error: Infallible) -> Self::Error {
        match error {}
    }

    fn closure_error(&self, error: ResourceError) -> Self::Error {
        InductiveLispRuntimeError::Resource(error)
    }

    fn environment_error(&self, error: Infallible) -> Self::Error {
        match error {}
    }
}

impl<S, A, P> LispRuntimeSnapshot for InductiveRuntime<S, A, P>
where
    S: Clone + PartialEq,
    A: Clone + PartialEq,
    P: Clone + PartialEq,
{
    fn replay_snapshot(&self) -> Self {
        Self {
            data: self.data.clone(),
            values: self.values.clone(),
            expressions: self.expressions.clone(),
            closures: InductiveClosures {
                closures: self.closures.closures.snapshot(),
            },
            environments: self.environments.clone(),
        }
    }
}

#[cfg(test)]
mod tests {
    use covalence_sexpr_api::{Free, FreeSExpr};

    use super::*;
    use crate::{inject_datum, project_datum};

    type Values = InductiveRuntimeValues<&'static str, u32, &'static str>;

    #[test]
    fn realizes_every_runtime_constructor_and_lambek_round_trip() {
        let values = Values::new();
        let atom = values.atom("a").unwrap();
        let primitive = values.primitive("cons").unwrap();
        let pair = values.cons(atom.clone(), primitive.clone()).unwrap();

        for layer in [
            RuntimeValueLayer::Atom("a"),
            RuntimeValueLayer::Nil,
            RuntimeValueLayer::Cons {
                head: atom,
                tail: primitive,
            },
            RuntimeValueLayer::Closure(7),
            RuntimeValueLayer::Primitive("car"),
            RuntimeValueLayer::ApplyListProcedure,
        ] {
            let value = values.roll(layer.clone()).unwrap();
            assert_eq!(values.unroll(&value).unwrap(), layer);
        }

        assert!(matches!(
            values.view(&pair).unwrap(),
            RuntimeValueView::Cons { .. }
        ));
    }

    #[test]
    fn shares_the_inductive_datum_embedding() {
        let data = Free::<&str>::new();
        let values = Values::new();
        let datum = FreeSExpr::list([
            FreeSExpr::Atom("one"),
            FreeSExpr::list([FreeSExpr::Atom("two")]),
        ]);

        let value = inject_datum(&data, &values, &datum).unwrap();
        assert_eq!(project_datum(&data, &values, &value).unwrap(), Some(datum));
        assert_eq!(
            project_datum(&data, &values, &values.primitive("car").unwrap()).unwrap(),
            None
        );
    }
}
