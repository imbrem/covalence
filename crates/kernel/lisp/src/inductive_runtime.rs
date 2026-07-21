//! Runtime values realized through the shared `data/inductive` backend.
//!
//! This is the representation-stress backend for [`crate::runtime_value_fixpoint`].
//! Unlike the direct host enum and opaque arena, its values are generic tagged
//! inductive values. The evaluator-facing API is nevertheless exactly
//! [`crate::LispMachineValue`].

use covalence_sexpr_api::{
    EncodingError, InductiveRepresentation, RawArgument, RawEncoding, RawInductive,
};

use crate::{
    LispMachineValue, LispValue, RuntimeValueCase, RuntimeValueLayer, RuntimeValueParameter,
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
