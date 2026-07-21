//! Concatenative runtime values realized through `data/inductive`.

use covalence_sexpr_api::{
    EncodingError, InductiveRepresentation, RawArgument, RawEncoding, RawInductive,
};

use crate::{
    StackMachineValue, StackValue, StackValueCase, StackValueLayer, StackValueParameter,
    StackValueView, stack_value_fixpoint,
};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum StackValueExternal<D, C> {
    Datum(D),
    Closure(C),
}

pub type InductiveStackValue<D, C> = RawInductive<StackValueParameter, StackValueExternal<D, C>>;

#[derive(Clone, Debug)]
pub struct InductiveStackValues<D, C> {
    encoding: RawEncoding<StackValueParameter, StackValueExternal<D, C>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InductiveStackValueError {
    Encoding(EncodingError),
    MalformedValue,
}

impl From<EncodingError> for InductiveStackValueError {
    fn from(error: EncodingError) -> Self {
        Self::Encoding(error)
    }
}

impl<D, C> Default for InductiveStackValues<D, C> {
    fn default() -> Self {
        Self {
            encoding: RawEncoding::from_inductive_fixpoint(stack_value_fixpoint()),
        }
    }
}

impl<D, C> InductiveStackValues<D, C> {
    pub fn new() -> Self {
        Self::default()
    }

    fn external(
        &self,
        case: StackValueCase,
        sort: StackValueParameter,
        value: StackValueExternal<D, C>,
    ) -> Result<InductiveStackValue<D, C>, InductiveStackValueError>
    where
        D: Clone,
        C: Clone,
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

impl<D: Clone + PartialEq, C: Clone + PartialEq> StackValue for InductiveStackValues<D, C> {
    type Datum = D;
    type Value = InductiveStackValue<D, C>;
    type Error = InductiveStackValueError;

    fn datum(&self, datum: D) -> Result<Self::Value, Self::Error> {
        self.external(
            StackValueCase::Datum,
            StackValueParameter::Datum,
            StackValueExternal::Datum(datum),
        )
    }

    fn view(&self, value: &Self::Value) -> Result<StackValueView<D>, Self::Error> {
        match self.unroll(value)? {
            StackValueLayer::Datum(datum) => Ok(StackValueView::Datum(datum)),
            StackValueLayer::Closure(_) => Ok(StackValueView::Closure),
        }
    }

    fn equivalent(&self, left: &Self::Value, right: &Self::Value) -> Result<bool, Self::Error> {
        Ok(left == right)
    }
}

impl<D: Clone + PartialEq, C: Clone + PartialEq> StackMachineValue for InductiveStackValues<D, C> {
    type Closure = C;

    fn roll(&self, layer: StackValueLayer<D, C>) -> Result<Self::Value, Self::Error> {
        match layer {
            StackValueLayer::Datum(datum) => self.datum(datum),
            StackValueLayer::Closure(closure) => self.external(
                StackValueCase::Closure,
                StackValueParameter::Closure,
                StackValueExternal::Closure(closure),
            ),
        }
    }

    fn unroll(&self, value: &Self::Value) -> Result<StackValueLayer<D, C>, Self::Error> {
        let layer = self
            .encoding
            .view(value)
            .ok_or(InductiveStackValueError::MalformedValue)?;
        match (
            StackValueCase::from_index(layer.constructor),
            layer.arguments.as_slice(),
        ) {
            (
                Some(StackValueCase::Datum),
                [
                    RawArgument::External {
                        sort: StackValueParameter::Datum,
                        value: StackValueExternal::Datum(datum),
                    },
                ],
            ) => Ok(StackValueLayer::Datum(datum.clone())),
            (
                Some(StackValueCase::Closure),
                [
                    RawArgument::External {
                        sort: StackValueParameter::Closure,
                        value: StackValueExternal::Closure(closure),
                    },
                ],
            ) => Ok(StackValueLayer::Closure(closure.clone())),
            _ => Err(InductiveStackValueError::MalformedValue),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn stack_values_round_trip_through_the_inductive_backend() {
        let values = InductiveStackValues::<&str, u32>::new();
        let datum = values.roll(StackValueLayer::Datum("x")).unwrap();
        let closure = values.roll(StackValueLayer::Closure(7)).unwrap();
        assert_eq!(values.unroll(&datum).unwrap(), StackValueLayer::Datum("x"));
        assert_eq!(
            values.unroll(&closure).unwrap(),
            StackValueLayer::Closure(7)
        );
        assert_eq!(values.view(&datum).unwrap(), StackValueView::Datum("x"));
        assert_eq!(values.view(&closure).unwrap(), StackValueView::Closure);
    }
}
