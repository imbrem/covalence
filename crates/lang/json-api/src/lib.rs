//! RFC 8259 JSON value vocabulary.
//!
//! This crate intentionally contains no byte parser. Numbers are exact finite
//! decimals, never binary floating-point values. Parsed object member
//! sequences are distinct from semantic JSON objects: sequence order and
//! duplicate names are syntax observations, not silently chosen value
//! semantics.

use covalence_decimal_api::CanonicalDecimal;
use covalence_inductive::{FieldSpec, PolynomialSpec, Position, VariantCase};

/// A JSON string code point.
///
/// RFC 8259's ABNF permits escaped unpaired UTF-16 surrogates, so using Rust
/// `String` alone would reject syntactically permitted JSON strings.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum JsonCodePoint {
    Scalar(char),
    UnpairedSurrogate(JsonSurrogate),
}

/// A UTF-16 surrogate code unit that was not paired during JSON decoding.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct JsonSurrogate(u16);

impl JsonSurrogate {
    pub fn new(code_unit: u16) -> Option<Self> {
        (0xd800..=0xdfff)
            .contains(&code_unit)
            .then_some(Self(code_unit))
    }

    pub fn code_unit(self) -> u16 {
        self.0
    }
}

/// A sequence of JSON string code points.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Default)]
pub struct JsonString(pub Vec<JsonCodePoint>);

impl From<&str> for JsonString {
    fn from(value: &str) -> Self {
        Self(value.chars().map(JsonCodePoint::Scalar).collect())
    }
}

/// An object member as it occurs in parsed syntax.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct JsonMember<D = CanonicalDecimal> {
    pub name: JsonString,
    pub value: JsonValue<D>,
}

/// Ordered parsed members. Duplicate names are retained.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct JsonMemberSequence<D = CanonicalDecimal>(pub Vec<JsonMember<D>>);

/// A semantic object with unique names.
///
/// Storage order is retained for deterministic traversal, but equality ignores
/// member order. Construction rejects duplicate names.
#[derive(Clone, Debug)]
pub struct JsonObject<D = CanonicalDecimal>(Vec<JsonMember<D>>);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DuplicateName(pub JsonString);

impl<D> JsonObject<D> {
    pub fn new(members: Vec<JsonMember<D>>) -> Result<Self, DuplicateName> {
        for (index, member) in members.iter().enumerate() {
            if members[..index]
                .iter()
                .any(|prior| prior.name == member.name)
            {
                return Err(DuplicateName(member.name.clone()));
            }
        }
        Ok(Self(members))
    }

    pub fn members(&self) -> &[JsonMember<D>] {
        &self.0
    }
}

impl<D: PartialEq> PartialEq for JsonObject<D> {
    fn eq(&self, other: &Self) -> bool {
        self.0.len() == other.0.len()
            && self.0.iter().all(|member| {
                other
                    .0
                    .iter()
                    .find(|candidate| candidate.name == member.name)
                    .is_some_and(|candidate| candidate.value == member.value)
            })
    }
}

impl<D: Eq> Eq for JsonObject<D> {}

/// A semantic JSON value, parameterized by an exact decimal representation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum JsonValue<D = CanonicalDecimal> {
    Null,
    Bool(bool),
    Number(D),
    String(JsonString),
    Array(Vec<JsonValue<D>>),
    Object(JsonObject<D>),
}

/// Policy for interpreting a parsed member sequence as a semantic object.
pub trait ObjectInterpretation<D> {
    type Error;

    fn interpret(&self, members: JsonMemberSequence<D>) -> Result<JsonObject<D>, Self::Error>;
}

/// Reject duplicate names, retaining the source order of unique members.
pub struct RejectDuplicates;

impl<D> ObjectInterpretation<D> for RejectDuplicates {
    type Error = DuplicateName;

    fn interpret(&self, members: JsonMemberSequence<D>) -> Result<JsonObject<D>, Self::Error> {
        JsonObject::new(members.0)
    }
}

/// External parameters required by the current first-order polynomial adapter.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum JsonParameter {
    Bool,
    Decimal,
    String,
    Array,
    Object,
}

/// JSON's top-level sum shape in the current inductive polynomial vocabulary.
///
/// Array and object are parameters because the current vocabulary supports
/// only direct recursion, not composition with list/member functors.
// TODO(cov:json.polynomial-composition, major): Replace Array/Object parameters with composed list and member polynomial functors once covalence-inductive supports functor composition.
pub fn json_value_polynomial() -> PolynomialSpec<JsonParameter> {
    let unary = |name, parameter| {
        VariantCase::new(
            name,
            vec![FieldSpec::new("value", Position::Param(parameter))],
        )
    };
    PolynomialSpec::new(
        "JsonValue",
        vec![
            VariantCase::nullary("Null"),
            unary("Bool", JsonParameter::Bool),
            unary("Number", JsonParameter::Decimal),
            unary("String", JsonParameter::String),
            unary("Array", JsonParameter::Array),
            unary("Object", JsonParameter::Object),
        ],
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn member(name: &str, value: JsonValue) -> JsonMember {
        JsonMember {
            name: name.into(),
            value,
        }
    }

    #[test]
    fn semantic_object_equality_ignores_order() {
        let left = JsonObject::new(vec![
            member("a", JsonValue::Null),
            member("b", JsonValue::Bool(true)),
        ])
        .unwrap();
        let right = JsonObject::new(vec![
            member("b", JsonValue::Bool(true)),
            member("a", JsonValue::Null),
        ])
        .unwrap();
        assert_eq!(left, right);
    }

    #[test]
    fn parsed_members_retain_duplicates_but_semantic_object_rejects_them() {
        let parsed = JsonMemberSequence(vec![
            member("x", JsonValue::Null),
            member("x", JsonValue::Bool(false)),
        ]);
        assert_eq!(parsed.0.len(), 2);
        assert!(RejectDuplicates.interpret(parsed).is_err());
    }

    #[test]
    fn polynomial_adapter_is_valid_and_nonrecursive() {
        let spec = json_value_polynomial();
        assert!(spec.validate().is_ok());
        assert!(!spec.is_recursive());
    }
}
