//! Representation-independent JSON capabilities.
//!
//! The traits are deliberately split by capability.  A backend may expose
//! scalar constructors without claiming arrays, objects, decidable equality,
//! or proof laws.  In particular, an inductive backend can expose the
//! constructor layer it has realized before nested fixpoints are available.

use core::convert::Infallible;
use core::marker::PhantomData;

use crate::{
    DuplicateName, JsonMember, JsonObject, JsonString, JsonValue, ObservedSemanticEquality,
    ParsedJsonMember, ParsedJsonValue, json_value_family,
};
use covalence_inductive::{
    DatatypeFamilyExpr, SymbolicFamilyBackend, SymbolicFamilyObject, ValidatedDatatypeFamily,
    interpret_family,
};

/// The six observable JSON value alternatives, with backend-owned payloads.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum JsonView<N, S, A, O> {
    Null,
    Bool(bool),
    Number(N),
    String(S),
    Array(A),
    Object(O),
}

/// Carrier types of one semantic JSON representation.
pub trait JsonRepresentation {
    type Value;
    type Number;
    type String;
    type Array;
    type Object;
    type Error;

    /// Observe one constructor layer without choosing aggregate storage.
    fn view(
        &self,
        value: &Self::Value,
    ) -> Result<JsonView<Self::Number, Self::String, Self::Array, Self::Object>, Self::Error>;
}

/// Scalar JSON construction.  Kept separate from recursive aggregates so
/// partial inductive implementations can advertise exactly what they support.
pub trait JsonScalarConstructors: JsonRepresentation {
    fn null(&self) -> Result<Self::Value, Self::Error>;
    fn boolean(&self, value: bool) -> Result<Self::Value, Self::Error>;
    fn number(&self, value: Self::Number) -> Result<Self::Value, Self::Error>;
    fn string(&self, value: Self::String) -> Result<Self::Value, Self::Error>;
}

/// Recursive JSON construction from already-realized aggregate carriers.
pub trait JsonAggregateConstructors: JsonRepresentation {
    fn array(&self, value: Self::Array) -> Result<Self::Value, Self::Error>;
    fn object(&self, value: Self::Object) -> Result<Self::Value, Self::Error>;
}

/// Abstract finite sequences used by JSON arrays.
pub trait JsonArrays: JsonRepresentation {
    fn array_from_values(
        &self,
        values: impl IntoIterator<Item = Self::Value>,
    ) -> Result<Self::Array, Self::Error>;
    fn array_values(&self, array: &Self::Array) -> Result<Vec<Self::Value>, Self::Error>;
}

/// Semantic JSON objects.  Implementations must reject duplicate names;
/// member order is not part of semantic equality.
pub trait JsonSemanticObjects: JsonRepresentation {
    fn object_from_members(
        &self,
        members: impl IntoIterator<Item = (Self::String, Self::Value)>,
    ) -> Result<Self::Object, Self::Error>;
    fn object_members(
        &self,
        object: &Self::Object,
    ) -> Result<Vec<(Self::String, Self::Value)>, Self::Error>;
}

/// Decidable semantic equality is optional and carries no theorem authority.
pub trait JsonDecidableEquality: JsonRepresentation {
    fn equal(&self, left: &Self::Value, right: &Self::Value) -> Result<bool, Self::Error>;
}

/// Evidence-bearing partial equivalence relation for semantic JSON values.
///
/// A proof backend may use an unforgeable theorem as `Evidence`; the host
/// reference implementation returns an observation token.
pub trait JsonPer: JsonRepresentation {
    type Evidence;
    fn related(
        &self,
        left: &Self::Value,
        right: &Self::Value,
    ) -> Result<Option<Self::Evidence>, Self::Error>;
}

/// Optional evidence for constructor/view computation laws.
pub trait JsonConstructorLaws: JsonScalarConstructors {
    type Evidence;
    fn view_null(&self) -> Result<Self::Evidence, Self::Error>;
    fn view_boolean(&self, value: bool) -> Result<Self::Evidence, Self::Error>;
    fn view_number(&self, value: Self::Number) -> Result<Self::Evidence, Self::Error>;
    fn view_string(&self, value: Self::String) -> Result<Self::Evidence, Self::Error>;
}

/// The six alternatives of decoded JSON syntax.  Objects here are ordered and
/// may contain duplicate names.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum JsonSyntaxView<N, S, A, O> {
    Null,
    Bool(bool),
    Number(N),
    String(S),
    Array(A),
    Object(O),
}

/// Separate carrier family for decoded, policy-free JSON syntax.
pub trait JsonSyntaxRepresentation {
    type Value;
    type Number;
    type String;
    type Array;
    type OrderedObject;
    type Error;

    fn syntax_view(
        &self,
        value: &Self::Value,
    ) -> Result<
        JsonSyntaxView<Self::Number, Self::String, Self::Array, Self::OrderedObject>,
        Self::Error,
    >;

    fn syntax_null(&self) -> Result<Self::Value, Self::Error>;
    fn syntax_boolean(&self, value: bool) -> Result<Self::Value, Self::Error>;
    fn syntax_number(&self, value: Self::Number) -> Result<Self::Value, Self::Error>;
    fn syntax_string(&self, value: Self::String) -> Result<Self::Value, Self::Error>;
    fn syntax_array(&self, value: Self::Array) -> Result<Self::Value, Self::Error>;
    fn syntax_object(&self, value: Self::OrderedObject) -> Result<Self::Value, Self::Error>;
}

/// Ordered, duplicate-preserving syntax aggregate operations.
pub trait JsonSyntaxAggregates: JsonSyntaxRepresentation {
    fn syntax_array_from_values(
        &self,
        values: impl IntoIterator<Item = Self::Value>,
    ) -> Result<Self::Array, Self::Error>;
    fn syntax_array_values(&self, array: &Self::Array) -> Result<Vec<Self::Value>, Self::Error>;
    fn ordered_object_from_members(
        &self,
        members: impl IntoIterator<Item = (Self::String, Self::Value)>,
    ) -> Result<Self::OrderedObject, Self::Error>;
    fn ordered_object_members(
        &self,
        object: &Self::OrderedObject,
    ) -> Result<Vec<(Self::String, Self::Value)>, Self::Error>;
}

/// The existing Rust enum backend, parameterized by exact decimal storage.
#[derive(Clone, Copy, Debug, Default)]
pub struct ReferenceJson<D>(PhantomData<fn() -> D>);

impl<D> ReferenceJson<D> {
    pub const fn new() -> Self {
        Self(PhantomData)
    }
}

impl<D: Clone> JsonRepresentation for ReferenceJson<D> {
    type Value = JsonValue<D>;
    type Number = D;
    type String = JsonString;
    type Array = Vec<JsonValue<D>>;
    type Object = JsonObject<D>;
    type Error = DuplicateName;

    fn view(
        &self,
        value: &Self::Value,
    ) -> Result<JsonView<D, JsonString, Self::Array, Self::Object>, Self::Error> {
        Ok(match value {
            JsonValue::Null => JsonView::Null,
            JsonValue::Bool(value) => JsonView::Bool(*value),
            JsonValue::Number(value) => JsonView::Number(value.clone()),
            JsonValue::String(value) => JsonView::String(value.clone()),
            JsonValue::Array(value) => JsonView::Array(value.clone()),
            JsonValue::Object(value) => JsonView::Object(value.clone()),
        })
    }
}

impl<D: Clone> JsonScalarConstructors for ReferenceJson<D> {
    fn null(&self) -> Result<Self::Value, Self::Error> {
        Ok(JsonValue::Null)
    }
    fn boolean(&self, value: bool) -> Result<Self::Value, Self::Error> {
        Ok(JsonValue::Bool(value))
    }
    fn number(&self, value: D) -> Result<Self::Value, Self::Error> {
        Ok(JsonValue::Number(value))
    }
    fn string(&self, value: JsonString) -> Result<Self::Value, Self::Error> {
        Ok(JsonValue::String(value))
    }
}

impl<D: Clone> JsonAggregateConstructors for ReferenceJson<D> {
    fn array(&self, value: Self::Array) -> Result<Self::Value, Self::Error> {
        Ok(JsonValue::Array(value))
    }
    fn object(&self, value: Self::Object) -> Result<Self::Value, Self::Error> {
        Ok(JsonValue::Object(value))
    }
}

impl<D: Clone> JsonArrays for ReferenceJson<D> {
    fn array_from_values(
        &self,
        values: impl IntoIterator<Item = Self::Value>,
    ) -> Result<Self::Array, Self::Error> {
        Ok(values.into_iter().collect())
    }
    fn array_values(&self, array: &Self::Array) -> Result<Vec<Self::Value>, Self::Error> {
        Ok(array.clone())
    }
}

impl<D: Clone> JsonSemanticObjects for ReferenceJson<D> {
    fn object_from_members(
        &self,
        members: impl IntoIterator<Item = (Self::String, Self::Value)>,
    ) -> Result<Self::Object, Self::Error> {
        JsonObject::new(
            members
                .into_iter()
                .map(|(name, value)| JsonMember { name, value })
                .collect(),
        )
    }
    fn object_members(
        &self,
        object: &Self::Object,
    ) -> Result<Vec<(Self::String, Self::Value)>, Self::Error> {
        Ok(object
            .members()
            .iter()
            .map(|member| (member.name.clone(), member.value.clone()))
            .collect())
    }
}

impl<D: Clone + PartialEq> JsonDecidableEquality for ReferenceJson<D> {
    fn equal(&self, left: &Self::Value, right: &Self::Value) -> Result<bool, Self::Error> {
        Ok(left == right)
    }
}

impl<D: Clone + PartialEq> JsonPer for ReferenceJson<D> {
    type Evidence = ObservedSemanticEquality;
    fn related(
        &self,
        left: &Self::Value,
        right: &Self::Value,
    ) -> Result<Option<Self::Evidence>, Self::Error> {
        Ok((left == right).then_some(ObservedSemanticEquality))
    }
}

impl<D: Clone + PartialEq> JsonConstructorLaws for ReferenceJson<D> {
    type Evidence = ObservedSemanticEquality;
    fn view_null(&self) -> Result<Self::Evidence, Self::Error> {
        Ok(ObservedSemanticEquality)
    }
    fn view_boolean(&self, _value: bool) -> Result<Self::Evidence, Self::Error> {
        Ok(ObservedSemanticEquality)
    }
    fn view_number(&self, _value: D) -> Result<Self::Evidence, Self::Error> {
        Ok(ObservedSemanticEquality)
    }
    fn view_string(&self, _value: JsonString) -> Result<Self::Evidence, Self::Error> {
        Ok(ObservedSemanticEquality)
    }
}

impl<D: Clone> JsonSyntaxRepresentation for ReferenceJson<D> {
    type Value = ParsedJsonValue<D>;
    type Number = D;
    type String = JsonString;
    type Array = Vec<ParsedJsonValue<D>>;
    type OrderedObject = Vec<ParsedJsonMember<D>>;
    type Error = Infallible;

    fn syntax_view(
        &self,
        value: &Self::Value,
    ) -> Result<JsonSyntaxView<D, JsonString, Self::Array, Self::OrderedObject>, Self::Error> {
        Ok(match value {
            ParsedJsonValue::Null => JsonSyntaxView::Null,
            ParsedJsonValue::Bool(value) => JsonSyntaxView::Bool(*value),
            ParsedJsonValue::Number(value) => JsonSyntaxView::Number(value.clone()),
            ParsedJsonValue::String(value) => JsonSyntaxView::String(value.clone()),
            ParsedJsonValue::Array(value) => JsonSyntaxView::Array(value.clone()),
            ParsedJsonValue::Object(value) => JsonSyntaxView::Object(value.clone()),
        })
    }
    fn syntax_null(&self) -> Result<Self::Value, Self::Error> {
        Ok(ParsedJsonValue::Null)
    }
    fn syntax_boolean(&self, value: bool) -> Result<Self::Value, Self::Error> {
        Ok(ParsedJsonValue::Bool(value))
    }
    fn syntax_number(&self, value: D) -> Result<Self::Value, Self::Error> {
        Ok(ParsedJsonValue::Number(value))
    }
    fn syntax_string(&self, value: JsonString) -> Result<Self::Value, Self::Error> {
        Ok(ParsedJsonValue::String(value))
    }
    fn syntax_array(&self, value: Self::Array) -> Result<Self::Value, Self::Error> {
        Ok(ParsedJsonValue::Array(value))
    }
    fn syntax_object(&self, value: Self::OrderedObject) -> Result<Self::Value, Self::Error> {
        Ok(ParsedJsonValue::Object(value))
    }
}

impl<D: Clone> JsonSyntaxAggregates for ReferenceJson<D> {
    fn syntax_array_from_values(
        &self,
        values: impl IntoIterator<Item = Self::Value>,
    ) -> Result<Self::Array, Self::Error> {
        Ok(values.into_iter().collect())
    }
    fn syntax_array_values(&self, array: &Self::Array) -> Result<Vec<Self::Value>, Self::Error> {
        Ok(array.clone())
    }
    fn ordered_object_from_members(
        &self,
        members: impl IntoIterator<Item = (Self::String, Self::Value)>,
    ) -> Result<Self::OrderedObject, Self::Error> {
        Ok(members
            .into_iter()
            .map(|(name, value)| ParsedJsonMember { name, value })
            .collect())
    }
    fn ordered_object_members(
        &self,
        object: &Self::OrderedObject,
    ) -> Result<Vec<(Self::String, Self::Value)>, Self::Error> {
        Ok(object
            .iter()
            .map(|member| (member.name.clone(), member.value.clone()))
            .collect())
    }
}

/// The reference least-fixpoint list used by the inductive JSON backend.
///
/// This intentionally does not reuse `Vec`: `Nil + A × X` mirrors the nested
/// `μ` nodes in [`json_value_family`] and makes the stacking boundary visible.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InductiveJsonList<A> {
    Nil,
    Cons(A, Box<Self>),
}

impl<A> InductiveJsonList<A> {
    pub fn from_values(values: impl IntoIterator<Item = A>) -> Self {
        values
            .into_iter()
            .collect::<Vec<_>>()
            .into_iter()
            .rev()
            .fold(Self::Nil, |tail, head| Self::Cons(head, Box::new(tail)))
    }

    pub fn iter(&self) -> InductiveJsonListIter<'_, A> {
        InductiveJsonListIter { next: Some(self) }
    }
}

pub struct InductiveJsonListIter<'a, A> {
    next: Option<&'a InductiveJsonList<A>>,
}

impl<'a, A> Iterator for InductiveJsonListIter<'a, A> {
    type Item = &'a A;

    fn next(&mut self) -> Option<Self::Item> {
        match self.next.take()? {
            InductiveJsonList::Nil => None,
            InductiveJsonList::Cons(head, tail) => {
                self.next = Some(tail);
                Some(head)
            }
        }
    }
}

impl<A: Clone> InductiveJsonList<A> {
    pub fn values(&self) -> Vec<A> {
        self.iter().cloned().collect()
    }
}

/// Semantic object subset of the ordered inductive member-list carrier.
#[derive(Clone, Debug)]
pub struct InductiveJsonObject<D, S>(Box<InductiveJsonList<(S, InductiveJsonValue<D, S>)>>);

impl<D: PartialEq, S: PartialEq> PartialEq for InductiveJsonObject<D, S> {
    fn eq(&self, other: &Self) -> bool {
        self.0.iter().count() == other.0.iter().count()
            && self.0.iter().all(|(name, value)| {
                other
                    .0
                    .iter()
                    .find(|(other, _)| other == name)
                    .is_some_and(|(_, other)| other == value)
            })
    }
}

impl<D: Eq, S: Eq> Eq for InductiveJsonObject<D, S> {}

/// Full host realization of the nested least-fixpoint JSON family.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InductiveJsonValue<D, S> {
    Null,
    Bool(bool),
    Number(D),
    String(S),
    Array(Box<InductiveJsonList<InductiveJsonValue<D, S>>>),
    Object(InductiveJsonObject<D, S>),
}

/// Duplicate-name failure at the semantic-subset boundary.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InductiveJsonDuplicateName<S>(pub S);

/// Decoded syntax over the same inductive list implementation.
///
/// Unlike [`InductiveJsonValue`], the object branch is the raw ordered carrier
/// and therefore retains duplicates.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InductiveParsedJsonValue<D, S> {
    Null,
    Bool(bool),
    Number(D),
    String(S),
    Array(Box<InductiveJsonList<InductiveParsedJsonValue<D, S>>>),
    Object(Box<InductiveJsonList<(S, InductiveParsedJsonValue<D, S>)>>),
}

/// A concrete proof-free A0007 backend stacked on A0004's scoped family API.
///
/// The Rust carriers above are the host interpretation of the two nested
/// least fixpoints. [`family_layer_at`](Self::family_layer_at) runs the shared
/// A0004 interpretation pipeline, so the declared and implemented nesting
/// remain independently testable. This backend makes no theorem claim.
#[derive(Clone, Copy, Debug, Default)]
pub struct InductiveJsonLayer<D, S>(PhantomData<fn() -> (D, S)>);

impl<D, S> InductiveJsonLayer<D, S> {
    pub const fn new() -> Self {
        Self(PhantomData)
    }

    /// The A0004 declaration this host representation implements.
    pub fn family(&self) -> DatatypeFamilyExpr<crate::JsonParameter> {
        json_value_family()
    }

    /// Interpret `JsonF(X)` through A0004, including both nested list
    /// fixpoints, at a caller-supplied symbolic carrier `X`.
    pub fn family_layer_at(
        &self,
        variable: &SymbolicFamilyObject<crate::JsonParameter>,
    ) -> SymbolicFamilyObject<crate::JsonParameter> {
        let family = ValidatedDatatypeFamily::try_from(self.family())
            .expect("the public JSON datatype family is well scoped");
        interpret_family(&SymbolicFamilyBackend, &family, variable)
            .expect("the symbolic family backend is infallible")
    }
}

impl<D: Clone, S: Clone> JsonRepresentation for InductiveJsonLayer<D, S> {
    type Value = InductiveJsonValue<D, S>;
    type Number = D;
    type String = S;
    type Array = Box<InductiveJsonList<Self::Value>>;
    type Object = InductiveJsonObject<D, S>;
    type Error = InductiveJsonDuplicateName<S>;

    fn view(
        &self,
        value: &Self::Value,
    ) -> Result<JsonView<D, S, Self::Array, Self::Object>, Self::Error> {
        Ok(match value {
            InductiveJsonValue::Null => JsonView::Null,
            InductiveJsonValue::Bool(value) => JsonView::Bool(*value),
            InductiveJsonValue::Number(value) => JsonView::Number(value.clone()),
            InductiveJsonValue::String(value) => JsonView::String(value.clone()),
            InductiveJsonValue::Array(value) => JsonView::Array(value.clone()),
            InductiveJsonValue::Object(value) => JsonView::Object(value.clone()),
        })
    }
}

impl<D: Clone, S: Clone> JsonScalarConstructors for InductiveJsonLayer<D, S> {
    fn null(&self) -> Result<Self::Value, Self::Error> {
        Ok(InductiveJsonValue::Null)
    }
    fn boolean(&self, value: bool) -> Result<Self::Value, Self::Error> {
        Ok(InductiveJsonValue::Bool(value))
    }
    fn number(&self, value: D) -> Result<Self::Value, Self::Error> {
        Ok(InductiveJsonValue::Number(value))
    }
    fn string(&self, value: S) -> Result<Self::Value, Self::Error> {
        Ok(InductiveJsonValue::String(value))
    }
}

impl<D: Clone, S: Clone> JsonArrays for InductiveJsonLayer<D, S> {
    fn array_from_values(
        &self,
        values: impl IntoIterator<Item = Self::Value>,
    ) -> Result<Self::Array, Self::Error> {
        Ok(Box::new(InductiveJsonList::from_values(values)))
    }

    fn array_values(&self, array: &Self::Array) -> Result<Vec<Self::Value>, Self::Error> {
        Ok(array.values())
    }
}

impl<D: Clone, S: Clone> JsonAggregateConstructors for InductiveJsonLayer<D, S> {
    fn array(&self, value: Self::Array) -> Result<Self::Value, Self::Error> {
        Ok(InductiveJsonValue::Array(value))
    }

    fn object(&self, value: Self::Object) -> Result<Self::Value, Self::Error> {
        Ok(InductiveJsonValue::Object(value))
    }
}

impl<D: Clone, S: Clone + PartialEq> JsonSemanticObjects for InductiveJsonLayer<D, S> {
    fn object_from_members(
        &self,
        members: impl IntoIterator<Item = (Self::String, Self::Value)>,
    ) -> Result<Self::Object, Self::Error> {
        let members = members.into_iter().collect::<Vec<_>>();
        for (index, (name, _)) in members.iter().enumerate() {
            if members[..index].iter().any(|(seen, _)| seen == name) {
                return Err(InductiveJsonDuplicateName(name.clone()));
            }
        }
        Ok(InductiveJsonObject(Box::new(
            InductiveJsonList::from_values(members),
        )))
    }

    fn object_members(
        &self,
        object: &Self::Object,
    ) -> Result<Vec<(Self::String, Self::Value)>, Self::Error> {
        Ok(object.0.values())
    }
}

impl<D: Clone + PartialEq, S: Clone + PartialEq> JsonDecidableEquality
    for InductiveJsonLayer<D, S>
{
    fn equal(&self, left: &Self::Value, right: &Self::Value) -> Result<bool, Self::Error> {
        Ok(left == right)
    }
}

impl<D: Clone + PartialEq, S: Clone + PartialEq> JsonPer for InductiveJsonLayer<D, S> {
    type Evidence = ObservedSemanticEquality;

    fn related(
        &self,
        left: &Self::Value,
        right: &Self::Value,
    ) -> Result<Option<Self::Evidence>, Self::Error> {
        Ok((left == right).then_some(ObservedSemanticEquality))
    }
}

impl<D: Clone + PartialEq, S: Clone + PartialEq> JsonConstructorLaws for InductiveJsonLayer<D, S> {
    type Evidence = ObservedSemanticEquality;

    fn view_null(&self) -> Result<Self::Evidence, Self::Error> {
        Ok(ObservedSemanticEquality)
    }
    fn view_boolean(&self, _value: bool) -> Result<Self::Evidence, Self::Error> {
        Ok(ObservedSemanticEquality)
    }
    fn view_number(&self, _value: D) -> Result<Self::Evidence, Self::Error> {
        Ok(ObservedSemanticEquality)
    }
    fn view_string(&self, _value: S) -> Result<Self::Evidence, Self::Error> {
        Ok(ObservedSemanticEquality)
    }
}

impl<D: Clone, S: Clone> JsonSyntaxRepresentation for InductiveJsonLayer<D, S> {
    type Value = InductiveParsedJsonValue<D, S>;
    type Number = D;
    type String = S;
    type Array = Box<InductiveJsonList<Self::Value>>;
    type OrderedObject = Box<InductiveJsonList<(S, Self::Value)>>;
    type Error = Infallible;

    fn syntax_view(
        &self,
        value: &Self::Value,
    ) -> Result<
        JsonSyntaxView<Self::Number, Self::String, Self::Array, Self::OrderedObject>,
        Self::Error,
    > {
        Ok(match value {
            InductiveParsedJsonValue::Null => JsonSyntaxView::Null,
            InductiveParsedJsonValue::Bool(value) => JsonSyntaxView::Bool(*value),
            InductiveParsedJsonValue::Number(value) => JsonSyntaxView::Number(value.clone()),
            InductiveParsedJsonValue::String(value) => JsonSyntaxView::String(value.clone()),
            InductiveParsedJsonValue::Array(value) => JsonSyntaxView::Array(value.clone()),
            InductiveParsedJsonValue::Object(value) => JsonSyntaxView::Object(value.clone()),
        })
    }

    fn syntax_null(&self) -> Result<Self::Value, Self::Error> {
        Ok(InductiveParsedJsonValue::Null)
    }
    fn syntax_boolean(&self, value: bool) -> Result<Self::Value, Self::Error> {
        Ok(InductiveParsedJsonValue::Bool(value))
    }
    fn syntax_number(&self, value: D) -> Result<Self::Value, Self::Error> {
        Ok(InductiveParsedJsonValue::Number(value))
    }
    fn syntax_string(&self, value: S) -> Result<Self::Value, Self::Error> {
        Ok(InductiveParsedJsonValue::String(value))
    }
    fn syntax_array(&self, value: Self::Array) -> Result<Self::Value, Self::Error> {
        Ok(InductiveParsedJsonValue::Array(value))
    }
    fn syntax_object(&self, value: Self::OrderedObject) -> Result<Self::Value, Self::Error> {
        Ok(InductiveParsedJsonValue::Object(value))
    }
}

impl<D: Clone, S: Clone> JsonSyntaxAggregates for InductiveJsonLayer<D, S> {
    fn syntax_array_from_values(
        &self,
        values: impl IntoIterator<Item = Self::Value>,
    ) -> Result<Self::Array, Self::Error> {
        Ok(Box::new(InductiveJsonList::from_values(values)))
    }

    fn syntax_array_values(&self, array: &Self::Array) -> Result<Vec<Self::Value>, Self::Error> {
        Ok(array.values())
    }

    fn ordered_object_from_members(
        &self,
        members: impl IntoIterator<Item = (Self::String, Self::Value)>,
    ) -> Result<Self::OrderedObject, Self::Error> {
        Ok(Box::new(InductiveJsonList::from_values(members)))
    }

    fn ordered_object_members(
        &self,
        object: &Self::OrderedObject,
    ) -> Result<Vec<(Self::String, Self::Value)>, Self::Error> {
        Ok(object.values())
    }
}

// TODO(cov:json.inductive-proof-fixpoint-backend, major): Realize the closed proof-bearing Json ≅ JsonF(Json), nested list induction, and the semantic unique-name subset in a logic backend; the host backend here proves no theorems.

#[cfg(test)]
mod tests {
    use super::*;

    fn generic_boolean_roundtrip<J>(json: &J)
    where
        J: JsonScalarConstructors,
        J::Error: core::fmt::Debug,
        J::Number: core::fmt::Debug,
        J::String: core::fmt::Debug,
        J::Array: core::fmt::Debug,
        J::Object: core::fmt::Debug,
    {
        let value = json.boolean(true).unwrap();
        assert!(matches!(json.view(&value).unwrap(), JsonView::Bool(true)));
    }

    #[test]
    fn same_generic_consumer_runs_on_reference_and_inductive_layer() {
        generic_boolean_roundtrip(&ReferenceJson::<()>::new());
        generic_boolean_roundtrip(&InductiveJsonLayer::<(), JsonString>::new());
    }

    #[test]
    fn reference_separates_ordered_syntax_from_unique_semantics() {
        let json = ReferenceJson::<()>::new();
        let duplicate = [
            (JsonString::from("x"), ParsedJsonValue::Null),
            (JsonString::from("x"), ParsedJsonValue::Bool(true)),
        ];
        let syntax = json.ordered_object_from_members(duplicate).unwrap();
        assert_eq!(json.ordered_object_members(&syntax).unwrap().len(), 2);

        let semantic = [
            (JsonString::from("x"), JsonValue::Null),
            (JsonString::from("x"), JsonValue::Bool(true)),
        ];
        assert!(json.object_from_members(semantic).is_err());
    }

    #[test]
    fn inductive_backend_names_exact_a0004_family() {
        let backend = InductiveJsonLayer::<(), JsonString>::new();
        assert_eq!(backend.family(), json_value_family());
    }

    fn generic_array_roundtrip<J>(json: &J)
    where
        J: JsonScalarConstructors + JsonArrays + JsonAggregateConstructors,
        J::Error: core::fmt::Debug,
        J::Number: core::fmt::Debug,
        J::String: core::fmt::Debug,
        J::Array: core::fmt::Debug,
        J::Object: core::fmt::Debug,
    {
        let first = json.boolean(true).unwrap();
        let second = json.null().unwrap();
        let array = json.array_from_values([first, second]).unwrap();
        let value = json.array(array).unwrap();
        let JsonView::Array(array) = json.view(&value).unwrap() else {
            panic!("expected array");
        };
        assert_eq!(json.array_values(&array).unwrap().len(), 2);
    }

    #[test]
    fn same_generic_array_consumer_runs_on_both_backends() {
        generic_array_roundtrip(&ReferenceJson::<()>::new());
        generic_array_roundtrip(&InductiveJsonLayer::<(), JsonString>::new());
    }

    #[test]
    fn inductive_syntax_retains_duplicates_but_semantics_rejects_them() {
        let json = InductiveJsonLayer::<(), JsonString>::new();
        let duplicate_syntax = json
            .ordered_object_from_members([
                (JsonString::from("x"), InductiveParsedJsonValue::Null),
                (JsonString::from("x"), InductiveParsedJsonValue::Bool(true)),
            ])
            .unwrap();
        assert_eq!(
            json.ordered_object_members(&duplicate_syntax)
                .unwrap()
                .len(),
            2
        );

        assert!(
            json.object_from_members([
                (JsonString::from("x"), InductiveJsonValue::Null),
                (JsonString::from("x"), InductiveJsonValue::Bool(true)),
            ])
            .is_err()
        );
    }

    #[test]
    fn a0004_interpretation_sees_both_nested_least_fixpoints() {
        let backend = InductiveJsonLayer::<(), JsonString>::new();
        let variable = SymbolicFamilyObject::Parameter(crate::JsonParameter::String);
        let layer = backend.family_layer_at(&variable);
        let SymbolicFamilyObject::Sum(cases) = layer else {
            panic!("JSON layer must be a sum");
        };
        assert_eq!(cases.len(), 6);
        assert!(matches!(
            cases[4],
            SymbolicFamilyObject::Fixpoint {
                kind: covalence_inductive::FamilyFixpointKind::Least,
                ..
            }
        ));
        assert!(matches!(
            cases[5],
            SymbolicFamilyObject::Fixpoint {
                kind: covalence_inductive::FamilyFixpointKind::Least,
                ..
            }
        ));
    }
}
