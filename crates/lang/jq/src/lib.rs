//! A small, relational jq-like vocabulary over A0007 JSON values.
//!
//! Filters relate one input to zero, one, or many outputs. Evaluation is
//! deliberately proof-free: diagnostics and traces are observations that a
//! logic backend may later replay, not theorem authority.
//!
//! @covalence-api {"id":"A0020","title":"Relational JSON queries","status":"experimental","dependsOn":["A0007"]}

#![forbid(unsafe_code)]

use covalence_json_api::{DuplicateName, JsonString, JsonValue, ReferenceJson};

pub mod generic;
pub use generic::{EvaluationOf, FilterOf, GenericJsonQuery, StructuralEvalError};

/// Source-compatible reference-backend filter spelling.
pub type Filter<D> = FilterOf<JsonValue<D>, JsonString>;

/// Explicit bounds for the reference evaluator.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EvalBudget {
    pub steps: usize,
    pub values: usize,
    pub depth: usize,
}

impl Default for EvalBudget {
    fn default() -> Self {
        Self {
            steps: 10_000,
            values: 10_000,
            depth: 256,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diagnostic {
    /// Branch indexes through union and pipe evaluation.
    pub path: Vec<usize>,
    pub kind: DiagnosticKind,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DiagnosticKind {
    CannotLookupField { actual: JsonKind },
    CannotIndex { actual: JsonKind },
    IndexOutOfRange { index: isize, len: usize },
    CannotIterate { actual: JsonKind },
    StepLimitExceeded,
    ValueLimitExceeded,
    DepthLimitExceeded,
}

impl DiagnosticKind {
    fn is_resource_limit(&self) -> bool {
        matches!(
            self,
            Self::StepLimitExceeded | Self::ValueLimitExceeded | Self::DepthLimitExceeded
        )
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum JsonKind {
    Null,
    Bool,
    Number,
    String,
    Array,
    Object,
}

/// Observable resource use, useful for benchmarks without granting authority.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct EvalUsage {
    pub steps: usize,
    pub values: usize,
    pub maximum_depth: usize,
}

/// A bounded relation result. Diagnostics coexist with successful branches.
pub type Evaluation<D> = EvaluationOf<JsonValue<D>>;

/// Backend-neutral capability seam for jq-like relations.
pub trait JsonQueryEvaluator<D> {
    type Error;

    fn evaluate(
        &self,
        filter: &Filter<D>,
        input: &JsonValue<D>,
        budget: EvalBudget,
    ) -> Result<Evaluation<D>, Self::Error>;
}

/// A PER-like observation seam for comparing filter interpretations.
///
/// A positive answer is host evidence only. Proof backends must replay it.
pub trait SameJsonQueryInterpretation<D>: JsonQueryEvaluator<D> {
    type Observation;

    fn same_interpretation(
        &self,
        left: &Filter<D>,
        right: &Filter<D>,
        examples: &[JsonValue<D>],
        budget: EvalBudget,
    ) -> Result<Option<Self::Observation>, Self::Error>;
}

/// Optional proof-bearing laws, intentionally separate from evaluation.
pub trait JsonQueryLaws<D>: JsonQueryEvaluator<D> {
    type Law;

    fn identity_laws(&self) -> Result<Self::Law, Self::Error>;
    fn pipe_associativity(&self) -> Result<Self::Law, Self::Error>;
    fn union_associativity(&self) -> Result<Self::Law, Self::Error>;
}

/// Deterministic bounded reference implementation of the relational API.
#[derive(Clone, Copy, Debug, Default)]
pub struct BoundedJsonQuery;

impl<D: Clone + PartialEq> JsonQueryEvaluator<D> for BoundedJsonQuery {
    type Error = DuplicateName;

    fn evaluate(
        &self,
        filter: &Filter<D>,
        input: &JsonValue<D>,
        budget: EvalBudget,
    ) -> Result<Evaluation<D>, Self::Error> {
        GenericJsonQuery::new(ReferenceJson::<D>::new()).evaluate(filter, input, budget)
    }
}

/// Finite-example equality observation for demos and differential tests.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ObservedSameInterpretation;

impl<D: Clone + PartialEq> SameJsonQueryInterpretation<D> for BoundedJsonQuery {
    type Observation = ObservedSameInterpretation;

    fn same_interpretation(
        &self,
        left: &Filter<D>,
        right: &Filter<D>,
        examples: &[JsonValue<D>],
        budget: EvalBudget,
    ) -> Result<Option<Self::Observation>, Self::Error> {
        for example in examples {
            let left = self.evaluate(left, example, budget)?;
            let right = self.evaluate(right, example, budget)?;
            if left.values != right.values || left.diagnostics != right.diagnostics {
                return Ok(None);
            }
        }
        Ok(Some(ObservedSameInterpretation))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_decimal_api::CanonicalDecimal;
    use covalence_json_api::{JsonMember, JsonObject};
    use covalence_types::Int;

    type Value = JsonValue<()>;

    fn string(value: &str) -> Value {
        Value::String(JsonString::from(value))
    }

    fn object(members: Vec<(&str, Value)>) -> Value {
        Value::Object(
            JsonObject::new(
                members
                    .into_iter()
                    .map(|(name, value)| JsonMember {
                        name: JsonString::from(name),
                        value,
                    })
                    .collect(),
            )
            .unwrap(),
        )
    }

    fn evaluate(filter: &Filter<()>, input: &Value) -> Evaluation<()> {
        BoundedJsonQuery
            .evaluate(filter, input, EvalBudget::default())
            .unwrap()
    }

    #[test]
    fn field_pipe_and_iteration_form_a_relational_query() {
        let input = object(vec![(
            "users",
            Value::Array(vec![
                object(vec![("name", string("Ada"))]),
                object(vec![("name", string("Grace"))]),
            ]),
        )]);
        let query = Filter::Pipe(
            Box::new(Filter::Field(JsonString::from("users"))),
            Box::new(Filter::Pipe(
                Box::new(Filter::Iterate),
                Box::new(Filter::Field(JsonString::from("name"))),
            )),
        );
        let result = evaluate(&query, &input);
        assert_eq!(result.values, vec![string("Ada"), string("Grace")]);
        assert!(result.diagnostics.is_empty());
    }

    #[test]
    fn union_preserves_successful_and_failing_branches() {
        let query = Filter::Union(vec![Filter::Identity, Filter::Iterate]);
        let result = evaluate(&query, &Value::Bool(true));
        assert_eq!(result.values, vec![Value::Bool(true)]);
        assert_eq!(result.diagnostics.len(), 1);
    }

    #[test]
    fn optional_suppresses_errors_but_not_successful_outputs() {
        let query = Filter::Optional(Box::new(Filter::Iterate));
        let result = evaluate(&query, &Value::Null);
        assert!(result.values.is_empty());
        assert!(result.diagnostics.is_empty());
    }

    #[test]
    fn optional_does_not_hide_resource_exhaustion() {
        let result = BoundedJsonQuery
            .evaluate(
                &Filter::Optional(Box::new(Filter::Identity)),
                &Value::Null,
                EvalBudget {
                    steps: 1,
                    ..EvalBudget::default()
                },
            )
            .unwrap();
        assert_eq!(
            result.diagnostics[0].kind,
            DiagnosticKind::StepLimitExceeded
        );
    }

    #[test]
    fn array_collects_all_outputs_and_negative_index_counts_from_end() {
        let input = Value::Array(vec![Value::Bool(false), Value::Bool(true)]);
        assert_eq!(
            evaluate(&Filter::Array(Box::new(Filter::Iterate)), &input).values,
            vec![input.clone()]
        );
        assert_eq!(
            evaluate(&Filter::Index(-1), &input).values,
            vec![Value::Bool(true)]
        );
    }

    #[test]
    fn field_miss_is_null_while_wrong_input_kind_is_diagnostic() {
        let field = Filter::Field(JsonString::from("missing"));
        assert_eq!(evaluate(&field, &object(vec![])).values, vec![Value::Null]);
        assert!(matches!(
            evaluate(&field, &Value::Null).diagnostics[0].kind,
            DiagnosticKind::CannotLookupField {
                actual: JsonKind::Null
            }
        ));
    }

    #[test]
    fn explicit_value_budget_reports_truncation() {
        let input = Value::Array(vec![Value::Null, Value::Null]);
        let result = BoundedJsonQuery
            .evaluate(
                &Filter::Iterate,
                &input,
                EvalBudget {
                    values: 1,
                    ..EvalBudget::default()
                },
            )
            .unwrap();
        assert_eq!(result.values.len(), 1);
        assert_eq!(
            result.diagnostics[0].kind,
            DiagnosticKind::ValueLimitExceeded
        );
    }

    #[test]
    fn finite_example_per_distinguishes_relations() {
        let inputs = [Value::Bool(true), Value::Null];
        assert!(
            BoundedJsonQuery
                .same_interpretation(
                    &Filter::Identity,
                    &Filter::Pipe(Box::new(Filter::Identity), Box::new(Filter::Identity)),
                    &inputs,
                    EvalBudget::default()
                )
                .unwrap()
                .is_some()
        );
        assert!(
            BoundedJsonQuery
                .same_interpretation(
                    &Filter::Identity,
                    &Filter::Literal(Value::Null),
                    &inputs,
                    EvalBudget::default()
                )
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn literal_and_identity_preserve_exact_decimal_representation() {
        let decimal = CanonicalDecimal::new(false, vec![1, 2, 3, 4, 5], Int::from(-3_i64)).unwrap();
        let value = JsonValue::Number(decimal);
        let result = BoundedJsonQuery
            .evaluate(&Filter::Identity, &value, EvalBudget::default())
            .unwrap();
        assert_eq!(result.values, vec![value]);
    }
}
