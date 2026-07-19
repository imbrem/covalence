//! A small, relational jq-like vocabulary over A0007 JSON values.
//!
//! Filters relate one input to zero, one, or many outputs. Evaluation is
//! deliberately proof-free: diagnostics and traces are observations that a
//! logic backend may later replay, not theorem authority.
//!
//! @covalence-api {"id":"A0020","title":"Relational JSON queries","status":"experimental","dependsOn":["A0007"]}

#![forbid(unsafe_code)]

use covalence_json_api::{JsonString, JsonValue};

/// The initial jq-like filter language.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Filter<D> {
    Identity,
    Literal(JsonValue<D>),
    Field(JsonString),
    Index(isize),
    Iterate,
    Pipe(Box<Self>, Box<Self>),
    Union(Vec<Self>),
    Optional(Box<Self>),
    Array(Box<Self>),
}

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
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Evaluation<D> {
    pub values: Vec<JsonValue<D>>,
    pub diagnostics: Vec<Diagnostic>,
    pub usage: EvalUsage,
}

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
    type Error = core::convert::Infallible;

    fn evaluate(
        &self,
        filter: &Filter<D>,
        input: &JsonValue<D>,
        budget: EvalBudget,
    ) -> Result<Evaluation<D>, Self::Error> {
        let mut state = State {
            budget,
            usage: EvalUsage::default(),
        };
        let batch = state.eval(filter, input, 0, &[]);
        Ok(Evaluation {
            values: batch.values,
            diagnostics: batch.diagnostics,
            usage: state.usage,
        })
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

struct State {
    budget: EvalBudget,
    usage: EvalUsage,
}

struct Batch<D> {
    values: Vec<JsonValue<D>>,
    diagnostics: Vec<Diagnostic>,
}

impl<D> Default for Batch<D> {
    fn default() -> Self {
        Self {
            values: Vec::new(),
            diagnostics: Vec::new(),
        }
    }
}

impl<D> Batch<D> {
    fn diagnostic(path: &[usize], kind: DiagnosticKind) -> Self {
        Self {
            values: Vec::new(),
            diagnostics: vec![Diagnostic {
                path: path.to_vec(),
                kind,
            }],
        }
    }

    fn append(&mut self, mut other: Self) {
        self.values.append(&mut other.values);
        self.diagnostics.append(&mut other.diagnostics);
    }
}

impl State {
    fn eval<D: Clone + PartialEq>(
        &mut self,
        filter: &Filter<D>,
        input: &JsonValue<D>,
        depth: usize,
        path: &[usize],
    ) -> Batch<D> {
        self.usage.maximum_depth = self.usage.maximum_depth.max(depth);
        if depth > self.budget.depth {
            return Batch::diagnostic(path, DiagnosticKind::DepthLimitExceeded);
        }
        if self.usage.steps >= self.budget.steps {
            return Batch::diagnostic(path, DiagnosticKind::StepLimitExceeded);
        }
        self.usage.steps += 1;

        match filter {
            Filter::Identity => self.one(input.clone(), path),
            Filter::Literal(value) => self.one(value.clone(), path),
            Filter::Field(name) => match input {
                JsonValue::Object(object) => {
                    let value = object
                        .members()
                        .iter()
                        .find(|member| member.name == *name)
                        .map_or(JsonValue::Null, |member| member.value.clone());
                    self.one(value, path)
                }
                other => Batch::diagnostic(
                    path,
                    DiagnosticKind::CannotLookupField {
                        actual: kind(other),
                    },
                ),
            },
            Filter::Index(index) => match input {
                JsonValue::Array(values) => {
                    let resolved = if *index < 0 {
                        values.len().checked_sub(index.unsigned_abs())
                    } else {
                        usize::try_from(*index)
                            .ok()
                            .filter(|resolved| *resolved < values.len())
                    };
                    match resolved.and_then(|resolved| values.get(resolved)) {
                        Some(value) => self.one(value.clone(), path),
                        None => Batch::diagnostic(
                            path,
                            DiagnosticKind::IndexOutOfRange {
                                index: *index,
                                len: values.len(),
                            },
                        ),
                    }
                }
                other => Batch::diagnostic(
                    path,
                    DiagnosticKind::CannotIndex {
                        actual: kind(other),
                    },
                ),
            },
            Filter::Iterate => match input {
                JsonValue::Array(values) => self.many(values.iter().cloned(), path),
                JsonValue::Object(object) => self.many(
                    object.members().iter().map(|member| member.value.clone()),
                    path,
                ),
                other => Batch::diagnostic(
                    path,
                    DiagnosticKind::CannotIterate {
                        actual: kind(other),
                    },
                ),
            },
            Filter::Pipe(left, right) => {
                let left = self.eval(left, input, depth + 1, path);
                let mut result = Batch {
                    values: Vec::new(),
                    diagnostics: left.diagnostics,
                };
                for (index, value) in left.values.iter().enumerate() {
                    let mut child_path = path.to_vec();
                    child_path.push(index);
                    result.append(self.eval(right, value, depth + 1, &child_path));
                }
                result
            }
            Filter::Union(filters) => {
                let mut result = Batch::default();
                for (index, filter) in filters.iter().enumerate() {
                    let mut child_path = path.to_vec();
                    child_path.push(index);
                    result.append(self.eval(filter, input, depth + 1, &child_path));
                }
                result
            }
            Filter::Optional(filter) => {
                let mut result = self.eval(filter, input, depth + 1, path);
                result
                    .diagnostics
                    .retain(|diagnostic| diagnostic.kind.is_resource_limit());
                result
            }
            Filter::Array(filter) => {
                let mut result = self.eval(filter, input, depth + 1, path);
                if result.diagnostics.is_empty() {
                    self.one(JsonValue::Array(result.values), path)
                } else {
                    result.values.clear();
                    result
                }
            }
        }
    }

    fn one<D>(&mut self, value: JsonValue<D>, path: &[usize]) -> Batch<D> {
        self.many(core::iter::once(value), path)
    }

    fn many<D>(
        &mut self,
        values: impl IntoIterator<Item = JsonValue<D>>,
        path: &[usize],
    ) -> Batch<D> {
        let mut batch = Batch::default();
        for value in values {
            if self.usage.values >= self.budget.values {
                batch.diagnostics.push(Diagnostic {
                    path: path.to_vec(),
                    kind: DiagnosticKind::ValueLimitExceeded,
                });
                break;
            }
            self.usage.values += 1;
            batch.values.push(value);
        }
        batch
    }
}

fn kind<D>(value: &JsonValue<D>) -> JsonKind {
    match value {
        JsonValue::Null => JsonKind::Null,
        JsonValue::Bool(_) => JsonKind::Bool,
        JsonValue::Number(_) => JsonKind::Number,
        JsonValue::String(_) => JsonKind::String,
        JsonValue::Array(_) => JsonKind::Array,
        JsonValue::Object(_) => JsonKind::Object,
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
