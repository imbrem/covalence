//! Representation-independent jq evaluation.
//!
//! The evaluator consumes only A0007 capability traits.  `evaluate_structural`
//! is available to every JSON representation; aggregate filters additionally
//! require the array/object constructor and observation capabilities.

use covalence_json_api::{
    JsonAggregateConstructors, JsonArrays, JsonRepresentation, JsonScalarConstructors,
    JsonSemanticObjects, JsonView,
};

use crate::{Diagnostic, DiagnosticKind, EvalBudget, EvalUsage, JsonKind};

/// A jq filter parameterized by backend-owned value and string carriers.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FilterOf<V, S> {
    Identity,
    Literal(V),
    Field(S),
    Index(isize),
    Iterate,
    Pipe(Box<Self>, Box<Self>),
    Union(Vec<Self>),
    Optional(Box<Self>),
    Array(Box<Self>),
}

/// A representation-independent bounded result.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EvaluationOf<V> {
    pub values: Vec<V>,
    pub diagnostics: Vec<Diagnostic>,
    pub usage: EvalUsage,
}

/// Filters outside the representation-only structural fragment.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StructuralEvalError {
    /// This filter requires array or object capabilities.
    AggregateCapabilityRequired,
}

/// Bounded evaluator carrying the chosen JSON implementation.
#[derive(Clone, Debug)]
pub struct GenericJsonQuery<J> {
    json: J,
}

impl<J> GenericJsonQuery<J> {
    pub const fn new(json: J) -> Self {
        Self { json }
    }

    pub fn representation(&self) -> &J {
        &self.json
    }
}

impl<J: JsonRepresentation> GenericJsonQuery<J>
where
    J::Value: Clone,
{
    /// Evaluate the capability-free relational fragment.
    ///
    /// Identity, literals, pipes, unions, and optional filters need only the
    /// carrier type. Aggregate-dependent syntax is rejected before execution.
    pub fn evaluate_structural(
        &self,
        filter: &FilterOf<J::Value, J::String>,
        input: &J::Value,
        budget: EvalBudget,
    ) -> Result<EvaluationOf<J::Value>, StructuralEvalError> {
        if needs_aggregates(filter) {
            return Err(StructuralEvalError::AggregateCapabilityRequired);
        }
        let mut state = StructuralState {
            budget,
            usage: EvalUsage::default(),
        };
        let batch = state.eval(filter, input, 0, &[]);
        Ok(EvaluationOf {
            values: batch.values,
            diagnostics: batch.diagnostics,
            usage: state.usage,
        })
    }
}

impl<J> GenericJsonQuery<J>
where
    J: JsonScalarConstructors + JsonAggregateConstructors + JsonArrays + JsonSemanticObjects,
    J::Value: Clone,
    J::String: PartialEq,
{
    /// Evaluate the complete A0020 filter set through A0007 capabilities.
    pub fn evaluate(
        &self,
        filter: &FilterOf<J::Value, J::String>,
        input: &J::Value,
        budget: EvalBudget,
    ) -> Result<EvaluationOf<J::Value>, J::Error> {
        let mut state = GenericState {
            json: &self.json,
            budget,
            usage: EvalUsage::default(),
        };
        let batch = state.eval(filter, input, 0, &[])?;
        Ok(EvaluationOf {
            values: batch.values,
            diagnostics: batch.diagnostics,
            usage: state.usage,
        })
    }
}

fn needs_aggregates<V, S>(filter: &FilterOf<V, S>) -> bool {
    match filter {
        FilterOf::Identity | FilterOf::Literal(_) => false,
        FilterOf::Pipe(left, right) => needs_aggregates(left) || needs_aggregates(right),
        FilterOf::Union(filters) => filters.iter().any(needs_aggregates),
        FilterOf::Optional(filter) => needs_aggregates(filter),
        FilterOf::Field(_) | FilterOf::Index(_) | FilterOf::Iterate | FilterOf::Array(_) => true,
    }
}

struct Batch<V> {
    values: Vec<V>,
    diagnostics: Vec<Diagnostic>,
}

impl<V> Default for Batch<V> {
    fn default() -> Self {
        Self {
            values: Vec::new(),
            diagnostics: Vec::new(),
        }
    }
}

impl<V> Batch<V> {
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

struct StructuralState {
    budget: EvalBudget,
    usage: EvalUsage,
}

impl StructuralState {
    fn eval<V: Clone, S>(
        &mut self,
        filter: &FilterOf<V, S>,
        input: &V,
        depth: usize,
        path: &[usize],
    ) -> Batch<V> {
        if let Some(diagnostic) = enter(&mut self.usage, self.budget, depth, path) {
            return diagnostic;
        }
        match filter {
            FilterOf::Identity => one(&mut self.usage, self.budget, input.clone(), path),
            FilterOf::Literal(value) => one(&mut self.usage, self.budget, value.clone(), path),
            FilterOf::Pipe(left, right) => {
                let left = self.eval(left, input, depth + 1, path);
                let mut result = Batch {
                    values: Vec::new(),
                    diagnostics: left.diagnostics,
                };
                for (index, value) in left.values.iter().enumerate() {
                    let mut child = path.to_vec();
                    child.push(index);
                    result.append(self.eval(right, value, depth + 1, &child));
                }
                result
            }
            FilterOf::Union(filters) => {
                let mut result = Batch::default();
                for (index, filter) in filters.iter().enumerate() {
                    let mut child = path.to_vec();
                    child.push(index);
                    result.append(self.eval(filter, input, depth + 1, &child));
                }
                result
            }
            FilterOf::Optional(filter) => {
                let mut result = self.eval(filter, input, depth + 1, path);
                result
                    .diagnostics
                    .retain(|diagnostic| diagnostic.kind.is_resource_limit());
                result
            }
            _ => unreachable!("aggregate filters are rejected before structural evaluation"),
        }
    }
}

struct GenericState<'a, J> {
    json: &'a J,
    budget: EvalBudget,
    usage: EvalUsage,
}

impl<J> GenericState<'_, J>
where
    J: JsonScalarConstructors + JsonAggregateConstructors + JsonArrays + JsonSemanticObjects,
    J::Value: Clone,
    J::String: PartialEq,
{
    fn eval(
        &mut self,
        filter: &FilterOf<J::Value, J::String>,
        input: &J::Value,
        depth: usize,
        path: &[usize],
    ) -> Result<Batch<J::Value>, J::Error> {
        if let Some(diagnostic) = enter(&mut self.usage, self.budget, depth, path) {
            return Ok(diagnostic);
        }
        Ok(match filter {
            FilterOf::Identity => one(&mut self.usage, self.budget, input.clone(), path),
            FilterOf::Literal(value) => one(&mut self.usage, self.budget, value.clone(), path),
            FilterOf::Field(name) => match self.json.view(input)? {
                JsonView::Object(object) => {
                    let value = self
                        .json
                        .object_members(&object)?
                        .into_iter()
                        .find(|(member_name, _)| member_name == name)
                        .map_or_else(|| self.json.null(), |(_, value)| Ok(value))?;
                    one(&mut self.usage, self.budget, value, path)
                }
                view => Batch::diagnostic(
                    path,
                    DiagnosticKind::CannotLookupField {
                        actual: view_kind(&view),
                    },
                ),
            },
            FilterOf::Index(index) => match self.json.view(input)? {
                JsonView::Array(array) => {
                    let values = self.json.array_values(&array)?;
                    let resolved = if *index < 0 {
                        values.len().checked_sub(index.unsigned_abs())
                    } else {
                        usize::try_from(*index)
                            .ok()
                            .filter(|resolved| *resolved < values.len())
                    };
                    match resolved.and_then(|resolved| values.get(resolved)) {
                        Some(value) => one(&mut self.usage, self.budget, value.clone(), path),
                        None => Batch::diagnostic(
                            path,
                            DiagnosticKind::IndexOutOfRange {
                                index: *index,
                                len: values.len(),
                            },
                        ),
                    }
                }
                view => Batch::diagnostic(
                    path,
                    DiagnosticKind::CannotIndex {
                        actual: view_kind(&view),
                    },
                ),
            },
            FilterOf::Iterate => match self.json.view(input)? {
                JsonView::Array(array) => many(
                    &mut self.usage,
                    self.budget,
                    self.json.array_values(&array)?,
                    path,
                ),
                JsonView::Object(object) => many(
                    &mut self.usage,
                    self.budget,
                    self.json
                        .object_members(&object)?
                        .into_iter()
                        .map(|(_, value)| value),
                    path,
                ),
                view => Batch::diagnostic(
                    path,
                    DiagnosticKind::CannotIterate {
                        actual: view_kind(&view),
                    },
                ),
            },
            FilterOf::Pipe(left, right) => {
                let left = self.eval(left, input, depth + 1, path)?;
                let mut result = Batch {
                    values: Vec::new(),
                    diagnostics: left.diagnostics,
                };
                for (index, value) in left.values.iter().enumerate() {
                    let mut child = path.to_vec();
                    child.push(index);
                    result.append(self.eval(right, value, depth + 1, &child)?);
                }
                result
            }
            FilterOf::Union(filters) => {
                let mut result = Batch::default();
                for (index, filter) in filters.iter().enumerate() {
                    let mut child = path.to_vec();
                    child.push(index);
                    result.append(self.eval(filter, input, depth + 1, &child)?);
                }
                result
            }
            FilterOf::Optional(filter) => {
                let mut result = self.eval(filter, input, depth + 1, path)?;
                result
                    .diagnostics
                    .retain(|diagnostic| diagnostic.kind.is_resource_limit());
                result
            }
            FilterOf::Array(filter) => {
                let mut result = self.eval(filter, input, depth + 1, path)?;
                if result.diagnostics.is_empty() {
                    let array = self.json.array_from_values(result.values)?;
                    let value = self.json.array(array)?;
                    one(&mut self.usage, self.budget, value, path)
                } else {
                    result.values.clear();
                    result
                }
            }
        })
    }
}

fn enter<V>(
    usage: &mut EvalUsage,
    budget: EvalBudget,
    depth: usize,
    path: &[usize],
) -> Option<Batch<V>> {
    usage.maximum_depth = usage.maximum_depth.max(depth);
    if depth > budget.depth {
        return Some(Batch::diagnostic(path, DiagnosticKind::DepthLimitExceeded));
    }
    if usage.steps >= budget.steps {
        return Some(Batch::diagnostic(path, DiagnosticKind::StepLimitExceeded));
    }
    usage.steps += 1;
    None
}

fn one<V>(usage: &mut EvalUsage, budget: EvalBudget, value: V, path: &[usize]) -> Batch<V> {
    many(usage, budget, core::iter::once(value), path)
}

fn many<V>(
    usage: &mut EvalUsage,
    budget: EvalBudget,
    values: impl IntoIterator<Item = V>,
    path: &[usize],
) -> Batch<V> {
    let mut batch = Batch::default();
    for value in values {
        if usage.values >= budget.values {
            batch.diagnostics.push(Diagnostic {
                path: path.to_vec(),
                kind: DiagnosticKind::ValueLimitExceeded,
            });
            break;
        }
        usage.values += 1;
        batch.values.push(value);
    }
    batch
}

fn view_kind<N, S, A, O>(view: &JsonView<N, S, A, O>) -> JsonKind {
    match view {
        JsonView::Null => JsonKind::Null,
        JsonView::Bool(_) => JsonKind::Bool,
        JsonView::Number(_) => JsonKind::Number,
        JsonView::String(_) => JsonKind::String,
        JsonView::Array(_) => JsonKind::Array,
        JsonView::Object(_) => JsonKind::Object,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_json_api::{
        InductiveJsonLayer, InductiveJsonScalar, JsonMember, JsonObject, JsonString, JsonValue,
        ReferenceJson,
    };

    #[test]
    fn unchanged_structural_filter_runs_on_reference_and_inductive_stack() {
        fn identity<J>(json: J, value: J::Value)
        where
            J: JsonRepresentation,
            J::Value: Clone + PartialEq + core::fmt::Debug,
        {
            let filter = FilterOf::Identity;
            let result = GenericJsonQuery::new(json)
                .evaluate_structural(&filter, &value, EvalBudget::default())
                .unwrap();
            assert_eq!(result.values, vec![value]);
        }

        identity(ReferenceJson::<()>::new(), JsonValue::Bool(true));
        identity(
            InductiveJsonLayer::<(), JsonString>::new(),
            InductiveJsonScalar::Bool(true),
        );
    }

    #[test]
    fn aggregate_query_uses_only_public_json_capabilities() {
        let json = ReferenceJson::<()>::new();
        let ada = JsonValue::String(JsonString::from("Ada"));
        let object = JsonValue::Object(
            JsonObject::new(vec![JsonMember {
                name: JsonString::from("name"),
                value: ada.clone(),
            }])
            .unwrap(),
        );
        let filter = FilterOf::Field(JsonString::from("name"));
        let result = GenericJsonQuery::new(json)
            .evaluate(&filter, &object, EvalBudget::default())
            .unwrap();
        assert_eq!(result.values, vec![ada]);
    }
}
