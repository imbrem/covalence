//! Caller-visible bounds and the evaluator-failure vocabulary shared by both encodings.
//!
//! Budgets are passed in, never stored per combinator node. Storing a bound on a node
//! makes association-dependent: one association of a union trips its inner node's limit
//! while the other does not, and the associativity law then fails as a resource artifact
//! rather than a semantic disagreement.

use core::fmt;

/// Bounds that make evaluation predictable under hostile inputs and grammars.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CombinatorBudget {
    pub max_source_units: usize,
    pub max_work: usize,
    pub max_depth: usize,
    pub max_witness_nodes: usize,
    /// Bind is where nontermination enters the algebra without passing through a rule
    /// reference, so it is bounded separately and a runaway continuation is diagnosable
    /// as such rather than as generic work exhaustion.
    pub max_continuation_resolutions: usize,
}

impl CombinatorBudget {
    pub const fn new(
        max_source_units: usize,
        max_work: usize,
        max_depth: usize,
        max_witness_nodes: usize,
        max_continuation_resolutions: usize,
    ) -> Self {
        Self {
            max_source_units,
            max_work,
            max_depth,
            max_witness_nodes,
            max_continuation_resolutions,
        }
    }
}

/// Bounds meaningful only to relational evaluation. Kept out of [`CombinatorBudget`] so no
/// bound leaks into a capability that cannot observe it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RelationalLimits {
    pub max_results: usize,
    pub max_results_per_node: usize,
}

impl RelationalLimits {
    pub const fn new(max_results: usize, max_results_per_node: usize) -> Self {
        Self {
            max_results,
            max_results_per_node,
        }
    }
}

/// The bounded resources. Every variant must be reachable by some evaluator: an
/// unconstructible variant means the corresponding bound is not implemented.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CombinatorResource {
    SourceUnits,
    Work,
    Depth,
    WitnessNodes,
    ContinuationResolutions,
    Results,
    ResultsPerNode,
}

/// The resource that was exhausted, together with the limit that was in force.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CombinatorLimit {
    pub resource: CombinatorResource,
    pub limit: usize,
}

impl CombinatorLimit {
    pub const fn new(resource: CombinatorResource, limit: usize) -> Self {
        Self { resource, limit }
    }
}

/// Evaluator failures, distinct from ordinary non-match.
///
/// `StartOutOfBounds` is deliberately absent: a start offset past the end of the source is
/// ordinary non-match with a diagnostic, exactly as in `PegParser`. Classifying caller
/// input as evaluator failure would violate the Error/NoMatch discipline.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CombinatorEvalError<E> {
    ResourceExhausted(CombinatorLimit),
    UndefinedRule {
        rule: usize,
    },
    /// Left recursion detected through `Core::Rule` by an (offset, rule) memo. Recursion
    /// through `Core::Bind` is not structurally detectable and is bounded only by
    /// `max_continuation_resolutions`. The asymmetry is permanent.
    LeftRecursion {
        rule: usize,
        offset: usize,
    },
    /// The environment failed. Ill-typed application (`Ap` of a non-function) arrives here.
    Environment(E),
}

// `thiserror` is the house idiom for library error types, but this crate has no
// `thiserror` dependency and `peg-parsing`'s plain enum is in-family precedent, so the
// impls below are hand-written rather than earning a new dependency.
impl<E: fmt::Display> fmt::Display for CombinatorEvalError<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ResourceExhausted(limit) => write!(
                f,
                "combinator evaluation exhausted {:?} (limit {})",
                limit.resource, limit.limit
            ),
            Self::UndefinedRule { rule } => write!(f, "undefined rule {rule}"),
            Self::LeftRecursion { rule, offset } => {
                write!(f, "left recursion through rule {rule} at offset {offset}")
            }
            Self::Environment(error) => write!(f, "environment error: {error}"),
        }
    }
}

impl<E: std::error::Error + 'static> std::error::Error for CombinatorEvalError<E> {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Environment(error) => Some(error),
            _ => None,
        }
    }
}

/// Why the reference spine declined. Ordinary non-match, never evaluator failure.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CombinatorDiagnosticKind {
    NoMatch,
    TrailingInput,
    StartOutOfBounds,
}

/// The reference spine's flat diagnostic. `offset` is the farthest position reached.
///
/// This shape is fixed only for the syntax encoding. The host encoding is
/// diagnostic-polymorphic by design: its `Diagnostic` is an associated type and its
/// ordered choice takes a caller-supplied merge, so a caller wanting structure gets
/// structure and a caller wanting flat gets this.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CombinatorDiagnostic {
    pub offset: usize,
    pub kind: CombinatorDiagnosticKind,
}

impl CombinatorDiagnostic {
    pub const fn new(offset: usize, kind: CombinatorDiagnosticKind) -> Self {
        Self { offset, kind }
    }
}
