//! One-step relations, finite executions, and proof-producing replay seams.

use core::fmt::{Debug, Display, Formatter};
use std::collections::VecDeque;

/// A possibly nondeterministic one-step operational relation.
pub trait StepRelation {
    type Configuration: Clone + PartialEq + Debug;
    type Error;

    /// Enumerate the legal immediate successors of `configuration`.
    ///
    /// The empty vector represents a terminal or stuck configuration; those
    /// cases are distinguished by language-specific observation capabilities.
    fn successors(
        &self,
        configuration: &Self::Configuration,
    ) -> Result<Vec<Self::Configuration>, Self::Error>;

    fn is_step(
        &self,
        from: &Self::Configuration,
        to: &Self::Configuration,
    ) -> Result<bool, Self::Error> {
        Ok(self
            .successors(from)?
            .iter()
            .any(|candidate| candidate == to))
    }
}

/// One immediate successor paired with the semantic rule that produced it.
///
/// Labels are explanatory data, not theorem authority.  A proof-producing
/// backend must still replay the transition itself; the label lets it select
/// the corresponding rule without reverse-engineering an opaque state change.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClassifiedStep<C, L> {
    pub configuration: C,
    pub label: L,
}

/// A one-step relation that exposes stable semantic rule classes.
///
/// This is the bridge between an executable transition system and backends
/// which replay the same transitions in a logic.  In particular, Lisp
/// backends can distinguish lexical lookup (δ) from closure application (β)
/// while sharing the ordinary [`StepRelation`] API.
pub trait ClassifiedStepRelation: StepRelation {
    type Label: Clone + PartialEq + Debug;

    /// Classify the rule enabled at `configuration`, or return `None` when it
    /// has no successor.
    fn classify(
        &self,
        configuration: &Self::Configuration,
    ) -> Result<Option<Self::Label>, Self::Error>;

    fn classified_successors(
        &self,
        configuration: &Self::Configuration,
    ) -> Result<Vec<ClassifiedStep<Self::Configuration, Self::Label>>, Self::Error> {
        let successors = self.successors(configuration)?;
        let Some(label) = self.classify(configuration)? else {
            return Ok(Vec::new());
        };
        Ok(successors
            .into_iter()
            .map(|configuration| ClassifiedStep {
                configuration,
                label: label.clone(),
            })
            .collect())
    }
}

/// A checked finite path which retains the semantic class of every step.
///
/// Unlike a plain [`CheckedTrace`], this is directly consumable by a
/// proof-producing replay backend: each label has been checked against the
/// executable relation and may be used to select a logic rule.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckedClassifiedTrace<C, L> {
    trace: CheckedTrace<C>,
    labels: Vec<L>,
}

impl<C, L> CheckedClassifiedTrace<C, L> {
    pub fn initial(&self) -> &C {
        self.trace.start()
    }

    pub fn labels(&self) -> &[L] {
        &self.labels
    }

    pub fn end(&self) -> &C {
        self.trace.end()
    }

    pub fn trace(&self) -> &CheckedTrace<C> {
        &self.trace
    }

    pub fn into_trace(self) -> CheckedTrace<C> {
        self.trace
    }
}

impl<C: Clone + PartialEq + Debug, L: Clone + PartialEq + Debug> CheckedClassifiedTrace<C, L> {
    /// Attach checked semantic labels to an already checked state trace.
    ///
    /// Transition authority remains in `trace`; this operation checks only
    /// that every label names the rule enabled at the corresponding source
    /// state.  Keeping those checks separate matters for resource runtimes
    /// whose semantically equal replay may allocate different opaque handles.
    pub fn label<R>(
        relation: &R,
        trace: CheckedTrace<C>,
        labels: Vec<L>,
    ) -> Result<Self, ExecutionError<R::Error>>
    where
        R: ClassifiedStepRelation<Configuration = C, Label = L>,
    {
        if labels.len() != trace.steps() {
            return Err(ExecutionError::InvalidStep {
                index: labels.len().min(trace.steps()),
            });
        }
        for (index, (configuration, claimed)) in trace.states().iter().zip(&labels).enumerate() {
            let actual = relation
                .classify(configuration)
                .map_err(ExecutionError::Relation)?;
            if actual.as_ref() != Some(claimed) {
                return Err(ExecutionError::InvalidStep { index });
            }
        }
        Ok(Self { trace, labels })
    }
}

/// Optional deterministic execution strategy.
pub trait DeterministicStep: StepRelation {
    fn next(
        &self,
        configuration: &Self::Configuration,
    ) -> Result<Option<Self::Configuration>, Self::Error>;
}

/// Observation of terminal values, independent of their representation.
///
/// Returning `None` does not mean that a step exists; when a checked trace
/// has no successor and this observation returns `None`, evaluation is stuck.
pub trait TerminalValue: StepRelation {
    type Value: Clone + PartialEq + Debug;

    fn terminal_value(&self, configuration: &Self::Configuration) -> Option<Self::Value>;
}

/// A finite path through a one-step relation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckedTrace<C> {
    states: Vec<C>,
}

impl<C> CheckedTrace<C> {
    pub fn reflexive(configuration: C) -> Self {
        Self {
            states: vec![configuration],
        }
    }

    pub fn states(&self) -> &[C] {
        &self.states
    }

    pub fn start(&self) -> &C {
        &self.states[0]
    }

    pub fn end(&self) -> &C {
        self.states.last().expect("checked traces are nonempty")
    }

    pub fn steps(&self) -> usize {
        self.states.len() - 1
    }
}

/// Failure while checking an untrusted candidate trace.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExecutionError<E> {
    EmptyTrace,
    InvalidStep { index: usize },
    NotTerminalValue,
    ValueMismatch,
    Relation(E),
    FuelExhausted { fuel: usize },
}

impl<E: Display> Display for ExecutionError<E> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::EmptyTrace => f.write_str("an execution trace must contain a state"),
            Self::InvalidStep { index } => {
                write!(
                    f,
                    "candidate trace contains an invalid step at index {index}"
                )
            }
            Self::NotTerminalValue => {
                f.write_str("candidate evaluation does not end in a terminal value")
            }
            Self::ValueMismatch => {
                f.write_str("candidate evaluation names the wrong terminal value")
            }
            Self::Relation(error) => write!(f, "step relation failed: {error}"),
            Self::FuelExhausted { fuel } => {
                write!(f, "execution did not terminate within {fuel} steps")
            }
        }
    }
}

impl<E: Debug + Display> core::error::Error for ExecutionError<E> {}

impl<C: Clone + PartialEq + Debug> CheckedTrace<C> {
    /// Check untrusted path data against the relation.
    pub fn check<R>(relation: &R, states: Vec<C>) -> Result<Self, ExecutionError<R::Error>>
    where
        R: StepRelation<Configuration = C>,
    {
        if states.is_empty() {
            return Err(ExecutionError::EmptyTrace);
        }
        for (index, pair) in states.windows(2).enumerate() {
            if !relation
                .is_step(&pair[0], &pair[1])
                .map_err(ExecutionError::Relation)?
            {
                return Err(ExecutionError::InvalidStep { index });
            }
        }
        Ok(Self { states })
    }
}

/// Drive a deterministic relation, retaining every state as auditable data.
pub fn execute<R>(
    relation: &R,
    initial: R::Configuration,
    fuel: usize,
) -> Result<CheckedTrace<R::Configuration>, ExecutionError<R::Error>>
where
    R: DeterministicStep,
{
    let mut states = vec![initial];
    for step in 0..=fuel {
        let next = relation
            .next(states.last().expect("execution state"))
            .map_err(ExecutionError::Relation)?;
        match next {
            Some(next) if step < fuel => states.push(next),
            Some(_) => return Err(ExecutionError::FuelExhausted { fuel }),
            None => return Ok(CheckedTrace { states }),
        }
    }
    unreachable!("the inclusive fuel loop always returns")
}

/// Plain evidence that an expression may evaluate to a value.
///
/// This carries no theorem authority. Proof-producing backends replay its
/// checked trace through [`TraceReplay`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MayEval<C, V> {
    pub trace: CheckedTrace<C>,
    pub value: V,
}

impl<C, V> MayEval<C, V>
where
    C: Clone + PartialEq + Debug,
    V: Clone + PartialEq + Debug,
{
    /// Check the claimed result against the endpoint of an already checked
    /// trace. This validates untrusted serialized [`MayEval`] data without
    /// rerunning the whole execution.
    pub fn check<R>(
        relation: &R,
        trace: CheckedTrace<C>,
        value: V,
    ) -> Result<Self, ExecutionError<R::Error>>
    where
        R: TerminalValue<Configuration = C, Value = V>,
    {
        let observed = relation
            .terminal_value(trace.end())
            .ok_or(ExecutionError::NotTerminalValue)?;
        if observed != value {
            return Err(ExecutionError::ValueMismatch);
        }
        Ok(Self { trace, value })
    }
}

/// A terminal evaluation result.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Evaluation<C, V> {
    Value(MayEval<C, V>),
    Stuck(CheckedTrace<C>),
}

/// Explicit limits for relational execution.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExplorationBounds {
    /// Maximum number of transitions in one explored trace.
    pub max_steps: usize,
    /// Maximum number of trace prefixes removed from the work queue.
    pub max_traces: usize,
}

/// Result of bounded relational execution.
///
/// Equal values reached by different traces remain distinct entries. This
/// preserves proof/search provenance and makes nondeterministic ambiguity
/// visible to callers.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Exploration<C, V> {
    pub values: Vec<MayEval<C, V>>,
    pub stuck: Vec<CheckedTrace<C>>,
    /// Valid prefixes that were not expanded because a bound was reached.
    pub frontier: Vec<CheckedTrace<C>>,
    pub truncated: bool,
}

/// Explore a possibly nondeterministic relation breadth-first.
pub fn explore<R>(
    relation: &R,
    initial: R::Configuration,
    bounds: ExplorationBounds,
) -> Result<Exploration<R::Configuration, R::Value>, ExecutionError<R::Error>>
where
    R: TerminalValue,
{
    let mut queue = VecDeque::from([CheckedTrace::reflexive(initial)]);
    let mut values = Vec::new();
    let mut stuck = Vec::new();
    let mut frontier = Vec::new();
    let mut processed = 0;
    let mut truncated = false;

    while let Some(trace) = queue.pop_front() {
        if processed == bounds.max_traces {
            frontier.push(trace);
            frontier.extend(queue);
            truncated = true;
            break;
        }
        processed += 1;

        if let Some(value) = relation.terminal_value(trace.end()) {
            values.push(MayEval::check(relation, trace, value)?);
            continue;
        }
        let successors = relation
            .successors(trace.end())
            .map_err(ExecutionError::Relation)?;
        if successors.is_empty() {
            stuck.push(trace);
            continue;
        }
        if trace.steps() == bounds.max_steps {
            frontier.push(trace);
            truncated = true;
            continue;
        }
        for successor in successors {
            let mut states = trace.states.clone();
            states.push(successor);
            queue.push_back(CheckedTrace { states });
        }
    }

    Ok(Exploration {
        values,
        stuck,
        frontier,
        truncated,
    })
}

/// Drive a deterministic semantics and classify its terminal configuration.
pub fn evaluate<R>(
    relation: &R,
    initial: R::Configuration,
    fuel: usize,
) -> Result<Evaluation<R::Configuration, R::Value>, ExecutionError<R::Error>>
where
    R: DeterministicStep + TerminalValue,
{
    let trace = execute(relation, initial, fuel)?;
    Ok(match relation.terminal_value(trace.end()) {
        Some(value) => Evaluation::Value(MayEval::check(relation, trace, value)?),
        None => Evaluation::Stuck(trace),
    })
}

/// Backend capability for replaying a checked finite trace.
pub trait TraceReplay<R: StepRelation> {
    type Evidence;
    type Error;

    fn replay(
        &self,
        relation: &R,
        trace: &CheckedTrace<R::Configuration>,
    ) -> Result<Self::Evidence, Self::Error>;
}

/// Optional proof-producing statement that replay evidence entails the
/// reflexive-transitive closure of the one-step relation.
///
/// Implementations must return an existing backend theorem/certificate type;
/// this trait does not grant authority to construct one.
pub trait TraceSoundness<R: StepRelation>: TraceReplay<R> {
    type Theorem;

    fn trace_implies_execution(
        &self,
        evidence: &Self::Evidence,
    ) -> Result<Self::Theorem, Self::Error>;
}

/// Proof-producing replay that additionally checks the terminal value.
///
/// Implementations must verify that `evaluation.value` is the value observed
/// at the trace endpoint; [`MayEval`] remains transportable, untrusted data.
pub trait MayEvalReplay<R: TerminalValue>: TraceReplay<R> {
    type EvaluationEvidence;

    fn replay_may_eval(
        &self,
        relation: &R,
        evaluation: &MayEval<R::Configuration, R::Value>,
        trace_evidence: &Self::Evidence,
    ) -> Result<Self::EvaluationEvidence, Self::Error>;
}

/// Proof-producing interpretation of a concrete `MayEval` witness in another
/// semantics.
///
/// Unlike [`MayEvalReplay`], this need not use the same configuration type or
/// one-step relation. Implementations must validate the source endpoint,
/// interpret both the source program and value, and return existing target
/// evidence that the interpreted program reaches that interpreted value.
pub trait MayEvalTransport<C, V> {
    type Evidence;
    type Error;

    fn transport_may_eval(&self, evaluation: &MayEval<C, V>)
    -> Result<Self::Evidence, Self::Error>;
}

/// Optional proof that a semantics has at most one result for an initial
/// configuration.
///
/// This capability is intentionally separate from finite evaluation replay:
/// a trace proves existence for one input, whereas determinacy is a universal
/// semantic property. The returned value must be an existing backend theorem
/// or certificate type.
pub trait EvaluationDeterminacy<R: TerminalValue>: MayEvalReplay<R> {
    type Theorem;

    fn results_equal(
        &self,
        left: &Self::EvaluationEvidence,
        right: &Self::EvaluationEvidence,
    ) -> Result<Self::Theorem, Self::Error>;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Clone, Debug)]
    struct Countdown;

    impl StepRelation for Countdown {
        type Configuration = u8;
        type Error = core::convert::Infallible;

        fn successors(&self, configuration: &u8) -> Result<Vec<u8>, Self::Error> {
            Ok(configuration.checked_sub(1).into_iter().collect::<Vec<_>>())
        }
    }

    impl DeterministicStep for Countdown {
        fn next(&self, configuration: &u8) -> Result<Option<u8>, Self::Error> {
            Ok(configuration.checked_sub(1))
        }
    }

    impl TerminalValue for Countdown {
        type Value = u8;

        fn terminal_value(&self, configuration: &u8) -> Option<Self::Value> {
            (*configuration == 0).then_some(0)
        }
    }

    #[test]
    fn deterministic_execution_is_a_checked_trace() {
        let trace = execute(&Countdown, 3, 4).unwrap();
        assert_eq!(trace.states(), &[3, 2, 1, 0]);
        assert_eq!(
            CheckedTrace::check(&Countdown, trace.states().to_vec()),
            Ok(trace)
        );
    }

    #[test]
    fn forged_trace_is_rejected() {
        assert!(matches!(
            CheckedTrace::check(&Countdown, vec![3, 1]),
            Err(ExecutionError::InvalidStep { index: 0 })
        ));
    }

    #[test]
    fn zero_fuel_observes_an_already_terminal_value() {
        let Evaluation::Value(result) = evaluate(&Countdown, 0, 0).unwrap() else {
            panic!("zero is terminal")
        };
        assert_eq!(result.value, 0);
        assert_eq!(result.trace.steps(), 0);
    }

    #[test]
    fn evaluation_distinguishes_values_from_stuck_states() {
        #[derive(Clone, Debug)]
        struct Stuck;

        impl StepRelation for Stuck {
            type Configuration = u8;
            type Error = core::convert::Infallible;

            fn successors(&self, _: &u8) -> Result<Vec<u8>, Self::Error> {
                Ok(Vec::new())
            }
        }

        impl DeterministicStep for Stuck {
            fn next(&self, _: &u8) -> Result<Option<u8>, Self::Error> {
                Ok(None)
            }
        }

        impl TerminalValue for Stuck {
            type Value = u8;

            fn terminal_value(&self, _: &u8) -> Option<Self::Value> {
                None
            }
        }

        assert!(matches!(
            evaluate(&Stuck, 7, 0).unwrap(),
            Evaluation::Stuck(_)
        ));
    }

    #[test]
    fn forged_terminal_value_is_rejected() {
        let trace = execute(&Countdown, 1, 1).unwrap();
        assert!(matches!(
            MayEval::check(&Countdown, trace, 9),
            Err(ExecutionError::ValueMismatch)
        ));
    }

    #[test]
    fn bounded_exploration_reports_its_frontier() {
        let result = explore(
            &Countdown,
            3,
            ExplorationBounds {
                max_steps: 1,
                max_traces: 8,
            },
        )
        .unwrap();
        assert!(result.values.is_empty());
        assert_eq!(result.frontier.len(), 1);
        assert_eq!(result.frontier[0].end(), &2);
        assert!(result.truncated);
    }
}
