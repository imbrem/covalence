//! One-step relations, finite executions, and proof-producing replay seams.

use core::fmt::{Debug, Display, Formatter};

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

/// Optional deterministic execution strategy.
pub trait DeterministicStep: StepRelation {
    fn next(
        &self,
        configuration: &Self::Configuration,
    ) -> Result<Option<Self::Configuration>, Self::Error>;
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
    for _ in 0..fuel {
        let next = relation
            .next(states.last().expect("execution state"))
            .map_err(ExecutionError::Relation)?;
        match next {
            Some(next) => states.push(next),
            None => return Ok(CheckedTrace { states }),
        }
    }
    Err(ExecutionError::FuelExhausted { fuel })
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

/// A terminal evaluation result.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Evaluation<C, V> {
    Value(MayEval<C, V>),
    Stuck(CheckedTrace<C>),
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
}
