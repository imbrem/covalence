//! Explicit, inspectable vocabulary for simulation claims.

use crate::TransitionSystem;

/// A relation between configurations, optionally producing inspectable
/// evidence for a related pair.
pub trait StateRelation<Left, Right> {
    /// Evidence chosen by the relation implementation.
    type Witness;

    /// Return evidence when the states are related.
    fn relate(&self, left: &Left, right: &Right) -> Option<Self::Witness>;
}

/// Evidence that one source transition corresponds to zero or more target
/// transitions.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SimulationStep<W> {
    /// Number of source transitions represented (normally one).
    pub source_steps: u64,
    /// Number of target transitions used.
    pub target_steps: u64,
    /// Model-specific, independently checkable evidence.
    pub evidence: W,
}

/// A simulation interface between two transition systems.
///
/// Implementing this trait states where configurations map and how step
/// witnesses are constructed. It does not establish a theorem.
pub trait Simulation<Source, Target>
where
    Source: TransitionSystem,
    Target: TransitionSystem,
{
    /// Evidence attached to configuration translation.
    type StateWitness;
    /// Evidence attached to a simulated step.
    type StepWitness;
    /// Failure to construct or validate a witness.
    type Error;

    /// Translate a source configuration and expose translation evidence.
    fn translate_state(
        &self,
        source: &Source::State,
    ) -> Result<(Target::State, Self::StateWitness), Self::Error>;

    /// Witness how one source transition is represented at the target.
    fn simulate_step(
        &self,
        before: &Source::State,
        after: &Source::State,
        target_before: &Target::State,
        target_after: &Target::State,
    ) -> Result<SimulationStep<Self::StepWitness>, Self::Error>;
}

/// A named simulation together with its model-specific description.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SimulationWitness<S> {
    /// Human-readable identifier for the encoding or construction.
    pub name: &'static str,
    /// Data needed to replay or check the simulation.
    pub simulation: S,
}

/// Paired simulations in opposite directions.
///
/// This is useful vocabulary for an equivalence candidate. The two fields do
/// not by themselves prove preservation, reflection, or inverse laws.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EquivalenceWitness<Forward, Backward> {
    pub forward: SimulationWitness<Forward>,
    pub backward: SimulationWitness<Backward>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn equivalence_keeps_both_constructions_explicit() {
        let witness = EquivalenceWitness {
            forward: SimulationWitness {
                name: "binary-to-unary",
                simulation: 2_u8,
            },
            backward: SimulationWitness {
                name: "unary-to-binary",
                simulation: 1_u8,
            },
        };
        assert_eq!(witness.forward.simulation, 2);
        assert_eq!(witness.backward.name, "unary-to-binary");
    }
}
