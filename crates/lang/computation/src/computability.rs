//! Capability-sized vocabulary for computability.
//!
//! @covalence-api-impl {"api":"A0009","name":"Computability vocabulary","representation":"logic-generic partial/total functions, sets, reductions, and supplied law bundles"}
//!
//! Syntax values contain logic carriers only. Host search witnesses are
//! explicitly non-authoritative, and every theorem-level closure or
//! equivalence claim is delegated to a backend certificate.

use std::{convert::Infallible, fmt};

use covalence_hol_logic::Logic;

use crate::{compiler::PartialCompiler, theory::Theory};

/// A positive host observation of a terminating computation.
///
/// This is data for replay or benchmarking, never theorem evidence.
#[derive(Clone, Debug, PartialEq)]
pub struct HostComputationWitness<I, O, Trace = ()> {
    pub input: I,
    pub output: O,
    pub steps: u64,
    pub trace: Trace,
}

/// Optional host executor for a partial function.
pub trait HostPartialFunction<I> {
    type Output;
    type Error;

    /// `None` means no result was observed within the executor's policy; it
    /// does not prove divergence.
    fn observe(&self, input: &I) -> Result<Option<Self::Output>, Self::Error>;
}

/// Logic syntax for a partial function represented by its graph.
#[derive(Clone, Debug, PartialEq)]
pub struct PartialFunction<L: Logic> {
    pub input_type: L::Type,
    pub output_type: L::Type,
    /// Relation `input → output → prop`.
    pub graph: L::Term,
}

/// A partial function together with a machine/program realization claim.
///
/// The terms state vocabulary only; correctness lives in
/// [`PartialComputableFacts`].
#[derive(Clone, Debug, PartialEq)]
pub struct PartialComputable<L: Logic> {
    pub function: PartialFunction<L>,
    pub machine: L::Term,
    pub program: L::Term,
    /// Proposition relating machine observations to `function.graph`.
    pub realizes: L::Term,
}

impl<L: Logic> PartialComputable<L> {
    /// Build syntax from an already realized machine theory.
    ///
    /// This does not infer correctness from [`Theory`]; it merely keeps the
    /// machine term type-correct at the vocabulary boundary.
    pub fn from_machine(
        theory: &Theory<L>,
        function: PartialFunction<L>,
        program: L::Term,
        realizes: L::Term,
    ) -> Self {
        Self {
            function,
            machine: theory.machine.clone(),
            program,
            realizes,
        }
    }
}

/// Supplied correctness laws for a partial computability realization.
pub trait PartialComputableFacts<L: Logic> {
    type Certificate;
    type Error;

    fn syntax(&self) -> &PartialComputable<L>;
    /// Terminating machine observations lie in the function graph.
    fn soundness(&self) -> Result<Self::Certificate, Self::Error>;
    /// Every graph pair has a corresponding terminating computation.
    fn completeness(&self) -> Result<Self::Certificate, Self::Error>;
    /// The graph is single-valued.
    fn functionality(&self) -> Result<Self::Certificate, Self::Error>;
}

/// Syntax for a total computable function.
#[derive(Clone, Debug, PartialEq)]
pub struct TotalComputable<L: Logic> {
    pub partial: PartialComputable<L>,
    /// Proposition that every input is in the graph domain.
    pub total: L::Term,
}

/// Additional certificate required to promote partial to total computability.
pub trait TotalComputableFacts<L: Logic>: PartialComputableFacts<L> {
    fn total_syntax(&self) -> &TotalComputable<L>;
    fn termination(&self) -> Result<Self::Certificate, Self::Error>;
}

/// A predicate term and its total Boolean-valued computation.
#[derive(Clone, Debug, PartialEq)]
pub struct ComputablePredicate<L: Logic> {
    pub predicate: L::Term,
    pub characteristic: TotalComputable<L>,
}

/// Supplied agreement between a predicate and its characteristic function.
pub trait ComputablePredicateFacts<L: Logic>: TotalComputableFacts<L> {
    fn predicate_syntax(&self) -> &ComputablePredicate<L>;
    fn characteristic_correct(&self) -> Result<Self::Certificate, Self::Error>;
}

/// A set is represented extensionally by its membership predicate.
#[derive(Clone, Debug, PartialEq)]
pub struct ComputableSet<L: Logic> {
    pub element_type: L::Type,
    pub membership: ComputablePredicate<L>,
}

/// A binary relation with a computable characteristic predicate.
#[derive(Clone, Debug, PartialEq)]
pub struct ComputableRelation<L: Logic> {
    pub left_type: L::Type,
    pub right_type: L::Type,
    pub relation: ComputablePredicate<L>,
}

/// An enumerator and the set claimed to be its range.
#[derive(Clone, Debug, PartialEq)]
pub struct EnumerableSet<L: Logic> {
    pub element_type: L::Type,
    pub membership: L::Term,
    pub enumerator: PartialComputable<L>,
}

pub trait EnumerableSetFacts<L: Logic>: PartialComputableFacts<L> {
    fn enumerable_syntax(&self) -> &EnumerableSet<L>;
    fn range_soundness(&self) -> Result<Self::Certificate, Self::Error>;
    fn range_completeness(&self) -> Result<Self::Certificate, Self::Error>;
}

/// A semidecision procedure: members are accepted; nonmembers may diverge.
#[derive(Clone, Debug, PartialEq)]
pub struct RecognizableSet<L: Logic> {
    pub element_type: L::Type,
    pub membership: L::Term,
    pub recognizer: PartialComputable<L>,
}

pub trait RecognizableSetFacts<L: Logic>: PartialComputableFacts<L> {
    fn recognizable_syntax(&self) -> &RecognizableSet<L>;
    fn accepts_members(&self) -> Result<Self::Certificate, Self::Error>;
    fn accepts_only_members(&self) -> Result<Self::Certificate, Self::Error>;
}

/// A decision procedure terminates with a correct Boolean answer.
#[derive(Clone, Debug, PartialEq)]
pub struct DecidableSet<L: Logic> {
    pub set: ComputableSet<L>,
}

pub trait DecidableSetFacts<L: Logic>: ComputablePredicateFacts<L> {
    fn decidable_syntax(&self) -> &DecidableSet<L>;
}

/// Syntax for composition `outer ∘ inner`.
#[derive(Clone, Debug, PartialEq)]
pub struct PartialComposition<L: Logic> {
    pub inner: PartialComputable<L>,
    pub outer: PartialComputable<L>,
    pub composite: PartialComputable<L>,
}

/// Optional supplied closure law; composition syntax alone proves nothing.
pub trait PartialCompositionFacts<L: Logic> {
    type Certificate;
    type Error;

    fn composition(&self) -> &PartialComposition<L>;
    fn graph_composition(&self) -> Result<Self::Certificate, Self::Error>;
}

/// Total-function composition, kept separate from partial graph composition.
#[derive(Clone, Debug, PartialEq)]
pub struct TotalComposition<L: Logic> {
    pub inner: TotalComputable<L>,
    pub outer: TotalComputable<L>,
    pub composite: TotalComputable<L>,
}

pub trait TotalCompositionFacts<L: Logic> {
    type Certificate;
    type Error;

    fn composition(&self) -> &TotalComposition<L>;
    fn graph_composition(&self) -> Result<Self::Certificate, Self::Error>;
    fn totality_closure(&self) -> Result<Self::Certificate, Self::Error>;
}

/// A many-one reduction between predicates.
#[derive(Clone, Debug, PartialEq)]
pub struct ManyOneReduction<L: Logic> {
    pub source: L::Term,
    pub target: L::Term,
    pub reducer: TotalComputable<L>,
}

pub trait ManyOneReductionFacts<L: Logic>: TotalComputableFacts<L> {
    fn reduction(&self) -> &ManyOneReduction<L>;
    fn preserves_membership(&self) -> Result<Self::Certificate, Self::Error>;
    fn reflects_membership(&self) -> Result<Self::Certificate, Self::Error>;
}

/// Proof-bearing equivalence through reductions in both directions.
#[derive(Clone, Debug)]
pub struct ComputableEquivalence<Forward, Backward, ForwardLaw, BackwardLaw> {
    pub forward: Forward,
    pub backward: Backward,
    pub forward_law: ForwardLaw,
    pub backward_law: BackwardLaw,
}

/// Computability syntax before and after a partial compiler pass.
#[derive(Clone, Debug)]
pub struct PartialCompilerTransport<Source: Logic, Target: Logic, Artifact> {
    pub source: PartialComputable<Source>,
    pub artifact: Artifact,
    pub target: PartialComputable<Target>,
}

/// Optional theorem capability connecting [`PartialCompiler`] correctness to
/// preservation of partial computability.
pub trait PartialCompilerComputabilityFacts<Source: Logic, Target: Logic>:
    PartialCompiler<Source, Target>
{
    type ComputabilityCertificate;

    fn transport_computability(
        &self,
        source: &PartialComputable<Source>,
        domain: &Self::DomainCertificate,
        artifact: &Self::Artifact,
        target: &PartialComputable<Target>,
    ) -> Result<Self::ComputabilityCertificate, Self::Error>;
}

/// Search-only symbolic logic used to test syntax consumers.
#[derive(Clone, Copy, Debug)]
pub struct SymbolicLogic;

/// Symbolic errors; no proof operations are exposed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SymbolicError;

impl fmt::Display for SymbolicError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("symbolic computability error")
    }
}

impl std::error::Error for SymbolicError {}

impl Logic for SymbolicLogic {
    type Kind = ();
    type Type = String;
    type Term = String;
    type Thm = Infallible;
    type Error = SymbolicError;
}

/// Reference syntax builder. Its theorem carrier is [`Infallible`], so it
/// cannot implement any fact bundle by manufacturing certificates.
///
/// ```compile_fail
/// use covalence_computation::{PartialComputableFacts, SymbolicComputability, SymbolicLogic};
///
/// fn needs_facts(value: &impl PartialComputableFacts<SymbolicLogic>) {}
/// needs_facts(&SymbolicComputability);
/// ```
#[derive(Clone, Copy, Debug, Default)]
pub struct SymbolicComputability;

impl SymbolicComputability {
    pub fn partial(
        &self,
        name: &str,
        input: &str,
        output: &str,
    ) -> PartialComputable<SymbolicLogic> {
        PartialComputable {
            function: PartialFunction {
                input_type: input.into(),
                output_type: output.into(),
                graph: format!("{name}.graph"),
            },
            machine: format!("{name}.machine"),
            program: format!("{name}.program"),
            realizes: format!("{name}.realizes"),
        }
    }

    pub fn total(&self, name: &str, input: &str, output: &str) -> TotalComputable<SymbolicLogic> {
        TotalComputable {
            partial: self.partial(name, input, output),
            total: format!("{name}.total"),
        }
    }
}

// TODO(cov:computability.machine-realizations, major): Realize partial/total computability facts for concrete Machine theories without treating finite host runs as proofs.
// TODO(cov:computability.compiler-transport, major): Realize PartialCompilerComputabilityFacts from concrete compiler preservation/reflection bundles.
// TODO(cov:computability.model-equivalences, major): Supply checked equivalences among concrete computation models; do not assume a Church-Turing thesis.

#[cfg(test)]
mod tests {
    use super::*;

    struct Even;

    impl HostPartialFunction<u64> for Even {
        type Output = bool;
        type Error = Infallible;

        fn observe(&self, input: &u64) -> Result<Option<bool>, Self::Error> {
            Ok(Some(input & 1 == 0))
        }
    }

    #[test]
    fn host_observations_are_plain_positive_data() {
        assert_eq!(Even.observe(&4), Ok(Some(true)));
        let witness = HostComputationWitness {
            input: 4,
            output: true,
            steps: 1,
            trace: (),
        };
        assert_eq!(witness.steps, 1);
    }

    #[test]
    fn symbolic_backend_builds_layered_syntax_without_theorems() {
        let syntax = SymbolicComputability;
        let partial = syntax.partial("search", "input", "output");
        assert_eq!(partial.function.graph, "search.graph");
        let total = syntax.total("normalize", "input", "output");
        assert_eq!(total.total, "normalize.total");

        let predicate = ComputablePredicate {
            predicate: "even".into(),
            characteristic: total,
        };
        let set = ComputableSet {
            element_type: "input".into(),
            membership: predicate,
        };
        assert_eq!(set.membership.predicate, "even");
    }

    #[test]
    fn composition_reduction_and_equivalence_retain_all_components() {
        let syntax = SymbolicComputability;
        let inner = syntax.partial("inner", "a", "b");
        let outer = syntax.partial("outer", "b", "c");
        let composite = syntax.partial("composite", "a", "c");
        let composition = PartialComposition {
            inner,
            outer,
            composite,
        };
        assert_eq!(composition.composite.function.output_type, "c");

        let reduction = ManyOneReduction {
            source: "source-set".into(),
            target: "target-set".into(),
            reducer: syntax.total("reduce", "a", "b"),
        };
        let equivalence = ComputableEquivalence {
            forward: reduction.clone(),
            backward: reduction,
            forward_law: "supplied-forward-certificate",
            backward_law: "supplied-backward-certificate",
        };
        assert_eq!(equivalence.forward.source, "source-set");
    }
}
