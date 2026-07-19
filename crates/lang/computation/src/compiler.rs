//! Proof-oriented compilation and simulation between realized HOL theories.
//!
//! Compilation artifacts may contain object code, decoding information, and
//! source maps.  They are deliberately not identified with a bare target
//! term.  Likewise, constructing an artifact or a search witness proves
//! nothing: authority enters only through certificates supplied by a backend.

use covalence_hol_logic::Logic;

use crate::theory::Theory;

/// A compilation artifact that exposes the target program it describes.
///
/// Backends are free to retain representation metadata needed to state or
/// interpret subsequent theorems.
pub trait CompilationArtifact<L: Logic> {
    fn target_program(&self) -> &L::Term;
}

/// A simple artifact suitable for backends which only need attached metadata.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CompiledTerm<L: Logic, Metadata> {
    pub term: L::Term,
    pub metadata: Metadata,
}

impl<L: Logic, Metadata> CompilationArtifact<L> for CompiledTerm<L, Metadata> {
    fn target_program(&self) -> &L::Term {
        &self.term
    }
}

/// HOL vocabulary used to state a compiler simulation.
///
/// `state_relation` relates source and target states. `step_bound` describes
/// the target-step cost assigned to a source step; its exact numeric
/// representation belongs to the target backend.
#[derive(Clone, Debug)]
pub struct SimulationVocabulary<Target: Logic> {
    pub state_relation: Target::Term,
    pub step_bound: Target::Term,
}

/// Inspectable, non-authoritative cost data produced during proof search.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct StepMapping {
    pub source_steps: u64,
    pub target_steps: u64,
}

/// Total translation from programs in one realized theory to another.
///
/// `Source` and `Target` may be the same HOL implementation or distinct
/// implementations. The latter is useful during representation migrations:
/// the compiler artifact belongs to `Target`, while correctness certificates
/// can retain whatever cross-logic interpretation data the backend requires.
pub trait Compiler<Source: Logic, Target: Logic> {
    type Artifact: CompilationArtifact<Target>;
    type Error;

    fn compile(
        &self,
        source_logic: &Source,
        source_theory: &Theory<Source>,
        target_logic: &Target,
        target_theory: &Theory<Target>,
        source_program: &Source::Term,
    ) -> Result<Self::Artifact, Self::Error>;
}

/// Proof obligations supplied for a compiler.
///
/// Preservation says source behavior is simulated by compiled behavior.
/// Reflection says target observations of compiled programs correspond to
/// source observations; it is separated because not every useful compiler is
/// fully abstract.
pub trait CompilerLaws<Source: Logic, Target: Logic>: Compiler<Source, Target> {
    type PreservationCertificate;
    type ReflectionCertificate;

    fn simulation_vocabulary(&self) -> &SimulationVocabulary<Target>;

    fn certify_preservation(
        &self,
        source_logic: &Source,
        source_theory: &Theory<Source>,
        target_logic: &Target,
        target_theory: &Theory<Target>,
        source_program: &Source::Term,
        artifact: &Self::Artifact,
    ) -> Result<Self::PreservationCertificate, Self::Error>;

    fn certify_reflection(
        &self,
        source_logic: &Source,
        source_theory: &Theory<Source>,
        target_logic: &Target,
        target_theory: &Theory<Target>,
        source_program: &Source::Term,
        artifact: &Self::Artifact,
    ) -> Result<Self::ReflectionCertificate, Self::Error>;
}

/// Logical outcome of deciding whether a source term is in a partial
/// compiler's domain.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DomainDecision<Inside, Outside> {
    Inside(Inside),
    Outside(Outside),
}

/// Successful compilation or certified logical non-membership.
///
/// Operational failures are returned through `Result::Err`; they must not be
/// represented as `OutsideDomain`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PartialCompilation<Artifact, OutsideCertificate> {
    Compiled(Artifact),
    OutsideDomain(OutsideCertificate),
}

/// Translation whose logical domain is a proper subset of source programs.
pub trait PartialCompiler<Source: Logic, Target: Logic> {
    type Artifact: CompilationArtifact<Target>;
    type DomainCertificate;
    type OutsideDomainCertificate;
    type Error;

    /// HOL predicate characterizing the compiler domain.
    fn domain_predicate(&self) -> &Source::Term;

    /// Decide domain membership with proof-bearing evidence on either branch.
    fn certify_domain(
        &self,
        source_logic: &Source,
        source_theory: &Theory<Source>,
        source_program: &Source::Term,
    ) -> Result<DomainDecision<Self::DomainCertificate, Self::OutsideDomainCertificate>, Self::Error>;

    /// Compile a term in the certified domain.
    fn compile_in_domain(
        &self,
        source_logic: &Source,
        source_theory: &Theory<Source>,
        target_logic: &Target,
        target_theory: &Theory<Target>,
        source_program: &Source::Term,
        domain: &Self::DomainCertificate,
    ) -> Result<Self::Artifact, Self::Error>;

    /// Convenience operation preserving the distinction between logical
    /// non-membership and an operational error.
    fn compile_partial(
        &self,
        source_logic: &Source,
        source_theory: &Theory<Source>,
        target_logic: &Target,
        target_theory: &Theory<Target>,
        source_program: &Source::Term,
    ) -> Result<PartialCompilation<Self::Artifact, Self::OutsideDomainCertificate>, Self::Error>
    {
        match self.certify_domain(source_logic, source_theory, source_program)? {
            DomainDecision::Inside(domain) => self
                .compile_in_domain(
                    source_logic,
                    source_theory,
                    target_logic,
                    target_theory,
                    source_program,
                    &domain,
                )
                .map(PartialCompilation::Compiled),
            DomainDecision::Outside(certificate) => {
                Ok(PartialCompilation::OutsideDomain(certificate))
            }
        }
    }
}

/// Correctness laws for a partial compiler, conditional on domain evidence.
pub trait PartialCompilerLaws<Source: Logic, Target: Logic>:
    PartialCompiler<Source, Target>
{
    type PreservationCertificate;
    type ReflectionCertificate;

    fn simulation_vocabulary(&self) -> &SimulationVocabulary<Target>;

    fn certify_preservation(
        &self,
        source_logic: &Source,
        source_theory: &Theory<Source>,
        target_logic: &Target,
        target_theory: &Theory<Target>,
        source_program: &Source::Term,
        domain: &Self::DomainCertificate,
        artifact: &Self::Artifact,
    ) -> Result<Self::PreservationCertificate, Self::Error>;

    fn certify_reflection(
        &self,
        source_logic: &Source,
        source_theory: &Theory<Source>,
        target_logic: &Target,
        target_theory: &Theory<Target>,
        source_program: &Source::Term,
        domain: &Self::DomainCertificate,
        artifact: &Self::Artifact,
    ) -> Result<Self::ReflectionCertificate, Self::Error>;
}

/// Composition data for two compiler passes.
///
/// Keeping both artifacts is important for replaying per-pass theorems and
/// interpreting costs. It also works uniformly for total/partial pass
/// combinations; adapters can use [`DomainDecision`] at either boundary.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ComposedArtifact<Intermediate, Target> {
    pub intermediate: Intermediate,
    pub target: Target,
}

/// Proof-bearing claim that two models compute the same observations.
///
/// The forward/backward compiler values are accompanied by distinct
/// round-trip and observational certificates. No theorem is inferred merely
/// from the existence of the two compiler implementations.
#[derive(Clone, Debug)]
pub struct ComputationalEquivalence<Forward, Backward, ForwardRoundTrip, BackwardRoundTrip, Observe>
{
    pub forward: Forward,
    pub backward: Backward,
    pub forward_round_trip: ForwardRoundTrip,
    pub backward_round_trip: BackwardRoundTrip,
    pub observational: Observe,
}

/// Candidate produced by compiler proof search.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CompilerSearchWitness<W> {
    pub step_mapping: StepMapping,
    pub candidate: W,
}

/// Trusted seam that validates a compiler-search candidate.
pub trait CompilerReplayBackend<Source: Logic, Target: Logic, W> {
    type Certificate;
    type Error;

    fn replay_simulation(
        &self,
        source_logic: &Source,
        source_theory: &Theory<Source>,
        target_logic: &Target,
        target_theory: &Theory<Target>,
        witness: &CompilerSearchWitness<W>,
    ) -> Result<Self::Certificate, Self::Error>;
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::fmt;

    #[derive(Clone, Debug, PartialEq, Eq)]
    struct MockLogic;

    #[derive(Clone, Debug, PartialEq, Eq)]
    struct MockError;

    impl fmt::Display for MockError {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("mock failure")
        }
    }

    impl core::error::Error for MockError {}

    impl Logic for MockLogic {
        type Kind = ();
        type Type = &'static str;
        type Term = &'static str;
        type Thm = &'static str;
        type Error = MockError;
    }

    fn theory() -> Theory<MockLogic> {
        Theory {
            machine_type: "Machine",
            input_type: "Input",
            state_type: "State",
            output_type: "Output",
            machine: "machine",
            initialize: "init",
            step: "step",
            output: "output",
            halts: "halts",
        }
    }

    struct FiniteOnly;

    impl PartialCompiler<MockLogic, MockLogic> for FiniteOnly {
        type Artifact = CompiledTerm<MockLogic, usize>;
        type DomainCertificate = &'static str;
        type OutsideDomainCertificate = &'static str;
        type Error = MockError;

        fn domain_predicate(&self) -> &&'static str {
            &"finite"
        }

        fn certify_domain(
            &self,
            _logic: &MockLogic,
            _theory: &Theory<MockLogic>,
            source: &&'static str,
        ) -> Result<DomainDecision<&'static str, &'static str>, MockError> {
            Ok(if *source == "finite-program" {
                DomainDecision::Inside("|- finite finite-program")
            } else {
                DomainDecision::Outside("|- ~finite infinite-program")
            })
        }

        fn compile_in_domain(
            &self,
            _source_logic: &MockLogic,
            _source_theory: &Theory<MockLogic>,
            _target_logic: &MockLogic,
            _target_theory: &Theory<MockLogic>,
            _source: &&'static str,
            _domain: &&'static str,
        ) -> Result<Self::Artifact, MockError> {
            Ok(CompiledTerm {
                term: "automaton",
                metadata: 3,
            })
        }
    }

    #[test]
    fn partial_compilation_separates_non_membership_from_failure() {
        let logic = MockLogic;
        let theory = theory();
        let compiled = FiniteOnly
            .compile_partial(&logic, &theory, &logic, &theory, &"finite-program")
            .unwrap();
        let PartialCompilation::Compiled(artifact) = compiled else {
            panic!("expected compilation");
        };
        assert_eq!(artifact.target_program(), &"automaton");

        assert_eq!(
            FiniteOnly
                .compile_partial(&logic, &theory, &logic, &theory, &"infinite-program",)
                .unwrap(),
            PartialCompilation::OutsideDomain("|- ~finite infinite-program")
        );
    }

    #[test]
    fn equivalence_keeps_the_logical_obligations_explicit() {
        let equivalence = ComputationalEquivalence {
            forward: "compile-a-b",
            backward: "compile-b-a",
            forward_round_trip: "|- observe (back (forward x)) = observe x",
            backward_round_trip: "|- observe (forward (back y)) = observe y",
            observational: "|- computes_a f <=> computes_b (forward f)",
        };
        assert!(equivalence.observational.contains("<=>"));
    }
}
