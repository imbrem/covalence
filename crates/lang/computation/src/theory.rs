//! Proof-bearing, representation-independent computation theories.
//!
//! A plain-data model specification stays outside the logic. A
//! [`TheoryBackend`] interprets that specification into a [`Theory`] whose
//! types, operations, predicates, and certificates all belong to one
//! [`Logic`]. Different backends may therefore realize the same serialized
//! specification using different encodings without changing consumers.
//!
//! This module only transports certificates supplied by a backend. It has no
//! primitive for constructing a theorem.

use covalence_hol_logic::Logic;

/// Optional projection implemented by certificate artifacts that expose an
/// underlying logic theorem.
pub trait TheoremCertificate<L: Logic> {
    fn theorem(&self) -> &L::Thm;
}

/// Basic certificate packaging for backends that need interpretation metadata
/// alongside a theorem.
#[derive(Clone, Debug)]
pub struct TheoremArtifact<L: Logic, Metadata> {
    pub theorem: L::Thm,
    pub metadata: Metadata,
}

impl<L: Logic, Metadata> TheoremCertificate<L> for TheoremArtifact<L, Metadata> {
    fn theorem(&self) -> &L::Thm {
        &self.theorem
    }
}

/// HOL vocabulary for a transition system.
///
/// Term conventions:
///
/// - `machine : machine_type`
/// - `initialize : machine_type -> input_type -> state_type`
/// - `step : machine_type -> state_type -> state_type -> prop`
/// - `output : machine_type -> state_type -> output_type`
/// - `halts : machine_type -> state_type -> prop`
///
/// The arrows and proposition type are descriptive conventions checked by the
/// realizing backend; this crate deliberately does not duplicate a type
/// checker's authority.
#[derive(Clone, Debug)]
pub struct Theory<L: Logic> {
    pub machine_type: L::Type,
    pub input_type: L::Type,
    pub state_type: L::Type,
    pub output_type: L::Type,
    pub machine: L::Term,
    pub initialize: L::Term,
    pub step: L::Term,
    pub output: L::Term,
    pub halts: L::Term,
}

/// The transition-system syntax capability, usable without requesting laws.
pub trait TransitionSyntax<L: Logic> {
    fn machine_type(&self) -> &L::Type;
    fn input_type(&self) -> &L::Type;
    fn state_type(&self) -> &L::Type;
    fn output_type(&self) -> &L::Type;
    fn machine(&self) -> &L::Term;
    fn initialize(&self) -> &L::Term;
    fn step(&self) -> &L::Term;
    fn output(&self) -> &L::Term;
    fn halts(&self) -> &L::Term;
}

impl<L: Logic> TransitionSyntax<L> for Theory<L> {
    fn machine_type(&self) -> &L::Type {
        &self.machine_type
    }
    fn input_type(&self) -> &L::Type {
        &self.input_type
    }
    fn state_type(&self) -> &L::Type {
        &self.state_type
    }
    fn output_type(&self) -> &L::Type {
        &self.output_type
    }
    fn machine(&self) -> &L::Term {
        &self.machine
    }
    fn initialize(&self) -> &L::Term {
        &self.initialize
    }
    fn step(&self) -> &L::Term {
        &self.step
    }
    fn output(&self) -> &L::Term {
        &self.output
    }
    fn halts(&self) -> &L::Term {
        &self.halts
    }
}

/// Supplied universal laws for a realized transition theory.
///
/// Each result is a backend theorem whose conclusion follows the term
/// conventions on [`Theory`]. Implementations should expose universally
/// quantified theorems, not perform unchecked host-language assertions.
pub trait TransitionLaws<L: Logic> {
    /// Proof-bearing artifact, possibly with cost or representation metadata.
    type Certificate;

    /// Initialization produces a well-typed state.
    fn initialization_closed(&self) -> Result<Self::Certificate, L::Error>;
    /// The step relation relates machine states.
    fn step_closed(&self) -> Result<Self::Certificate, L::Error>;
    /// A halting state has a well-typed observable output.
    fn halting_output(&self) -> Result<Self::Certificate, L::Error>;
}

/// Optional law capability for deterministic realizations.
pub trait DeterministicTransitionLaws<L: Logic>: TransitionLaws<L> {
    /// Two successors of the same machine state are equal.
    fn step_deterministic(&self) -> Result<Self::Certificate, L::Error>;
    /// Halting states have unique observations.
    fn output_unique(&self) -> Result<Self::Certificate, L::Error>;
}

/// Proof-producing actions for concrete states and observations.
///
/// Implementations validate the requested judgment; terms alone are never
/// treated as evidence.
pub trait TransitionRules<L: Logic>: TransitionLaws<L> {
    fn certify_initial(
        &self,
        input: &L::Term,
        state: &L::Term,
    ) -> Result<Self::Certificate, L::Error>;
    fn certify_step(
        &self,
        before: &L::Term,
        after: &L::Term,
    ) -> Result<Self::Certificate, L::Error>;
    fn certify_halts(&self, state: &L::Term) -> Result<Self::Certificate, L::Error>;
}

/// A transition theory extended with a language-acceptance predicate.
///
/// `accepts : machine_type -> input_type -> prop`.
#[derive(Clone, Debug)]
pub struct RecognizerTheory<L: Logic> {
    pub transition: Theory<L>,
    pub accepts: L::Term,
}

impl<L: Logic> TransitionSyntax<L> for RecognizerTheory<L> {
    fn machine_type(&self) -> &L::Type {
        self.transition.machine_type()
    }
    fn input_type(&self) -> &L::Type {
        self.transition.input_type()
    }
    fn state_type(&self) -> &L::Type {
        self.transition.state_type()
    }
    fn output_type(&self) -> &L::Type {
        self.transition.output_type()
    }
    fn machine(&self) -> &L::Term {
        self.transition.machine()
    }
    fn initialize(&self) -> &L::Term {
        self.transition.initialize()
    }
    fn step(&self) -> &L::Term {
        self.transition.step()
    }
    fn output(&self) -> &L::Term {
        self.transition.output()
    }
    fn halts(&self) -> &L::Term {
        self.transition.halts()
    }
}

/// Acceptance syntax, separated so non-recognizing transition systems do not
/// need to invent an acceptance predicate.
pub trait RecognizerSyntax<L: Logic>: TransitionSyntax<L> {
    fn accepts(&self) -> &L::Term;
}

impl<L: Logic> RecognizerSyntax<L> for RecognizerTheory<L> {
    fn accepts(&self) -> &L::Term {
        &self.accepts
    }
}

/// Supplied laws connecting acceptance to execution.
pub trait RecognizerLaws<L: Logic>: TransitionLaws<L> {
    /// Acceptance implies that execution reaches a halting state.
    fn acceptance_halts(&self) -> Result<Self::Certificate, L::Error>;
    /// Acceptance is invariant under the backend's canonical input encoding.
    fn acceptance_representation_invariant(&self) -> Result<Self::Certificate, L::Error>;
}

/// Proof-producing acceptance action.
pub trait RecognizerRules<L: Logic>: RecognizerLaws<L> {
    fn certify_accepts(&self, input: &L::Term) -> Result<Self::Certificate, L::Error>;
}

/// A realized theory paired with the backend object that supplies its laws.
#[derive(Clone, Debug)]
pub struct Realization<T, F> {
    pub theory: T,
    pub facts: F,
}

/// Representation seam from plain model data to a proof-bearing HOL theory.
///
/// `Spec` is intentionally unconstrained: callers can choose a minimal
/// serde-free struct, bits, bytes, or a separately serializable schema. It
/// should not contain `L::Type`, `L::Term`, or `L::Thm`.
pub trait TheoryBackend<L: Logic, Spec: ?Sized> {
    type Facts: TransitionLaws<L>;
    type Error;

    fn realize(
        &self,
        logic: &L,
        spec: &Spec,
    ) -> Result<Realization<Theory<L>, Self::Facts>, Self::Error>;
}

/// Stronger representation seam for language recognizers.
pub trait RecognizerBackend<L: Logic, Spec: ?Sized> {
    type Facts: RecognizerLaws<L>;
    type Error;

    fn realize_recognizer(
        &self,
        logic: &L,
        spec: &Spec,
    ) -> Result<Realization<RecognizerTheory<L>, Self::Facts>, Self::Error>;
}

/// The proposition an untrusted search procedure claims its candidate supports.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CandidateClaim {
    /// Execution reaches a state satisfying `halts`.
    Halts,
    /// The recognizer's `accepts` predicate holds.
    Accepts,
}

/// An untrusted candidate discovered by a reference interpreter or proof
/// search procedure.
///
/// Constructing this value grants no logical authority. In particular,
/// `steps` is only search metadata; it is not a certified complexity bound.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SearchWitness<W: ?Sized> {
    pub claim: CandidateClaim,
    pub steps: u64,
    /// Model-specific trace, run, or certificate candidate.
    pub candidate: W,
}

/// Trusted replay seam for candidate executions.
///
/// An implementation must parse and validate the entire candidate against the
/// supplied theory before returning its logic's theorem carrier. Failure stays
/// in `Error`; it must never be represented by a forged `L::Thm`.
pub trait ReplayBackend<L: Logic, W: ?Sized> {
    /// Validated artifact; it may expose `L::Thm` through
    /// [`TheoremCertificate`] and carry replay metadata.
    type Certificate;
    type Error;

    /// Validate a halting candidate and return the corresponding theorem.
    fn replay_halting(
        &self,
        logic: &L,
        theory: &Theory<L>,
        witness: &SearchWitness<W>,
    ) -> Result<Self::Certificate, Self::Error>;
}

/// Trusted replay seam for acceptance candidates.
pub trait RecognizerReplayBackend<L: Logic, W: ?Sized>: ReplayBackend<L, W> {
    /// Validate an acceptance candidate and return the corresponding theorem.
    fn replay_acceptance(
        &self,
        logic: &L,
        theory: &RecognizerTheory<L>,
        witness: &SearchWitness<W>,
    ) -> Result<Self::Certificate, Self::Error>;
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::convert::Infallible;
    use core::fmt;

    #[derive(Clone, Debug, PartialEq, Eq)]
    struct MockLogic;

    #[derive(Clone, Debug, PartialEq, Eq)]
    struct MockError;

    impl fmt::Display for MockError {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("mock error")
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

    #[derive(Clone, Debug)]
    struct PlainSpec {
        name: &'static str,
    }

    #[derive(Clone, Debug)]
    struct Facts;

    impl TransitionLaws<MockLogic> for Facts {
        type Certificate = TheoremArtifact<MockLogic, ()>;

        fn initialization_closed(&self) -> Result<Self::Certificate, MockError> {
            Ok(TheoremArtifact {
                theorem: "|- init m i : State",
                metadata: (),
            })
        }
        fn step_closed(&self) -> Result<Self::Certificate, MockError> {
            Ok(TheoremArtifact {
                theorem: "|- step m s s' ==> State s'",
                metadata: (),
            })
        }
        fn halting_output(&self) -> Result<Self::Certificate, MockError> {
            Ok(TheoremArtifact {
                theorem: "|- halts m s ==> Output (output m s)",
                metadata: (),
            })
        }
    }

    struct NamedBackend;

    impl TheoryBackend<MockLogic, PlainSpec> for NamedBackend {
        type Facts = Facts;
        type Error = Infallible;

        fn realize(
            &self,
            _logic: &MockLogic,
            spec: &PlainSpec,
        ) -> Result<Realization<Theory<MockLogic>, Facts>, Infallible> {
            Ok(Realization {
                theory: Theory {
                    machine_type: "Machine",
                    input_type: "Input",
                    state_type: "State",
                    output_type: "Output",
                    machine: spec.name,
                    initialize: "initialize",
                    step: "step",
                    output: "output",
                    halts: "halts",
                },
                facts: Facts,
            })
        }
    }

    #[test]
    fn plain_spec_realizes_logic_owned_vocabulary_and_facts() {
        let spec = PlainSpec { name: "counter" };
        let realized = NamedBackend.realize(&MockLogic, &spec).unwrap();
        assert_eq!(realized.theory.machine(), &"counter");
        assert_eq!(realized.theory.state_type(), &"State");
        assert_eq!(
            realized.facts.step_closed().unwrap().theorem(),
            &"|- step m s s' ==> State s'"
        );
    }

    struct Replay;

    impl ReplayBackend<MockLogic, Vec<u8>> for Replay {
        type Certificate = TheoremArtifact<MockLogic, usize>;
        type Error = MockError;

        fn replay_halting(
            &self,
            _logic: &MockLogic,
            _theory: &Theory<MockLogic>,
            witness: &SearchWitness<Vec<u8>>,
        ) -> Result<Self::Certificate, MockError> {
            if witness.claim == CandidateClaim::Halts && witness.candidate == [2, 1, 0] {
                Ok(TheoremArtifact {
                    theorem: "|- halts counter 0",
                    metadata: witness.candidate.len(),
                })
            } else {
                Err(MockError)
            }
        }
    }

    #[test]
    fn search_data_has_no_authority_until_replayed() {
        let candidate = SearchWitness {
            claim: CandidateClaim::Halts,
            steps: 2,
            candidate: vec![2, 1, 0],
        };
        let realized = NamedBackend
            .realize(&MockLogic, &PlainSpec { name: "counter" })
            .unwrap();
        let theorem = Replay
            .replay_halting(&MockLogic, &realized.theory, &candidate)
            .unwrap();
        assert_eq!(theorem.theorem(), &"|- halts counter 0");
        assert_eq!(theorem.metadata, 3);
        assert!(
            Replay
                .replay_halting(
                    &MockLogic,
                    &realized.theory,
                    &SearchWitness {
                        claim: CandidateClaim::Halts,
                        steps: 1,
                        candidate: vec![2, 0],
                    }
                )
                .is_err()
        );
    }
}
