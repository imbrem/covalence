//! HOL-facing relational API for finite automata.
//!
//! @covalence-api {"id":"A0011","title":"Finite automata theories","status":"experimental","dependsOn":["A0001","A0009"]}
//!
//! The vocabulary is shared by DFAs, NFAs, and epsilon-NFAs. Determinism and
//! epsilon-closure algorithms belong to optional backends and law bundles;
//! the core transition is deliberately relational.

use covalence_hol_logic::Logic;

/// HOL vocabulary for configurations, one-step transition, closure,
/// reachability, final configurations, and word acceptance.
#[derive(Clone, Debug)]
pub struct FiniteAutomataTheory<L: Logic> {
    pub machine_type: L::Type,
    pub symbol_type: L::Type,
    pub state_type: L::Type,
    pub word_type: L::Type,
    pub configuration_type: L::Type,
    pub machine: L::Term,
    /// `configuration : state -> word -> configuration`.
    pub configuration: L::Term,
    /// `initial : machine -> word -> configuration -> prop`.
    pub initial: L::Term,
    /// `transition : machine -> configuration -> configuration -> prop`.
    pub transition: L::Term,
    /// `closure : machine -> configuration -> configuration -> prop`.
    pub closure: L::Term,
    /// `reachable : machine -> word -> configuration -> prop`.
    pub reachable: L::Term,
    /// `accepting_configuration : machine -> configuration -> prop`.
    pub accepting_configuration: L::Term,
    /// `accepts : machine -> word -> prop`.
    pub accepts: L::Term,
}

/// Read-only syntax capability, usable without assuming any laws.
pub trait FiniteAutomataSyntax<L: Logic> {
    fn theory(&self) -> &FiniteAutomataTheory<L>;
}

impl<L: Logic> FiniteAutomataSyntax<L> for FiniteAutomataTheory<L> {
    fn theory(&self) -> &FiniteAutomataTheory<L> {
        self
    }
}

/// Universal laws characterizing closure, reachability, and acceptance.
///
/// A concrete trace certificate does not implement this bundle. Backends must
/// supply genuinely universal theorems for all configurations and words.
pub trait FiniteAutomataLaws<L: Logic>: FiniteAutomataSyntax<L> {
    type Certificate;
    type Error;

    /// Every configuration is related to itself by `closure`.
    fn closure_reflexive(&self) -> Result<Self::Certificate, Self::Error>;
    /// Every one-step transition is in `closure`.
    fn transition_in_closure(&self) -> Result<Self::Certificate, Self::Error>;
    /// `closure` is transitive.
    fn closure_transitive(&self) -> Result<Self::Certificate, Self::Error>;
    /// Reachability agrees with closure from an initial configuration.
    fn reachable_iff_initial_closure(&self) -> Result<Self::Certificate, Self::Error>;
    /// Acceptance agrees with reachability of an accepting configuration.
    fn accepts_iff_reachable_final(&self) -> Result<Self::Certificate, Self::Error>;
}

/// The recognition result claimed by untrusted host search.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RecognitionClaim {
    Accepts,
    Rejects,
}

/// An untrusted automaton trace candidate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AutomataSearchWitness<W> {
    pub claim: RecognitionClaim,
    pub transitions: u64,
    pub candidate: W,
}

/// Replay rules for concrete recognition or reachability evidence.
///
/// This is intentionally independent of [`FiniteAutomataLaws`]: a backend can
/// replay one bounded theorem before proving the universal characterization.
pub trait FiniteAutomataReplay<L: Logic, W> {
    type Certificate;
    type Error;

    fn replay(
        &self,
        logic: &L,
        theory: &FiniteAutomataTheory<L>,
        witness: &AutomataSearchWitness<W>,
    ) -> Result<Self::Certificate, Self::Error>;
}

/// Optional deterministic laws. NFA and epsilon-NFA backends do not implement
/// this capability.
pub trait DeterministicFiniteAutomataLaws<L: Logic>: FiniteAutomataLaws<L> {
    fn initial_unique(&self) -> Result<Self::Certificate, Self::Error>;
    fn transition_unique(&self) -> Result<Self::Certificate, Self::Error>;
}

/// Optional epsilon-transition vocabulary layered over the finite theory.
#[derive(Clone, Debug)]
pub struct EpsilonFiniteAutomataTheory<L: Logic> {
    pub finite: FiniteAutomataTheory<L>,
    /// `epsilon_transition : machine -> state -> state -> prop`.
    pub epsilon_transition: L::Term,
    /// `epsilon_closure : machine -> state -> state -> prop`.
    pub epsilon_closure: L::Term,
}

/// Universal epsilon-closure laws, separate from ordinary closure laws.
pub trait EpsilonFiniteAutomataLaws<L: Logic>: FiniteAutomataLaws<L> {
    fn epsilon_reflexive(&self) -> Result<Self::Certificate, Self::Error>;
    fn epsilon_transition_in_closure(&self) -> Result<Self::Certificate, Self::Error>;
    fn epsilon_transitive(&self) -> Result<Self::Certificate, Self::Error>;
}
