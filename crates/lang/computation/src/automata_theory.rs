//! Proof-bearing HOL vocabulary shared by finite and pushdown automata.
//!
//! Concrete state-set, transition-table, word, and stack representations are
//! backend choices.  This module fixes only their observable interface, so a
//! dense-numeral DFA, a characteristic-function DFA, and a relational NFA can
//! implement the same consumer API.

use covalence_hol_logic::Logic;

use crate::theory::{SearchWitness, TheoremCertificate};

/// HOL terms and types describing an automaton representation.
///
/// Term conventions:
///
/// - `initial : automaton -> state -> prop`
/// - `transition : automaton -> state -> symbol -> state -> prop`
/// - `final_state : automaton -> state -> prop`
/// - `accepts : automaton -> word -> prop`
///
/// For a DFA, `initial` and `transition` have unique witnesses.  An NFA or PDA
/// deliberately uses the same relational interface without claiming those
/// laws.
#[derive(Clone, Debug)]
pub struct AutomatonTheory<L: Logic> {
    pub automaton_type: L::Type,
    pub symbol_type: L::Type,
    pub word_type: L::Type,
    pub state_type: L::Type,
    pub automaton: L::Term,
    pub initial: L::Term,
    pub transition: L::Term,
    pub final_state: L::Term,
    pub accepts: L::Term,
}

/// Additional stack vocabulary for a pushdown automaton.
#[derive(Clone, Debug)]
pub struct PushdownTheory<L: Logic> {
    pub finite: AutomatonTheory<L>,
    pub stack_symbol_type: L::Type,
    pub stack_type: L::Type,
    pub configuration_type: L::Type,
    /// `configuration : state -> word -> stack -> configuration`.
    pub configuration: L::Term,
    /// Epsilon-or-consuming PDA transition relation over configurations.
    pub pushdown_step: L::Term,
}

/// Characteristic laws for a finite-automaton realization.
pub trait AutomatonLaws<L: Logic> {
    type Certificate;

    /// `accepts` agrees with the reflexive-transitive closure of `transition`
    /// from an initial state to a final state after consuming the word.
    fn accepts_iff_run(&self) -> Result<Self::Certificate, L::Error>;
}

/// Optional deterministic finite-automaton laws.
pub trait DeterministicAutomatonLaws<L: Logic>: AutomatonLaws<L> {
    fn initial_unique(&self) -> Result<Self::Certificate, L::Error>;
    fn transition_unique(&self) -> Result<Self::Certificate, L::Error>;
}

/// Characteristic laws for a pushdown realization.
pub trait PushdownLaws<L: Logic>: AutomatonLaws<L> {
    /// The selected final-state/empty-stack acceptance policy agrees with the
    /// configuration transition closure.
    fn pushdown_accepts_iff_run(&self) -> Result<Self::Certificate, L::Error>;
}

/// Realize a plain DFA/NFA specification in a backend-selected HOL
/// representation.
pub trait AutomatonBackend<L: Logic, Spec: ?Sized> {
    type Facts: AutomatonLaws<L>;
    type Error;

    fn realize_automaton(
        &self,
        logic: &L,
        specification: &Spec,
    ) -> Result<(AutomatonTheory<L>, Self::Facts), Self::Error>;
}

/// Realize a plain PDA specification.
pub trait PushdownBackend<L: Logic, Spec: ?Sized> {
    type Facts: PushdownLaws<L>;
    type Error;

    fn realize_pushdown(
        &self,
        logic: &L,
        specification: &Spec,
    ) -> Result<(PushdownTheory<L>, Self::Facts), Self::Error>;
}

/// Replay an untrusted accepting-run search result into a backend certificate.
pub trait AutomatonReplay<L: Logic, Witness: ?Sized> {
    type Certificate;
    type Error;

    fn replay_accepting_run(
        &self,
        logic: &L,
        theory: &AutomatonTheory<L>,
        witness: &SearchWitness<Witness>,
    ) -> Result<Self::Certificate, Self::Error>;
}

/// Convenience capability for replay artifacts that expose a kernel theorem.
pub trait TheoremAutomatonReplay<L: Logic, Witness: ?Sized>: AutomatonReplay<L, Witness>
where
    Self::Certificate: TheoremCertificate<L>,
{
}

impl<L, W, R> TheoremAutomatonReplay<L, W> for R
where
    L: Logic,
    W: ?Sized,
    R: AutomatonReplay<L, W>,
    R::Certificate: TheoremCertificate<L>,
{
}
