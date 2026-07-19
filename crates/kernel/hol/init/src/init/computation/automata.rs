//! Native-HOL validation for finite- and pushdown-automaton theories.
//!
//! Automaton representations remain selectable: callers may use dense natural
//! states, predicates, quotients, or another encoding.  This adapter checks the
//! common relational signature and preserves the supplied kernel theorem which
//! connects `accepts` to runs.

use core::fmt;

use covalence_computation::automata_theory::{
    AutomatonLaws, AutomatonReplay, AutomatonTheory, PushdownLaws, PushdownTheory,
};
use covalence_computation::finite::{Dfa, EpsilonNfa};
use covalence_computation::theory::{CandidateClaim, SearchWitness, TheoremArtifact};
use covalence_core::{Error, Term, Type};
use covalence_hol_eval::{
    EvalThm as Thm,
    defs::{cons, list, nil},
};
use covalence_types::Nat;

use super::super::inductive::hol::{Hol, NativeHol};

/// A closed theorem paired with the proposition advertised by the backend.
#[derive(Clone, Debug)]
pub struct SuppliedAutomatonLaw {
    pub proposition: Term,
    pub theorem: Thm,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AutomatonLaw {
    AcceptsIffRun,
    PushdownAcceptsIffRun,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AutomatonCertificateMetadata {
    pub law: AutomatonLaw,
}

pub type AutomatonCertificate = TheoremArtifact<NativeHol, AutomatonCertificateMetadata>;

/// A complete DFA accepting run, including the initial state and one state
/// after every input symbol.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DfaAcceptingRun {
    pub input: Vec<u64>,
    pub states: Vec<usize>,
}

/// Complete epsilon-NFA subset construction run. Each entry is the canonical
/// sorted epsilon-closed state set before/after consuming a symbol.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EpsilonNfaAcceptingRun {
    pub input: Vec<u64>,
    pub state_sets: Vec<Vec<usize>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReplayKind {
    Dfa,
    EpsilonNfa,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AcceptingRunMetadata {
    pub kind: ReplayKind,
    pub input: Vec<u64>,
    pub states: Vec<Vec<usize>>,
    pub transitions: usize,
}

pub type AcceptingRunCertificate = TheoremArtifact<NativeHol, AcceptingRunMetadata>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AcceptingRunError {
    WrongClaim,
    StepCountMismatch { advertised: u64, actual: usize },
    UnknownSymbol { input_offset: usize },
    ForgedRun,
    NotAccepting,
    Kernel,
}

impl fmt::Display for AcceptingRunError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}

impl std::error::Error for AcceptingRunError {}

/// Native replay backend for one validated DFA.
pub struct DfaReplay<'a> {
    pub automaton: &'a Dfa<u64>,
}

/// Native replay backend for one validated epsilon-NFA.
pub struct EpsilonNfaReplay<'a> {
    pub automaton: &'a EpsilonNfa<u64>,
}

impl<'a> AutomatonReplay<NativeHol, DfaAcceptingRun> for DfaReplay<'a> {
    type Certificate = AcceptingRunCertificate;
    type Error = AcceptingRunError;

    fn replay_accepting_run(
        &self,
        _logic: &NativeHol,
        _theory: &AutomatonTheory<NativeHol>,
        witness: &SearchWitness<DfaAcceptingRun>,
    ) -> Result<Self::Certificate, Self::Error> {
        if witness.claim != CandidateClaim::Accepts {
            return Err(AcceptingRunError::WrongClaim);
        }
        let expected =
            self.automaton
                .run(&witness.candidate.input)
                .map_err(|error| match error {
                    covalence_computation::finite::RunError::UnknownSymbol { input_offset } => {
                        AcceptingRunError::UnknownSymbol { input_offset }
                    }
                })?;
        let transitions = witness.candidate.input.len();
        if witness.steps != transitions as u64 {
            return Err(AcceptingRunError::StepCountMismatch {
                advertised: witness.steps,
                actual: transitions,
            });
        }
        if expected.states != witness.candidate.states {
            return Err(AcceptingRunError::ForgedRun);
        }
        if !expected.accepted {
            return Err(AcceptingRunError::NotAccepting);
        }
        certify_run(
            ReplayKind::Dfa,
            witness.candidate.input.clone(),
            expected
                .states
                .into_iter()
                .map(|state| vec![state])
                .collect(),
        )
    }
}

impl<'a> AutomatonReplay<NativeHol, EpsilonNfaAcceptingRun> for EpsilonNfaReplay<'a> {
    type Certificate = AcceptingRunCertificate;
    type Error = AcceptingRunError;

    fn replay_accepting_run(
        &self,
        _logic: &NativeHol,
        _theory: &AutomatonTheory<NativeHol>,
        witness: &SearchWitness<EpsilonNfaAcceptingRun>,
    ) -> Result<Self::Certificate, Self::Error> {
        if witness.claim != CandidateClaim::Accepts {
            return Err(AcceptingRunError::WrongClaim);
        }
        let expected =
            self.automaton
                .run(&witness.candidate.input)
                .map_err(|error| match error {
                    covalence_computation::finite::RunError::UnknownSymbol { input_offset } => {
                        AcceptingRunError::UnknownSymbol { input_offset }
                    }
                })?;
        let transitions = witness.candidate.input.len();
        if witness.steps != transitions as u64 {
            return Err(AcceptingRunError::StepCountMismatch {
                advertised: witness.steps,
                actual: transitions,
            });
        }
        if expected.state_sets != witness.candidate.state_sets {
            return Err(AcceptingRunError::ForgedRun);
        }
        if !expected.accepted {
            return Err(AcceptingRunError::NotAccepting);
        }
        certify_run(
            ReplayKind::EpsilonNfa,
            witness.candidate.input.clone(),
            expected.state_sets,
        )
    }
}

fn certify_run(
    kind: ReplayKind,
    input: Vec<u64>,
    states: Vec<Vec<usize>>,
) -> Result<AcceptingRunCertificate, AcceptingRunError> {
    let transitions = input.len();
    let encoded = encode_state_sets(&states);
    let theorem = NativeHol
        .refl(encoded)
        .map_err(|_| AcceptingRunError::Kernel)?;
    Ok(TheoremArtifact {
        theorem,
        metadata: AcceptingRunMetadata {
            kind,
            input,
            states,
            transitions,
        },
    })
}

fn numeral(value: usize) -> Term {
    covalence_hol_eval::mk_nat(Nat::from_inner(value.into()))
}

fn numeral_u64(value: u64) -> Term {
    covalence_hol_eval::mk_nat(Nat::from_inner(value.into()))
}

fn nat_list(values: impl IntoIterator<Item = usize>) -> Term {
    let mut values: Vec<_> = values.into_iter().collect();
    let mut result = nil(Type::nat());
    while let Some(value) = values.pop() {
        result = Term::app(Term::app(cons(Type::nat()), numeral(value)), result);
    }
    result
}

fn encode_state_sets(states: &[Vec<usize>]) -> Term {
    let state_set_type = list(Type::nat());
    let mut result = nil(state_set_type.clone());
    for states in states.iter().rev() {
        result = Term::app(
            Term::app(
                cons(state_set_type.clone()),
                nat_list(states.iter().copied()),
            ),
            result,
        );
    }
    result
}

/// Canonical `list nat` vocabulary shared by concrete finite automata.
pub fn concrete_theory(machine: Term) -> AutomatonTheory<NativeHol> {
    let data = list(Type::nat());
    AutomatonTheory {
        automaton_type: data.clone(),
        symbol_type: Type::nat(),
        word_type: data.clone(),
        state_type: Type::nat(),
        automaton: machine,
        initial: Term::free(
            "automata.initial",
            Type::fun(data.clone(), Type::fun(Type::nat(), Type::bool())),
        ),
        transition: Term::free(
            "automata.transition",
            Type::fun(
                data.clone(),
                Type::fun(
                    Type::nat(),
                    Type::fun(Type::nat(), Type::fun(Type::nat(), Type::bool())),
                ),
            ),
        ),
        final_state: Term::free(
            "automata.final",
            Type::fun(data.clone(), Type::fun(Type::nat(), Type::bool())),
        ),
        accepts: Term::free(
            "automata.accepts",
            Type::fun(data.clone(), Type::fun(data, Type::bool())),
        ),
    }
}

/// Canonical table serialization: tag, alphabet, initial, accepting bitmap,
/// then the row-major transition table, all length-prefixed where necessary.
pub fn encode_dfa(machine: &Dfa<u64>) -> Term {
    let mut words = vec![0, machine.alphabet().len() as u64];
    words.extend(machine.alphabet());
    words.extend([machine.state_count() as u64, machine.initial_state() as u64]);
    words.extend(
        (0..machine.state_count()).map(|state| u64::from(machine.is_accepting_state(state))),
    );
    for state in 0..machine.state_count() {
        for symbol in 0..machine.alphabet().len() {
            words.push(
                machine
                    .transition_target(state, symbol)
                    .expect("validated DFA has a complete table") as u64,
            );
        }
    }
    nat_list_u64(words)
}

/// Canonical epsilon-NFA serialization with sorted state sets inherited from
/// the validated plain-data model.
pub fn encode_epsilon_nfa(machine: &EpsilonNfa<u64>) -> Term {
    let mut words = vec![1, machine.alphabet().len() as u64];
    words.extend(machine.alphabet());
    words.push(machine.state_count() as u64);
    append_set(&mut words, machine.initial_states());
    let accepting: Vec<_> = (0..machine.state_count())
        .filter(|state| machine.is_accepting_state(*state))
        .collect();
    append_set(&mut words, &accepting);
    for state in 0..machine.state_count() {
        for symbol in 0..machine.alphabet().len() {
            append_set(
                &mut words,
                machine
                    .transition_targets(state, symbol)
                    .expect("validated epsilon-NFA has a complete table"),
            );
        }
        append_set(
            &mut words,
            machine
                .epsilon_targets(state)
                .expect("validated epsilon-NFA has an epsilon row"),
        );
    }
    nat_list_u64(words)
}

fn append_set(words: &mut Vec<u64>, states: &[usize]) {
    words.push(states.len() as u64);
    words.extend(states.iter().map(|state| *state as u64));
}

fn nat_list_u64(values: impl IntoIterator<Item = u64>) -> Term {
    let mut values: Vec<_> = values.into_iter().collect();
    let mut result = nil(Type::nat());
    while let Some(value) = values.pop() {
        result = Term::app(Term::app(cons(Type::nat()), numeral_u64(value)), result);
    }
    result
}

pub fn dfa_theory(machine: &Dfa<u64>) -> AutomatonTheory<NativeHol> {
    concrete_theory(encode_dfa(machine))
}

pub fn epsilon_nfa_theory(machine: &EpsilonNfa<u64>) -> AutomatonTheory<NativeHol> {
    concrete_theory(encode_epsilon_nfa(machine))
}

#[derive(Clone, Debug)]
pub struct ValidatedAutomatonFacts {
    accepts_iff_run: AutomatonCertificate,
}

impl AutomatonLaws<NativeHol> for ValidatedAutomatonFacts {
    type Certificate = AutomatonCertificate;

    fn accepts_iff_run(&self) -> Result<Self::Certificate, Error> {
        Ok(self.accepts_iff_run.clone())
    }
}

#[derive(Clone, Debug)]
pub struct ValidatedPushdownFacts {
    accepts_iff_run: AutomatonCertificate,
    pushdown_accepts_iff_run: AutomatonCertificate,
}

impl AutomatonLaws<NativeHol> for ValidatedPushdownFacts {
    type Certificate = AutomatonCertificate;

    fn accepts_iff_run(&self) -> Result<Self::Certificate, Error> {
        Ok(self.accepts_iff_run.clone())
    }
}

impl PushdownLaws<NativeHol> for ValidatedPushdownFacts {
    fn pushdown_accepts_iff_run(&self) -> Result<Self::Certificate, Error> {
        Ok(self.pushdown_accepts_iff_run.clone())
    }
}

#[derive(Debug)]
pub enum AutomatonTheoryError {
    Kernel(Error),
    TypeMismatch {
        field: &'static str,
        expected: Type,
        actual: Type,
    },
    LawNotBoolean {
        law: AutomatonLaw,
        actual: Type,
    },
    LawConclusionMismatch {
        law: AutomatonLaw,
    },
    LawHasHypotheses {
        law: AutomatonLaw,
        count: usize,
    },
}

impl fmt::Display for AutomatonTheoryError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Kernel(error) => write!(f, "HOL kernel rejected automaton theory: {error}"),
            Self::TypeMismatch {
                field,
                expected,
                actual,
            } => write!(f, "`{field}` has type {actual}, expected {expected}"),
            Self::LawNotBoolean { law, actual } => {
                write!(f, "{law:?} has type {actual}, expected bool")
            }
            Self::LawConclusionMismatch { law } => {
                write!(
                    f,
                    "{law:?} theorem does not prove its advertised proposition"
                )
            }
            Self::LawHasHypotheses { law, count } => {
                write!(f, "{law:?} has {count} undischarged hypothesis(es)")
            }
        }
    }
}

impl std::error::Error for AutomatonTheoryError {}

impl From<Error> for AutomatonTheoryError {
    fn from(value: Error) -> Self {
        Self::Kernel(value)
    }
}

/// Validate a native DFA/NFA vocabulary and its run-characterization theorem.
pub fn validate_automaton(
    theory: AutomatonTheory<NativeHol>,
    law: SuppliedAutomatonLaw,
) -> Result<(AutomatonTheory<NativeHol>, ValidatedAutomatonFacts), AutomatonTheoryError> {
    validate_finite_vocabulary(&theory)?;
    Ok((
        theory,
        ValidatedAutomatonFacts {
            accepts_iff_run: validate_law(AutomatonLaw::AcceptsIffRun, law)?,
        },
    ))
}

/// Validate a native PDA vocabulary and both acceptance theorems.
pub fn validate_pushdown(
    theory: PushdownTheory<NativeHol>,
    finite_law: SuppliedAutomatonLaw,
    pushdown_law: SuppliedAutomatonLaw,
) -> Result<(PushdownTheory<NativeHol>, ValidatedPushdownFacts), AutomatonTheoryError> {
    validate_finite_vocabulary(&theory.finite)?;
    check(
        "configuration",
        &theory.configuration,
        arrow(
            theory.finite.state_type.clone(),
            arrow(
                theory.finite.word_type.clone(),
                arrow(theory.stack_type.clone(), theory.configuration_type.clone()),
            ),
        ),
    )?;
    check(
        "pushdown_step",
        &theory.pushdown_step,
        arrow(
            theory.finite.automaton_type.clone(),
            arrow(
                theory.configuration_type.clone(),
                arrow(theory.configuration_type.clone(), Type::bool()),
            ),
        ),
    )?;
    Ok((
        theory,
        ValidatedPushdownFacts {
            accepts_iff_run: validate_law(AutomatonLaw::AcceptsIffRun, finite_law)?,
            pushdown_accepts_iff_run: validate_law(
                AutomatonLaw::PushdownAcceptsIffRun,
                pushdown_law,
            )?,
        },
    ))
}

fn validate_finite_vocabulary(
    theory: &AutomatonTheory<NativeHol>,
) -> Result<(), AutomatonTheoryError> {
    check(
        "automaton",
        &theory.automaton,
        theory.automaton_type.clone(),
    )?;
    check(
        "initial",
        &theory.initial,
        arrow(
            theory.automaton_type.clone(),
            arrow(theory.state_type.clone(), Type::bool()),
        ),
    )?;
    check(
        "transition",
        &theory.transition,
        arrow(
            theory.automaton_type.clone(),
            arrow(
                theory.state_type.clone(),
                arrow(
                    theory.symbol_type.clone(),
                    arrow(theory.state_type.clone(), Type::bool()),
                ),
            ),
        ),
    )?;
    check(
        "final_state",
        &theory.final_state,
        arrow(
            theory.automaton_type.clone(),
            arrow(theory.state_type.clone(), Type::bool()),
        ),
    )?;
    check(
        "accepts",
        &theory.accepts,
        arrow(
            theory.automaton_type.clone(),
            arrow(theory.word_type.clone(), Type::bool()),
        ),
    )
}

fn arrow(domain: Type, codomain: Type) -> Type {
    Type::fun(domain, codomain)
}

fn check(field: &'static str, term: &Term, expected: Type) -> Result<(), AutomatonTheoryError> {
    let actual = Hol::type_of(&NativeHol, term)?;
    if actual == expected {
        Ok(())
    } else {
        Err(AutomatonTheoryError::TypeMismatch {
            field,
            expected,
            actual,
        })
    }
}

fn validate_law(
    law: AutomatonLaw,
    supplied: SuppliedAutomatonLaw,
) -> Result<AutomatonCertificate, AutomatonTheoryError> {
    let actual_type = Hol::type_of(&NativeHol, &supplied.proposition)?;
    if actual_type != Type::bool() {
        return Err(AutomatonTheoryError::LawNotBoolean {
            law,
            actual: actual_type,
        });
    }
    if Hol::concl(&NativeHol, &supplied.theorem) != supplied.proposition {
        return Err(AutomatonTheoryError::LawConclusionMismatch { law });
    }
    let count = Hol::hyps(&NativeHol, &supplied.theorem).len();
    if count != 0 {
        return Err(AutomatonTheoryError::LawHasHypotheses { law, count });
    }
    Ok(TheoremArtifact {
        theorem: supplied.theorem,
        metadata: AutomatonCertificateMetadata { law },
    })
}

// TODO(cov:computation.automata-native-definitions, major): Define the
// canonical DFA, NFA, epsilon-NFA, and PDA table relations inside HOL.
// TODO(cov:computation.automata-accepts-iff-run, major): Prove the universal
// accepts-iff-run laws and lift checked concrete runs to those predicates.
// TODO(cov:computation.automata-partial-compilers, major): Implement
// proof-bearing partial compilers from finite-state-restricted machines to
// automata, with certified domain predicates.
// TODO(cov:computation.pda-acceptance-replay, major): Extract and replay one
// complete accepting PDA path from bounded breadth-first search.

#[cfg(test)]
mod tests {
    use super::*;
    use crate::init::inductive::hol::Hol;
    use covalence_computation::theory::TheoremCertificate;

    fn theory() -> AutomatonTheory<NativeHol> {
        let automaton_type = Type::tfree("automaton");
        let symbol_type = Type::tfree("symbol");
        let word_type = Type::tfree("word");
        let state_type = Type::tfree("state");
        AutomatonTheory {
            automaton: Term::free("a", automaton_type.clone()),
            initial: Term::free(
                "initial",
                arrow(
                    automaton_type.clone(),
                    arrow(state_type.clone(), Type::bool()),
                ),
            ),
            transition: Term::free(
                "transition",
                arrow(
                    automaton_type.clone(),
                    arrow(
                        state_type.clone(),
                        arrow(symbol_type.clone(), arrow(state_type.clone(), Type::bool())),
                    ),
                ),
            ),
            final_state: Term::free(
                "final",
                arrow(
                    automaton_type.clone(),
                    arrow(state_type.clone(), Type::bool()),
                ),
            ),
            accepts: Term::free(
                "accepts",
                arrow(
                    automaton_type.clone(),
                    arrow(word_type.clone(), Type::bool()),
                ),
            ),
            automaton_type,
            symbol_type,
            word_type,
            state_type,
        }
    }

    fn law() -> SuppliedAutomatonLaw {
        let proposition = Term::free("accepts_iff_run", Type::bool());
        let theorem = NativeHol.refl(proposition).unwrap();
        SuppliedAutomatonLaw {
            proposition: Hol::concl(&NativeHol, &theorem),
            theorem,
        }
    }

    #[test]
    fn validates_representation_independent_automaton_signature() {
        let (theory, facts) = validate_automaton(theory(), law()).unwrap();
        assert_eq!(
            Hol::type_of(&NativeHol, &theory.accepts).unwrap(),
            Type::fun(
                theory.automaton_type.clone(),
                Type::fun(theory.word_type.clone(), Type::bool()),
            )
        );
        assert!(facts.accepts_iff_run().is_ok());
    }

    #[test]
    fn rejects_an_untyped_transition_relation() {
        let mut invalid = theory();
        invalid.transition = Term::free("transition", Type::bool());
        assert!(matches!(
            validate_automaton(invalid, law()),
            Err(AutomatonTheoryError::TypeMismatch {
                field: "transition",
                ..
            })
        ));
    }

    fn parity_dfa() -> Dfa<u64> {
        Dfa::new(vec![0, 1], 0, vec![0], vec![vec![0, 1], vec![1, 0]]).unwrap()
    }

    #[test]
    fn dfa_replay_checks_the_complete_accepting_run() {
        let automaton = parity_dfa();
        let input = vec![1, 0, 1];
        let states = automaton.run(&input).unwrap().states;
        let witness = SearchWitness {
            claim: CandidateClaim::Accepts,
            steps: input.len() as u64,
            candidate: DfaAcceptingRun { input, states },
        };
        let certificate = DfaReplay {
            automaton: &automaton,
        }
        .replay_accepting_run(&NativeHol, &dfa_theory(&automaton), &witness)
        .unwrap();
        assert_eq!(certificate.metadata.transitions, 3);
        assert_eq!(certificate.metadata.kind, ReplayKind::Dfa);
        assert!(NativeHol.hyps(certificate.theorem()).is_empty());
    }

    #[test]
    fn dfa_replay_rejects_a_forged_middle_state() {
        let automaton = parity_dfa();
        let input = vec![1, 0, 1];
        let mut states = automaton.run(&input).unwrap().states;
        states[1] = 0;
        let witness = SearchWitness {
            claim: CandidateClaim::Accepts,
            steps: input.len() as u64,
            candidate: DfaAcceptingRun { input, states },
        };
        assert!(matches!(
            DfaReplay {
                automaton: &automaton
            }
            .replay_accepting_run(&NativeHol, &dfa_theory(&automaton), &witness),
            Err(AcceptingRunError::ForgedRun)
        ));
    }

    #[test]
    fn epsilon_nfa_replay_checks_closure_at_every_position() {
        let automaton = EpsilonNfa::new(
            vec![7],
            vec![0],
            vec![2],
            vec![vec![vec![]], vec![vec![2]], vec![vec![]]],
            vec![vec![1], vec![], vec![]],
        )
        .unwrap();
        let input = vec![7];
        let state_sets = automaton.run(&input).unwrap().state_sets;
        let witness = SearchWitness {
            claim: CandidateClaim::Accepts,
            steps: 1,
            candidate: EpsilonNfaAcceptingRun { input, state_sets },
        };
        let certificate = EpsilonNfaReplay {
            automaton: &automaton,
        }
        .replay_accepting_run(&NativeHol, &epsilon_nfa_theory(&automaton), &witness)
        .unwrap();
        assert_eq!(certificate.metadata.states, vec![vec![0, 1], vec![2]]);
        assert_eq!(certificate.metadata.kind, ReplayKind::EpsilonNfa);
    }
}
