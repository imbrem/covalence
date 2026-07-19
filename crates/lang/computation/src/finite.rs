//! Dependency-free finite-state automata.
//!
//! States are dense integer identifiers and alphabets are explicit ordered
//! vectors. This makes automata easy to validate, serialize, and audit. NFA
//! state sets are represented as sorted, duplicate-free `Vec<usize>` values.

use core::fmt;

/// A recognizer for finite words over `Symbol`.
pub trait Recognizer<Symbol> {
    fn accepts(&self, input: &[Symbol]) -> bool;
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ValidationError {
    NoStates,
    DuplicateSymbol {
        first: usize,
        duplicate: usize,
    },
    InvalidInitialState {
        state: usize,
        state_count: usize,
    },
    InvalidAcceptingState {
        state: usize,
        state_count: usize,
    },
    WrongTransitionRowCount {
        expected: usize,
        actual: usize,
    },
    WrongTransitionColumnCount {
        state: usize,
        expected: usize,
        actual: usize,
    },
    InvalidTransitionTarget {
        source: usize,
        symbol: Option<usize>,
        target: usize,
        state_count: usize,
    },
}

impl fmt::Display for ValidationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NoStates => write!(f, "an automaton must have at least one state"),
            Self::DuplicateSymbol { first, duplicate } => write!(
                f,
                "alphabet entries {first} and {duplicate} are duplicate symbols"
            ),
            Self::InvalidInitialState { state, state_count } => write!(
                f,
                "initial state {state} is outside the {state_count} states"
            ),
            Self::InvalidAcceptingState { state, state_count } => write!(
                f,
                "accepting state {state} is outside the {state_count} states"
            ),
            Self::WrongTransitionRowCount { expected, actual } => {
                write!(f, "expected {expected} transition rows, found {actual}")
            }
            Self::WrongTransitionColumnCount {
                state,
                expected,
                actual,
            } => write!(
                f,
                "state {state} has {actual} transition columns; expected {expected}"
            ),
            Self::InvalidTransitionTarget {
                source,
                symbol,
                target,
                state_count,
            } => match symbol {
                Some(symbol) => write!(
                    f,
                    "transition from state {source} on alphabet entry {symbol} targets \
                     state {target}, outside the {state_count} states"
                ),
                None => write!(
                    f,
                    "epsilon transition from state {source} targets state {target}, \
                     outside the {state_count} states"
                ),
            },
        }
    }
}

impl std::error::Error for ValidationError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RunError {
    UnknownSymbol { input_offset: usize },
}

impl fmt::Display for RunError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnknownSymbol { input_offset } => {
                write!(f, "unknown alphabet symbol at input offset {input_offset}")
            }
        }
    }
}

impl std::error::Error for RunError {}

/// A complete deterministic finite automaton.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Dfa<Symbol> {
    alphabet: Vec<Symbol>,
    initial: usize,
    accepting: Vec<bool>,
    transitions: Vec<Vec<usize>>,
}

impl<Symbol: Eq> Dfa<Symbol> {
    pub fn new(
        alphabet: Vec<Symbol>,
        initial: usize,
        accepting_states: Vec<usize>,
        transitions: Vec<Vec<usize>>,
    ) -> Result<Self, ValidationError> {
        validate_shape(&alphabet, initial, &accepting_states, &transitions)?;
        let state_count = transitions.len();
        for (source, row) in transitions.iter().enumerate() {
            for (symbol, target) in row.iter().copied().enumerate() {
                validate_target(source, Some(symbol), target, state_count)?;
            }
        }
        Ok(Self {
            alphabet,
            initial,
            accepting: accepting_bits(state_count, &accepting_states),
            transitions,
        })
    }

    pub fn alphabet(&self) -> &[Symbol] {
        &self.alphabet
    }

    pub fn state_count(&self) -> usize {
        self.transitions.len()
    }

    pub fn initial_state(&self) -> usize {
        self.initial
    }

    pub fn is_accepting_state(&self, state: usize) -> bool {
        self.accepting.get(state).copied().unwrap_or(false)
    }

    pub fn transition_target(&self, state: usize, alphabet_index: usize) -> Option<usize> {
        self.transitions
            .get(state)
            .and_then(|row| row.get(alphabet_index))
            .copied()
    }

    pub fn run(&self, input: &[Symbol]) -> Result<DfaTrace, RunError> {
        let mut state = self.initial;
        let mut states = Vec::with_capacity(input.len().saturating_add(1));
        states.push(state);
        for (input_offset, symbol) in input.iter().enumerate() {
            let alphabet_index = symbol_index(&self.alphabet, symbol)
                .ok_or(RunError::UnknownSymbol { input_offset })?;
            state = self.transitions[state][alphabet_index];
            states.push(state);
        }
        Ok(DfaTrace {
            accepted: self.accepting[state],
            states,
        })
    }

    /// Returns all states reachable from the initial state, in ascending order.
    pub fn reachable_states(&self) -> Vec<usize> {
        let mut seen = vec![false; self.state_count()];
        let mut pending = vec![self.initial];
        seen[self.initial] = true;
        while let Some(state) = pending.pop() {
            for target in self.transitions[state].iter().copied() {
                if !seen[target] {
                    seen[target] = true;
                    pending.push(target);
                }
            }
        }
        seen.into_iter()
            .enumerate()
            .filter_map(|(state, reachable)| reachable.then_some(state))
            .collect()
    }
}

impl<Symbol: Eq> Recognizer<Symbol> for Dfa<Symbol> {
    fn accepts(&self, input: &[Symbol]) -> bool {
        self.run(input).map(|trace| trace.accepted).unwrap_or(false)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DfaTrace {
    /// Includes the initial state, followed by one state per consumed symbol.
    pub states: Vec<usize>,
    pub accepted: bool,
}

/// A nondeterministic finite automaton without epsilon transitions.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Nfa<Symbol> {
    alphabet: Vec<Symbol>,
    initial: Vec<usize>,
    accepting: Vec<bool>,
    transitions: Vec<Vec<Vec<usize>>>,
}

impl<Symbol: Eq> Nfa<Symbol> {
    pub fn new(
        alphabet: Vec<Symbol>,
        initial_states: Vec<usize>,
        accepting_states: Vec<usize>,
        mut transitions: Vec<Vec<Vec<usize>>>,
    ) -> Result<Self, ValidationError> {
        let state_count = transitions.len();
        validate_common(&alphabet, state_count, &initial_states, &accepting_states)?;
        for (source, row) in transitions.iter_mut().enumerate() {
            if row.len() != alphabet.len() {
                return Err(ValidationError::WrongTransitionColumnCount {
                    state: source,
                    expected: alphabet.len(),
                    actual: row.len(),
                });
            }
            for (symbol, targets) in row.iter_mut().enumerate() {
                normalize_set(targets);
                for target in targets.iter().copied() {
                    validate_target(source, Some(symbol), target, state_count)?;
                }
            }
        }
        let mut initial = initial_states;
        normalize_set(&mut initial);
        Ok(Self {
            alphabet,
            initial,
            accepting: accepting_bits(state_count, &accepting_states),
            transitions,
        })
    }

    pub fn run(&self, input: &[Symbol]) -> Result<NfaTrace, RunError> {
        let mut current = self.initial.clone();
        let mut state_sets = vec![current.clone()];
        for (input_offset, symbol) in input.iter().enumerate() {
            let alphabet_index = symbol_index(&self.alphabet, symbol)
                .ok_or(RunError::UnknownSymbol { input_offset })?;
            current = move_set(&current, alphabet_index, &self.transitions);
            state_sets.push(current.clone());
        }
        Ok(NfaTrace {
            accepted: set_accepts(&current, &self.accepting),
            state_sets,
        })
    }

    pub fn determinize(&self) -> Determinization<Symbol>
    where
        Symbol: Clone,
    {
        determinize_from(
            self.alphabet.clone(),
            self.initial.clone(),
            &self.accepting,
            |states, symbol| move_set(states, symbol, &self.transitions),
        )
    }
}

impl<Symbol: Eq> Recognizer<Symbol> for Nfa<Symbol> {
    fn accepts(&self, input: &[Symbol]) -> bool {
        self.run(input).map(|trace| trace.accepted).unwrap_or(false)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NfaTrace {
    /// Includes the initial set, followed by one set per consumed symbol.
    pub state_sets: Vec<Vec<usize>>,
    pub accepted: bool,
}

/// A nondeterministic finite automaton with explicit epsilon transitions.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EpsilonNfa<Symbol> {
    alphabet: Vec<Symbol>,
    initial: Vec<usize>,
    accepting: Vec<bool>,
    transitions: Vec<Vec<Vec<usize>>>,
    epsilon: Vec<Vec<usize>>,
}

impl<Symbol: Eq> EpsilonNfa<Symbol> {
    pub fn new(
        alphabet: Vec<Symbol>,
        initial_states: Vec<usize>,
        accepting_states: Vec<usize>,
        mut transitions: Vec<Vec<Vec<usize>>>,
        mut epsilon: Vec<Vec<usize>>,
    ) -> Result<Self, ValidationError> {
        let state_count = transitions.len();
        validate_common(&alphabet, state_count, &initial_states, &accepting_states)?;
        if epsilon.len() != state_count {
            return Err(ValidationError::WrongTransitionRowCount {
                expected: state_count,
                actual: epsilon.len(),
            });
        }
        for (source, row) in transitions.iter_mut().enumerate() {
            if row.len() != alphabet.len() {
                return Err(ValidationError::WrongTransitionColumnCount {
                    state: source,
                    expected: alphabet.len(),
                    actual: row.len(),
                });
            }
            for (symbol, targets) in row.iter_mut().enumerate() {
                normalize_set(targets);
                for target in targets.iter().copied() {
                    validate_target(source, Some(symbol), target, state_count)?;
                }
            }
        }
        for (source, targets) in epsilon.iter_mut().enumerate() {
            normalize_set(targets);
            for target in targets.iter().copied() {
                validate_target(source, None, target, state_count)?;
            }
        }
        let mut initial = initial_states;
        normalize_set(&mut initial);
        Ok(Self {
            alphabet,
            initial,
            accepting: accepting_bits(state_count, &accepting_states),
            transitions,
            epsilon,
        })
    }

    pub fn epsilon_closure(&self, states: &[usize]) -> Vec<usize> {
        epsilon_closure(states, &self.epsilon)
    }

    pub fn alphabet(&self) -> &[Symbol] {
        &self.alphabet
    }

    pub fn state_count(&self) -> usize {
        self.transitions.len()
    }

    pub fn initial_states(&self) -> &[usize] {
        &self.initial
    }

    pub fn is_accepting_state(&self, state: usize) -> bool {
        self.accepting.get(state).copied().unwrap_or(false)
    }

    pub fn transition_targets(&self, state: usize, alphabet_index: usize) -> Option<&[usize]> {
        self.transitions
            .get(state)
            .and_then(|row| row.get(alphabet_index))
            .map(Vec::as_slice)
    }

    pub fn epsilon_targets(&self, state: usize) -> Option<&[usize]> {
        self.epsilon.get(state).map(Vec::as_slice)
    }

    pub fn run(&self, input: &[Symbol]) -> Result<NfaTrace, RunError> {
        let mut current = self.epsilon_closure(&self.initial);
        let mut state_sets = vec![current.clone()];
        for (input_offset, symbol) in input.iter().enumerate() {
            let alphabet_index = symbol_index(&self.alphabet, symbol)
                .ok_or(RunError::UnknownSymbol { input_offset })?;
            current = self.epsilon_closure(&move_set(&current, alphabet_index, &self.transitions));
            state_sets.push(current.clone());
        }
        Ok(NfaTrace {
            accepted: set_accepts(&current, &self.accepting),
            state_sets,
        })
    }

    pub fn determinize(&self) -> Determinization<Symbol>
    where
        Symbol: Clone,
    {
        let initial = self.epsilon_closure(&self.initial);
        determinize_from(
            self.alphabet.clone(),
            initial,
            &self.accepting,
            |states, symbol| self.epsilon_closure(&move_set(states, symbol, &self.transitions)),
        )
    }
}

impl<Symbol: Eq> Recognizer<Symbol> for EpsilonNfa<Symbol> {
    fn accepts(&self, input: &[Symbol]) -> bool {
        self.run(input).map(|trace| trace.accepted).unwrap_or(false)
    }
}

/// A DFA together with the NFA-state subset represented by every DFA state.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Determinization<Symbol> {
    pub dfa: Dfa<Symbol>,
    pub subsets: Vec<Vec<usize>>,
}

fn determinize_from<Symbol: Clone + Eq>(
    alphabet: Vec<Symbol>,
    initial: Vec<usize>,
    accepting: &[bool],
    transition: impl Fn(&[usize], usize) -> Vec<usize>,
) -> Determinization<Symbol> {
    let mut subsets = vec![initial];
    let mut rows = Vec::new();
    let mut cursor = 0;
    while cursor < subsets.len() {
        let mut row = Vec::with_capacity(alphabet.len());
        for symbol in 0..alphabet.len() {
            let target = transition(&subsets[cursor], symbol);
            let target_index = subsets
                .iter()
                .position(|known| *known == target)
                .unwrap_or_else(|| {
                    subsets.push(target);
                    subsets.len() - 1
                });
            row.push(target_index);
        }
        rows.push(row);
        cursor += 1;
    }
    let accepting_states = subsets
        .iter()
        .enumerate()
        .filter_map(|(state, subset)| set_accepts(subset, accepting).then_some(state))
        .collect();
    let dfa = Dfa::new(alphabet, 0, accepting_states, rows)
        .expect("subset construction produces a valid complete DFA");
    Determinization { dfa, subsets }
}

fn validate_shape<Symbol: Eq, Target>(
    alphabet: &[Symbol],
    initial: usize,
    accepting: &[usize],
    transitions: &[Vec<Target>],
) -> Result<(), ValidationError> {
    validate_common(alphabet, transitions.len(), &[initial], accepting)?;
    for (state, row) in transitions.iter().enumerate() {
        if row.len() != alphabet.len() {
            return Err(ValidationError::WrongTransitionColumnCount {
                state,
                expected: alphabet.len(),
                actual: row.len(),
            });
        }
    }
    Ok(())
}

fn validate_common<Symbol: Eq>(
    alphabet: &[Symbol],
    state_count: usize,
    initial: &[usize],
    accepting: &[usize],
) -> Result<(), ValidationError> {
    if state_count == 0 {
        return Err(ValidationError::NoStates);
    }
    for duplicate in 0..alphabet.len() {
        if let Some(first) = alphabet[..duplicate]
            .iter()
            .position(|symbol| symbol == &alphabet[duplicate])
        {
            return Err(ValidationError::DuplicateSymbol { first, duplicate });
        }
    }
    for state in initial.iter().copied() {
        if state >= state_count {
            return Err(ValidationError::InvalidInitialState { state, state_count });
        }
    }
    for state in accepting.iter().copied() {
        if state >= state_count {
            return Err(ValidationError::InvalidAcceptingState { state, state_count });
        }
    }
    Ok(())
}

fn validate_target(
    source: usize,
    symbol: Option<usize>,
    target: usize,
    state_count: usize,
) -> Result<(), ValidationError> {
    if target < state_count {
        Ok(())
    } else {
        Err(ValidationError::InvalidTransitionTarget {
            source,
            symbol,
            target,
            state_count,
        })
    }
}

fn accepting_bits(state_count: usize, accepting: &[usize]) -> Vec<bool> {
    let mut bits = vec![false; state_count];
    for state in accepting.iter().copied() {
        bits[state] = true;
    }
    bits
}

fn symbol_index<Symbol: Eq>(alphabet: &[Symbol], symbol: &Symbol) -> Option<usize> {
    alphabet.iter().position(|candidate| candidate == symbol)
}

fn normalize_set(states: &mut Vec<usize>) {
    states.sort_unstable();
    states.dedup();
}

fn move_set(states: &[usize], symbol: usize, transitions: &[Vec<Vec<usize>>]) -> Vec<usize> {
    let mut result = Vec::new();
    for state in states.iter().copied() {
        result.extend(transitions[state][symbol].iter().copied());
    }
    normalize_set(&mut result);
    result
}

fn epsilon_closure(states: &[usize], epsilon: &[Vec<usize>]) -> Vec<usize> {
    let mut closure = states.to_vec();
    normalize_set(&mut closure);
    let mut seen = vec![false; epsilon.len()];
    let mut pending = closure.clone();
    for state in closure.iter().copied() {
        seen[state] = true;
    }
    while let Some(state) = pending.pop() {
        for target in epsilon[state].iter().copied() {
            if !seen[target] {
                seen[target] = true;
                closure.push(target);
                pending.push(target);
            }
        }
    }
    normalize_set(&mut closure);
    closure
}

fn set_accepts(states: &[usize], accepting: &[bool]) -> bool {
    states.iter().copied().any(|state| accepting[state])
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dfa_trace_and_reachability() {
        // Even number of ones, plus an unreachable state.
        let dfa = Dfa::new(
            vec![false, true],
            0,
            vec![0],
            vec![vec![0, 1], vec![1, 0], vec![2, 2]],
        )
        .unwrap();
        let trace = dfa.run(&[true, false, true]).unwrap();
        assert_eq!(trace.states, vec![0, 1, 1, 0]);
        assert!(trace.accepted);
        assert_eq!(dfa.reachable_states(), vec![0, 1]);
        assert_eq!(dfa.run(&[true, true, false, false]).unwrap().accepted, true);
    }

    #[test]
    fn validation_reports_structural_errors() {
        assert_eq!(
            Dfa::new(vec!['a', 'a'], 0, vec![], vec![vec![0, 0]]),
            Err(ValidationError::DuplicateSymbol {
                first: 0,
                duplicate: 1
            })
        );
        assert_eq!(
            Dfa::new(vec!['a'], 0, vec![], vec![vec![1]]),
            Err(ValidationError::InvalidTransitionTarget {
                source: 0,
                symbol: Some(0),
                target: 1,
                state_count: 1
            })
        );
    }

    #[test]
    fn nfa_tracks_all_possible_states() {
        // Contains the substring "ab".
        let nfa = Nfa::new(
            vec!['a', 'b'],
            vec![0],
            vec![2],
            vec![
                vec![vec![0, 1], vec![0]],
                vec![vec![1], vec![2]],
                vec![vec![2], vec![2]],
            ],
        )
        .unwrap();
        let trace = nfa.run(&['b', 'a', 'a', 'b']).unwrap();
        assert_eq!(
            trace.state_sets,
            vec![vec![0], vec![0], vec![0, 1], vec![0, 1], vec![0, 2]]
        );
        assert!(trace.accepted);
        assert!(!nfa.accepts(&['b', 'b', 'a']));
    }

    #[test]
    fn epsilon_closure_is_transitive_and_cycle_safe() {
        let nfa = EpsilonNfa::new(
            vec!['x'],
            vec![0],
            vec![2],
            vec![vec![vec![]], vec![vec![]], vec![vec![2]]],
            vec![vec![1], vec![0, 2], vec![]],
        )
        .unwrap();
        assert_eq!(nfa.epsilon_closure(&[0]), vec![0, 1, 2]);
        assert!(nfa.accepts(&[]));
        assert!(nfa.accepts(&['x']));
    }

    #[test]
    fn determinization_agrees_with_nfa_language() {
        let nfa = Nfa::new(
            vec![false, true],
            vec![0],
            vec![2],
            vec![
                vec![vec![0], vec![0, 1]],
                vec![vec![2], vec![1]],
                vec![vec![2], vec![2]],
            ],
        )
        .unwrap();
        let deterministic = nfa.determinize();
        for length in 0..7 {
            for word in 0usize..(1usize << length) {
                let input: Vec<bool> = (0..length)
                    .map(|offset| word & (1 << offset) != 0)
                    .collect();
                assert_eq!(
                    nfa.accepts(&input),
                    deterministic.dfa.accepts(&input),
                    "language mismatch for {input:?}"
                );
            }
        }
        assert_eq!(deterministic.subsets[0], vec![0]);
    }

    #[test]
    fn determinization_agrees_with_epsilon_nfa_language() {
        // a* b, with epsilon edges selecting the a-loop or final b edge.
        let nfa = EpsilonNfa::new(
            vec!['a', 'b'],
            vec![0],
            vec![3],
            vec![
                vec![vec![], vec![]],
                vec![vec![1], vec![]],
                vec![vec![], vec![3]],
                vec![vec![], vec![]],
            ],
            vec![vec![1, 2], vec![2], vec![], vec![]],
        )
        .unwrap();
        let deterministic = nfa.determinize();
        for input in [
            vec![],
            vec!['b'],
            vec!['a', 'b'],
            vec!['a', 'a', 'b'],
            vec!['a'],
            vec!['b', 'a'],
        ] {
            assert_eq!(
                nfa.accepts(&input),
                deterministic.dfa.accepts(&input),
                "language mismatch for {input:?}"
            );
        }
    }

    #[test]
    fn unknown_symbols_are_explicit_run_errors() {
        let dfa = Dfa::new(vec!['a'], 0, vec![0], vec![vec![0]]).unwrap();
        assert_eq!(
            dfa.run(&['a', 'z']),
            Err(RunError::UnknownSymbol { input_offset: 1 })
        );
        assert!(!dfa.accepts(&['z']));
    }
}
