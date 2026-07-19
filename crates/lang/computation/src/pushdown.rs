//! Nondeterministic pushdown automata with bounded breadth-first exploration.
//!
//! A stack is represented by a vector whose last element is the top. Epsilon
//! transitions use `input: None`; all other transitions consume one symbol.

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StackAction<A> {
    Keep,
    Push(A),
    Pop {
        expected: A,
    },
    /// Replaces the expected top with `replacement`, whose last element
    /// becomes the new top. An empty replacement is a pop.
    Rewrite {
        expected: A,
        replacement: Vec<A>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Transition<S, I, A> {
    pub state: S,
    pub input: Option<I>,
    pub stack: StackAction<A>,
    pub next: S,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Acceptance {
    FinalState,
    EmptyStack,
    Either,
    Both,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Automaton<S, I, A> {
    pub states: Vec<S>,
    pub initial_state: S,
    pub initial_stack: Vec<A>,
    pub final_states: Vec<S>,
    pub acceptance: Acceptance,
    pub transitions: Vec<Transition<S, I, A>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Configuration<S, A> {
    pub state: S,
    pub input_position: usize,
    pub stack: Vec<A>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Limits {
    /// Maximum number of transition layers explored.
    pub steps: usize,
    /// Maximum number of distinct configurations retained.
    pub configurations: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Self {
            steps: 10_000,
            configurations: 100_000,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Budget {
    Steps,
    Configurations,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RunResult<S, A> {
    Accepted {
        configuration: Configuration<S, A>,
        steps: usize,
    },
    Rejected {
        steps: usize,
        configurations: usize,
    },
    BudgetExhausted {
        budget: Budget,
        steps: usize,
        configurations: usize,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Trace<S, A> {
    /// Breadth-first frontiers, beginning with the initial configuration.
    pub layers: Vec<Vec<Configuration<S, A>>>,
    pub result: RunResult<S, A>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ValidationError {
    DuplicateState,
    MissingInitialState,
    MissingFinalState,
    MissingTransitionState,
    MissingTransitionTarget,
}

impl<S: Eq, I, A> Automaton<S, I, A> {
    pub fn validate(&self) -> Result<(), ValidationError> {
        for (index, state) in self.states.iter().enumerate() {
            if self.states[..index].contains(state) {
                return Err(ValidationError::DuplicateState);
            }
        }
        if !self.states.contains(&self.initial_state) {
            return Err(ValidationError::MissingInitialState);
        }
        if self
            .final_states
            .iter()
            .any(|state| !self.states.contains(state))
        {
            return Err(ValidationError::MissingFinalState);
        }
        for transition in &self.transitions {
            if !self.states.contains(&transition.state) {
                return Err(ValidationError::MissingTransitionState);
            }
            if !self.states.contains(&transition.next) {
                return Err(ValidationError::MissingTransitionTarget);
            }
        }
        Ok(())
    }
}

impl<S: Clone + Eq, I: Eq, A: Clone + Eq> Automaton<S, I, A> {
    pub fn initial_configuration(&self) -> Configuration<S, A> {
        Configuration {
            state: self.initial_state.clone(),
            input_position: 0,
            stack: self.initial_stack.clone(),
        }
    }

    pub fn accepts(&self, input: &[I], limits: Limits) -> RunResult<S, A> {
        self.trace(input, limits).result
    }

    pub fn trace(&self, input: &[I], limits: Limits) -> Trace<S, A> {
        let initial = self.initial_configuration();
        let mut layers = vec![vec![initial.clone()]];
        let mut seen = vec![initial];
        let mut steps = 0;

        loop {
            let frontier = layers.last().expect("trace always has an initial layer");
            if let Some(configuration) = frontier
                .iter()
                .find(|configuration| self.is_accepting(configuration, input.len()))
                .cloned()
            {
                return Trace {
                    layers,
                    result: RunResult::Accepted {
                        configuration,
                        steps,
                    },
                };
            }
            if frontier.is_empty() {
                return Trace {
                    layers,
                    result: RunResult::Rejected {
                        steps,
                        configurations: seen.len(),
                    },
                };
            }
            if steps == limits.steps {
                return Trace {
                    layers,
                    result: RunResult::BudgetExhausted {
                        budget: Budget::Steps,
                        steps,
                        configurations: seen.len(),
                    },
                };
            }

            let mut next_layer = Vec::new();
            for configuration in frontier {
                for transition in &self.transitions {
                    if transition.state != configuration.state {
                        continue;
                    }
                    let next_position = match &transition.input {
                        None => configuration.input_position,
                        Some(expected)
                            if input.get(configuration.input_position) == Some(expected) =>
                        {
                            configuration.input_position + 1
                        }
                        Some(_) => continue,
                    };
                    let Some(stack) = apply_stack(&configuration.stack, &transition.stack) else {
                        continue;
                    };
                    let next = Configuration {
                        state: transition.next.clone(),
                        input_position: next_position,
                        stack,
                    };
                    if seen.contains(&next) {
                        continue;
                    }
                    if seen.len() == limits.configurations {
                        return Trace {
                            layers,
                            result: RunResult::BudgetExhausted {
                                budget: Budget::Configurations,
                                steps,
                                configurations: seen.len(),
                            },
                        };
                    }
                    seen.push(next.clone());
                    next_layer.push(next);
                }
            }
            layers.push(next_layer);
            steps += 1;
        }
    }

    fn is_accepting(&self, configuration: &Configuration<S, A>, input_length: usize) -> bool {
        if configuration.input_position != input_length {
            return false;
        }
        let final_state = self.final_states.contains(&configuration.state);
        let empty_stack = configuration.stack.is_empty();
        match self.acceptance {
            Acceptance::FinalState => final_state,
            Acceptance::EmptyStack => empty_stack,
            Acceptance::Either => final_state || empty_stack,
            Acceptance::Both => final_state && empty_stack,
        }
    }
}

fn apply_stack<A: Clone + Eq>(stack: &[A], action: &StackAction<A>) -> Option<Vec<A>> {
    let mut result = stack.to_vec();
    match action {
        StackAction::Keep => {}
        StackAction::Push(symbol) => result.push(symbol.clone()),
        StackAction::Pop { expected } => {
            if result.last() != Some(expected) {
                return None;
            }
            result.pop();
        }
        StackAction::Rewrite {
            expected,
            replacement,
        } => {
            if result.last() != Some(expected) {
                return None;
            }
            result.pop();
            result.extend(replacement.iter().cloned());
        }
    }
    Some(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum State {
        As,
        Bs,
    }

    // Push one marker for every `a`, then pop one for every `b`.
    fn an_bn() -> Automaton<State, char, ()> {
        Automaton {
            states: vec![State::As, State::Bs],
            initial_state: State::As,
            initial_stack: vec![],
            final_states: vec![],
            acceptance: Acceptance::EmptyStack,
            transitions: vec![
                Transition {
                    state: State::As,
                    input: Some('a'),
                    stack: StackAction::Push(()),
                    next: State::As,
                },
                Transition {
                    state: State::As,
                    input: Some('b'),
                    stack: StackAction::Pop { expected: () },
                    next: State::Bs,
                },
                Transition {
                    state: State::Bs,
                    input: Some('b'),
                    stack: StackAction::Pop { expected: () },
                    next: State::Bs,
                },
            ],
        }
    }

    #[test]
    fn recognizes_an_bn() {
        let automaton = an_bn();
        assert!(matches!(
            automaton.accepts(&['a', 'a', 'b', 'b'], Limits::default()),
            RunResult::Accepted { .. }
        ));
        assert!(matches!(
            automaton.accepts(&[], Limits::default()),
            RunResult::Accepted { .. }
        ));
    }

    #[test]
    fn rejects_wrong_order_or_count() {
        let automaton = an_bn();
        for input in [&['a', 'b', 'b'][..], &['a', 'a', 'b'][..], &['b', 'a'][..]] {
            assert!(matches!(
                automaton.accepts(input, Limits::default()),
                RunResult::Rejected { .. }
            ));
        }
    }

    #[test]
    fn bounds_epsilon_divergence() {
        let automaton = Automaton {
            states: vec![0],
            initial_state: 0,
            initial_stack: vec![],
            final_states: vec![],
            acceptance: Acceptance::FinalState,
            transitions: vec![Transition::<u8, char, u8> {
                state: 0,
                input: None,
                stack: StackAction::Push(1),
                next: 0,
            }],
        };
        let trace = automaton.trace(
            &[],
            Limits {
                steps: 3,
                configurations: 100,
            },
        );
        assert_eq!(trace.layers.len(), 4);
        assert!(matches!(
            trace.result,
            RunResult::BudgetExhausted {
                budget: Budget::Steps,
                steps: 3,
                ..
            }
        ));
    }

    #[test]
    fn validates_state_references() {
        let mut automaton = an_bn();
        automaton.transitions[0].next = State::Bs;
        assert_eq!(automaton.validate(), Ok(()));
        automaton.states.pop();
        assert_eq!(
            automaton.validate(),
            Err(ValidationError::MissingTransitionTarget)
        );
    }
}
