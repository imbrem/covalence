//! Bounded evaluation of parsing expression grammars.
//!
//! PEG choice is ordered and deterministic: after an alternative succeeds,
//! later alternatives are not explored. Positive witnesses retain that choice
//! and all other control decisions. This differs from relational CFG parsing,
//! which retains ambiguity.
//!
//! The action-free core is generic over its alphabet. [`BytePegParser`] uses
//! raw bytes; [`TextPegParser`] uses Unicode scalars. Captures and semantic
//! actions belong in a separate interpretation layer. Evaluation is untrusted
//! host computation: witnesses are data and grant no theorem authority.
//!
//! @covalence-api {"id":"A0019","title":"Parsing expression grammars","status":"experimental","dependsOn":["A0013","A0014","A0015"]}

#![forbid(unsafe_code)]

use covalence_logic_api::UnicodeScalar;
use covalence_parsing_api::{
    ParseAttempt, PartialExactParser, PartialPrefixParser, PrefixInterpretation, Span,
};
use std::collections::HashSet;

/// Capture- and action-free PEG syntax over alphabet `A`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Peg<A> {
    Empty,
    Literal(A),
    Any,
    Sequence(Vec<Self>),
    OrderedChoice(Vec<Self>),
    And(Box<Self>),
    Not(Box<Self>),
    ZeroOrMore(Box<Self>),
    Rule(usize),
}

/// A start expression and indexed recursive rules.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PegGrammar<A> {
    pub start: Peg<A>,
    pub rules: Vec<Peg<A>>,
}

impl<A> PegGrammar<A> {
    pub fn new(start: Peg<A>, rules: Vec<Peg<A>>) -> Self {
        Self { start, rules }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PegMode {
    Prefix,
    Exact,
}

/// Caller-visible bounds for hostile inputs and grammars.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PegBudget {
    pub max_source_units: usize,
    pub max_work: usize,
    pub max_depth: usize,
    pub max_witness_nodes: usize,
}

impl PegBudget {
    pub const fn new(
        max_source_units: usize,
        max_work: usize,
        max_depth: usize,
        max_witness_nodes: usize,
    ) -> Self {
        Self {
            max_source_units,
            max_work,
            max_depth,
            max_witness_nodes,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PegResource {
    SourceUnits,
    Work,
    Depth,
    WitnessNodes,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PegLimit {
    pub resource: PegResource,
    pub limit: usize,
}

/// Evaluator failures, distinct from ordinary grammar non-match.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PegEvalError {
    ResourceExhausted(PegLimit),
    UndefinedRule { rule: usize },
    LeftRecursion { rule: usize, offset: usize },
    NullableRepetition { offset: usize },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PegDiagnosticKind {
    NoMatch,
    TrailingInput,
    StartOutOfBounds,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PegDiagnostic {
    pub offset: usize,
    pub kind: PegDiagnosticKind,
}

/// Complete action-free evidence for one deterministic evaluation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PegWitness {
    Empty {
        at: usize,
    },
    Literal {
        span: Span,
    },
    Any {
        span: Span,
    },
    Sequence {
        parts: Vec<Self>,
        span: Span,
    },
    OrderedChoice {
        chosen: usize,
        witness: Box<Self>,
        span: Span,
    },
    And {
        witness: Box<Self>,
        at: usize,
    },
    Not {
        at: usize,
    },
    ZeroOrMore {
        iterations: Vec<Self>,
        span: Span,
    },
    Rule {
        rule: usize,
        witness: Box<Self>,
        span: Span,
    },
}

impl PegWitness {
    pub fn span(&self) -> Span {
        match self {
            Self::Empty { at } | Self::And { at, .. } | Self::Not { at } => Span {
                start: *at,
                end: *at,
            },
            Self::Literal { span }
            | Self::Any { span }
            | Self::Sequence { span, .. }
            | Self::OrderedChoice { span, .. }
            | Self::ZeroOrMore { span, .. }
            | Self::Rule { span, .. } => *span,
        }
    }
}

#[derive(Clone, Debug)]
pub struct PegParser<A> {
    grammar: PegGrammar<A>,
    budget: PegBudget,
}

pub type BytePegParser = PegParser<u8>;
pub type TextPegParser = PegParser<UnicodeScalar>;

impl<A> PegParser<A> {
    pub fn new(grammar: PegGrammar<A>, budget: PegBudget) -> Self {
        Self { grammar, budget }
    }
    pub fn grammar(&self) -> &PegGrammar<A> {
        &self.grammar
    }
    pub fn budget(&self) -> PegBudget {
        self.budget
    }
}

impl<A: PartialEq> PegParser<A> {
    pub fn parse(
        &self,
        source: &[A],
        start: usize,
        mode: PegMode,
    ) -> Result<ParseAttempt<PrefixInterpretation<(), PegWitness>, PegDiagnostic>, PegEvalError>
    {
        if source.len() > self.budget.max_source_units {
            return Err(limit(
                PegResource::SourceUnits,
                self.budget.max_source_units,
            ));
        }
        if start > source.len() {
            return Ok(ParseAttempt::NoMatch(PegDiagnostic {
                offset: source.len(),
                kind: PegDiagnosticKind::StartOutOfBounds,
            }));
        }
        let mut state = EvalState::new(self.budget);
        let Some((end, witness)) =
            state.eval(&self.grammar, &self.grammar.start, source, start, 0)?
        else {
            return Ok(ParseAttempt::NoMatch(PegDiagnostic {
                offset: state.farthest,
                kind: PegDiagnosticKind::NoMatch,
            }));
        };
        if mode == PegMode::Exact && end != source.len() {
            return Ok(ParseAttempt::NoMatch(PegDiagnostic {
                offset: end,
                kind: PegDiagnosticKind::TrailingInput,
            }));
        }
        Ok(ParseAttempt::Match(PrefixInterpretation {
            value: (),
            witness,
            consumed: Span { start, end },
            remainder: end,
        }))
    }
}

impl<A: PartialEq> PartialPrefixParser for PegParser<A> {
    type Source = [A];
    type Value = ();
    type Witness = PegWitness;
    type Diagnostic = PegDiagnostic;
    type Error = PegEvalError;
    fn parse_prefix(
        &self,
        source: &[A],
        start: usize,
    ) -> Result<ParseAttempt<PrefixInterpretation<(), PegWitness>, PegDiagnostic>, PegEvalError>
    {
        self.parse(source, start, PegMode::Prefix)
    }
}

impl<A: PartialEq> PartialExactParser for PegParser<A> {
    type Source = [A];
    type Value = ();
    type Witness = PegWitness;
    type Diagnostic = PegDiagnostic;
    type Error = PegEvalError;
    fn parse_exact(
        &self,
        source: &[A],
    ) -> Result<ParseAttempt<((), PegWitness), PegDiagnostic>, PegEvalError> {
        Ok(match self.parse(source, 0, PegMode::Exact)? {
            ParseAttempt::Match(result) => ParseAttempt::Match(((), result.witness)),
            ParseAttempt::NoMatch(diagnostic) => ParseAttempt::NoMatch(diagnostic),
        })
    }
}

fn limit(resource: PegResource, limit: usize) -> PegEvalError {
    PegEvalError::ResourceExhausted(PegLimit { resource, limit })
}

struct EvalState {
    budget: PegBudget,
    work: usize,
    witness_nodes: usize,
    farthest: usize,
    active_rules: HashSet<(usize, usize)>,
}

impl EvalState {
    fn new(budget: PegBudget) -> Self {
        Self {
            budget,
            work: 0,
            witness_nodes: 0,
            farthest: 0,
            active_rules: HashSet::new(),
        }
    }
    fn charge_work(&mut self, offset: usize) -> Result<(), PegEvalError> {
        self.farthest = self.farthest.max(offset);
        if self.work >= self.budget.max_work {
            return Err(limit(PegResource::Work, self.budget.max_work));
        }
        self.work += 1;
        Ok(())
    }
    fn charge_witness(&mut self) -> Result<(), PegEvalError> {
        if self.witness_nodes >= self.budget.max_witness_nodes {
            return Err(limit(
                PegResource::WitnessNodes,
                self.budget.max_witness_nodes,
            ));
        }
        self.witness_nodes += 1;
        Ok(())
    }
    fn eval<A: PartialEq>(
        &mut self,
        grammar: &PegGrammar<A>,
        expression: &Peg<A>,
        source: &[A],
        offset: usize,
        depth: usize,
    ) -> Result<Option<(usize, PegWitness)>, PegEvalError> {
        if depth > self.budget.max_depth {
            return Err(limit(PegResource::Depth, self.budget.max_depth));
        }
        self.charge_work(offset)?;
        let matched = match expression {
            Peg::Empty => Some((offset, PegWitness::Empty { at: offset })),
            Peg::Literal(expected) => {
                self.farthest = self.farthest.max((offset + 1).min(source.len()));
                source
                    .get(offset)
                    .filter(|actual| *actual == expected)
                    .map(|_| {
                        let end = offset + 1;
                        (
                            end,
                            PegWitness::Literal {
                                span: Span { start: offset, end },
                            },
                        )
                    })
            }
            Peg::Any => source.get(offset).map(|_| {
                let end = offset + 1;
                (
                    end,
                    PegWitness::Any {
                        span: Span { start: offset, end },
                    },
                )
            }),
            Peg::Sequence(parts) => {
                let mut end = offset;
                let mut witnesses = Vec::with_capacity(parts.len());
                for part in parts {
                    let Some((next, witness)) = self.eval(grammar, part, source, end, depth + 1)?
                    else {
                        return Ok(None);
                    };
                    end = next;
                    witnesses.push(witness);
                }
                Some((
                    end,
                    PegWitness::Sequence {
                        parts: witnesses,
                        span: Span { start: offset, end },
                    },
                ))
            }
            Peg::OrderedChoice(alternatives) => {
                let mut result = None;
                for (chosen, alternative) in alternatives.iter().enumerate() {
                    if let Some((end, witness)) =
                        self.eval(grammar, alternative, source, offset, depth + 1)?
                    {
                        result = Some((
                            end,
                            PegWitness::OrderedChoice {
                                chosen,
                                witness: Box::new(witness),
                                span: Span { start: offset, end },
                            },
                        ));
                        break;
                    }
                }
                result
            }
            Peg::And(inner) => {
                self.eval(grammar, inner, source, offset, depth + 1)?
                    .map(|(_, witness)| {
                        (
                            offset,
                            PegWitness::And {
                                witness: Box::new(witness),
                                at: offset,
                            },
                        )
                    })
            }
            Peg::Not(inner) => self
                .eval(grammar, inner, source, offset, depth + 1)?
                .is_none()
                .then_some((offset, PegWitness::Not { at: offset })),
            Peg::ZeroOrMore(inner) => {
                let mut end = offset;
                let mut iterations = Vec::new();
                while let Some((next, witness)) =
                    self.eval(grammar, inner, source, end, depth + 1)?
                {
                    if next == end {
                        return Err(PegEvalError::NullableRepetition { offset: end });
                    }
                    end = next;
                    iterations.push(witness);
                }
                Some((
                    end,
                    PegWitness::ZeroOrMore {
                        iterations,
                        span: Span { start: offset, end },
                    },
                ))
            }
            Peg::Rule(rule) => {
                let Some(body) = grammar.rules.get(*rule) else {
                    return Err(PegEvalError::UndefinedRule { rule: *rule });
                };
                if !self.active_rules.insert((*rule, offset)) {
                    return Err(PegEvalError::LeftRecursion {
                        rule: *rule,
                        offset,
                    });
                }
                let body_result = self.eval(grammar, body, source, offset, depth + 1);
                self.active_rules.remove(&(*rule, offset));
                body_result?.map(|(end, witness)| {
                    (
                        end,
                        PegWitness::Rule {
                            rule: *rule,
                            witness: Box::new(witness),
                            span: Span { start: offset, end },
                        },
                    )
                })
            }
        };
        if matched.is_some() {
            self.charge_witness()?;
        }
        Ok(matched)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    const BUDGET: PegBudget = PegBudget::new(128, 1_000, 128, 1_000);
    fn bytes(start: Peg<u8>) -> BytePegParser {
        PegParser::new(PegGrammar::new(start, vec![]), BUDGET)
    }

    #[test]
    fn ordered_choice_commits_unlike_ambiguous_cfg() {
        let parser = bytes(Peg::OrderedChoice(vec![
            Peg::Literal(b'a'),
            Peg::Sequence(vec![Peg::Literal(b'a'), Peg::Literal(b'b')]),
        ]));
        let ParseAttempt::Match(parsed) = parser.parse(b"ab", 0, PegMode::Prefix).unwrap() else {
            panic!("expected prefix")
        };
        assert_eq!(parsed.remainder, 1);
        assert!(matches!(
            parsed.witness,
            PegWitness::OrderedChoice { chosen: 0, .. }
        ));
        assert!(matches!(
            parser.parse(b"ab", 0, PegMode::Exact).unwrap(),
            ParseAttempt::NoMatch(PegDiagnostic {
                kind: PegDiagnosticKind::TrailingInput,
                ..
            })
        ));
    }

    #[test]
    fn lookahead_does_not_consume() {
        let parser = bytes(Peg::Sequence(vec![
            Peg::And(Box::new(Peg::Literal(b'a'))),
            Peg::Not(Box::new(Peg::Literal(b'b'))),
            Peg::Literal(b'a'),
        ]));
        let ParseAttempt::Match(parsed) = parser.parse(b"a", 0, PegMode::Exact).unwrap() else {
            panic!("expected exact match")
        };
        assert_eq!(parsed.consumed, Span { start: 0, end: 1 });
    }

    #[test]
    fn unicode_offsets_are_scalar_offsets() {
        let lambda = UnicodeScalar::from('λ');
        let dot = UnicodeScalar::from('.');
        let parser = TextPegParser::new(
            PegGrammar::new(
                Peg::Sequence(vec![Peg::Literal(lambda), Peg::Literal(dot)]),
                vec![],
            ),
            BUDGET,
        );
        let ParseAttempt::Match(parsed) = parser.parse(&[lambda, dot], 0, PegMode::Exact).unwrap()
        else {
            panic!("expected Unicode match")
        };
        assert_eq!(parsed.consumed, Span { start: 0, end: 2 });
    }

    #[test]
    fn nullable_repetition_is_rejected() {
        assert_eq!(
            bytes(Peg::ZeroOrMore(Box::new(Peg::Empty))).parse(b"", 0, PegMode::Prefix),
            Err(PegEvalError::NullableRepetition { offset: 0 })
        );
    }

    #[test]
    fn every_bound_is_observable() {
        let literal = PegGrammar::new(Peg::Literal(b'a'), vec![]);
        let cases = [
            (
                PegParser::new(literal.clone(), PegBudget::new(0, 9, 9, 9)).parse(
                    b"a",
                    0,
                    PegMode::Prefix,
                ),
                PegResource::SourceUnits,
            ),
            (
                PegParser::new(literal.clone(), PegBudget::new(9, 0, 9, 9)).parse(
                    b"a",
                    0,
                    PegMode::Prefix,
                ),
                PegResource::Work,
            ),
            (
                PegParser::new(
                    PegGrammar::new(Peg::Sequence(vec![Peg::Literal(b'a')]), vec![]),
                    PegBudget::new(9, 9, 0, 9),
                )
                .parse(b"a", 0, PegMode::Prefix),
                PegResource::Depth,
            ),
            (
                PegParser::new(literal, PegBudget::new(9, 9, 9, 0)).parse(b"a", 0, PegMode::Prefix),
                PegResource::WitnessNodes,
            ),
        ];
        for (result, resource) in cases {
            assert!(
                matches!(result, Err(PegEvalError::ResourceExhausted(PegLimit {
                resource: actual, ..
            })) if actual == resource)
            );
        }
    }

    #[test]
    fn right_recursion_works_and_left_recursion_fails() {
        let right = PegParser::new(
            PegGrammar::new(
                Peg::Rule(0),
                vec![Peg::OrderedChoice(vec![
                    Peg::Sequence(vec![Peg::Literal(b'a'), Peg::Rule(0)]),
                    Peg::Empty,
                ])],
            ),
            BUDGET,
        );
        assert!(matches!(
            right.parse(b"aaa", 0, PegMode::Exact).unwrap(),
            ParseAttempt::Match(_)
        ));
        let left = PegParser::new(PegGrammar::new(Peg::Rule(0), vec![Peg::Rule(0)]), BUDGET);
        assert_eq!(
            left.parse(b"", 0, PegMode::Prefix),
            Err(PegEvalError::LeftRecursion { rule: 0, offset: 0 })
        );
    }
}
