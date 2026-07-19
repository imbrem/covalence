//! Relational A0015 evaluation for [`covalence_grammar::Cfg`].
//!
//! The grammar crate remains a neutral description layer. This crate depends
//! on both that IR and `covalence-parsing-api`, and supplies a bounded,
//! untrusted evaluator. Every successful derivation is retained: ambiguity is
//! data, not an arbitrary first-result choice.
//!
//! This evaluator rejects left-recursive grammars. It is intended as the
//! smallest auditable adapter and reference implementation, not as the final
//! generalized parser. Earley/GLR backends can implement the same relational
//! interface without this restriction.
// TODO(cov:lang.cfg-parsing.left-recursion, major): Add a bounded Earley or GLR backend that retains left-recursive derivations and implements this relational interface.

#![forbid(unsafe_code)]

use std::collections::{HashMap, HashSet};

use covalence_grammar::{
    Cfg, CfgError, NtId, Seg,
    regex::{Class, Regex},
};
use covalence_parsing_api::{
    ParseAttempt, ParserSyntax, PrefixInterpretation, RelationalParser, Span,
};

/// Independent bounds for evaluator work and retained ambiguity.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CfgParseLimits {
    /// Maximum parser states, segment splits, and terminal checks.
    pub work: usize,
    /// Maximum derivations retained for any parser state.
    pub results: usize,
}

impl Default for CfgParseLimits {
    fn default() -> Self {
        Self {
            work: 100_000,
            results: 10_000,
        }
    }
}

/// Why a bounded CFG interpretation could not run to completion.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum CfgParseError {
    #[error("invalid context-free grammar: {0}")]
    InvalidGrammar(#[from] CfgError),
    #[error("the reference CFG evaluator does not support left recursion")]
    LeftRecursion { cycle: Vec<NtId> },
    #[error("CFG parser work budget of {limit} exhausted")]
    WorkLimit { limit: usize },
    #[error("CFG parser result limit of {limit} exceeded")]
    ResultLimit { limit: usize },
}

/// Ordinary absence of a derivation, distinct from evaluator failure.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CfgNoMatch {
    pub attempted: Span,
    pub mode: CfgParseMode,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CfgParseMode {
    Prefix,
    Exact,
}

/// A concrete derivation of one grammar segment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SegmentDerivation {
    Terminal { span: Span },
    NonTerminal(Box<Derivation>),
}

/// A concrete production choice, including every source extent.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Derivation {
    pub nonterminal: NtId,
    /// Global insertion-order production index from the grammar IR.
    pub production: usize,
    pub span: Span,
    pub segments: Vec<SegmentDerivation>,
}

/// A bounded relational interpreter for a borrowed grammar.
#[derive(Clone, Copy, Debug)]
pub struct CfgParser<'g, T> {
    grammar: &'g Cfg<T>,
    start: NtId,
    limits: CfgParseLimits,
}

impl<'g, T> CfgParser<'g, T> {
    pub const fn new(grammar: &'g Cfg<T>, start: NtId, limits: CfgParseLimits) -> Self {
        Self {
            grammar,
            start,
            limits,
        }
    }

    pub const fn start(&self) -> NtId {
        self.start
    }

    pub const fn limits(&self) -> CfgParseLimits {
        self.limits
    }
}

impl<T> ParserSyntax for CfgParser<'_, T> {
    type Syntax = Cfg<T>;

    fn syntax(&self) -> &Self::Syntax {
        self.grammar
    }
}

impl<T: Clone + PartialOrd> CfgParser<'_, T> {
    /// Enumerate every derivable prefix beginning at `start`.
    pub fn parse_prefixes(
        &self,
        source: &[T],
        start: usize,
    ) -> Result<ParseAttempt<Vec<PrefixInterpretation<(), Derivation>>, CfgNoMatch>, CfgParseError>
    {
        let attempted = Span::new(start.min(source.len()), source.len()).expect("ordered");
        if start > source.len() {
            return Ok(ParseAttempt::NoMatch(CfgNoMatch {
                attempted,
                mode: CfgParseMode::Prefix,
            }));
        }
        let derivations = self.run(source, start)?;
        if derivations.is_empty() {
            return Ok(ParseAttempt::NoMatch(CfgNoMatch {
                attempted,
                mode: CfgParseMode::Prefix,
            }));
        }
        Ok(ParseAttempt::Match(
            derivations
                .into_iter()
                .map(|derivation| PrefixInterpretation {
                    value: (),
                    witness: derivation.clone(),
                    consumed: derivation.span,
                    remainder: derivation.span.end,
                })
                .collect(),
        ))
    }

    /// Enumerate every derivation consuming the whole source.
    pub fn parse_exact(
        &self,
        source: &[T],
    ) -> Result<ParseAttempt<Vec<((), Derivation)>, CfgNoMatch>, CfgParseError> {
        let matches = self
            .run(source, 0)?
            .into_iter()
            .filter(|derivation| derivation.span.end == source.len())
            .map(|derivation| ((), derivation))
            .collect::<Vec<_>>();
        if matches.is_empty() {
            Ok(ParseAttempt::NoMatch(CfgNoMatch {
                attempted: Span::new(0, source.len()).expect("ordered"),
                mode: CfgParseMode::Exact,
            }))
        } else {
            Ok(ParseAttempt::Match(matches))
        }
    }

    fn run(&self, source: &[T], start: usize) -> Result<Vec<Derivation>, CfgParseError> {
        self.grammar.validate()?;
        if let Some(cycle) = self.grammar.left_recursion() {
            return Err(CfgParseError::LeftRecursion { cycle });
        }
        let mut evaluator = Evaluator {
            grammar: self.grammar,
            source,
            limits: self.limits,
            work: 0,
            memo: HashMap::new(),
            active: HashSet::new(),
        };
        evaluator.nonterminal(self.start, start)
    }
}

impl<T: Clone + PartialOrd> RelationalParser for CfgParser<'_, T> {
    type Source = [T];
    type Value = ();
    type Witness = Derivation;
    type Error = CfgParseError;

    fn parses(&self, source: &[T]) -> Result<Vec<((), Derivation)>, Self::Error> {
        Ok(match self.parse_exact(source)? {
            ParseAttempt::Match(results) => results,
            ParseAttempt::NoMatch(_) => Vec::new(),
        })
    }
}

type State = (usize, usize);

struct Evaluator<'a, T> {
    grammar: &'a Cfg<T>,
    source: &'a [T],
    limits: CfgParseLimits,
    work: usize,
    memo: HashMap<State, Vec<Derivation>>,
    active: HashSet<State>,
}

impl<T: Clone + PartialOrd> Evaluator<'_, T> {
    fn tick(&mut self) -> Result<(), CfgParseError> {
        if self.work >= self.limits.work {
            return Err(CfgParseError::WorkLimit {
                limit: self.limits.work,
            });
        }
        self.work += 1;
        Ok(())
    }

    fn retain<R>(&self, values: &mut Vec<R>, value: R) -> Result<(), CfgParseError> {
        if values.len() >= self.limits.results {
            return Err(CfgParseError::ResultLimit {
                limit: self.limits.results,
            });
        }
        values.push(value);
        Ok(())
    }

    fn nonterminal(&mut self, nt: NtId, start: usize) -> Result<Vec<Derivation>, CfgParseError> {
        self.tick()?;
        let key = (nt.index(), start);
        if let Some(cached) = self.memo.get(&key) {
            return Ok(cached.clone());
        }
        // Defensive termination if a malformed future analysis misses a cycle.
        if !self.active.insert(key) {
            return Ok(Vec::new());
        }

        let mut results = Vec::new();
        for (production, prod) in self.grammar.productions_of(nt) {
            for (end, segments) in self.segments(&prod.segs, start)? {
                self.retain(
                    &mut results,
                    Derivation {
                        nonterminal: nt,
                        production,
                        span: Span::new(start, end).expect("parser extents are ordered"),
                        segments,
                    },
                )?;
            }
        }
        self.active.remove(&key);
        self.memo.insert(key, results.clone());
        Ok(results)
    }

    fn segments(
        &mut self,
        segments: &[Seg<T>],
        start: usize,
    ) -> Result<Vec<(usize, Vec<SegmentDerivation>)>, CfgParseError> {
        self.tick()?;
        let Some((head, tail)) = segments.split_first() else {
            return Ok(vec![(start, Vec::new())]);
        };

        let mut heads = Vec::new();
        match head {
            Seg::Term(regex) => {
                for end in start..=self.source.len() {
                    self.tick()?;
                    if regex_matches(regex, &self.source[start..end]) {
                        self.retain(
                            &mut heads,
                            (
                                end,
                                SegmentDerivation::Terminal {
                                    span: Span::new(start, end).expect("ordered"),
                                },
                            ),
                        )?;
                    }
                }
            }
            Seg::NonTerm(nt) => {
                for derivation in self.nonterminal(*nt, start)? {
                    self.retain(
                        &mut heads,
                        (
                            derivation.span.end,
                            SegmentDerivation::NonTerminal(Box::new(derivation)),
                        ),
                    )?;
                }
            }
        }

        let mut results = Vec::new();
        for (middle, head_derivation) in heads {
            for (end, mut rest) in self.segments(tail, middle)? {
                let mut all = Vec::with_capacity(rest.len() + 1);
                all.push(head_derivation.clone());
                all.append(&mut rest);
                self.retain(&mut results, (end, all))?;
            }
        }
        Ok(results)
    }
}

fn regex_matches<T: Clone + PartialOrd>(regex: &Regex<T>, input: &[T]) -> bool {
    match regex {
        Regex::Empty => false,
        Regex::Eps => input.is_empty(),
        Regex::Lit(item) => input == [item.clone()],
        Regex::Class(class) => input.len() == 1 && class_contains(class, &input[0]),
        Regex::Concat(items) => concat_matches(items, input),
        Regex::Alt(items) => items.iter().any(|item| regex_matches(item, input)),
        Regex::Star(inner) => star_matches(inner, input),
        Regex::Plus(inner) => {
            (1..=input.len()).any(|middle| {
                regex_matches(inner, &input[..middle]) && star_matches(inner, &input[middle..])
            }) || (input.is_empty() && regex_matches(inner, input))
        }
        Regex::Opt(inner) => input.is_empty() || regex_matches(inner, input),
        Regex::Rep { inner, min, max } => rep_matches(inner, *min, *max, input),
    }
}

fn class_contains<T: PartialOrd>(class: &Class<T>, item: &T) -> bool {
    let inside = class
        .ranges
        .iter()
        .any(|range| range.lo <= *item && *item <= range.hi);
    inside != class.negated
}

fn concat_matches<T: Clone + PartialOrd>(items: &[Regex<T>], input: &[T]) -> bool {
    let Some((head, tail)) = items.split_first() else {
        return input.is_empty();
    };
    (0..=input.len()).any(|middle| {
        regex_matches(head, &input[..middle]) && concat_matches(tail, &input[middle..])
    })
}

fn star_matches<T: Clone + PartialOrd>(inner: &Regex<T>, input: &[T]) -> bool {
    input.is_empty()
        || (1..=input.len()).any(|middle| {
            regex_matches(inner, &input[..middle]) && star_matches(inner, &input[middle..])
        })
}

fn rep_matches<T: Clone + PartialOrd>(
    inner: &Regex<T>,
    min: u32,
    max: Option<u32>,
    input: &[T],
) -> bool {
    if max.is_some_and(|max| max < min) {
        return false;
    }
    if input.is_empty() {
        return min == 0 || regex_matches(inner, input);
    }
    if max == Some(0) {
        return false;
    }
    (1..=input.len()).any(|middle| {
        regex_matches(inner, &input[..middle])
            && rep_matches(
                inner,
                min.saturating_sub(1),
                max.map(|value| value.saturating_sub(1)),
                &input[middle..],
            )
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn literal(byte: u8) -> Regex<u8> {
        Regex::Lit(byte)
    }

    #[test]
    fn ambiguity_is_retained_as_distinct_derivations() {
        let mut grammar = Cfg::new();
        let start = grammar.add_nt("S");
        let left = grammar.add_nt("Left");
        let right = grammar.add_nt("Right");
        grammar.add_prod(start, vec![Seg::nt(left)]);
        grammar.add_prod(start, vec![Seg::nt(right)]);
        grammar.add_prod(left, vec![Seg::term(literal(b'x'))]);
        grammar.add_prod(right, vec![Seg::term(literal(b'x'))]);

        let parser = CfgParser::new(&grammar, start, CfgParseLimits::default());
        let ParseAttempt::Match(results) = parser.parse_exact(b"x").unwrap() else {
            panic!("expected both derivations");
        };
        assert_eq!(results.len(), 2);
        assert_ne!(results[0].1.segments, results[1].1.segments);
    }

    #[test]
    fn prefix_and_exact_modes_are_distinct() {
        let mut grammar = Cfg::new();
        let start = grammar.add_nt("S");
        grammar.add_prod(start, vec![Seg::term(literal(b'x'))]);
        let parser = CfgParser::new(&grammar, start, CfgParseLimits::default());

        let ParseAttempt::Match(prefixes) = parser.parse_prefixes(b"xy", 0).unwrap() else {
            panic!("expected a prefix");
        };
        assert_eq!(prefixes[0].consumed, Span::new(0, 1).unwrap());
        assert_eq!(prefixes[0].remainder, 1);
        assert_eq!(
            parser.parse_exact(b"xy").unwrap(),
            ParseAttempt::NoMatch(CfgNoMatch {
                attempted: Span::new(0, 2).unwrap(),
                mode: CfgParseMode::Exact,
            })
        );
    }

    #[test]
    fn rejection_is_not_an_evaluator_error() {
        let mut grammar = Cfg::new();
        let start = grammar.add_nt("S");
        grammar.add_prod(start, vec![Seg::term(literal(b'x'))]);
        let parser = CfgParser::new(&grammar, start, CfgParseLimits::default());
        assert!(matches!(
            parser.parse_exact(b"y"),
            Ok(ParseAttempt::NoMatch(_))
        ));
        assert!(parser.parses(b"y").unwrap().is_empty());
    }

    #[test]
    fn right_recursive_grammar_records_nested_spans() {
        // S → a S b | ε
        let mut grammar = Cfg::new();
        let start = grammar.add_nt("S");
        grammar.add_prod(
            start,
            vec![
                Seg::term(literal(b'a')),
                Seg::nt(start),
                Seg::term(literal(b'b')),
            ],
        );
        grammar.add_prod(start, vec![]);
        let parser = CfgParser::new(&grammar, start, CfgParseLimits::default());
        let ParseAttempt::Match(results) = parser.parse_exact(b"aabb").unwrap() else {
            panic!("expected a derivation");
        };
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].1.span, Span::new(0, 4).unwrap());
        let SegmentDerivation::NonTerminal(inner) = &results[0].1.segments[1] else {
            panic!("expected the recursive derivation");
        };
        assert_eq!(inner.span, Span::new(1, 3).unwrap());
    }

    #[test]
    fn work_and_result_limits_are_explicit() {
        let mut grammar = Cfg::new();
        let start = grammar.add_nt("S");
        grammar.add_prod(start, vec![Seg::term(literal(b'x'))]);
        let parser = CfgParser::new(
            &grammar,
            start,
            CfgParseLimits {
                work: 0,
                results: 10,
            },
        );
        assert_eq!(
            parser.parse_exact(b"x"),
            Err(CfgParseError::WorkLimit { limit: 0 })
        );

        let mut grammar = Cfg::new();
        let start = grammar.add_nt("S");
        grammar.add_prod(start, vec![]);
        grammar.add_prod(start, vec![]);
        let parser = CfgParser::new(
            &grammar,
            start,
            CfgParseLimits {
                work: 100,
                results: 1,
            },
        );
        assert_eq!(
            parser.parse_exact(b""),
            Err(CfgParseError::ResultLimit { limit: 1 })
        );
    }

    #[test]
    fn unsupported_left_recursion_is_reported() {
        let mut grammar = Cfg::new();
        let start = grammar.add_nt("S");
        grammar.add_prod(start, vec![Seg::nt(start)]);
        let parser = CfgParser::new(&grammar, start, CfgParseLimits::default());
        assert!(matches!(
            parser.parse_exact(b""),
            Err(CfgParseError::LeftRecursion { .. })
        ));
    }
}
