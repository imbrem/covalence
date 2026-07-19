//! Relational A0015 evaluation for [`covalence_grammar::Cfg`].
//!
//! The grammar crate remains a neutral description layer. This crate depends
//! on both that IR and `covalence-parsing-api`, and supplies a bounded,
//! untrusted evaluator. Every successful derivation is retained: ambiguity is
//! data, not an arbitrary first-result choice.
//!
//! [`CfgParser`] is the smallest auditable recursive reference implementation
//! and rejects left recursion. [`ChartCfgParser`] is a bounded bottom-up chart
//! implementation which handles left recursion and nullable productions.

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

/// Independent bounds for the bottom-up chart evaluator.
///
/// `results_per_cell` bounds ambiguity at one `(nonterminal, start, end)`
/// extent. `chart_entries` bounds all retained derivation witnesses, rather
/// than merely the number of occupied extents.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ChartParseLimits {
    pub work: usize,
    pub results_per_cell: usize,
    pub chart_entries: usize,
}

impl Default for ChartParseLimits {
    fn default() -> Self {
        Self {
            work: 1_000_000,
            results_per_cell: 10_000,
            chart_entries: 100_000,
        }
    }
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
    #[error("CFG parser chart-entry limit of {limit} exceeded")]
    ChartLimit { limit: usize },
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

/// A bounded bottom-up chart parser.
///
/// This is deliberately a simpler fixed-point algorithm than optimized
/// Earley: every production is reconsidered until no new derivation witness is
/// discovered. It has the same important semantic property for this API:
/// left-recursive and nullable grammars are evaluated without recursive calls.
/// The tradeoff is intentionally explicit work bounds rather than a performance
/// claim.
///
/// Distinct derivation trees are retained, including trees with the same
/// nonterminal and extent. Grammars with a productive zero-width cycle have
/// infinitely many finite derivation trees, so evaluation ends with a result or
/// chart limit rather than pretending that enumeration is complete.
// TODO(cov:lang.cfg-parsing.packed-forest, major): Represent cyclic/ambiguous derivations as a bounded shared packed parse forest instead of expanding every tree.
#[derive(Clone, Copy, Debug)]
pub struct ChartCfgParser<'g, T> {
    grammar: &'g Cfg<T>,
    start: NtId,
    limits: ChartParseLimits,
}

impl<'g, T> ChartCfgParser<'g, T> {
    pub const fn new(grammar: &'g Cfg<T>, start: NtId, limits: ChartParseLimits) -> Self {
        Self {
            grammar,
            start,
            limits,
        }
    }

    pub const fn start(&self) -> NtId {
        self.start
    }

    pub const fn limits(&self) -> ChartParseLimits {
        self.limits
    }
}

impl<T> ParserSyntax for ChartCfgParser<'_, T> {
    type Syntax = Cfg<T>;

    fn syntax(&self) -> &Self::Syntax {
        self.grammar
    }
}

impl<T: Clone + PartialOrd> ChartCfgParser<'_, T> {
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
        let chart = self.run(source)?;
        let mut derivations = chart
            .into_iter()
            .filter_map(|((nt, begin, _), values)| {
                (nt == self.start.index() && begin == start).then_some(values)
            })
            .flatten()
            .collect::<Vec<_>>();
        sort_derivations(&mut derivations);
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

    pub fn parse_exact(
        &self,
        source: &[T],
    ) -> Result<ParseAttempt<Vec<((), Derivation)>, CfgNoMatch>, CfgParseError> {
        let mut matches = self
            .run(source)?
            .remove(&(self.start.index(), 0, source.len()))
            .unwrap_or_default();
        sort_derivations(&mut matches);
        if matches.is_empty() {
            Ok(ParseAttempt::NoMatch(CfgNoMatch {
                attempted: Span::new(0, source.len()).expect("ordered"),
                mode: CfgParseMode::Exact,
            }))
        } else {
            Ok(ParseAttempt::Match(
                matches
                    .into_iter()
                    .map(|derivation| ((), derivation))
                    .collect(),
            ))
        }
    }

    fn run(&self, source: &[T]) -> Result<Chart, CfgParseError> {
        self.grammar.validate()?;
        let mut evaluator = ChartEvaluator {
            grammar: self.grammar,
            source,
            limits: self.limits,
            work: 0,
            entries: 0,
            chart: HashMap::new(),
        };
        evaluator.fixed_point()?;
        Ok(evaluator.chart)
    }
}

impl<T: Clone + PartialOrd> RelationalParser for ChartCfgParser<'_, T> {
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

type ChartKey = (usize, usize, usize);
type Chart = HashMap<ChartKey, Vec<Derivation>>;

struct ChartEvaluator<'a, T> {
    grammar: &'a Cfg<T>,
    source: &'a [T],
    limits: ChartParseLimits,
    work: usize,
    entries: usize,
    chart: Chart,
}

impl<T: Clone + PartialOrd> ChartEvaluator<'_, T> {
    fn tick(&mut self) -> Result<(), CfgParseError> {
        if self.work >= self.limits.work {
            return Err(CfgParseError::WorkLimit {
                limit: self.limits.work,
            });
        }
        self.work += 1;
        Ok(())
    }

    fn fixed_point(&mut self) -> Result<(), CfgParseError> {
        loop {
            let before = self.entries;
            for (production, prod) in self.grammar.productions().iter().enumerate() {
                for start in 0..=self.source.len() {
                    self.tick()?;
                    for (end, segments) in self.segments(&prod.segs, start)? {
                        self.insert(Derivation {
                            nonterminal: prod.lhs,
                            production,
                            span: Span::new(start, end).expect("ordered"),
                            segments,
                        })?;
                    }
                }
            }
            if self.entries == before {
                return Ok(());
            }
        }
    }

    fn insert(&mut self, derivation: Derivation) -> Result<(), CfgParseError> {
        self.tick()?;
        let key = (
            derivation.nonterminal.index(),
            derivation.span.start,
            derivation.span.end,
        );
        let cell = self.chart.entry(key).or_default();
        if cell.contains(&derivation) {
            return Ok(());
        }
        if cell.len() >= self.limits.results_per_cell {
            return Err(CfgParseError::ResultLimit {
                limit: self.limits.results_per_cell,
            });
        }
        if self.entries >= self.limits.chart_entries {
            return Err(CfgParseError::ChartLimit {
                limit: self.limits.chart_entries,
            });
        }
        cell.push(derivation);
        self.entries += 1;
        Ok(())
    }

    fn segments(
        &mut self,
        segments: &[Seg<T>],
        start: usize,
    ) -> Result<Vec<(usize, Vec<SegmentDerivation>)>, CfgParseError> {
        let mut partial = vec![(start, Vec::new())];
        for segment in segments {
            let mut next = Vec::new();
            for (middle, witnesses) in partial {
                self.tick()?;
                match segment {
                    Seg::Term(regex) => {
                        for end in middle..=self.source.len() {
                            self.tick()?;
                            if regex_matches(regex, &self.source[middle..end]) {
                                let mut all = witnesses.clone();
                                all.push(SegmentDerivation::Terminal {
                                    span: Span::new(middle, end).expect("ordered"),
                                });
                                if next.len() >= self.limits.results_per_cell {
                                    return Err(CfgParseError::ResultLimit {
                                        limit: self.limits.results_per_cell,
                                    });
                                }
                                next.push((end, all));
                            }
                        }
                    }
                    Seg::NonTerm(nt) => {
                        let mut children = self
                            .chart
                            .iter()
                            .filter_map(|((child_nt, child_start, _), values)| {
                                (*child_nt == nt.index() && *child_start == middle)
                                    .then_some(values.as_slice())
                            })
                            .flatten()
                            .cloned()
                            .collect::<Vec<_>>();
                        sort_derivations(&mut children);
                        for child in children {
                            let end = child.span.end;
                            let mut all = witnesses.clone();
                            all.push(SegmentDerivation::NonTerminal(Box::new(child)));
                            if next.len() >= self.limits.results_per_cell {
                                return Err(CfgParseError::ResultLimit {
                                    limit: self.limits.results_per_cell,
                                });
                            }
                            next.push((end, all));
                        }
                    }
                }
            }
            partial = next;
        }
        Ok(partial)
    }
}

fn sort_derivations(derivations: &mut [Derivation]) {
    derivations.sort_by_key(|derivation| {
        (
            derivation.span.start,
            derivation.span.end,
            derivation.production,
            format!("{:?}", derivation.segments),
        )
    });
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

    #[test]
    fn chart_parser_handles_direct_left_recursion() {
        // S → S a | a
        let mut grammar = Cfg::new();
        let start = grammar.add_nt("S");
        grammar.add_prod(start, vec![Seg::nt(start), Seg::term(literal(b'a'))]);
        grammar.add_prod(start, vec![Seg::term(literal(b'a'))]);

        let parser = ChartCfgParser::new(&grammar, start, ChartParseLimits::default());
        let ParseAttempt::Match(results) = parser.parse_exact(b"aaa").unwrap() else {
            panic!("expected a left-recursive derivation");
        };
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].1.span, Span::new(0, 3).unwrap());
    }

    #[test]
    fn chart_parser_handles_indirect_left_recursion() {
        // S → A b; A → S a | x
        let mut grammar = Cfg::new();
        let start = grammar.add_nt("S");
        let a = grammar.add_nt("A");
        grammar.add_prod(start, vec![Seg::nt(a), Seg::term(literal(b'b'))]);
        grammar.add_prod(a, vec![Seg::nt(start), Seg::term(literal(b'a'))]);
        grammar.add_prod(a, vec![Seg::term(literal(b'x'))]);

        let parser = ChartCfgParser::new(&grammar, start, ChartParseLimits::default());
        assert!(matches!(
            parser.parse_exact(b"xbab"),
            Ok(ParseAttempt::Match(results)) if results.len() == 1
        ));
    }

    #[test]
    fn chart_parser_handles_nullable_prefixes() {
        // S → A x; A → ε | A a
        let mut grammar = Cfg::new();
        let start = grammar.add_nt("S");
        let a = grammar.add_nt("A");
        grammar.add_prod(start, vec![Seg::nt(a), Seg::term(literal(b'x'))]);
        grammar.add_prod(a, vec![]);
        grammar.add_prod(a, vec![Seg::nt(a), Seg::term(literal(b'a'))]);

        let parser = ChartCfgParser::new(&grammar, start, ChartParseLimits::default());
        assert!(matches!(
            parser.parse_exact(b"x"),
            Ok(ParseAttempt::Match(results)) if results.len() == 1
        ));
        assert!(matches!(
            parser.parse_exact(b"aax"),
            Ok(ParseAttempt::Match(results)) if results.len() == 1
        ));
    }

    #[test]
    fn chart_parser_retains_left_recursive_ambiguity_deterministically() {
        // The two recursive productions are intentionally identical.
        let mut grammar = Cfg::new();
        let start = grammar.add_nt("S");
        grammar.add_prod(start, vec![Seg::nt(start), Seg::term(literal(b'a'))]);
        grammar.add_prod(start, vec![Seg::nt(start), Seg::term(literal(b'a'))]);
        grammar.add_prod(start, vec![Seg::term(literal(b'a'))]);

        let parser = ChartCfgParser::new(&grammar, start, ChartParseLimits::default());
        let ParseAttempt::Match(first) = parser.parse_exact(b"aa").unwrap() else {
            panic!("expected ambiguous derivations");
        };
        let ParseAttempt::Match(second) = parser.parse_exact(b"aa").unwrap() else {
            panic!("expected ambiguous derivations");
        };
        assert_eq!(first.len(), 2);
        assert_eq!(first, second);
        assert_eq!(first[0].1.production, 0);
        assert_eq!(first[1].1.production, 1);
    }

    #[test]
    fn chart_prefix_mode_reports_all_extents_in_order() {
        let mut grammar = Cfg::new();
        let start = grammar.add_nt("S");
        grammar.add_prod(start, vec![Seg::term(Regex::Plus(literal(b'a').into()))]);
        let parser = ChartCfgParser::new(&grammar, start, ChartParseLimits::default());

        let ParseAttempt::Match(prefixes) = parser.parse_prefixes(b"aab", 0).unwrap() else {
            panic!("expected prefixes");
        };
        assert_eq!(
            prefixes
                .iter()
                .map(|prefix| prefix.consumed)
                .collect::<Vec<_>>(),
            vec![Span::new(0, 1).unwrap(), Span::new(0, 2).unwrap()]
        );
    }

    #[test]
    fn chart_bounds_are_independent() {
        let mut grammar = Cfg::new();
        let start = grammar.add_nt("S");
        grammar.add_prod(start, vec![]);
        grammar.add_prod(start, vec![]);

        let parser = ChartCfgParser::new(
            &grammar,
            start,
            ChartParseLimits {
                work: 100,
                results_per_cell: 1,
                chart_entries: 100,
            },
        );
        assert_eq!(
            parser.parse_exact(b""),
            Err(CfgParseError::ResultLimit { limit: 1 })
        );

        let parser = ChartCfgParser::new(
            &grammar,
            start,
            ChartParseLimits {
                work: 100,
                results_per_cell: 10,
                chart_entries: 1,
            },
        );
        assert_eq!(
            parser.parse_exact(b""),
            Err(CfgParseError::ChartLimit { limit: 1 })
        );
    }
}
