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
/// `results_per_cell` bounds packed alternatives at one
/// `(nonterminal, start, end)` node. `chart_entries` bounds the sum of nodes
/// and packed alternatives. Tree expansion has its own bounds because a small
/// forest may denote exponentially or infinitely many derivations.
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
/// Earley: every production is reconsidered until no new packed alternative is
/// discovered. It has the same important semantic property for this API:
/// left-recursive and nullable grammars are evaluated without recursive calls.
/// The tradeoff is intentionally explicit work bounds rather than a performance
/// claim.
///
/// The chart is a [`PackedParseForest`]: ambiguity shares nonterminal/span
/// nodes, and nullable cycles are finite graph cycles. The original tree API is
/// retained as a bounded compatibility view over that forest.
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
    /// Build the complete bounded packed forest for `source`.
    pub fn parse_forest(&self, source: &[T]) -> Result<PackedParseForest, CfgParseError> {
        self.grammar.validate()?;
        let mut evaluator = ForestBuilder {
            grammar: self.grammar,
            source,
            limits: self.limits,
            work: 0,
            entries: 0,
            forest: PackedParseForest::default(),
        };
        evaluator.fixed_point()?;
        Ok(evaluator.forest)
    }

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
        let forest = self.parse_forest(source)?;
        let roots = forest.root_ids(self.start, start, None);
        let mut derivations = Vec::new();
        for root in roots {
            let expanded = forest
                .expand(root, self.expansion_limits(source.len()))
                .expect("root belongs to this forest");
            if expanded.truncated {
                return Err(CfgParseError::ResultLimit {
                    limit: self.limits.results_per_cell,
                });
            }
            derivations.extend(expanded.derivations);
        }
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
        let forest = self.parse_forest(source)?;
        let roots = forest.root_ids(self.start, 0, Some(source.len()));
        let mut matches = Vec::new();
        for root in roots {
            let expanded = forest
                .expand(root, self.expansion_limits(source.len()))
                .expect("root belongs to this forest");
            if expanded.truncated {
                return Err(CfgParseError::ResultLimit {
                    limit: self.limits.results_per_cell,
                });
            }
            matches.extend(expanded.derivations);
        }
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

    fn expansion_limits(&self, source_len: usize) -> DerivationExpansionLimits {
        DerivationExpansionLimits {
            work: self.limits.work,
            results: self.limits.results_per_cell,
            depth: source_len
                .saturating_add(self.grammar.productions().len())
                .saturating_add(1),
        }
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

/// Stable index of a node within one [`PackedParseForest`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ForestNodeId(usize);

impl ForestNodeId {
    pub const fn index(self) -> usize {
        self.0
    }
}

/// One shared nonterminal occurrence.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackedNode {
    pub nonterminal: NtId,
    pub span: Span,
    pub alternatives: Vec<PackedAlternative>,
}

/// One production/split choice at a packed node.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackedAlternative {
    pub production: usize,
    pub segments: Vec<PackedSegment>,
}

/// A terminal extent or reference to another shared forest node.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PackedSegment {
    Terminal { span: Span },
    NonTerminal(ForestNodeId),
}

/// A finite shared representation of all recognized derivations.
///
/// Nodes are interned by `(nonterminal, start, end)`. Their insertion order,
/// and the order of alternatives within each node, are deterministic.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct PackedParseForest {
    nodes: Vec<PackedNode>,
    lookup: HashMap<(usize, usize, usize), ForestNodeId>,
}

impl PackedParseForest {
    pub fn nodes(&self) -> &[PackedNode] {
        &self.nodes
    }

    pub fn node(&self, id: ForestNodeId) -> Option<&PackedNode> {
        self.nodes.get(id.0)
    }

    /// Root nodes in ascending end-offset order.
    pub fn root_ids(&self, nt: NtId, start: usize, end: Option<usize>) -> Vec<ForestNodeId> {
        let mut roots = self
            .nodes
            .iter()
            .enumerate()
            .filter(|(_, node)| {
                node.nonterminal == nt
                    && node.span.start == start
                    && end.is_none_or(|end| node.span.end == end)
            })
            .map(|(index, _)| ForestNodeId(index))
            .collect::<Vec<_>>();
        roots.sort_by_key(|id| {
            let node = &self.nodes[id.0];
            (node.span.end, id.0)
        });
        roots
    }

    /// Materialize derivation trees under explicit bounds.
    ///
    /// `truncated` is true when a work, result, or depth bound prevented full
    /// enumeration. In particular, a productive nullable cycle necessarily
    /// truncates: its finite forest denotes infinitely many finite trees.
    pub fn expand(
        &self,
        root: ForestNodeId,
        limits: DerivationExpansionLimits,
    ) -> Option<DerivationExpansion> {
        self.node(root)?;
        let mut context = ExpansionContext {
            forest: self,
            limits,
            work: 0,
            truncated: false,
        };
        let derivations = context.node(root, limits.depth);
        Some(DerivationExpansion {
            derivations,
            truncated: context.truncated,
        })
    }
}

/// Independent bounds for turning a packed forest back into trees.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DerivationExpansionLimits {
    pub work: usize,
    pub results: usize,
    pub depth: usize,
}

impl Default for DerivationExpansionLimits {
    fn default() -> Self {
        Self {
            work: 100_000,
            results: 10_000,
            depth: 1_000,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DerivationExpansion {
    pub derivations: Vec<Derivation>,
    pub truncated: bool,
}

struct ExpansionContext<'a> {
    forest: &'a PackedParseForest,
    limits: DerivationExpansionLimits,
    work: usize,
    truncated: bool,
}

impl ExpansionContext<'_> {
    fn tick(&mut self) -> bool {
        if self.work >= self.limits.work {
            self.truncated = true;
            false
        } else {
            self.work += 1;
            true
        }
    }

    fn node(&mut self, id: ForestNodeId, depth: usize) -> Vec<Derivation> {
        if depth == 0 || !self.tick() {
            self.truncated = true;
            return Vec::new();
        }
        let node = &self.forest.nodes[id.0];
        let mut results = Vec::new();
        for alternative in &node.alternatives {
            for segments in self.segments(&alternative.segments, depth - 1) {
                if results.len() >= self.limits.results {
                    self.truncated = true;
                    return results;
                }
                results.push(Derivation {
                    nonterminal: node.nonterminal,
                    production: alternative.production,
                    span: node.span,
                    segments,
                });
            }
        }
        results
    }

    fn segments(
        &mut self,
        segments: &[PackedSegment],
        depth: usize,
    ) -> Vec<Vec<SegmentDerivation>> {
        let mut partial = vec![Vec::new()];
        for segment in segments {
            if !self.tick() {
                return Vec::new();
            }
            let choices = match segment {
                PackedSegment::Terminal { span } => {
                    vec![SegmentDerivation::Terminal { span: *span }]
                }
                PackedSegment::NonTerminal(child) => self
                    .node(*child, depth)
                    .into_iter()
                    .map(|tree| SegmentDerivation::NonTerminal(Box::new(tree)))
                    .collect(),
            };
            let mut next = Vec::new();
            for prefix in &partial {
                for choice in &choices {
                    if next.len() >= self.limits.results {
                        self.truncated = true;
                        return Vec::new();
                    }
                    let mut combined = prefix.clone();
                    combined.push(choice.clone());
                    next.push(combined);
                }
            }
            partial = next;
        }
        partial
    }
}

struct ForestBuilder<'a, T> {
    grammar: &'a Cfg<T>,
    source: &'a [T],
    limits: ChartParseLimits,
    work: usize,
    entries: usize,
    forest: PackedParseForest,
}

impl<T: Clone + PartialOrd> ForestBuilder<'_, T> {
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
                        self.insert(
                            prod.lhs,
                            Span::new(start, end).expect("ordered"),
                            PackedAlternative {
                                production,
                                segments,
                            },
                        )?;
                    }
                }
            }
            if self.entries == before {
                return Ok(());
            }
        }
    }

    fn insert(
        &mut self,
        nonterminal: NtId,
        span: Span,
        alternative: PackedAlternative,
    ) -> Result<(), CfgParseError> {
        self.tick()?;
        let key = (nonterminal.index(), span.start, span.end);
        let id = if let Some(id) = self.forest.lookup.get(&key) {
            *id
        } else {
            self.reserve_entry()?;
            let id = ForestNodeId(self.forest.nodes.len());
            self.forest.nodes.push(PackedNode {
                nonterminal,
                span,
                alternatives: Vec::new(),
            });
            self.forest.lookup.insert(key, id);
            id
        };
        if self.forest.nodes[id.0].alternatives.contains(&alternative) {
            return Ok(());
        }
        if self.forest.nodes[id.0].alternatives.len() >= self.limits.results_per_cell {
            return Err(CfgParseError::ResultLimit {
                limit: self.limits.results_per_cell,
            });
        }
        self.reserve_entry()?;
        self.forest.nodes[id.0].alternatives.push(alternative);
        Ok(())
    }

    fn reserve_entry(&mut self) -> Result<(), CfgParseError> {
        if self.entries >= self.limits.chart_entries {
            return Err(CfgParseError::ChartLimit {
                limit: self.limits.chart_entries,
            });
        }
        self.entries += 1;
        Ok(())
    }

    fn segments(
        &mut self,
        segments: &[Seg<T>],
        start: usize,
    ) -> Result<Vec<(usize, Vec<PackedSegment>)>, CfgParseError> {
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
                                all.push(PackedSegment::Terminal {
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
                        let children = self
                            .forest
                            .nodes
                            .iter()
                            .enumerate()
                            .filter(|(_, node)| {
                                node.nonterminal == *nt && node.span.start == middle
                            })
                            .map(|(index, _)| ForestNodeId(index))
                            .collect::<Vec<_>>();
                        for child in children {
                            let end = self.forest.nodes[child.0].span.end;
                            let mut all = witnesses.clone();
                            all.push(PackedSegment::NonTerminal(child));
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

    #[test]
    fn nullable_cycle_is_finite_in_forest_and_bounded_when_expanded() {
        // S → ε | S has infinitely many finite derivation trees, but one
        // shared node with a self-referential packed alternative.
        let mut grammar = Cfg::new();
        let start = grammar.add_nt("S");
        grammar.add_prod(start, vec![]);
        grammar.add_prod(start, vec![Seg::nt(start)]);
        let parser = ChartCfgParser::new(&grammar, start, ChartParseLimits::default());

        let forest = parser.parse_forest(b"").unwrap();
        let roots = forest.root_ids(start, 0, Some(0));
        assert_eq!(forest.nodes().len(), 1);
        assert_eq!(roots.len(), 1);
        assert_eq!(forest.node(roots[0]).unwrap().alternatives.len(), 2);
        assert!(matches!(
            forest.node(roots[0]).unwrap().alternatives[1].segments[0],
            PackedSegment::NonTerminal(id) if id == roots[0]
        ));

        let first = forest
            .expand(
                roots[0],
                DerivationExpansionLimits {
                    work: 1_000,
                    results: 100,
                    depth: 4,
                },
            )
            .unwrap();
        let second = forest
            .expand(
                roots[0],
                DerivationExpansionLimits {
                    work: 1_000,
                    results: 100,
                    depth: 4,
                },
            )
            .unwrap();
        assert!(first.truncated);
        assert_eq!(first, second);
        assert_eq!(first.derivations.len(), 4);
    }

    #[test]
    fn packed_forest_is_smaller_than_ambiguous_tree_family() {
        // S → S S | a has Catalan-many trees. Seven input symbols have 132
        // trees, while the forest has one node per recognized span and one
        // packed alternative per split.
        let mut grammar = Cfg::new();
        let start = grammar.add_nt("S");
        grammar.add_prod(start, vec![Seg::nt(start), Seg::nt(start)]);
        grammar.add_prod(start, vec![Seg::term(literal(b'a'))]);
        let parser = ChartCfgParser::new(&grammar, start, ChartParseLimits::default());

        let forest = parser.parse_forest(b"aaaaaaa").unwrap();
        let root = forest.root_ids(start, 0, Some(7))[0];
        let packed_alternatives = forest
            .nodes()
            .iter()
            .map(|node| node.alternatives.len())
            .sum::<usize>();
        let expanded = forest
            .expand(
                root,
                DerivationExpansionLimits {
                    work: 100_000,
                    results: 1_000,
                    depth: 16,
                },
            )
            .unwrap();

        assert!(!expanded.truncated);
        assert_eq!(expanded.derivations.len(), 132);
        assert!(forest.nodes().len() <= 28);
        assert!(packed_alternatives < expanded.derivations.len());
    }

    #[test]
    fn expansion_work_bound_never_returns_partial_trees() {
        let mut grammar = Cfg::new();
        let start = grammar.add_nt("S");
        grammar.add_prod(
            start,
            vec![
                Seg::term(literal(b'a')),
                Seg::term(literal(b'b')),
                Seg::term(literal(b'c')),
            ],
        );
        let parser = ChartCfgParser::new(&grammar, start, ChartParseLimits::default());
        let forest = parser.parse_forest(b"abc").unwrap();
        let root = forest.root_ids(start, 0, Some(3))[0];
        let expanded = forest
            .expand(
                root,
                DerivationExpansionLimits {
                    work: 2,
                    results: 100,
                    depth: 10,
                },
            )
            .unwrap();
        assert!(expanded.truncated);
        assert!(expanded.derivations.is_empty());
    }
}
