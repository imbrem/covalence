//! Bounded, provenance-preserving lexer → CFG evaluation.
//!
//! This composes A0016 with the bounded chart evaluator without making the
//! regex or grammar IR depend on evaluation. Results retain the full lexical
//! trace (including skips) and a token-indexed packed parse forest.
//!
//! @covalence-api {"id":"A0017","title":"Lexer to CFG parsing","status":"experimental","dependsOn":["A0015","A0016"]}

#![forbid(unsafe_code)]

use covalence_cfg_parsing::{
    CfgParseError, ChartCfgParser, ChartParseLimits, ForestNodeId, PackedParseForest,
};
use covalence_grammar::{Cfg, NtId};
use covalence_kernel_data::UnicodeScalar;
use covalence_lexer_parsing::{
    ByteLexer, LexerBudget, LexerDiagnostic, LexerError, Lexing, SourceSpan, TextLexer,
};
use covalence_parsing_api::{DecodedText, Span};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PipelineMode {
    Prefix,
    Exact,
}

/// Independent lexical and syntactic bounds.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PipelineBudget {
    pub lexer: LexerBudget,
    pub parser: ChartParseLimits,
}

/// An untrusted composition witness. Forest spans index emitted tokens.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PipelineMatch<K> {
    pub lexing: Lexing<K>,
    pub forest: PackedParseForest,
    pub roots: Vec<ForestNodeId>,
    pub mode: PipelineMode,
    pub source: SourceSpan,
}

impl<K> PipelineMatch<K> {
    /// Smallest source span covering emitted tokens. Skipped regions remain
    /// separately visible in `lexing.trace`.
    pub fn source_cover(&self, tokens: Span) -> Option<SourceSpan> {
        if tokens.end > self.lexing.tokens.len() {
            return None;
        }
        if tokens.start == tokens.end {
            let boundary = self
                .lexing
                .tokens
                .get(tokens.start)
                .map(|t| t.span)
                .or((tokens.start == self.lexing.tokens.len()).then_some(self.source))?;
            return Some(SourceSpan {
                units: Span::new(boundary.units.start, boundary.units.start)?,
                bytes: boundary.bytes.and_then(|s| Span::new(s.start, s.start)),
            });
        }
        let first = self.lexing.tokens.get(tokens.start)?.span;
        let last = self.lexing.tokens.get(tokens.end - 1)?.span;
        Some(SourceSpan {
            units: Span::new(first.units.start, last.units.end)?,
            bytes: match (first.bytes, last.bytes) {
                (Some(a), Some(b)) => Span::new(a.start, b.end),
                _ => None,
            },
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PipelineDiagnostic {
    Lexical(LexerDiagnostic),
    Syntactic {
        attempted_tokens: Span,
        mode: PipelineMode,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PipelineError {
    Lexical(LexerError),
    Syntactic(CfgParseError),
}

pub type PipelineResult<K> = Result<Result<PipelineMatch<K>, PipelineDiagnostic>, PipelineError>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RelationalPipelineResult<K> {
    Match(PipelineMatch<K>),
    SyntacticNoMatch {
        lexing: Lexing<K>,
        attempted_tokens: Span,
        mode: PipelineMode,
    },
}

#[derive(Clone, Debug)]
pub struct ByteLexerCfg<'g, K> {
    lexer: ByteLexer<K>,
    grammar: &'g Cfg<K>,
    start: NtId,
}

impl<'g, K: Clone + PartialOrd> ByteLexerCfg<'g, K> {
    pub const fn new(lexer: ByteLexer<K>, grammar: &'g Cfg<K>, start: NtId) -> Self {
        Self {
            lexer,
            grammar,
            start,
        }
    }

    pub fn parse(
        &self,
        source: &[u8],
        mode: PipelineMode,
        budget: PipelineBudget,
    ) -> PipelineResult<K> {
        let lexing = match self.lexer.lex(source, budget.lexer) {
            Err(e) => return Err(PipelineError::Lexical(e)),
            Ok(Err(d)) => return Ok(Err(PipelineDiagnostic::Lexical(d))),
            Ok(Ok(x)) => x,
        };
        parse_one(
            self.grammar,
            self.start,
            lexing,
            mode,
            budget.parser,
            byte_extent(source.len()),
        )
    }

    /// Retains lexical ambiguity as separate paths and syntactic ambiguity as
    /// packed alternatives within each matching path.
    pub fn parse_relational(
        &self,
        source: &[u8],
        mode: PipelineMode,
        budget: PipelineBudget,
    ) -> Result<Vec<RelationalPipelineResult<K>>, PipelineError> {
        let paths = self
            .lexer
            .lex_relational(source, budget.lexer)
            .map_err(PipelineError::Lexical)?;
        parse_many(
            self.grammar,
            self.start,
            paths,
            mode,
            budget.parser,
            byte_extent(source.len()),
        )
    }
}

#[derive(Clone, Debug)]
pub struct TextLexerCfg<'g, K> {
    lexer: TextLexer<K>,
    grammar: &'g Cfg<K>,
    start: NtId,
}

impl<'g, K: Clone + PartialOrd> TextLexerCfg<'g, K> {
    pub const fn new(lexer: TextLexer<K>, grammar: &'g Cfg<K>, start: NtId) -> Self {
        Self {
            lexer,
            grammar,
            start,
        }
    }

    pub fn parse_decoded(
        &self,
        source: &DecodedText,
        mode: PipelineMode,
        budget: PipelineBudget,
    ) -> PipelineResult<K> {
        let lexing = match self.lexer.lex_decoded(source, budget.lexer) {
            Err(e) => return Err(PipelineError::Lexical(e)),
            Ok(Err(d)) => return Ok(Err(PipelineDiagnostic::Lexical(d))),
            Ok(Ok(x)) => x,
        };
        parse_one(
            self.grammar,
            self.start,
            lexing,
            mode,
            budget.parser,
            decoded_extent(source),
        )
    }

    pub fn parse_decoded_relational(
        &self,
        source: &DecodedText,
        mode: PipelineMode,
        budget: PipelineBudget,
    ) -> Result<Vec<RelationalPipelineResult<K>>, PipelineError> {
        let paths = self
            .lexer
            .lex_decoded_relational(source, budget.lexer)
            .map_err(PipelineError::Lexical)?;
        parse_many(
            self.grammar,
            self.start,
            paths,
            mode,
            budget.parser,
            decoded_extent(source),
        )
    }

    pub fn parse_scalars(
        &self,
        source: &[UnicodeScalar],
        mode: PipelineMode,
        budget: PipelineBudget,
    ) -> PipelineResult<K> {
        let lexing = match self.lexer.lex(source, budget.lexer) {
            Err(e) => return Err(PipelineError::Lexical(e)),
            Ok(Err(d)) => return Ok(Err(PipelineDiagnostic::Lexical(d))),
            Ok(Ok(x)) => x,
        };
        parse_one(
            self.grammar,
            self.start,
            lexing,
            mode,
            budget.parser,
            SourceSpan {
                units: Span::new(0, source.len()).expect("ordered"),
                bytes: None,
            },
        )
    }
}

fn parse_one<K: Clone + PartialOrd>(
    grammar: &Cfg<K>,
    start: NtId,
    lexing: Lexing<K>,
    mode: PipelineMode,
    limits: ChartParseLimits,
    source: SourceSpan,
) -> PipelineResult<K> {
    match parse_lexing(grammar, start, lexing, mode, limits, source)? {
        RelationalPipelineResult::Match(x) => Ok(Ok(x)),
        RelationalPipelineResult::SyntacticNoMatch {
            attempted_tokens,
            mode,
            ..
        } => Ok(Err(PipelineDiagnostic::Syntactic {
            attempted_tokens,
            mode,
        })),
    }
}

fn parse_many<K: Clone + PartialOrd>(
    grammar: &Cfg<K>,
    start: NtId,
    paths: Vec<Lexing<K>>,
    mode: PipelineMode,
    limits: ChartParseLimits,
    source: SourceSpan,
) -> Result<Vec<RelationalPipelineResult<K>>, PipelineError> {
    paths
        .into_iter()
        .map(|path| parse_lexing(grammar, start, path, mode, limits, source))
        .collect()
}

fn parse_lexing<K: Clone + PartialOrd>(
    grammar: &Cfg<K>,
    start: NtId,
    lexing: Lexing<K>,
    mode: PipelineMode,
    limits: ChartParseLimits,
    source: SourceSpan,
) -> Result<RelationalPipelineResult<K>, PipelineError> {
    let kinds = lexing
        .tokens
        .iter()
        .map(|t| t.kind.clone())
        .collect::<Vec<_>>();
    let forest = ChartCfgParser::new(grammar, start, limits)
        .parse_forest(&kinds)
        .map_err(PipelineError::Syntactic)?;
    let end = (mode == PipelineMode::Exact).then_some(kinds.len());
    let roots = forest.root_ids(start, 0, end);
    if roots.is_empty() {
        return Ok(RelationalPipelineResult::SyntacticNoMatch {
            lexing,
            attempted_tokens: Span::new(0, kinds.len()).expect("ordered"),
            mode,
        });
    }
    Ok(RelationalPipelineResult::Match(PipelineMatch {
        lexing,
        forest,
        roots,
        mode,
        source,
    }))
}

fn byte_extent(len: usize) -> SourceSpan {
    let span = Span::new(0, len).expect("ordered");
    SourceSpan {
        units: span,
        bytes: Some(span),
    }
}

fn decoded_extent(source: &DecodedText) -> SourceSpan {
    SourceSpan {
        units: Span::new(0, source.scalars.len()).expect("ordered"),
        bytes: source
            .scalar_byte_offsets
            .last()
            .copied()
            .and_then(|end| Span::new(0, end)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_grammar::{Regex, Seg, parse_regex, parse_regex_u8};
    use covalence_kernel_data::RawByte;
    use covalence_lexer_parsing::{LexerPolicy, TiePolicy, TokenRule};
    use covalence_parsing_api::{TextEncodingBoundary, Utf8};

    #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
    enum Kind {
        Number,
        Plus,
        Space,
        Short,
        Long,
        Unicode,
    }

    const LEX: LexerBudget = LexerBudget::new(128, 4_000, 128, 512, 128, 128);
    const CHART: ChartParseLimits = ChartParseLimits {
        work: 100_000,
        results_per_cell: 1_000,
        chart_entries: 10_000,
    };
    const BUDGET: PipelineBudget = PipelineBudget {
        lexer: LEX,
        parser: CHART,
    };

    fn arithmetic() -> (Cfg<Kind>, NtId) {
        let mut g = Cfg::new();
        let s = g.add_nt("expression");
        g.add_prod(
            s,
            vec![
                Seg::term(Regex::lit(Kind::Number)),
                Seg::term(Regex::lit(Kind::Plus)),
                Seg::term(Regex::lit(Kind::Number)),
            ],
        );
        (g, s)
    }

    #[test]
    fn arithmetic_demo_retains_skip_trace_and_exactness() {
        let lexer = ByteLexer::new(
            vec![
                TokenRule::token(Kind::Number, parse_regex_u8("[0-9]+").unwrap(), 0),
                TokenRule::token(Kind::Plus, parse_regex_u8("\\+").unwrap(), 0),
                TokenRule::skip(Kind::Space, parse_regex_u8(" +").unwrap(), 0),
            ],
            LexerPolicy::default(),
        )
        .unwrap();
        let (g, s) = arithmetic();
        let x = ByteLexerCfg::new(lexer, &g, s)
            .parse(b"12 + 3", PipelineMode::Exact, BUDGET)
            .unwrap()
            .unwrap();
        assert_eq!(x.lexing.tokens.len(), 3);
        assert_eq!(x.lexing.trace.len(), 5);
        assert_eq!(x.roots.len(), 1);
        assert_eq!(
            x.source_cover(Span::new(0, 3).unwrap()).unwrap().bytes,
            Some(Span::new(0, 6).unwrap())
        );
    }

    #[test]
    fn lexical_diagnostic_is_stage_specific() {
        let lexer = ByteLexer::new(
            vec![
                TokenRule::token(Kind::Short, parse_regex_u8("a").unwrap(), 0),
                TokenRule::token(Kind::Long, parse_regex_u8("a").unwrap(), 0),
            ],
            LexerPolicy {
                tie: TiePolicy::RejectAmbiguous,
            },
        )
        .unwrap();
        let mut g = Cfg::new();
        let s = g.add_nt("s");
        g.add_prod(s, vec![Seg::term(Regex::lit(Kind::Short))]);
        assert!(matches!(
            ByteLexerCfg::new(lexer, &g, s).parse(b"a", PipelineMode::Exact, BUDGET),
            Ok(Err(PipelineDiagnostic::Lexical(
                LexerDiagnostic::Ambiguous { .. }
            )))
        ));
    }

    #[test]
    fn lexical_ambiguity_remains_separate() {
        let lexer = ByteLexer::new(
            vec![
                TokenRule::token(Kind::Short, parse_regex_u8("a").unwrap(), 0),
                TokenRule::token(Kind::Long, parse_regex_u8("aa").unwrap(), 0),
            ],
            LexerPolicy::default(),
        )
        .unwrap();
        let mut g = Cfg::new();
        let s = g.add_nt("s");
        g.add_prod(s, vec![Seg::term(Regex::lit(Kind::Long))]);
        g.add_prod(
            s,
            vec![Seg::term(Regex::concat([
                Regex::lit(Kind::Short),
                Regex::lit(Kind::Short),
            ]))],
        );
        let xs = ByteLexerCfg::new(lexer, &g, s)
            .parse_relational(b"aa", PipelineMode::Exact, BUDGET)
            .unwrap();
        assert_eq!(xs.len(), 2);
        assert!(
            xs.iter()
                .all(|x| matches!(x, RelationalPipelineResult::Match(_)))
        );
    }

    #[test]
    fn syntactic_ambiguity_stays_packed() {
        let lexer = ByteLexer::new(
            vec![TokenRule::token(
                Kind::Short,
                parse_regex_u8("a").unwrap(),
                0,
            )],
            LexerPolicy::default(),
        )
        .unwrap();
        let mut g = Cfg::new();
        let s = g.add_nt("s");
        g.add_prod(s, vec![Seg::term(Regex::lit(Kind::Short))]);
        g.add_prod(s, vec![Seg::term(Regex::lit(Kind::Short))]);
        let x = ByteLexerCfg::new(lexer, &g, s)
            .parse(b"a", PipelineMode::Exact, BUDGET)
            .unwrap()
            .unwrap();
        assert_eq!(x.forest.node(x.roots[0]).unwrap().alternatives.len(), 2);
    }

    #[test]
    fn prefix_and_exact_modes_are_distinct() {
        let lexer = ByteLexer::new(
            vec![
                TokenRule::token(Kind::Short, parse_regex_u8("a").unwrap(), 0),
                TokenRule::token(Kind::Long, parse_regex_u8("b").unwrap(), 0),
            ],
            LexerPolicy::default(),
        )
        .unwrap();
        let mut g = Cfg::new();
        let s = g.add_nt("s");
        g.add_prod(s, vec![Seg::term(Regex::lit(Kind::Short))]);
        let p = ByteLexerCfg::new(lexer, &g, s);
        let prefix = p
            .parse(b"ab", PipelineMode::Prefix, BUDGET)
            .unwrap()
            .unwrap();
        assert_eq!(prefix.forest.node(prefix.roots[0]).unwrap().span.end, 1);
        assert!(matches!(
            p.parse(b"ab", PipelineMode::Exact, BUDGET),
            Ok(Err(PipelineDiagnostic::Syntactic {
                mode: PipelineMode::Exact,
                ..
            }))
        ));
    }

    #[test]
    fn unicode_spans_retain_scalar_and_byte_offsets() {
        let lexer = TextLexer::new(
            vec![
                TokenRule::token(Kind::Unicode, parse_regex("é").unwrap(), 0),
                TokenRule::token(Kind::Short, parse_regex("x").unwrap(), 0),
            ],
            LexerPolicy::default(),
        )
        .unwrap();
        let mut g = Cfg::new();
        let s = g.add_nt("s");
        g.add_prod(
            s,
            vec![Seg::term(Regex::concat([
                Regex::lit(Kind::Unicode),
                Regex::lit(Kind::Short),
            ]))],
        );
        let raw = "éx"
            .as_bytes()
            .iter()
            .copied()
            .map(RawByte)
            .collect::<Vec<_>>();
        let decoded = Utf8.decode_text(&raw).unwrap();
        let x = TextLexerCfg::new(lexer, &g, s)
            .parse_decoded(&decoded, PipelineMode::Exact, BUDGET)
            .unwrap()
            .unwrap();
        let span = x.source_cover(Span::new(0, 2).unwrap()).unwrap();
        assert_eq!(span.units, Span::new(0, 2).unwrap());
        assert_eq!(span.bytes, Some(Span::new(0, 3).unwrap()));
    }

    #[test]
    fn independent_bounds_report_their_stage() {
        let lexer = ByteLexer::new(
            vec![TokenRule::token(
                Kind::Short,
                parse_regex_u8("a").unwrap(),
                0,
            )],
            LexerPolicy::default(),
        )
        .unwrap();
        let mut g = Cfg::new();
        let s = g.add_nt("s");
        g.add_prod(s, vec![Seg::term(Regex::lit(Kind::Short))]);
        let p = ByteLexerCfg::new(lexer, &g, s);
        let lexical = PipelineBudget {
            lexer: LexerBudget::new(0, 1, 1, 1, 1, 1),
            parser: CHART,
        };
        assert!(matches!(
            p.parse(b"a", PipelineMode::Exact, lexical),
            Err(PipelineError::Lexical(LexerError::InputTooLarge { .. }))
        ));
        let syntactic = PipelineBudget {
            lexer: LEX,
            parser: ChartParseLimits { work: 0, ..CHART },
        };
        assert!(matches!(
            p.parse(b"a", PipelineMode::Exact, syntactic),
            Err(PipelineError::Syntactic(CfgParseError::WorkLimit {
                limit: 0
            }))
        ));
    }
}
