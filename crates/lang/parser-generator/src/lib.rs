//! Deterministic compilation of named lexer and CFG specifications.
//!
//! A0018 is a convenience layer over A0016 and A0017. Compilation resolves
//! names to dense IDs and validates the specification, but its output remains
//! untrusted configuration. Execution still goes through the checked, bounded
//! regex, lexer, and packed chart evaluators; this crate mints no theorem.
//!
//! @covalence-api {"id":"A0018","title":"Declarative parser generation","status":"experimental","dependsOn":["A0016","A0017"]}

#![forbid(unsafe_code)]

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use covalence_grammar::{Cfg, NtId, Regex, Seg};
use covalence_lexer_cfg_parsing::{
    ByteLexerCfg, PipelineBudget, PipelineError, PipelineMode, PipelineResult,
    RelationalPipelineResult,
};
use covalence_lexer_parsing::{ByteLexer, LexerBuildError, LexerPolicy, TokenRule};

/// Dense token identity assigned in declaration order.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TokenId(pub usize);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TokenSpec {
    pub name: String,
    pub regex: Regex<u8>,
    pub priority: u32,
    pub skip: bool,
}

impl TokenSpec {
    pub fn token(name: impl Into<String>, regex: Regex<u8>, priority: u32) -> Self {
        Self {
            name: name.into(),
            regex,
            priority,
            skip: false,
        }
    }

    pub fn skip(name: impl Into<String>, regex: Regex<u8>, priority: u32) -> Self {
        Self {
            name: name.into(),
            regex,
            priority,
            skip: true,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NamedSymbol {
    Token(String),
    Nonterminal(String),
}

impl NamedSymbol {
    pub fn token(name: impl Into<String>) -> Self {
        Self::Token(name.into())
    }

    pub fn nonterminal(name: impl Into<String>) -> Self {
        Self::Nonterminal(name.into())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProductionSpec {
    pub lhs: String,
    pub rhs: Vec<NamedSymbol>,
}

impl ProductionSpec {
    pub fn new(lhs: impl Into<String>, rhs: Vec<NamedSymbol>) -> Self {
        Self {
            lhs: lhs.into(),
            rhs,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GrammarSpec {
    pub name: String,
    pub start: String,
    /// The declaration order fixes dense nonterminal IDs. Each name must have
    /// at least one production; production order remains yacc-style priority
    /// and is preserved exactly.
    pub nonterminals: Vec<String>,
    pub productions: Vec<ProductionSpec>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParserSpec {
    pub name: String,
    pub lexer_policy: LexerPolicy,
    pub tokens: Vec<TokenSpec>,
    pub grammar: GrammarSpec,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DiagnosticLevel {
    Error,
    Warning,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DiagnosticKind {
    DuplicateToken {
        name: String,
    },
    DuplicateNonterminal {
        name: String,
    },
    NullableToken {
        name: String,
    },
    MissingStart {
        name: String,
    },
    MissingProduction {
        name: String,
    },
    UnknownToken {
        production: usize,
        symbol: usize,
        name: String,
    },
    UnknownNonterminal {
        production: usize,
        symbol: usize,
        name: String,
    },
    UnknownLhs {
        production: usize,
        name: String,
    },
    UnreachableNonterminal {
        name: String,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ValidationDiagnostic {
    pub level: DiagnosticLevel,
    pub kind: DiagnosticKind,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ValidationReport {
    /// Nullable grammar nonterminals are accepted and made explicit. Nullable
    /// token regexes are errors because they could prevent lexer progress.
    pub nullable_nonterminals: Vec<String>,
    pub reachable_nonterminals: Vec<String>,
    pub diagnostics: Vec<ValidationDiagnostic>,
}

impl ValidationReport {
    pub fn is_valid(&self) -> bool {
        !self
            .diagnostics
            .iter()
            .any(|d| d.level == DiagnosticLevel::Error)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CompileError {
    pub report: ValidationReport,
}

/// Deterministically generated untrusted configuration.
#[derive(Clone, Debug)]
pub struct GeneratedByteParser {
    name: String,
    grammar_name: String,
    token_names: Vec<String>,
    nonterminal_names: Vec<String>,
    lexer: ByteLexer<TokenId>,
    grammar: Cfg<TokenId>,
    start: NtId,
    report: ValidationReport,
}

impl GeneratedByteParser {
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn token_name(&self, id: TokenId) -> Option<&str> {
        self.token_names.get(id.0).map(String::as_str)
    }

    pub fn grammar_name(&self) -> &str {
        &self.grammar_name
    }

    pub fn nonterminal_names(&self) -> &[String] {
        &self.nonterminal_names
    }

    pub fn grammar(&self) -> &Cfg<TokenId> {
        &self.grammar
    }

    pub fn validation(&self) -> &ValidationReport {
        &self.report
    }

    pub fn parse(
        &self,
        source: &[u8],
        mode: PipelineMode,
        budget: PipelineBudget,
    ) -> PipelineResult<TokenId> {
        ByteLexerCfg::new(self.lexer.clone(), &self.grammar, self.start).parse(source, mode, budget)
    }

    pub fn parse_relational(
        &self,
        source: &[u8],
        mode: PipelineMode,
        budget: PipelineBudget,
    ) -> Result<Vec<RelationalPipelineResult<TokenId>>, PipelineError> {
        ByteLexerCfg::new(self.lexer.clone(), &self.grammar, self.start)
            .parse_relational(source, mode, budget)
    }
}

impl ParserSpec {
    pub fn validate(&self) -> ValidationReport {
        let mut diagnostics = Vec::new();
        let tokens = unique_names(
            self.tokens.iter().map(|t| t.name.as_str()),
            |name| DiagnosticKind::DuplicateToken { name },
            &mut diagnostics,
        );
        let nts = unique_names(
            self.grammar.nonterminals.iter().map(String::as_str),
            |name| DiagnosticKind::DuplicateNonterminal { name },
            &mut diagnostics,
        );

        for token in &self.tokens {
            if token.regex.nullable() {
                error(
                    &mut diagnostics,
                    DiagnosticKind::NullableToken {
                        name: token.name.clone(),
                    },
                );
            }
        }
        if !nts.contains_key(self.grammar.start.as_str()) {
            error(
                &mut diagnostics,
                DiagnosticKind::MissingStart {
                    name: self.grammar.start.clone(),
                },
            );
        }

        let mut has_production = BTreeSet::new();
        let mut edges: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
        for (production, p) in self.grammar.productions.iter().enumerate() {
            if !nts.contains_key(p.lhs.as_str()) {
                error(
                    &mut diagnostics,
                    DiagnosticKind::UnknownLhs {
                        production,
                        name: p.lhs.clone(),
                    },
                );
            } else {
                has_production.insert(p.lhs.as_str());
            }
            for (symbol, s) in p.rhs.iter().enumerate() {
                match s {
                    NamedSymbol::Token(name) if !tokens.contains_key(name.as_str()) => error(
                        &mut diagnostics,
                        DiagnosticKind::UnknownToken {
                            production,
                            symbol,
                            name: name.clone(),
                        },
                    ),
                    NamedSymbol::Nonterminal(name) if !nts.contains_key(name.as_str()) => error(
                        &mut diagnostics,
                        DiagnosticKind::UnknownNonterminal {
                            production,
                            symbol,
                            name: name.clone(),
                        },
                    ),
                    NamedSymbol::Nonterminal(name) => {
                        edges.entry(p.lhs.as_str()).or_default().push(name);
                    }
                    NamedSymbol::Token(_) => {}
                }
            }
        }
        for name in &self.grammar.nonterminals {
            if !has_production.contains(name.as_str()) {
                error(
                    &mut diagnostics,
                    DiagnosticKind::MissingProduction { name: name.clone() },
                );
            }
        }

        let reachable = reachable_from(&self.grammar.start, &edges, &nts);
        for name in &self.grammar.nonterminals {
            if !reachable.contains(name.as_str()) {
                diagnostics.push(ValidationDiagnostic {
                    level: DiagnosticLevel::Warning,
                    kind: DiagnosticKind::UnreachableNonterminal { name: name.clone() },
                });
            }
        }
        let nullable = nullable_nonterminals(self, &nts, &tokens);

        ValidationReport {
            nullable_nonterminals: self
                .grammar
                .nonterminals
                .iter()
                .filter(|name| nullable.contains(name.as_str()))
                .cloned()
                .collect(),
            reachable_nonterminals: self
                .grammar
                .nonterminals
                .iter()
                .filter(|name| reachable.contains(name.as_str()))
                .cloned()
                .collect(),
            diagnostics,
        }
    }

    pub fn compile(&self) -> Result<GeneratedByteParser, CompileError> {
        let report = self.validate();
        if !report.is_valid() {
            return Err(CompileError { report });
        }

        let token_ids = self
            .tokens
            .iter()
            .enumerate()
            .map(|(i, t)| (t.name.as_str(), TokenId(i)))
            .collect::<BTreeMap<_, _>>();
        let rules = self
            .tokens
            .iter()
            .enumerate()
            .map(|(i, t)| {
                let id = TokenId(i);
                if t.skip {
                    TokenRule::skip(id, t.regex.clone(), t.priority)
                } else {
                    TokenRule::token(id, t.regex.clone(), t.priority)
                }
            })
            .collect();
        let lexer = ByteLexer::new(rules, self.lexer_policy).map_err(|e| CompileError {
            report: impossible_lexer_error(report.clone(), e),
        })?;

        let mut grammar = Cfg::new();
        let nt_ids = self
            .grammar
            .nonterminals
            .iter()
            .map(|name| (name.as_str(), grammar.add_nt(name)))
            .collect::<BTreeMap<_, _>>();
        for p in &self.grammar.productions {
            let lhs = nt_ids[p.lhs.as_str()];
            let rhs = p
                .rhs
                .iter()
                .map(|s| match s {
                    NamedSymbol::Token(name) => Seg::term(Regex::lit(token_ids[name.as_str()])),
                    NamedSymbol::Nonterminal(name) => Seg::nt(nt_ids[name.as_str()]),
                })
                .collect();
            grammar.add_prod(lhs, rhs);
        }
        let start = nt_ids[self.grammar.start.as_str()];
        Ok(GeneratedByteParser {
            name: self.name.clone(),
            grammar_name: self.grammar.name.clone(),
            token_names: self.tokens.iter().map(|t| t.name.clone()).collect(),
            nonterminal_names: self.grammar.nonterminals.clone(),
            lexer,
            grammar,
            start,
            report,
        })
    }
}

fn unique_names<'a>(
    names: impl Iterator<Item = &'a str>,
    duplicate: impl Fn(String) -> DiagnosticKind,
    diagnostics: &mut Vec<ValidationDiagnostic>,
) -> BTreeMap<&'a str, usize> {
    let mut out = BTreeMap::new();
    for (index, name) in names.enumerate() {
        if out.insert(name, index).is_some() {
            error(diagnostics, duplicate(name.to_owned()));
        }
    }
    out
}

fn error(diagnostics: &mut Vec<ValidationDiagnostic>, kind: DiagnosticKind) {
    diagnostics.push(ValidationDiagnostic {
        level: DiagnosticLevel::Error,
        kind,
    });
}

fn reachable_from<'a>(
    start: &'a str,
    edges: &BTreeMap<&'a str, Vec<&'a str>>,
    nts: &BTreeMap<&'a str, usize>,
) -> BTreeSet<&'a str> {
    let mut reachable = BTreeSet::new();
    let mut queue = VecDeque::from([start]);
    while let Some(name) = queue.pop_front() {
        if !nts.contains_key(name) || !reachable.insert(name) {
            continue;
        }
        queue.extend(edges.get(name).into_iter().flatten().copied());
    }
    reachable
}

fn nullable_nonterminals<'a>(
    spec: &'a ParserSpec,
    nts: &BTreeMap<&'a str, usize>,
    tokens: &BTreeMap<&'a str, usize>,
) -> BTreeSet<&'a str> {
    let mut nullable = BTreeSet::new();
    loop {
        let mut changed = false;
        for p in &spec.grammar.productions {
            if !nts.contains_key(p.lhs.as_str()) {
                continue;
            }
            let derives_empty = p.rhs.iter().all(|s| match s {
                NamedSymbol::Nonterminal(name) => nullable.contains(name.as_str()),
                NamedSymbol::Token(name) => spec
                    .tokens
                    .get(tokens.get(name.as_str()).copied().unwrap_or(usize::MAX))
                    .is_some_and(|t| t.regex.nullable()),
            });
            if derives_empty && nullable.insert(p.lhs.as_str()) {
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    nullable
}

fn impossible_lexer_error(
    mut report: ValidationReport,
    error: LexerBuildError,
) -> ValidationReport {
    let LexerBuildError::NullableRule { rule_index } = error;
    let name = format!("rule-{rule_index}");
    error_diagnostic(&mut report, DiagnosticKind::NullableToken { name });
    report
}

fn error_diagnostic(report: &mut ValidationReport, kind: DiagnosticKind) {
    report.diagnostics.push(ValidationDiagnostic {
        level: DiagnosticLevel::Error,
        kind,
    });
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_cfg_parsing::{CfgParseError, ChartParseLimits};
    use covalence_grammar::parse_regex_u8;
    use covalence_lexer_cfg_parsing::{PipelineDiagnostic, PipelineError};
    use covalence_lexer_parsing::{LexerBudget, LexerError};
    use covalence_parsing_api::Span;

    const BUDGET: PipelineBudget = PipelineBudget {
        lexer: LexerBudget::new(128, 4_000, 128, 512, 128, 128),
        parser: ChartParseLimits {
            work: 100_000,
            results_per_cell: 1_000,
            chart_entries: 10_000,
        },
    };

    fn arithmetic() -> ParserSpec {
        use NamedSymbol::{Nonterminal as N, Token as T};
        ParserSpec {
            name: "arithmetic".into(),
            lexer_policy: LexerPolicy::default(),
            tokens: vec![
                TokenSpec::token("number", parse_regex_u8("[0-9]+").unwrap(), 0),
                TokenSpec::token("plus", parse_regex_u8("\\+").unwrap(), 0),
                TokenSpec::skip("space", parse_regex_u8(" +").unwrap(), 0),
            ],
            grammar: GrammarSpec {
                name: "expressions".into(),
                start: "expr".into(),
                nonterminals: vec!["expr".into()],
                productions: vec![
                    ProductionSpec::new(
                        "expr",
                        vec![N("expr".into()), T("plus".into()), N("expr".into())],
                    ),
                    ProductionSpec::new("expr", vec![T("number".into())]),
                ],
            },
        }
    }

    #[test]
    fn yacc_style_arithmetic_preserves_spans_and_packs_ambiguity() {
        let parser = arithmetic().compile().unwrap();
        let parsed = parser
            .parse(b"1 + 2 + 3", PipelineMode::Exact, BUDGET)
            .unwrap()
            .unwrap();
        assert_eq!(parsed.source.bytes, Some(Span::new(0, 9).unwrap()));
        assert_eq!(parsed.lexing.tokens.len(), 5);
        assert_eq!(parsed.lexing.trace.len(), 9);
        assert_eq!(parsed.roots.len(), 1);
        let root = parsed.forest.node(parsed.roots[0]).unwrap();
        assert!(root.alternatives.len() >= 2);
    }

    #[test]
    fn validation_reports_names_nullability_and_reachability() {
        let mut spec = arithmetic();
        spec.tokens.push(TokenSpec::token("empty", Regex::eps(), 0));
        spec.grammar.nonterminals.push("unused".into());
        spec.grammar
            .productions
            .push(ProductionSpec::new("unused", vec![]));
        spec.grammar.productions.push(ProductionSpec::new(
            "expr",
            vec![NamedSymbol::token("missing")],
        ));
        let report = spec.validate();
        assert_eq!(report.nullable_nonterminals, vec!["unused"]);
        assert!(report.diagnostics.iter().any(|d| matches!(
            d.kind,
            DiagnosticKind::NullableToken { ref name } if name == "empty"
        )));
        assert!(report.diagnostics.iter().any(|d| matches!(
            d.kind,
            DiagnosticKind::UnknownToken { ref name, .. } if name == "missing"
        )));
        assert!(report.diagnostics.iter().any(|d| matches!(
            d.kind,
            DiagnosticKind::UnreachableNonterminal { ref name } if name == "unused"
        )));
        assert!(spec.compile().is_err());
    }

    #[test]
    fn generation_is_reproducible_and_order_preserving() {
        let a = arithmetic().compile().unwrap();
        let b = arithmetic().compile().unwrap();
        assert_eq!(a.token_names, b.token_names);
        assert_eq!(a.grammar_name, b.grammar_name);
        assert_eq!(a.nonterminal_names, b.nonterminal_names);
        assert_eq!(a.grammar, b.grammar);
        assert_eq!(a.start, b.start);
        assert_eq!(a.validation(), b.validation());
    }

    #[test]
    fn lexical_and_chart_budgets_remain_independent() {
        let parser = arithmetic().compile().unwrap();
        let lexical = PipelineBudget {
            lexer: LexerBudget::new(0, 1, 1, 1, 1, 1),
            parser: BUDGET.parser,
        };
        assert!(matches!(
            parser.parse(b"1", PipelineMode::Exact, lexical),
            Err(PipelineError::Lexical(LexerError::InputTooLarge { .. }))
        ));
        let syntactic = PipelineBudget {
            lexer: BUDGET.lexer,
            parser: ChartParseLimits {
                work: 0,
                ..BUDGET.parser
            },
        };
        assert!(matches!(
            parser.parse(b"1", PipelineMode::Exact, syntactic),
            Err(PipelineError::Syntactic(CfgParseError::WorkLimit { .. }))
        ));
    }

    #[test]
    fn valid_but_unrecognized_input_is_a_diagnostic_not_a_proof() {
        let parser = arithmetic().compile().unwrap();
        assert!(matches!(
            parser.parse(b"1+", PipelineMode::Exact, BUDGET),
            Ok(Err(PipelineDiagnostic::Syntactic { .. }))
        ));
    }
}
