//! Bounded, grammar-neutral lexical analysis over A0013/A0015 regex evaluators.
//!
//! Lexer rules are syntax. Results and traces are untrusted host data: this
//! crate neither mints theorems nor claims bounded failure proves non-membership.
//!
//! @covalence-api {"id":"A0016","title":"Bounded lexical analysis","status":"experimental","dependsOn":["A0013","A0015"]}

#![forbid(unsafe_code)]

use covalence_grammar::Regex;
use covalence_logic_api::UnicodeScalar;
use covalence_parsing_api::{ByteParserRelation, DecodedText, ParseBudget, RelationalParser, Span};
use covalence_regex_parsing::{ByteRegexParser, RegexBudget, RegexEvalError, TextRegexParser};

/// A token rule. Smaller `priority` values win after longest-match selection.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TokenRule<K, A> {
    pub kind: K,
    pub regex: Regex<A>,
    pub priority: u32,
    pub skip: bool,
}

impl<K, A> TokenRule<K, A> {
    pub fn token(kind: K, regex: Regex<A>, priority: u32) -> Self {
        Self {
            kind,
            regex,
            priority,
            skip: false,
        }
    }

    pub fn skip(kind: K, regex: Regex<A>, priority: u32) -> Self {
        Self {
            kind,
            regex,
            priority,
            skip: true,
        }
    }
}

/// How equal-length, equal-priority rules are resolved.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum TiePolicy {
    #[default]
    EarlierRule,
    LaterRule,
    RejectAmbiguous,
}

/// Functional selection is maximal munch, then minimum numeric priority,
/// followed by this explicit tie policy.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct LexerPolicy {
    pub tie: TiePolicy,
}

/// Global bounds. Regex fuel applies to each rule attempt, while
/// `max_rule_attempts` bounds their aggregate number.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LexerBudget {
    pub max_source_units: usize,
    pub regex_fuel: usize,
    pub max_regex_results: usize,
    pub max_rule_attempts: usize,
    pub max_tokens: usize,
    pub max_paths: usize,
}

impl LexerBudget {
    pub const fn new(
        max_source_units: usize,
        regex_fuel: usize,
        max_regex_results: usize,
        max_rule_attempts: usize,
        max_tokens: usize,
        max_paths: usize,
    ) -> Self {
        Self {
            max_source_units,
            regex_fuel,
            max_regex_results,
            max_rule_attempts,
            max_tokens,
            max_paths,
        }
    }
}

/// Span provenance in source units, with encoded-byte provenance when known.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SourceSpan {
    pub units: Span,
    pub bytes: Option<Span>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpannedToken<K> {
    pub kind: K,
    pub span: SourceSpan,
    pub rule_index: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LexStep {
    pub span: SourceSpan,
    pub rule_index: usize,
    pub skipped: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Lexing<K> {
    pub tokens: Vec<SpannedToken<K>>,
    pub trace: Vec<LexStep>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LexerBuildError {
    NullableRule { rule_index: usize },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LexerDiagnostic {
    NoRuleMatched {
        at: usize,
    },
    Ambiguous {
        span: Span,
        rule_indices: Vec<usize>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LexerError {
    InputTooLarge { actual: usize, limit: usize },
    RuleAttemptLimitExceeded { limit: usize },
    TokenLimitExceeded { limit: usize },
    PathLimitExceeded { limit: usize },
    RegexFuelExhausted,
    RegexResultLimitExceeded { limit: usize },
}

pub type LexResult<K> = Result<Result<Lexing<K>, LexerDiagnostic>, LexerError>;

/// A positive candidate edge in the lexical relation.
#[derive(Clone, Debug)]
struct Candidate<K> {
    kind: K,
    rule_index: usize,
    priority: u32,
    skip: bool,
    end: usize,
}

/// Bounded byte lexer. Byte offsets and source-unit offsets coincide.
#[derive(Clone, Debug)]
pub struct ByteLexer<K> {
    rules: Vec<TokenRule<K, u8>>,
    policy: LexerPolicy,
}

impl<K: Clone> ByteLexer<K> {
    pub fn new(rules: Vec<TokenRule<K, u8>>, policy: LexerPolicy) -> Result<Self, LexerBuildError> {
        reject_nullable(&rules)?;
        Ok(Self { rules, policy })
    }

    pub fn rules(&self) -> &[TokenRule<K, u8>] {
        &self.rules
    }

    pub fn lex(&self, source: &[u8], budget: LexerBudget) -> LexResult<K> {
        check_input(source.len(), budget)?;
        let mut attempts = 0;
        let mut at = 0;
        let mut result = empty_lexing();
        while at < source.len() {
            let candidates = self.byte_candidates(source, at, budget, &mut attempts)?;
            let chosen = match choose_candidate(candidates, self.policy.tie, at) {
                Ok(candidate) => candidate,
                Err(diagnostic) => return Ok(Err(diagnostic)),
            };
            let end = chosen.end;
            push_step(&mut result, chosen, byte_span(at, end), budget)?;
            at = end;
        }
        Ok(Ok(result))
    }

    /// Enumerate tokenizations using every positive regex match, independently
    /// of the functional maximal-munch policy.
    pub fn lex_relational(
        &self,
        source: &[u8],
        budget: LexerBudget,
    ) -> Result<Vec<Lexing<K>>, LexerError> {
        check_input(source.len(), budget)?;
        let mut attempts = 0;
        let mut frontier = vec![(0, empty_lexing())];
        let mut complete = Vec::new();
        while let Some((at, lexing)) = frontier.pop() {
            if at == source.len() {
                complete.push(lexing);
                enforce_paths(frontier.len() + complete.len(), budget)?;
                continue;
            }
            for candidate in self.byte_candidates(source, at, budget, &mut attempts)? {
                let end = candidate.end;
                let mut next = lexing.clone();
                push_step(&mut next, candidate, byte_span(at, end), budget)?;
                frontier.push((end, next));
                enforce_paths(frontier.len() + complete.len(), budget)?;
            }
        }
        Ok(complete)
    }

    fn byte_candidates(
        &self,
        source: &[u8],
        at: usize,
        budget: LexerBudget,
        attempts: &mut usize,
    ) -> Result<Vec<Candidate<K>>, LexerError> {
        let mut out = Vec::new();
        for (rule_index, rule) in self.rules.iter().enumerate() {
            spend_attempt(attempts, budget)?;
            let matches = ByteRegexParser::new(rule.regex.clone())
                .parse_relational(
                    &source[at..],
                    ParseBudget::new(
                        budget.max_source_units,
                        budget.regex_fuel,
                        budget.max_regex_results,
                    ),
                )
                .map_err(map_byte_regex_error)?;
            out.extend(matches.into_iter().filter_map(|(_, witness)| {
                let end = at + witness.consumed.end;
                (end > at).then(|| Candidate {
                    kind: rule.kind.clone(),
                    rule_index,
                    priority: rule.priority,
                    skip: rule.skip,
                    end,
                })
            }));
        }
        Ok(out)
    }
}

/// Bounded Unicode-scalar lexer. `lex_decoded` retains UTF-8 byte provenance.
#[derive(Clone, Debug)]
pub struct TextLexer<K> {
    rules: Vec<TokenRule<K, char>>,
    policy: LexerPolicy,
}

impl<K: Clone> TextLexer<K> {
    pub fn new(
        rules: Vec<TokenRule<K, char>>,
        policy: LexerPolicy,
    ) -> Result<Self, LexerBuildError> {
        reject_nullable(&rules)?;
        Ok(Self { rules, policy })
    }

    pub fn rules(&self) -> &[TokenRule<K, char>] {
        &self.rules
    }

    pub fn lex(&self, source: &[UnicodeScalar], budget: LexerBudget) -> LexResult<K> {
        self.lex_with_spans(source, budget, |span| SourceSpan {
            units: span,
            bytes: None,
        })
    }

    pub fn lex_decoded(&self, source: &DecodedText, budget: LexerBudget) -> LexResult<K> {
        self.lex_with_spans(&source.scalars, budget, |span| SourceSpan {
            units: span,
            bytes: source.byte_span(span),
        })
    }

    /// Enumerate Unicode tokenizations without applying functional
    /// longest-match/priority resolution.
    pub fn lex_relational(
        &self,
        source: &[UnicodeScalar],
        budget: LexerBudget,
    ) -> Result<Vec<Lexing<K>>, LexerError> {
        self.lex_relational_with_spans(source, budget, |span| SourceSpan {
            units: span,
            bytes: None,
        })
    }

    /// Relational lexing with scalar-to-byte provenance retained.
    pub fn lex_decoded_relational(
        &self,
        source: &DecodedText,
        budget: LexerBudget,
    ) -> Result<Vec<Lexing<K>>, LexerError> {
        self.lex_relational_with_spans(&source.scalars, budget, |span| SourceSpan {
            units: span,
            bytes: source.byte_span(span),
        })
    }

    fn lex_with_spans<F>(
        &self,
        source: &[UnicodeScalar],
        budget: LexerBudget,
        provenance: F,
    ) -> LexResult<K>
    where
        F: Fn(Span) -> SourceSpan,
    {
        check_input(source.len(), budget)?;
        let mut attempts = 0;
        let mut at = 0;
        let mut result = empty_lexing();
        while at < source.len() {
            let candidates = self.text_candidates(source, at, budget, &mut attempts)?;
            let chosen = match choose_candidate(candidates, self.policy.tie, at) {
                Ok(candidate) => candidate,
                Err(diagnostic) => return Ok(Err(diagnostic)),
            };
            let end = chosen.end;
            let span = Span::new(at, end).expect("candidate advances");
            push_step(&mut result, chosen, provenance(span), budget)?;
            at = end;
        }
        Ok(Ok(result))
    }

    fn lex_relational_with_spans<F>(
        &self,
        source: &[UnicodeScalar],
        budget: LexerBudget,
        provenance: F,
    ) -> Result<Vec<Lexing<K>>, LexerError>
    where
        F: Fn(Span) -> SourceSpan,
    {
        check_input(source.len(), budget)?;
        let mut attempts = 0;
        let mut frontier = vec![(0, empty_lexing())];
        let mut complete = Vec::new();
        while let Some((at, lexing)) = frontier.pop() {
            if at == source.len() {
                complete.push(lexing);
                enforce_paths(frontier.len() + complete.len(), budget)?;
                continue;
            }
            for candidate in self.text_candidates(source, at, budget, &mut attempts)? {
                let end = candidate.end;
                let mut next = lexing.clone();
                let units = Span::new(at, end).expect("candidate advances");
                push_step(&mut next, candidate, provenance(units), budget)?;
                frontier.push((end, next));
                enforce_paths(frontier.len() + complete.len(), budget)?;
            }
        }
        Ok(complete)
    }

    fn text_candidates(
        &self,
        source: &[UnicodeScalar],
        at: usize,
        budget: LexerBudget,
        attempts: &mut usize,
    ) -> Result<Vec<Candidate<K>>, LexerError> {
        let mut out = Vec::new();
        for (rule_index, rule) in self.rules.iter().enumerate() {
            spend_attempt(attempts, budget)?;
            let parser = TextRegexParser::new(
                rule.regex.clone(),
                RegexBudget::new(
                    budget.max_source_units,
                    budget.regex_fuel,
                    budget.max_regex_results,
                ),
            );
            let matches = parser.parses(&source[at..]).map_err(map_text_regex_error)?;
            out.extend(matches.into_iter().filter_map(|(_, witness)| {
                let end = at + witness.accepting_end;
                (end > at).then(|| Candidate {
                    kind: rule.kind.clone(),
                    rule_index,
                    priority: rule.priority,
                    skip: rule.skip,
                    end,
                })
            }));
        }
        Ok(out)
    }
}

fn empty_lexing<K>() -> Lexing<K> {
    Lexing {
        tokens: Vec::new(),
        trace: Vec::new(),
    }
}

fn reject_nullable<K, A: Clone + PartialOrd>(
    rules: &[TokenRule<K, A>],
) -> Result<(), LexerBuildError> {
    for (rule_index, rule) in rules.iter().enumerate() {
        if rule.regex.nullable() {
            return Err(LexerBuildError::NullableRule { rule_index });
        }
    }
    Ok(())
}

fn choose_candidate<K>(
    mut candidates: Vec<Candidate<K>>,
    tie: TiePolicy,
    at: usize,
) -> Result<Candidate<K>, LexerDiagnostic> {
    let Some(longest) = candidates.iter().map(|candidate| candidate.end).max() else {
        return Err(LexerDiagnostic::NoRuleMatched { at });
    };
    candidates.retain(|candidate| candidate.end == longest);
    let priority = candidates
        .iter()
        .map(|candidate| candidate.priority)
        .min()
        .unwrap();
    candidates.retain(|candidate| candidate.priority == priority);
    if candidates.len() == 1 {
        return Ok(candidates.pop().unwrap());
    }
    candidates.sort_by_key(|candidate| candidate.rule_index);
    match tie {
        TiePolicy::EarlierRule => Ok(candidates.remove(0)),
        TiePolicy::LaterRule => Ok(candidates.pop().unwrap()),
        TiePolicy::RejectAmbiguous => Err(LexerDiagnostic::Ambiguous {
            span: Span::new(at, longest).expect("candidate advances"),
            rule_indices: candidates
                .into_iter()
                .map(|candidate| candidate.rule_index)
                .collect(),
        }),
    }
}

fn push_step<K: Clone>(
    result: &mut Lexing<K>,
    candidate: Candidate<K>,
    span: SourceSpan,
    budget: LexerBudget,
) -> Result<(), LexerError> {
    if result.trace.len() >= budget.max_tokens {
        return Err(LexerError::TokenLimitExceeded {
            limit: budget.max_tokens,
        });
    }
    if !candidate.skip {
        result.tokens.push(SpannedToken {
            kind: candidate.kind,
            span,
            rule_index: candidate.rule_index,
        });
    }
    result.trace.push(LexStep {
        span,
        rule_index: candidate.rule_index,
        skipped: candidate.skip,
    });
    Ok(())
}

fn byte_span(start: usize, end: usize) -> SourceSpan {
    let span = Span::new(start, end).expect("candidate advances");
    SourceSpan {
        units: span,
        bytes: Some(span),
    }
}

fn check_input(actual: usize, budget: LexerBudget) -> Result<(), LexerError> {
    if actual > budget.max_source_units {
        Err(LexerError::InputTooLarge {
            actual,
            limit: budget.max_source_units,
        })
    } else {
        Ok(())
    }
}

fn spend_attempt(attempts: &mut usize, budget: LexerBudget) -> Result<(), LexerError> {
    if *attempts >= budget.max_rule_attempts {
        Err(LexerError::RuleAttemptLimitExceeded {
            limit: budget.max_rule_attempts,
        })
    } else {
        *attempts += 1;
        Ok(())
    }
}

fn enforce_paths(actual: usize, budget: LexerBudget) -> Result<(), LexerError> {
    if actual > budget.max_paths {
        Err(LexerError::PathLimitExceeded {
            limit: budget.max_paths,
        })
    } else {
        Ok(())
    }
}

fn map_byte_regex_error(error: covalence_parsing_api::ByteParseError) -> LexerError {
    use covalence_parsing_api::ByteParseError;
    match error {
        ByteParseError::InputTooLarge { actual, limit } => {
            LexerError::InputTooLarge { actual, limit }
        }
        ByteParseError::FuelExhausted { .. } => LexerError::RegexFuelExhausted,
        ByteParseError::ResultLimitExceeded { limit } => {
            LexerError::RegexResultLimitExceeded { limit }
        }
    }
}

fn map_text_regex_error(error: RegexEvalError) -> LexerError {
    match error {
        RegexEvalError::InputTooLarge { actual, limit } => {
            LexerError::InputTooLarge { actual, limit }
        }
        RegexEvalError::FuelExhausted { .. } => LexerError::RegexFuelExhausted,
        RegexEvalError::ResultLimitExceeded { limit } => {
            LexerError::RegexResultLimitExceeded { limit }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_grammar::{parse_regex, parse_regex_u8};
    use covalence_logic_api::RawByte;
    use covalence_parsing_api::{TextEncodingBoundary, Utf8};

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum Kind {
        Short,
        Long,
        Keyword,
        Name,
        Space,
        Unicode,
    }

    const BUDGET: LexerBudget = LexerBudget::new(128, 4_000, 128, 128, 128, 128);

    #[test]
    fn maximal_munch_precedes_priority() {
        let lexer = ByteLexer::new(
            vec![
                TokenRule::token(Kind::Short, parse_regex_u8("a").unwrap(), 0),
                TokenRule::token(Kind::Long, parse_regex_u8("ab").unwrap(), 10),
            ],
            LexerPolicy::default(),
        )
        .unwrap();
        let result = lexer.lex(b"ab", BUDGET).unwrap().unwrap();
        assert_eq!(result.tokens[0].kind, Kind::Long);
        assert_eq!(result.tokens[0].span.units, Span::new(0, 2).unwrap());
    }

    #[test]
    fn priority_and_ambiguity_are_explicit() {
        let result = ByteLexer::new(
            vec![
                TokenRule::token(Kind::Keyword, parse_regex_u8("if").unwrap(), 0),
                TokenRule::token(Kind::Name, parse_regex_u8("if").unwrap(), 1),
            ],
            LexerPolicy::default(),
        )
        .unwrap()
        .lex(b"if", BUDGET)
        .unwrap()
        .unwrap();
        assert_eq!(result.tokens[0].kind, Kind::Keyword);

        let ambiguous = ByteLexer::new(
            vec![
                TokenRule::token(Kind::Keyword, parse_regex_u8("if").unwrap(), 0),
                TokenRule::token(Kind::Name, parse_regex_u8("if").unwrap(), 0),
            ],
            LexerPolicy {
                tie: TiePolicy::RejectAmbiguous,
            },
        )
        .unwrap()
        .lex(b"if", BUDGET)
        .unwrap();
        assert!(matches!(ambiguous, Err(LexerDiagnostic::Ambiguous { .. })));
    }

    #[test]
    fn skip_rules_remain_in_trace() {
        let lexer = ByteLexer::new(
            vec![
                TokenRule::skip(Kind::Space, parse_regex_u8(" +").unwrap(), 0),
                TokenRule::token(Kind::Name, parse_regex_u8("[a-z]+").unwrap(), 0),
            ],
            LexerPolicy::default(),
        )
        .unwrap();
        let result = lexer.lex(b"hi there", BUDGET).unwrap().unwrap();
        assert_eq!(result.tokens.len(), 2);
        assert_eq!(result.trace.len(), 3);
        assert!(result.trace[1].skipped);
    }

    #[test]
    fn nullable_rules_are_rejected() {
        assert_eq!(
            ByteLexer::new(
                vec![TokenRule::token(
                    Kind::Short,
                    parse_regex_u8("a*").unwrap(),
                    0
                ),],
                LexerPolicy::default()
            )
            .unwrap_err(),
            LexerBuildError::NullableRule { rule_index: 0 }
        );
    }

    #[test]
    fn relational_lexing_keeps_alternative_segmentations() {
        let lexer = ByteLexer::new(
            vec![
                TokenRule::token(Kind::Short, parse_regex_u8("a").unwrap(), 0),
                TokenRule::token(Kind::Long, parse_regex_u8("aa").unwrap(), 0),
            ],
            LexerPolicy::default(),
        )
        .unwrap();
        let paths = lexer.lex_relational(b"aa", BUDGET).unwrap();
        assert_eq!(paths.len(), 2);
        assert!(paths.iter().any(|path| path.tokens.len() == 1));
        assert!(paths.iter().any(|path| path.tokens.len() == 2));
    }

    #[test]
    fn decoded_text_retains_scalar_and_byte_spans() {
        let bytes = "éx"
            .as_bytes()
            .iter()
            .copied()
            .map(RawByte)
            .collect::<Vec<_>>();
        let decoded = Utf8.decode_text(&bytes).unwrap();
        let lexer = TextLexer::new(
            vec![
                TokenRule::token(Kind::Unicode, parse_regex("é").unwrap(), 0),
                TokenRule::token(Kind::Name, parse_regex("x").unwrap(), 0),
            ],
            LexerPolicy::default(),
        )
        .unwrap();
        let result = lexer.lex_decoded(&decoded, BUDGET).unwrap().unwrap();
        assert_eq!(result.tokens[0].span.units, Span::new(0, 1).unwrap());
        assert_eq!(result.tokens[0].span.bytes, Some(Span::new(0, 2).unwrap()));
        assert_eq!(result.tokens[1].span.bytes, Some(Span::new(2, 3).unwrap()));
    }

    #[test]
    fn evaluator_bounds_are_enforced() {
        let lexer = ByteLexer::new(
            vec![TokenRule::token(
                Kind::Short,
                parse_regex_u8("a").unwrap(),
                0,
            )],
            LexerPolicy::default(),
        )
        .unwrap();
        assert_eq!(
            lexer.lex(b"aa", LexerBudget::new(1, 100, 10, 10, 10, 10)),
            Err(LexerError::InputTooLarge {
                actual: 2,
                limit: 1
            })
        );
        assert_eq!(
            lexer.lex(b"a", LexerBudget::new(10, 100, 10, 0, 10, 10)),
            Err(LexerError::RuleAttemptLimitExceeded { limit: 0 })
        );
        assert_eq!(
            lexer.lex(b"aa", LexerBudget::new(10, 100, 10, 10, 1, 10)),
            Err(LexerError::TokenLimitExceeded { limit: 1 })
        );
        assert_eq!(
            lexer.lex_relational(b"a", LexerBudget::new(10, 100, 10, 10, 10, 0)),
            Err(LexerError::PathLimitExceeded { limit: 0 })
        );
    }
}
