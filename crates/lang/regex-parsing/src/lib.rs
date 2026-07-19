//! Bounded interpretation of the proper regular-expression syntax in
//! `covalence-grammar`.
//!
//! The grammar crate owns syntax; this crate supplies optional host evaluators
//! over raw bytes (A0013) and Unicode scalars (A0015). Search witnesses are
//! ordinary data, not kernel theorems. In particular, a non-match or exhausted
//! budget proves no negative fact about the object-language relation.

#![forbid(unsafe_code)]

use covalence_grammar::{Class, Regex};
use covalence_kernel_data::UnicodeScalar;
use covalence_parsing_api::{
    ByteParseDiagnostic, ByteParseError, ByteParseOutcome, ByteParseWitness, ByteParser,
    ByteParserRelation, ByteSpan, InterpretationPer, ParseAttempt, ParseBudget, ParseFailure,
    PartialExactParser, PartialParser, PartialPrefixParser, PrefixInterpretation, RelationalParser,
    SameInterpretation, Span, exact_from_prefix, same_interpretation_by,
};

/// Positive host evidence for one accepted prefix.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RegexMatchWitness {
    /// End offset in the parser's source units.
    pub accepting_end: usize,
}

/// Ordinary failure to find an accepted prefix.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RegexDiagnosticKind {
    NoMatch,
    TrailingInput,
    StartOutOfBounds,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RegexDiagnostic {
    pub span: Span,
    pub kind: RegexDiagnosticKind,
}

/// Failure of the bounded evaluator itself.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RegexEvalError {
    InputTooLarge { actual: usize, limit: usize },
    FuelExhausted { available: usize },
    ResultLimitExceeded { limit: usize },
}

/// Bounds for scalar-oriented evaluation. Source units are Unicode scalars,
/// not encoded bytes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RegexBudget {
    pub max_source_units: usize,
    pub fuel: usize,
    pub max_results: usize,
}

impl RegexBudget {
    pub const fn new(max_source_units: usize, fuel: usize, max_results: usize) -> Self {
        Self {
            max_source_units,
            fuel,
            max_results,
        }
    }
}

/// A byte-regex evaluator using an explicit A0013 budget.
#[derive(Clone, Debug)]
pub struct ByteRegexParser {
    regex: Regex<u8>,
}

impl ByteRegexParser {
    pub fn new(regex: Regex<u8>) -> Self {
        Self { regex }
    }

    pub fn regex(&self) -> &Regex<u8> {
        &self.regex
    }

    fn accepted_ends(
        &self,
        input: &[u8],
        budget: ParseBudget,
    ) -> Result<Vec<usize>, ByteParseError> {
        check_byte_input(input.len(), budget)?;
        let mut fuel = Fuel::new(budget.fuel);
        let ends = match_ends(&self.regex, input, 0, &mut fuel).map_err(|_| {
            ByteParseError::FuelExhausted {
                required: budget.fuel.saturating_add(1),
                available: budget.fuel,
            }
        })?;
        Ok(ends)
    }
}

impl ByteParser for ByteRegexParser {
    type Value = Vec<u8>;
    type Witness = RegexMatchWitness;

    /// Functional policy: choose the longest accepted prefix.
    fn parse_bytes(
        &self,
        input: &[u8],
        budget: ParseBudget,
    ) -> Result<ByteParseOutcome<Self::Value, Self::Witness>, ByteParseError> {
        let ends = self.accepted_ends(input, budget)?;
        let Some(end) = ends.last().copied() else {
            return Ok(ByteParseOutcome::NoMatch(ByteParseDiagnostic {
                span: ByteSpan { start: 0, end: 0 },
                failure: ParseFailure::NoMatch,
            }));
        };
        Ok(ByteParseOutcome::Match {
            value: input[..end].to_vec(),
            witness: ByteParseWitness::prefix(
                input.len(),
                end,
                RegexMatchWitness { accepting_end: end },
            )
            .expect("accepted endpoint is inside the input"),
        })
    }
}

impl ByteParserRelation for ByteRegexParser {
    type Value = Vec<u8>;
    type Witness = RegexMatchWitness;

    /// Enumerate each distinct accepted prefix. This is a language relation,
    /// not an enumeration of syntactically distinct derivation trees.
    fn parse_relational(
        &self,
        input: &[u8],
        budget: ParseBudget,
    ) -> Result<Vec<(Self::Value, ByteParseWitness<Self::Witness>)>, ByteParseError> {
        let ends = self.accepted_ends(input, budget)?;
        check_result_limit(ends.len(), budget.max_results)
            .map_err(|limit| ByteParseError::ResultLimitExceeded { limit })?;
        Ok(ends
            .into_iter()
            .map(|end| {
                (
                    input[..end].to_vec(),
                    ByteParseWitness::prefix(
                        input.len(),
                        end,
                        RegexMatchWitness { accepting_end: end },
                    )
                    .expect("accepted endpoint is inside the input"),
                )
            })
            .collect())
    }
}

/// A Unicode-scalar regex evaluator. Its configured limits remain visible in
/// the value instead of being hidden global policy.
#[derive(Clone, Debug)]
pub struct TextRegexParser {
    regex: Regex<char>,
    budget: RegexBudget,
}

impl TextRegexParser {
    pub fn new(regex: Regex<char>, budget: RegexBudget) -> Self {
        Self { regex, budget }
    }

    pub fn regex(&self) -> &Regex<char> {
        &self.regex
    }

    pub fn budget(&self) -> RegexBudget {
        self.budget
    }

    fn accepted_ends(
        &self,
        source: &[UnicodeScalar],
        start: usize,
    ) -> Result<Vec<usize>, RegexEvalError> {
        if source.len() > self.budget.max_source_units {
            return Err(RegexEvalError::InputTooLarge {
                actual: source.len(),
                limit: self.budget.max_source_units,
            });
        }
        if start > source.len() {
            return Ok(Vec::new());
        }
        let chars = source
            .iter()
            .map(|scalar| char::from_u32(scalar.value()).expect("UnicodeScalar invariant"))
            .collect::<Vec<_>>();
        let mut fuel = Fuel::new(self.budget.fuel);
        let ends = match_ends(&self.regex, &chars, start, &mut fuel).map_err(|_| {
            RegexEvalError::FuelExhausted {
                available: self.budget.fuel,
            }
        })?;
        Ok(ends)
    }
}

impl PartialPrefixParser for TextRegexParser {
    type Source = [UnicodeScalar];
    type Value = Vec<UnicodeScalar>;
    type Witness = RegexMatchWitness;
    type Diagnostic = RegexDiagnostic;
    type Error = RegexEvalError;

    /// Functional policy: choose the longest accepted prefix.
    fn parse_prefix(
        &self,
        source: &[UnicodeScalar],
        start: usize,
    ) -> Result<
        ParseAttempt<PrefixInterpretation<Self::Value, Self::Witness>, Self::Diagnostic>,
        Self::Error,
    > {
        if start > source.len() {
            return Ok(ParseAttempt::NoMatch(RegexDiagnostic {
                span: Span::new(source.len(), source.len()).unwrap(),
                kind: RegexDiagnosticKind::StartOutOfBounds,
            }));
        }
        let ends = self.accepted_ends(source, start)?;
        let Some(end) = ends.last().copied() else {
            return Ok(ParseAttempt::NoMatch(RegexDiagnostic {
                span: Span::new(start, start).unwrap(),
                kind: RegexDiagnosticKind::NoMatch,
            }));
        };
        let consumed = Span::new(start, end).expect("accepted endpoint follows start");
        Ok(ParseAttempt::Match(
            PrefixInterpretation::new(
                source[start..end].to_vec(),
                RegexMatchWitness { accepting_end: end },
                consumed,
                end,
            )
            .expect("span and remainder agree"),
        ))
    }
}

impl PartialExactParser for TextRegexParser {
    type Source = [UnicodeScalar];
    type Value = Vec<UnicodeScalar>;
    type Witness = RegexMatchWitness;
    type Diagnostic = RegexDiagnostic;
    type Error = RegexEvalError;

    fn parse_exact(
        &self,
        source: &[UnicodeScalar],
    ) -> Result<ParseAttempt<(Self::Value, Self::Witness), Self::Diagnostic>, Self::Error> {
        match exact_from_prefix(self, source, source.len(), |span| RegexDiagnostic {
            span,
            kind: RegexDiagnosticKind::TrailingInput,
        }) {
            Ok(attempt) => Ok(attempt),
            Err(covalence_parsing_api::PrefixAdapterError::Parse(error)) => Err(error),
            Err(covalence_parsing_api::PrefixAdapterError::InvalidExtent { .. }) => {
                unreachable!("TextRegexParser constructs valid extents")
            }
        }
    }
}

impl PartialParser for TextRegexParser {
    type Source = [UnicodeScalar];
    type Value = Vec<UnicodeScalar>;
    type Witness = RegexMatchWitness;
    type Error = RegexEvalError;

    fn parse(
        &self,
        source: &[UnicodeScalar],
    ) -> Result<Option<(Self::Value, Self::Witness)>, Self::Error> {
        Ok(match self.parse_exact(source)? {
            ParseAttempt::Match(value) => Some(value),
            ParseAttempt::NoMatch(_) => None,
        })
    }
}

impl RelationalParser for TextRegexParser {
    type Source = [UnicodeScalar];
    type Value = Vec<UnicodeScalar>;
    type Witness = RegexMatchWitness;
    type Error = RegexEvalError;

    fn parses(
        &self,
        source: &[UnicodeScalar],
    ) -> Result<Vec<(Self::Value, Self::Witness)>, Self::Error> {
        let ends = self.accepted_ends(source, 0)?;
        check_result_limit(ends.len(), self.budget.max_results)
            .map_err(|limit| RegexEvalError::ResultLimitExceeded { limit })?;
        Ok(ends
            .into_iter()
            .map(|end| {
                (
                    source[..end].to_vec(),
                    RegexMatchWitness { accepting_end: end },
                )
            })
            .collect())
    }
}

impl InterpretationPer for TextRegexParser {
    type EquivalenceWitness = ();

    fn same_interpretation(
        &self,
        left: &[UnicodeScalar],
        right: &[UnicodeScalar],
    ) -> Result<
        Option<SameInterpretation<Self::Value, Self::Witness, Self::EquivalenceWitness>>,
        Self::Error,
    > {
        same_interpretation_by(self, left, right, |left, right| {
            (left == right).then_some(())
        })
    }
}

fn check_byte_input(input_len: usize, budget: ParseBudget) -> Result<(), ByteParseError> {
    if input_len > budget.max_input_bytes {
        Err(ByteParseError::InputTooLarge {
            actual: input_len,
            limit: budget.max_input_bytes,
        })
    } else {
        Ok(())
    }
}

fn check_result_limit(actual: usize, limit: usize) -> Result<(), usize> {
    if actual > limit { Err(limit) } else { Ok(()) }
}

#[derive(Clone, Copy, Debug)]
struct OutOfFuel;

struct Fuel {
    remaining: usize,
}

impl Fuel {
    fn new(remaining: usize) -> Self {
        Self { remaining }
    }

    fn spend(&mut self) -> Result<(), OutOfFuel> {
        if self.remaining == 0 {
            Err(OutOfFuel)
        } else {
            self.remaining -= 1;
            Ok(())
        }
    }
}

fn class_contains<A: PartialOrd>(class: &Class<A>, letter: &A) -> bool {
    let inside = class
        .ranges
        .iter()
        .any(|range| range.lo <= *letter && *letter <= range.hi);
    inside != class.negated
}

/// Return sorted, distinct endpoints. This evaluates language membership,
/// deliberately quotienting multiple derivations of the same word.
fn match_ends<A: Clone + PartialOrd>(
    regex: &Regex<A>,
    input: &[A],
    start: usize,
    fuel: &mut Fuel,
) -> Result<Vec<usize>, OutOfFuel> {
    fuel.spend()?;
    let mut ends = match regex {
        Regex::Empty => Vec::new(),
        Regex::Eps => vec![start],
        Regex::Lit(expected) => input
            .get(start)
            .filter(|actual| *actual == expected)
            .map_or_else(Vec::new, |_| vec![start + 1]),
        Regex::Class(class) => input
            .get(start)
            .filter(|actual| class_contains(class, actual))
            .map_or_else(Vec::new, |_| vec![start + 1]),
        Regex::Concat(items) => sequence_ends(items, input, vec![start], fuel)?,
        Regex::Alt(items) => {
            let mut all = Vec::new();
            for item in items {
                all.extend(match_ends(item, input, start, fuel)?);
            }
            all
        }
        Regex::Star(inner) => repeat_ends(inner, input, start, 0, None, fuel)?,
        Regex::Plus(inner) => repeat_ends(inner, input, start, 1, None, fuel)?,
        Regex::Opt(inner) => {
            let mut all = vec![start];
            all.extend(match_ends(inner, input, start, fuel)?);
            all
        }
        Regex::Rep { inner, min, max } => repeat_ends(
            inner,
            input,
            start,
            *min as usize,
            max.map(|n| n as usize),
            fuel,
        )?,
    };
    ends.sort_unstable();
    ends.dedup();
    Ok(ends)
}

fn sequence_ends<A: Clone + PartialOrd>(
    items: &[Regex<A>],
    input: &[A],
    mut positions: Vec<usize>,
    fuel: &mut Fuel,
) -> Result<Vec<usize>, OutOfFuel> {
    for item in items {
        let mut next = Vec::new();
        for position in positions {
            next.extend(match_ends(item, input, position, fuel)?);
        }
        next.sort_unstable();
        next.dedup();
        positions = next;
        if positions.is_empty() {
            break;
        }
    }
    Ok(positions)
}

fn repeat_ends<A: Clone + PartialOrd>(
    inner: &Regex<A>,
    input: &[A],
    start: usize,
    min: usize,
    max: Option<usize>,
    fuel: &mut Fuel,
) -> Result<Vec<usize>, OutOfFuel> {
    // A nullable repetition can satisfy any finite minimum without consuming
    // input; quotient those epsilon derivations before exploring progress.
    let effective_min = if inner.nullable() { 0 } else { min };
    let hard_max = max.unwrap_or_else(|| {
        input
            .len()
            .saturating_sub(start)
            .saturating_add(effective_min)
    });
    let mut frontier = vec![start];
    let mut accepted = (effective_min == 0)
        .then_some(vec![start])
        .unwrap_or_default();
    for count in 1..=hard_max {
        let mut next = Vec::new();
        for position in frontier {
            // Ignore non-progressing repetition edges. They affect derivation
            // multiplicity, not the accepted language, and otherwise create
            // infinitely many epsilon derivations under star.
            next.extend(
                match_ends(inner, input, position, fuel)?
                    .into_iter()
                    .filter(|end| *end > position),
            );
        }
        next.sort_unstable();
        next.dedup();
        if next.is_empty() {
            break;
        }
        if count >= effective_min {
            accepted.extend(next.iter().copied());
        }
        frontier = next;
    }
    accepted.sort_unstable();
    accepted.dedup();
    Ok(accepted)
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_grammar::{ClassRange, parse_regex, parse_regex_u8};

    const BUDGET: ParseBudget = ParseBudget::new(128, 2_000, 128);
    const TEXT_BUDGET: RegexBudget = RegexBudget::new(128, 2_000, 128);

    fn scalars(text: &str) -> Vec<UnicodeScalar> {
        text.chars()
            .map(|c| UnicodeScalar::new(c as u32).unwrap())
            .collect()
    }

    #[test]
    fn byte_functional_parser_chooses_longest_prefix() {
        let parser = ByteRegexParser::new(parse_regex_u8("a|ab").unwrap());
        let ByteParseOutcome::Match { value, witness } =
            parser.parse_bytes(b"ab!", BUDGET).unwrap()
        else {
            panic!("expected match")
        };
        assert_eq!(value, b"ab");
        assert_eq!(witness.remainder, ByteSpan { start: 2, end: 3 });
    }

    #[test]
    fn byte_relation_exposes_distinct_accepted_prefixes() {
        let parser = ByteRegexParser::new(parse_regex_u8("a|ab").unwrap());
        let values = parser.parse_relational(b"ab!", BUDGET).unwrap();
        assert_eq!(
            values
                .iter()
                .map(|(value, _)| value.as_slice())
                .collect::<Vec<_>>(),
            vec![b"a".as_slice(), b"ab".as_slice()]
        );
    }

    #[test]
    fn duplicate_derivations_are_quotiented_as_language_membership() {
        let parser = ByteRegexParser::new(parse_regex_u8("a|a").unwrap());
        assert_eq!(parser.parse_relational(b"a", BUDGET).unwrap().len(), 1);
    }

    #[test]
    fn nonmatch_and_bounds_are_explicit() {
        let parser = ByteRegexParser::new(parse_regex_u8("ab").unwrap());
        assert!(matches!(
            parser.parse_bytes(b"ax", BUDGET).unwrap(),
            ByteParseOutcome::NoMatch(_)
        ));
        assert_eq!(
            parser.parse_bytes(b"ab", ParseBudget::new(1, 100, 10)),
            Err(ByteParseError::InputTooLarge {
                actual: 2,
                limit: 1
            })
        );
        assert!(matches!(
            parser.parse_bytes(b"ab", ParseBudget::new(10, 1, 10)),
            Err(ByteParseError::FuelExhausted { .. })
        ));
    }

    #[test]
    fn result_limit_is_not_silent() {
        let parser = ByteRegexParser::new(parse_regex_u8("a*").unwrap());
        assert!(matches!(
            parser.parse_bytes(b"aaa", ParseBudget::new(3, 100, 0)),
            Ok(ByteParseOutcome::Match { value, .. }) if value == b"aaa"
        ));
        assert_eq!(
            parser.parse_relational(b"aaa", ParseBudget::new(3, 100, 2)),
            Err(ByteParseError::ResultLimitExceeded { limit: 2 })
        );
    }

    #[test]
    fn nullable_repetition_minimum_preserves_empty_language_member() {
        let parser = ByteRegexParser::new(Regex::eps().rep(3, Some(3)));
        assert!(matches!(
            parser.parse_bytes(b"x", BUDGET),
            Ok(ByteParseOutcome::Match { value, .. }) if value.is_empty()
        ));
    }

    #[test]
    fn text_parser_uses_unicode_scalar_offsets() {
        let parser = TextRegexParser::new(parse_regex("β+").unwrap(), TEXT_BUDGET);
        let source = scalars("ββ!");
        let ParseAttempt::Match(result) = parser.parse_prefix(&source, 0).unwrap() else {
            panic!("expected match")
        };
        assert_eq!(result.consumed, Span::new(0, 2).unwrap());
        assert_eq!(result.value, scalars("ββ"));
    }

    #[test]
    fn exact_and_per_are_separate_from_prefix_policy() {
        let parser = TextRegexParser::new(parse_regex("[α-ω]+").unwrap(), TEXT_BUDGET);
        assert!(matches!(
            parser.parse_exact(&scalars("αβ!")).unwrap(),
            ParseAttempt::NoMatch(RegexDiagnostic {
                kind: RegexDiagnosticKind::TrailingInput,
                ..
            })
        ));
        assert!(
            parser
                .same_interpretation(&scalars("αβ"), &scalars("αβ"))
                .unwrap()
                .is_some()
        );
        assert!(
            parser
                .same_interpretation(&scalars("αβ"), &scalars("β"))
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn negated_unicode_class_matches_a_scalar() {
        let regex = Regex::class(Class::negated(vec![ClassRange::single('x')]));
        let parser = TextRegexParser::new(regex, TEXT_BUDGET);
        assert!(parser.parse(&scalars("𝄞")).unwrap().is_some());
    }
}
