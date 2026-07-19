//! A0015 interpretation of the dependency-light Covalence S-expression parser.
//!
//! This adapter deliberately lives above both `covalence-sexp` and
//! `covalence-sexpr-api`: neither foundational crate depends on the general
//! parsing vocabulary. Parser results lower to the abstract proper-list
//! representation [`FreeSExpr`].
//!
//! Host parse witnesses are data, not kernel theorems.

#![forbid(unsafe_code)]

use core::convert::Infallible;

use covalence_logic_api::{MalformedUtf8, RawByte, UnicodeScalar};
use covalence_parsing_api::{
    EncodedTextError, InterpretationPer, ParseAttempt, PartialExactParser, PartialParser,
    PartialPrefixParser, PrefixAdapterError, PrefixInterpretation, SameInterpretation, Span,
    TextEncodingBoundary, Utf8, exact_from_prefix, parse_encoded_text_prefix,
    same_interpretation_by,
};
use covalence_sexp::{Atom, ParseError, SExp};
use covalence_sexpr_api::FreeSExpr;

/// The abstract value produced by the concrete surface parser.
pub type ParsedSExpr = FreeSExpr<Atom>;

/// Positive evidence retained by the host adapter.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SExprParseWitness {
    /// Span in Unicode scalar positions.
    pub scalar_span: Span,
}

/// A syntax diagnostic in Unicode scalar positions.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SExprDiagnostic {
    pub span: Span,
    pub message: String,
}

/// Failure at the explicit encoded-bytes/text boundary.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SExprEncodingError {
    MalformedUtf8(MalformedUtf8),
    InvalidScalarExtent {
        consumed: Span,
        remainder: usize,
        scalar_len: usize,
    },
}

/// A byte-oriented prefix result with both byte and scalar provenance.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Utf8PrefixInterpretation {
    pub interpretation: PrefixInterpretation<ParsedSExpr, SExprParseWitness>,
    pub byte_span: Span,
    pub byte_remainder: usize,
}

/// Covalence-dialect S-expression interpretation.
#[derive(Clone, Copy, Debug, Default)]
pub struct SExprParser;

impl SExprParser {
    /// Parse a prefix after validating and decoding UTF-8.
    pub fn parse_utf8_prefix(
        &self,
        source: &[RawByte],
    ) -> Result<ParseAttempt<Utf8PrefixInterpretation, SExprDiagnostic>, SExprEncodingError> {
        let (_, parsed) =
            parse_encoded_text_prefix(&Utf8, self, source, 0).map_err(|error| match error {
                EncodedTextError::Decode(error) => SExprEncodingError::MalformedUtf8(error),
                EncodedTextError::Parse(error) => match error {},
                EncodedTextError::InvalidScalarExtent {
                    consumed,
                    remainder,
                    scalar_len,
                } => SExprEncodingError::InvalidScalarExtent {
                    consumed,
                    remainder,
                    scalar_len,
                },
            })?;
        Ok(match parsed {
            ParseAttempt::NoMatch(diagnostic) => ParseAttempt::NoMatch(diagnostic),
            ParseAttempt::Match(encoded) => {
                let scalar_span = encoded.witness.scalar_span;
                ParseAttempt::Match(Utf8PrefixInterpretation {
                    byte_span: encoded.consumed,
                    byte_remainder: encoded.remainder,
                    interpretation: PrefixInterpretation::new(
                        encoded.value,
                        encoded.witness,
                        scalar_span,
                        scalar_span.end,
                    )
                    .expect("witness span and scalar remainder agree"),
                })
            }
        })
    }

    /// Parse exactly one value after validating and decoding UTF-8.
    pub fn parse_utf8_exact(
        &self,
        source: &[RawByte],
    ) -> Result<ParseAttempt<(ParsedSExpr, SExprParseWitness), SExprDiagnostic>, SExprEncodingError>
    {
        let decoded = Utf8
            .decode_text(source)
            .map_err(SExprEncodingError::MalformedUtf8)?;
        Ok(self
            .parse_exact(&decoded.scalars)
            .expect("scalar parsing is infallible"))
    }
}

impl PartialPrefixParser for SExprParser {
    type Source = [UnicodeScalar];
    type Value = ParsedSExpr;
    type Witness = SExprParseWitness;
    type Diagnostic = SExprDiagnostic;
    type Error = Infallible;

    fn parse_prefix(
        &self,
        source: &[UnicodeScalar],
        start: usize,
    ) -> Result<
        ParseAttempt<PrefixInterpretation<ParsedSExpr, SExprParseWitness>, SExprDiagnostic>,
        Infallible,
    > {
        if start > source.len() {
            return Ok(ParseAttempt::NoMatch(SExprDiagnostic {
                span: Span::new(source.len(), source.len()).unwrap(),
                message: "start offset is outside the source".into(),
            }));
        }
        let text = scalars_to_string(&source[start..]);
        Ok(match covalence_sexp::parse_prefix(&text) {
            Ok((value, consumed_bytes)) => {
                let consumed_scalars = byte_to_scalar_offset(&text, consumed_bytes);
                let span = Span::new(start, start + consumed_scalars).unwrap();
                ParseAttempt::Match(
                    PrefixInterpretation::new(
                        lower(value),
                        SExprParseWitness { scalar_span: span },
                        span,
                        span.end,
                    )
                    .expect("span and remainder agree"),
                )
            }
            Err(error) => ParseAttempt::NoMatch(diagnostic(&text, start, error)),
        })
    }
}

impl PartialExactParser for SExprParser {
    type Source = [UnicodeScalar];
    type Value = ParsedSExpr;
    type Witness = SExprParseWitness;
    type Diagnostic = SExprDiagnostic;
    type Error = Infallible;

    fn parse_exact(
        &self,
        source: &[UnicodeScalar],
    ) -> Result<ParseAttempt<(ParsedSExpr, SExprParseWitness), SExprDiagnostic>, Infallible> {
        match exact_from_prefix(self, source, source.len(), |trailing| SExprDiagnostic {
            span: trailing,
            message: "trailing input after S-expression".into(),
        }) {
            Ok(attempt) => Ok(attempt),
            Err(PrefixAdapterError::Parse(error)) => match error {},
            Err(PrefixAdapterError::InvalidExtent { .. }) => {
                unreachable!("S-expression prefix parser constructs validated extents")
            }
        }
    }
}

impl PartialParser for SExprParser {
    type Source = [UnicodeScalar];
    type Value = ParsedSExpr;
    type Witness = SExprParseWitness;
    type Error = Infallible;

    fn parse(
        &self,
        source: &[UnicodeScalar],
    ) -> Result<Option<(ParsedSExpr, SExprParseWitness)>, Infallible> {
        Ok(match self.parse_exact(source)? {
            ParseAttempt::Match(value) => Some(value),
            ParseAttempt::NoMatch(_) => None,
        })
    }
}

impl InterpretationPer for SExprParser {
    type EquivalenceWitness = ();

    fn same_interpretation(
        &self,
        left: &[UnicodeScalar],
        right: &[UnicodeScalar],
    ) -> Result<Option<SameInterpretation<ParsedSExpr, SExprParseWitness, ()>>, Infallible> {
        same_interpretation_by(self, left, right, |left_value, right_value| {
            (left_value == right_value).then_some(())
        })
    }
}

fn lower(value: SExp<Atom>) -> ParsedSExpr {
    match value {
        SExp::Atom(atom) => FreeSExpr::Atom(atom),
        SExp::List(values) => values.into_iter().rev().fold(FreeSExpr::Nil, |tail, head| {
            FreeSExpr::Cons(Box::new(lower(head)), Box::new(tail))
        }),
    }
}

fn scalars_to_string(source: &[UnicodeScalar]) -> String {
    source
        .iter()
        .map(|scalar| char::from_u32(scalar.value()).expect("UnicodeScalar invariant"))
        .collect()
}

fn byte_to_scalar_offset(text: &str, byte: usize) -> usize {
    text[..byte].chars().count()
}

fn diagnostic(text: &str, base: usize, error: ParseError) -> SExprDiagnostic {
    let offset = base + byte_to_scalar_offset(text, error.offset.min(text.len()));
    SExprDiagnostic {
        span: Span::new(offset, offset).unwrap(),
        message: error.message,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn scalars(text: &str) -> Vec<UnicodeScalar> {
        text.chars()
            .map(|c| UnicodeScalar::new(c as u32).unwrap())
            .collect()
    }

    fn bytes(text: &str) -> Vec<RawByte> {
        text.as_bytes().iter().copied().map(RawByte).collect()
    }

    #[test]
    fn nested_prefix_retains_remainder_and_source_offset() {
        let source = scalars("xx (a (β c)) tail");
        let ParseAttempt::Match(parsed) = SExprParser.parse_prefix(&source, 3).unwrap() else {
            panic!("expected match");
        };
        assert_eq!(parsed.consumed, Span::new(3, 12).unwrap());
        assert_eq!(parsed.remainder, 12);
        assert_eq!(parsed.witness.scalar_span, parsed.consumed);
    }

    #[test]
    fn exact_rejects_a_valid_prefix_with_trailing_value() {
        assert_eq!(
            SExprParser.parse_exact(&scalars("(a) (b)")).unwrap(),
            ParseAttempt::NoMatch(SExprDiagnostic {
                span: Span::new(3, 7).unwrap(),
                message: "trailing input after S-expression".into(),
            })
        );
        assert!(matches!(
            SExprParser.parse_exact(&scalars("(a (b c))")).unwrap(),
            ParseAttempt::Match(_)
        ));
    }

    #[test]
    fn malformed_utf8_is_rejected_at_the_explicit_boundary() {
        assert_eq!(
            SExprParser.parse_utf8_prefix(&[RawByte(0xf0), RawByte(0x9d)]),
            Err(SExprEncodingError::MalformedUtf8(MalformedUtf8 {
                valid_up_to: 0,
                error_len: None,
            }))
        );
    }

    #[test]
    fn utf8_prefix_reports_byte_and_scalar_extents() {
        let ParseAttempt::Match(parsed) =
            SExprParser.parse_utf8_prefix(&bytes("(β) rest")).unwrap()
        else {
            panic!("expected match");
        };
        assert_eq!(parsed.interpretation.consumed, Span::new(0, 3).unwrap());
        assert_eq!(parsed.byte_span, Span::new(0, 4).unwrap());
        assert_eq!(parsed.byte_remainder, 4);
    }

    #[test]
    fn same_value_per_ignores_surface_whitespace() {
        let same = SExprParser
            .same_interpretation(&scalars("(a b)"), &scalars("( a  b )"))
            .unwrap();
        assert!(same.is_some());
        assert!(
            SExprParser
                .same_interpretation(&scalars("(a b)"), &scalars("(a c)"))
                .unwrap()
                .is_none()
        );
    }
}
