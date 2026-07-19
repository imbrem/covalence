//! A0015 interpretation of the dependency-light Covalence S-expression parser.
//!
//! This adapter deliberately lives above both `covalence-sexp` and
//! `covalence-sexpr-api`: neither foundational crate depends on the general
//! parsing vocabulary. Parser results lower to the abstract proper-list
//! representation [`FreeSExpr`].
//!
//! Host parse witnesses are data, not kernel theorems.

#![forbid(unsafe_code)]

use core::{convert::Infallible, marker::PhantomData};

use covalence_kernel_data::{MalformedUtf8, RawByte, UnicodeScalar};
use covalence_parsing_api::{
    EncodedTextError, InterpretationPer, ParseAttempt, PartialExactParser, PartialParser,
    PartialPrefixParser, PrefixAdapterError, PrefixInterpretation, SameInterpretation, Span,
    TextEncodingBoundary, Utf8, exact_from_prefix, parse_encoded_text_prefix,
    same_interpretation_by,
};
use covalence_sexp::{
    Atom, CovalenceDialect, DefaultBuilder, Dialect, EgglogDialect, ParseError, SExp,
    SmtLibDialect, TreeBuilder, WatDialect, parse_prefix_with,
};
use covalence_sexpr_api::FreeSExpr;

/// The abstract value produced by the concrete surface parser.
pub type ParsedSExpr = FreeSExpr<Atom>;

/// Positive evidence retained by the host adapter.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SExprParseWitness {
    /// Span in Unicode scalar positions.
    pub scalar_span: Span,
}

/// Stable identity of a concrete S-expression surface language.
///
/// This is intentionally part of dialect-adapter witnesses: a tree alone does
/// not establish which reader accepted its source text.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SExprDialect {
    Covalence,
    SmtLib,
    Wat,
    Egglog,
}

/// Positive evidence retained by a dialect-specific host adapter.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DialectSExprParseWitness {
    pub dialect: SExprDialect,
    /// Span in Unicode scalar positions.
    pub scalar_span: Span,
}

/// A byte-oriented dialect prefix result with byte and scalar provenance.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Utf8DialectPrefixInterpretation {
    pub interpretation: PrefixInterpretation<ParsedSExpr, DialectSExprParseWitness>,
    pub byte_span: Span,
    pub byte_remainder: usize,
}

mod sealed {
    pub trait Sealed {}
}

/// A low-level dialect that can be named in an A0015 witness.
///
/// This trait is sealed so an external dialect cannot claim the identity of
/// one of the four built-in readers.
pub trait NamedSExprDialect: Dialect + sealed::Sealed {
    const ID: SExprDialect;

    fn new() -> Self;
}

macro_rules! named_dialect {
    ($type:ty, $id:ident) => {
        impl sealed::Sealed for $type {}

        impl NamedSExprDialect for $type {
            const ID: SExprDialect = SExprDialect::$id;

            fn new() -> Self {
                Self
            }
        }
    };
}

named_dialect!(CovalenceDialect, Covalence);
named_dialect!(SmtLibDialect, SmtLib);
named_dialect!(WatDialect, Wat);
named_dialect!(EgglogDialect, Egglog);

/// A0015 adapter for one named low-level S-expression dialect.
///
/// The marker type fixes the accepted surface syntax while
/// [`DialectSExprParseWitness::dialect`] keeps that choice visible after
/// type erasure or serialization.
#[derive(Clone, Copy, Debug)]
pub struct DialectSExprParser<D>(PhantomData<fn() -> D>);

impl<D> Default for DialectSExprParser<D> {
    fn default() -> Self {
        Self(PhantomData)
    }
}

pub type CovalenceSExprParser = DialectSExprParser<CovalenceDialect>;
pub type SmtLibSExprParser = DialectSExprParser<SmtLibDialect>;
pub type WatSExprParser = DialectSExprParser<WatDialect>;
pub type EgglogSExprParser = DialectSExprParser<EgglogDialect>;

impl<D: NamedSExprDialect> DialectSExprParser<D> {
    pub const fn dialect(&self) -> SExprDialect {
        D::ID
    }

    /// Reject evidence produced under a different surface language.
    pub fn accepts_witness(&self, witness: &DialectSExprParseWitness) -> bool {
        witness.dialect == D::ID
    }

    /// Parse a prefix after validating and decoding UTF-8.
    pub fn parse_utf8_prefix(
        &self,
        source: &[RawByte],
    ) -> Result<ParseAttempt<Utf8DialectPrefixInterpretation, SExprDiagnostic>, SExprEncodingError>
    {
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
                ParseAttempt::Match(Utf8DialectPrefixInterpretation {
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
    ) -> Result<
        ParseAttempt<(ParsedSExpr, DialectSExprParseWitness), SExprDiagnostic>,
        SExprEncodingError,
    > {
        let decoded = Utf8
            .decode_text(source)
            .map_err(SExprEncodingError::MalformedUtf8)?;
        Ok(self
            .parse_exact(&decoded.scalars)
            .expect("scalar parsing is infallible"))
    }
}

impl<D: NamedSExprDialect> PartialPrefixParser for DialectSExprParser<D> {
    type Source = [UnicodeScalar];
    type Value = ParsedSExpr;
    type Witness = DialectSExprParseWitness;
    type Diagnostic = SExprDiagnostic;
    type Error = Infallible;

    fn parse_prefix(
        &self,
        source: &[UnicodeScalar],
        start: usize,
    ) -> Result<
        ParseAttempt<PrefixInterpretation<Self::Value, Self::Witness>, Self::Diagnostic>,
        Self::Error,
    > {
        parse_dialect_prefix::<D>(source, start)
    }
}

impl<D: NamedSExprDialect> PartialExactParser for DialectSExprParser<D> {
    type Source = [UnicodeScalar];
    type Value = ParsedSExpr;
    type Witness = DialectSExprParseWitness;
    type Diagnostic = SExprDiagnostic;
    type Error = Infallible;

    fn parse_exact(
        &self,
        source: &[UnicodeScalar],
    ) -> Result<ParseAttempt<(Self::Value, Self::Witness), Self::Diagnostic>, Self::Error> {
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

impl<D: NamedSExprDialect> PartialParser for DialectSExprParser<D> {
    type Source = [UnicodeScalar];
    type Value = ParsedSExpr;
    type Witness = DialectSExprParseWitness;
    type Error = Infallible;

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

impl<D: NamedSExprDialect> InterpretationPer for DialectSExprParser<D> {
    type EquivalenceWitness = SExprDialect;

    fn same_interpretation(
        &self,
        left: &[UnicodeScalar],
        right: &[UnicodeScalar],
    ) -> Result<
        Option<SameInterpretation<Self::Value, Self::Witness, Self::EquivalenceWitness>>,
        Self::Error,
    > {
        same_interpretation_by(self, left, right, |left_value, right_value| {
            (left_value == right_value).then_some(D::ID)
        })
    }
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

fn parse_dialect_prefix<D: NamedSExprDialect>(
    source: &[UnicodeScalar],
    start: usize,
) -> Result<
    ParseAttempt<PrefixInterpretation<ParsedSExpr, DialectSExprParseWitness>, SExprDiagnostic>,
    Infallible,
> {
    if start > source.len() {
        return Ok(ParseAttempt::NoMatch(SExprDiagnostic {
            span: Span::new(source.len(), source.len()).unwrap(),
            message: "start offset is outside the source".into(),
        }));
    }
    let text = scalars_to_string(&source[start..]);
    let mut visitor = TreeBuilder::new(DefaultBuilder, D::new());
    Ok(match parse_prefix_with(&text, &mut visitor) {
        Ok(consumed_bytes) => {
            let mut values = visitor.into_results();
            debug_assert_eq!(values.len(), 1);
            let consumed_scalars = byte_to_scalar_offset(&text, consumed_bytes);
            let span = Span::new(start, start + consumed_scalars).unwrap();
            ParseAttempt::Match(
                PrefixInterpretation::new(
                    lower(values.remove(0)),
                    DialectSExprParseWitness {
                        dialect: D::ID,
                        scalar_span: span,
                    },
                    span,
                    span.end,
                )
                .expect("span and remainder agree"),
            )
        }
        Err(error) => ParseAttempt::NoMatch(diagnostic(&text, start, error)),
    })
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

    #[test]
    fn dialect_witnesses_are_named_and_not_interchangeable() {
        let source = scalars("(a)");
        let ParseAttempt::Match((_, smt_witness)) =
            SmtLibSExprParser::default().parse_exact(&source).unwrap()
        else {
            panic!("expected SMT-LIB match");
        };
        assert_eq!(smt_witness.dialect, SExprDialect::SmtLib);
        assert!(SmtLibSExprParser::default().accepts_witness(&smt_witness));
        assert!(!WatSExprParser::default().accepts_witness(&smt_witness));
        assert!(!EgglogSExprParser::default().accepts_witness(&smt_witness));
    }

    #[test]
    fn smt_quoted_symbol_is_rejected_by_wat_but_pipes_are_egglog_atoms() {
        let quoted = scalars("|two words|");
        let ParseAttempt::Match((smt_value, smt_witness)) =
            SmtLibSExprParser::default().parse_exact(&quoted).unwrap()
        else {
            panic!("SMT-LIB quoted symbol should parse");
        };
        assert_eq!(smt_witness.scalar_span, Span::new(0, 11).unwrap());

        assert!(matches!(
            WatSExprParser::default().parse_exact(&quoted).unwrap(),
            ParseAttempt::NoMatch(_)
        ));
        assert!(matches!(
            EgglogSExprParser::default().parse_exact(&quoted).unwrap(),
            ParseAttempt::NoMatch(_)
        ));

        let bare_pipes = scalars("|two-words|");
        let ParseAttempt::Match((egglog_value, egglog_witness)) = EgglogSExprParser::default()
            .parse_exact(&bare_pipes)
            .unwrap()
        else {
            panic!("egglog pipes are ordinary atom characters");
        };
        assert_eq!(egglog_witness.dialect, SExprDialect::Egglog);
        assert_ne!(smt_value, egglog_value);
    }

    #[test]
    fn wat_nested_block_comments_are_not_smt_or_egglog_trivia() {
        let source = scalars("(; outer (; inner ;) ;) (module)");
        let ParseAttempt::Match((_, witness)) =
            WatSExprParser::default().parse_exact(&source).unwrap()
        else {
            panic!("WAT nested block comment should parse");
        };
        assert_eq!(witness.scalar_span, Span::new(0, 32).unwrap());

        assert!(matches!(
            SmtLibSExprParser::default().parse_exact(&source).unwrap(),
            ParseAttempt::NoMatch(_)
        ));
        assert!(matches!(
            EgglogSExprParser::default().parse_exact(&source).unwrap(),
            ParseAttempt::NoMatch(_)
        ));
    }

    #[test]
    fn dialect_utf8_offsets_report_bytes_and_scalars() {
        let source = bytes("; λ\n(β) tail");
        let ParseAttempt::Match(parsed) = SmtLibSExprParser::default()
            .parse_utf8_prefix(&source)
            .unwrap()
        else {
            panic!("expected SMT-LIB prefix");
        };
        assert_eq!(parsed.interpretation.consumed, Span::new(0, 7).unwrap());
        assert_eq!(
            parsed.interpretation.witness.scalar_span,
            Span::new(0, 7).unwrap()
        );
        assert_eq!(parsed.interpretation.witness.dialect, SExprDialect::SmtLib);
        assert_eq!(parsed.byte_span, Span::new(0, 9).unwrap());
        assert_eq!(parsed.byte_remainder, 9);
    }

    #[test]
    fn dialect_diagnostic_offsets_are_unicode_scalar_offsets() {
        let source = scalars("λ )");
        let ParseAttempt::NoMatch(diagnostic) =
            WatSExprParser::default().parse_exact(&source).unwrap()
        else {
            panic!("trailing close parenthesis should be rejected");
        };
        assert_eq!(diagnostic.span, Span::new(1, 3).unwrap());
    }
}
