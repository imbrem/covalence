//! Backend-neutral parsing and interpretation vocabulary.
//!
//! Parsing is an interpretation relation between source objects and values.
//! This crate distinguishes three computational capabilities:
//!
//! - [`PartialParser`]: a partial function (zero or one result);
//! - [`TotalParser`]: a total function;
//! - [`RelationalParser`]: a relation (zero, one, or many results).
//!
//! Returned witnesses are data. A logic backend may later check or reflect
//! them into theorems; implementing these traits alone grants no proof
//! authority. In particular, `None` or an empty result proves no negative fact.
//!
//! @covalence-api {"id":"A0015","title":"Text parsing and interpretation","status":"experimental","dependsOn":["A0014"]}

#![forbid(unsafe_code)]

pub mod adapters;
pub mod bytes;

pub use adapters::{
    EncodedTextError, PrefixAdapterError, exact_from_prefix, parse_encoded_text_prefix,
    same_interpretation_by,
};
pub use bytes::{
    ByteParseDiagnostic, ByteParseError, ByteParseJudgment, ByteParseLaws, ByteParseOutcome,
    ByteParseWitness, ByteParser, ByteParserRelation, ByteParserTheory, ByteRegexLanguageBackend,
    ByteRegexLanguageLaws, ByteRegexLanguageTheory, ByteRegexMembershipCertificate,
    ByteRegexMembershipReplay, ByteSpan, LiteralBytes, ParseBudget, ParseFailure,
    TheoremByteRegexMembershipReplay,
};

use covalence_logic_api::{Logic, MalformedUtf8, RawByte, UnicodeScalar, decode_utf8};

/// A half-open source interval, measured in units of the parser's source
/// carrier. Byte and Unicode-scalar offsets must not be silently mixed.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl Span {
    pub const fn new(start: usize, end: usize) -> Option<Self> {
        if start <= end {
            Some(Self { start, end })
        } else {
            None
        }
    }

    pub const fn len(self) -> usize {
        self.end - self.start
    }

    pub const fn is_empty(self) -> bool {
        self.start == self.end
    }
}

/// A successful prefix interpretation with explicit consumed extent and
/// unconsumed suffix position.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrefixInterpretation<V, W> {
    pub value: V,
    pub witness: W,
    pub consumed: Span,
    pub remainder: usize,
}

impl<V, W> PrefixInterpretation<V, W> {
    pub fn new(value: V, witness: W, consumed: Span, remainder: usize) -> Option<Self> {
        (consumed.end == remainder).then_some(Self {
            value,
            witness,
            consumed,
            remainder,
        })
    }

    pub fn is_complete(&self, source_len: usize) -> bool {
        self.consumed.start == 0 && self.remainder == source_len
    }
}

/// A parser description independent of any evaluation strategy.
pub trait ParserSyntax {
    type Syntax;

    fn syntax(&self) -> &Self::Syntax;
}

/// Positive parse or ordinary non-match. `Error` on the evaluator traits is
/// reserved for evaluator failure, rather than malformed user input.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ParseAttempt<M, D> {
    Match(M),
    NoMatch(D),
}

pub type PrefixParseResult<V, W, D, E> = Result<ParseAttempt<PrefixInterpretation<V, W>, D>, E>;
pub type ExactParseResult<V, W, D, E> = Result<ParseAttempt<(V, W), D>, E>;
pub type PartialParseResult<V, W, E> = Result<Option<(V, W)>, E>;
pub type RelationalParseResult<V, W, E> = Result<Vec<(V, W)>, E>;
pub type SameInterpretationResult<V, W, Q, E> = Result<Option<SameInterpretation<V, W, Q>>, E>;

/// Prefix parsing as a partial function with diagnostics and a remainder.
pub trait PartialPrefixParser {
    type Source: ?Sized;
    type Value;
    type Witness;
    type Diagnostic;
    type Error;

    fn parse_prefix(
        &self,
        source: &Self::Source,
        start: usize,
    ) -> PrefixParseResult<Self::Value, Self::Witness, Self::Diagnostic, Self::Error>;
}

/// Exact/whole-source partial parsing.
///
/// This stays separate from prefix parsing: requiring complete consumption is
/// a semantic choice, not an implicit convention about remainders.
pub trait PartialExactParser {
    type Source: ?Sized;
    type Value;
    type Witness;
    type Diagnostic;
    type Error;

    fn parse_exact(
        &self,
        source: &Self::Source,
    ) -> ExactParseResult<Self::Value, Self::Witness, Self::Diagnostic, Self::Error>;
}

/// Text parsing over abstract Unicode scalar sequences from A0014.
pub trait TextPrefixParser: PartialPrefixParser<Source = [UnicodeScalar]> {}

impl<T> TextPrefixParser for T where T: PartialPrefixParser<Source = [UnicodeScalar]> {}

/// Provenance for decoding bytes into an abstract Unicode-scalar source.
///
/// `scalar_byte_offsets[i]` is the byte offset of scalar `i`; the final entry
/// is the encoded length. It permits scalar spans to be mapped back to byte
/// spans without pretending the two offset spaces coincide.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DecodedText {
    pub scalars: Vec<UnicodeScalar>,
    pub scalar_byte_offsets: Vec<usize>,
}

impl DecodedText {
    pub fn byte_span(&self, scalar_span: Span) -> Option<Span> {
        Some(Span {
            start: *self.scalar_byte_offsets.get(scalar_span.start)?,
            end: *self.scalar_byte_offsets.get(scalar_span.end)?,
        })
    }
}

/// Explicit boundary from encoded bytes to abstract text.
pub trait TextEncodingBoundary {
    type Encoded: ?Sized;
    type Error;

    fn decode_text(&self, encoded: &Self::Encoded) -> Result<DecodedText, Self::Error>;
}

/// Canonical UTF-8 boundary backed by A0014 validation.
#[derive(Clone, Copy, Debug, Default)]
pub struct Utf8;

impl TextEncodingBoundary for Utf8 {
    type Encoded = [RawByte];
    type Error = MalformedUtf8;

    fn decode_text(&self, encoded: &[RawByte]) -> Result<DecodedText, MalformedUtf8> {
        let scalars = decode_utf8(encoded)?;
        let mut scalar_byte_offsets = Vec::with_capacity(scalars.len() + 1);
        let mut offset = 0;
        for scalar in &scalars {
            scalar_byte_offsets.push(offset);
            offset += char::from_u32(scalar.value())
                .expect("UnicodeScalar invariant")
                .len_utf8();
        }
        scalar_byte_offsets.push(offset);
        Ok(DecodedText {
            scalars,
            scalar_byte_offsets,
        })
    }
}

/// A positive interpretation judgment: `source` denotes `value`, witnessed by
/// backend-specific evidence.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Interpretation<S, V, W> {
    pub source: S,
    pub value: V,
    pub witness: W,
}

impl<S, V, W> Interpretation<S, V, W> {
    pub fn new(source: S, value: V, witness: W) -> Self {
        Self {
            source,
            value,
            witness,
        }
    }
}

/// Parsing as a partial function.
pub trait PartialParser {
    type Source: ?Sized;
    type Value;
    type Witness;
    type Error;

    /// Compute at most one positive interpretation.
    ///
    /// `Ok(None)` means only that this implementation produced no result.
    fn parse(
        &self,
        source: &Self::Source,
    ) -> PartialParseResult<Self::Value, Self::Witness, Self::Error>;
}

/// Parsing as a total function.
pub trait TotalParser {
    type Source: ?Sized;
    type Value;
    type Witness;
    type Error;

    fn parse_total(
        &self,
        source: &Self::Source,
    ) -> Result<(Self::Value, Self::Witness), Self::Error>;
}

/// Parsing as a relation, including ambiguous grammars.
pub trait RelationalParser {
    type Source: ?Sized;
    type Value;
    type Witness;
    type Error;

    /// Enumerate known positive interpretations. Completeness is a separate
    /// property/law and is not implied by this method.
    fn parses(
        &self,
        source: &Self::Source,
    ) -> RelationalParseResult<Self::Value, Self::Witness, Self::Error>;
}

/// A positive witness that two sources have a common interpretation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SameInterpretation<V, W, E> {
    pub value: V,
    pub left: W,
    pub right: W,
    pub equivalence: E,
}

/// The partial-equivalence relation induced by a functional interpreter:
/// two sources are related when both are valid and denote the same value.
///
/// The comparison may canonicalize values or construct backend evidence; it
/// need not use host-language equality.
pub trait InterpretationPer: PartialParser {
    type EquivalenceWitness;

    fn same_interpretation(
        &self,
        left: &Self::Source,
        right: &Self::Source,
    ) -> SameInterpretationResult<Self::Value, Self::Witness, Self::EquivalenceWitness, Self::Error>;
}

/// Logic-level positive interpretation relation.
///
/// This is syntax only. Backends choose how source and value carriers are
/// represented and may supply proof capabilities independently.
pub trait InterpretationRelationSyntax<L: Logic> {
    fn interprets(&self, source: L::Term, value: L::Term) -> Result<L::Term, L::Error>;
}

/// Optional proof that a relational interpretation is functional.
pub trait FunctionalInterpretationLaws<L: Logic>: InterpretationRelationSyntax<L> {
    fn interpretation_functional(&self) -> Result<L::Thm, L::Error>;
}

/// The source PER induced by sharing an interpretation value.
pub trait InterpretationPerSyntax<L: Logic>: InterpretationRelationSyntax<L> {
    fn same_interpretation_relation(
        &self,
        left: L::Term,
        right: L::Term,
    ) -> Result<L::Term, L::Error>;
}

/// Optional PER laws. Reflexivity is deliberately restricted to the
/// interpretation domain.
pub trait InterpretationPerLaws<L: Logic>: InterpretationPerSyntax<L> {
    fn same_interpretation_symmetric(&self) -> Result<L::Thm, L::Error>;
    fn same_interpretation_transitive(&self) -> Result<L::Thm, L::Error>;
    fn same_interpretation_reflexive_on_domain(&self) -> Result<L::Thm, L::Error>;
}

/// Laws/checkable evidence expected from a parser-printer pair.
///
/// These methods return backend evidence rather than asserting that every
/// implementation automatically satisfies round trips.
pub trait Transpose: PartialParser {
    type Printed;
    type RoundTripWitness;

    fn print(&self, value: &Self::Value) -> Result<Self::Printed, Self::Error>;
    fn parse_print_round_trip(
        &self,
        value: &Self::Value,
    ) -> Result<Self::RoundTripWitness, Self::Error>;
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::convert::Infallible;

    struct DecimalDigit;

    impl PartialParser for DecimalDigit {
        type Source = [u8];
        type Value = u8;
        type Witness = ();
        type Error = Infallible;

        fn parse(&self, source: &[u8]) -> Result<Option<(u8, ())>, Infallible> {
            Ok(match source {
                [b'0'..=b'9'] => Some((source[0] - b'0', ())),
                _ => None,
            })
        }
    }

    #[test]
    fn partial_parser_distinguishes_no_result_from_failure() {
        assert_eq!(DecimalDigit.parse(b"7"), Ok(Some((7, ()))));
        assert_eq!(DecimalDigit.parse(b"77"), Ok(None));
    }

    #[test]
    fn prefix_result_keeps_span_and_remainder_consistent() {
        let parsed = PrefixInterpretation::new(7, (), Span::new(2, 3).unwrap(), 3).unwrap();
        assert_eq!(parsed.consumed.len(), 1);
        assert!(!parsed.is_complete(3));
        assert!(PrefixInterpretation::new(7, (), Span::new(2, 3).unwrap(), 2).is_none());
    }

    #[test]
    fn utf8_boundary_maps_scalar_spans_back_to_bytes() {
        let bytes = "Aé𝄞"
            .as_bytes()
            .iter()
            .copied()
            .map(RawByte)
            .collect::<Vec<_>>();
        let decoded = Utf8.decode_text(&bytes).unwrap();
        assert_eq!(decoded.scalar_byte_offsets, vec![0, 1, 3, 7]);
        assert_eq!(decoded.byte_span(Span::new(1, 3).unwrap()), Span::new(1, 7));
    }

    #[test]
    fn utf8_boundary_retains_malformed_offset() {
        assert_eq!(
            Utf8.decode_text(&[RawByte(0xf0), RawByte(0x9d)]),
            Err(MalformedUtf8 {
                valid_up_to: 0,
                error_len: None,
            })
        );
    }
}
