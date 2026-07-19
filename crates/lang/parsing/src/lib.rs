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

#![forbid(unsafe_code)]

pub mod bytes;

pub use bytes::{
    ByteParseDiagnostic, ByteParseError, ByteParseJudgment, ByteParseLaws, ByteParseOutcome,
    ByteParseWitness, ByteParser, ByteParserRelation, ByteParserTheory, ByteSpan, LiteralBytes,
    ParseBudget, ParseFailure,
};

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
    ) -> Result<Option<(Self::Value, Self::Witness)>, Self::Error>;
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
    ) -> Result<Vec<(Self::Value, Self::Witness)>, Self::Error>;
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
    ) -> Result<
        Option<SameInterpretation<Self::Value, Self::Witness, Self::EquivalenceWitness>>,
        Self::Error,
    >;
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
}
