//! Small, policy-explicit adapters between the core parsing capabilities.
//!
//! These are free functions rather than blanket implementations: a parser must
//! still choose its trailing-input diagnostic, encoding boundary, and semantic
//! equality policy.

use crate::{
    DecodedText, ParseAttempt, PartialParser, PartialPrefixParser, PrefixInterpretation,
    SameInterpretation, SameInterpretationResult, Span, TextEncodingBoundary,
};
use covalence_kernel_data::UnicodeScalar;

/// Derive whole-source parsing from prefix parsing.
///
/// `trailing_input` remains caller-supplied because the shared layer cannot
/// know whether trailing input is an error token, a recovery point, or a
/// structured diagnostic.
pub fn exact_from_prefix<P, F>(
    parser: &P,
    source: &P::Source,
    source_len: usize,
    trailing_input: F,
) -> Result<ParseAttempt<(P::Value, P::Witness), P::Diagnostic>, PrefixAdapterError<P::Error>>
where
    P: PartialPrefixParser,
    F: FnOnce(Span) -> P::Diagnostic,
{
    match parser
        .parse_prefix(source, 0)
        .map_err(PrefixAdapterError::Parse)?
    {
        ParseAttempt::NoMatch(diagnostic) => Ok(ParseAttempt::NoMatch(diagnostic)),
        ParseAttempt::Match(parsed) => {
            if parsed.consumed.start != 0
                || parsed.consumed.end != parsed.remainder
                || parsed.remainder > source_len
            {
                return Err(PrefixAdapterError::InvalidExtent {
                    consumed: parsed.consumed,
                    remainder: parsed.remainder,
                    source_len,
                });
            }
            if parsed.is_complete(source_len) {
                Ok(ParseAttempt::Match((parsed.value, parsed.witness)))
            } else {
                Ok(ParseAttempt::NoMatch(trailing_input(Span {
                    start: parsed.remainder,
                    end: source_len,
                })))
            }
        }
    }
}

/// Failure while decoding bytes or transporting a scalar-indexed parse result.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EncodedTextError<DecodeError, ParseError> {
    Decode(DecodeError),
    Parse(ParseError),
    /// A parser returned a scalar span or remainder outside the decoded text.
    InvalidScalarExtent {
        consumed: Span,
        remainder: usize,
        scalar_len: usize,
    },
}

/// Decode encoded text, parse it, then express the successful extent in
/// encoded units.
///
/// Parser diagnostics deliberately remain scalar-indexed. Callers can map
/// diagnostic spans through the returned [`DecodedText`] when their diagnostic
/// type exposes a span; the shared layer does not prescribe such a shape.
pub fn parse_encoded_text_prefix<B, P>(
    boundary: &B,
    parser: &P,
    encoded: &B::Encoded,
    start: usize,
) -> Result<
    (
        DecodedText,
        ParseAttempt<PrefixInterpretation<P::Value, P::Witness>, P::Diagnostic>,
    ),
    EncodedTextError<B::Error, P::Error>,
>
where
    B: TextEncodingBoundary,
    P: PartialPrefixParser<Source = [UnicodeScalar]>,
{
    let decoded = boundary
        .decode_text(encoded)
        .map_err(EncodedTextError::Decode)?;
    let attempt = parser
        .parse_prefix(&decoded.scalars, start)
        .map_err(EncodedTextError::Parse)?;
    let attempt = match attempt {
        ParseAttempt::NoMatch(diagnostic) => ParseAttempt::NoMatch(diagnostic),
        ParseAttempt::Match(parsed) => {
            let Some(consumed) = decoded.byte_span(parsed.consumed) else {
                return Err(EncodedTextError::InvalidScalarExtent {
                    consumed: parsed.consumed,
                    remainder: parsed.remainder,
                    scalar_len: decoded.scalars.len(),
                });
            };
            let Some(&remainder) = decoded.scalar_byte_offsets.get(parsed.remainder) else {
                return Err(EncodedTextError::InvalidScalarExtent {
                    consumed: parsed.consumed,
                    remainder: parsed.remainder,
                    scalar_len: decoded.scalars.len(),
                });
            };
            ParseAttempt::Match(PrefixInterpretation {
                value: parsed.value,
                witness: parsed.witness,
                consumed,
                remainder,
            })
        }
    };
    Ok((decoded, attempt))
}

/// Construct the source PER induced by a functional parser and an explicit
/// semantic equality witness.
///
/// Returning `None` from `equivalent` means the two successfully parsed values
/// are not related. The witness is ordinary host data, not a theorem.
pub fn same_interpretation_by<P, Q, F>(
    parser: &P,
    left: &P::Source,
    right: &P::Source,
    equivalent: F,
) -> SameInterpretationResult<P::Value, P::Witness, Q, P::Error>
where
    P: PartialParser,
    F: FnOnce(&P::Value, &P::Value) -> Option<Q>,
{
    let Some((left_value, left_witness)) = parser.parse(left)? else {
        return Ok(None);
    };
    let Some((right_value, right_witness)) = parser.parse(right)? else {
        return Ok(None);
    };
    Ok(
        equivalent(&left_value, &right_value).map(|equivalence| SameInterpretation {
            value: left_value,
            left: left_witness,
            right: right_witness,
            equivalence,
        }),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ParseAttempt, PartialPrefixParser, Utf8};
    use core::convert::Infallible;
    use covalence_kernel_data::RawByte;

    struct FirstScalar;

    impl PartialPrefixParser for FirstScalar {
        type Source = [UnicodeScalar];
        type Value = UnicodeScalar;
        type Witness = ();
        type Diagnostic = Span;
        type Error = Infallible;

        fn parse_prefix(
            &self,
            source: &[UnicodeScalar],
            start: usize,
        ) -> Result<ParseAttempt<PrefixInterpretation<Self::Value, ()>, Span>, Infallible> {
            Ok(match source.get(start).copied() {
                Some(value) => ParseAttempt::Match(
                    PrefixInterpretation::new(
                        value,
                        (),
                        Span::new(start, start + 1).unwrap(),
                        start + 1,
                    )
                    .unwrap(),
                ),
                None => ParseAttempt::NoMatch(Span::new(start, start).unwrap()),
            })
        }
    }

    impl PartialParser for FirstScalar {
        type Source = [UnicodeScalar];
        type Value = UnicodeScalar;
        type Witness = ();
        type Error = Infallible;

        fn parse(
            &self,
            source: &[UnicodeScalar],
        ) -> Result<Option<(Self::Value, Self::Witness)>, Infallible> {
            Ok(source.first().copied().map(|value| (value, ())))
        }
    }

    #[test]
    fn exact_adapter_reports_the_unconsumed_extent() {
        let source = [
            UnicodeScalar::new('a' as u32).unwrap(),
            UnicodeScalar::new('b' as u32).unwrap(),
        ];
        assert_eq!(
            exact_from_prefix(&FirstScalar, &source, source.len(), |span| span),
            Ok(ParseAttempt::NoMatch(Span::new(1, 2).unwrap()))
        );
    }

    #[test]
    fn encoded_adapter_transports_scalar_extents_to_bytes() {
        let bytes = "éx"
            .as_bytes()
            .iter()
            .copied()
            .map(RawByte)
            .collect::<Vec<_>>();
        let (_, ParseAttempt::Match(parsed)) =
            parse_encoded_text_prefix(&Utf8, &FirstScalar, &bytes, 0).unwrap()
        else {
            panic!("expected a match")
        };
        assert_eq!(parsed.consumed, Span::new(0, 2).unwrap());
        assert_eq!(parsed.remainder, 2);
    }

    #[test]
    fn per_adapter_keeps_semantic_equality_policy_explicit() {
        let a = [UnicodeScalar::new('a' as u32).unwrap()];
        let b = [UnicodeScalar::new('b' as u32).unwrap()];
        let same = same_interpretation_by(&FirstScalar, &a, &a, |left, right| {
            (left == right).then_some(())
        })
        .unwrap();
        assert!(same.is_some());
        assert!(
            same_interpretation_by(&FirstScalar, &a, &b, |left, right| {
                (left == right).then_some(())
            })
            .unwrap()
            .is_none()
        );
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PrefixAdapterError<E> {
    Parse(E),
    InvalidExtent {
        consumed: Span,
        remainder: usize,
        source_len: usize,
    },
}
