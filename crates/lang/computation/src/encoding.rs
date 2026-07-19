//! Canonical, strict encodings for portable machine representations.

use core::fmt;

/// A decoding cursor over a borrowed symbol sequence.
///
/// Model-specific decoders use [`take`](Self::take) (or
/// [`take_exact`](Self::take_exact)); [`BitDecode::decode_bits`] and
/// [`ByteDecode::decode_bytes`] then reject any unconsumed suffix.
#[derive(Clone, Copy, Debug)]
pub struct Decoder<'a, T> {
    remaining: &'a [T],
    offset: usize,
}

impl<'a, T> Decoder<'a, T> {
    /// Start at the beginning of `input`.
    #[must_use]
    pub const fn new(input: &'a [T]) -> Self {
        Self {
            remaining: input,
            offset: 0,
        }
    }

    /// Number of symbols already consumed.
    #[must_use]
    pub const fn offset(&self) -> usize {
        self.offset
    }

    /// Number of symbols not yet consumed.
    #[must_use]
    pub const fn remaining_len(&self) -> usize {
        self.remaining.len()
    }

    /// Whether all input has been consumed.
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.remaining.is_empty()
    }

    /// The unconsumed suffix.
    #[must_use]
    pub const fn remaining(&self) -> &'a [T] {
        self.remaining
    }

    /// Consume one symbol.
    pub fn take(&mut self) -> Result<&'a T, DecodeError> {
        let Some((first, rest)) = self.remaining.split_first() else {
            return Err(DecodeError::UnexpectedEnd {
                offset: self.offset,
                needed: 1,
            });
        };
        self.remaining = rest;
        self.offset += 1;
        Ok(first)
    }

    /// Consume exactly `len` symbols.
    pub fn take_exact(&mut self, len: usize) -> Result<&'a [T], DecodeError> {
        if self.remaining.len() < len {
            return Err(DecodeError::UnexpectedEnd {
                offset: self.offset,
                needed: len,
            });
        }
        let (taken, rest) = self.remaining.split_at(len);
        self.remaining = rest;
        self.offset += len;
        Ok(taken)
    }

    fn finish(self) -> Result<(), DecodeError> {
        if self.remaining.is_empty() {
            Ok(())
        } else {
            Err(DecodeError::TrailingInput {
                offset: self.offset,
                remaining: self.remaining.len(),
            })
        }
    }
}

/// A representation was not a canonical encoding of the requested value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DecodeError {
    /// More symbols were required at `offset`.
    UnexpectedEnd { offset: usize, needed: usize },
    /// A complete value was followed by extra symbols.
    TrailingInput { offset: usize, remaining: usize },
    /// A symbol or prefix is not permitted by the model's format.
    InvalidSymbol {
        offset: usize,
        expected: &'static str,
    },
    /// The input describes a value but not its unique canonical spelling.
    NonCanonical { offset: usize, reason: &'static str },
    /// A decoded size or index cannot be represented on this platform.
    Overflow { offset: usize },
}

impl fmt::Display for DecodeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnexpectedEnd { offset, needed } => {
                write!(f, "unexpected end at {offset}; need {needed} symbol(s)")
            }
            Self::TrailingInput { offset, remaining } => {
                write!(f, "{remaining} trailing symbol(s) at {offset}")
            }
            Self::InvalidSymbol { offset, expected } => {
                write!(f, "invalid symbol at {offset}; expected {expected}")
            }
            Self::NonCanonical { offset, reason } => {
                write!(f, "non-canonical encoding at {offset}: {reason}")
            }
            Self::Overflow { offset } => write!(f, "decoded value overflows at {offset}"),
        }
    }
}

impl core::error::Error for DecodeError {}

/// Canonically encode a value as bits.
pub trait BitEncode {
    /// Return the unique bit representation selected by this implementation.
    fn encode_bits(&self) -> Vec<bool>;
}

/// Strictly decode a canonical bit representation.
pub trait BitDecode: Sized {
    /// Parse one value from a cursor.
    fn decode_bits_from(input: &mut Decoder<'_, bool>) -> Result<Self, DecodeError>;

    /// Parse one value and require the entire input to be consumed.
    fn decode_bits(input: &[bool]) -> Result<Self, DecodeError> {
        let mut decoder = Decoder::new(input);
        let value = Self::decode_bits_from(&mut decoder)?;
        decoder.finish()?;
        Ok(value)
    }
}

/// A type with both canonical bit encoding and strict decoding.
pub trait BitCodec: BitEncode + BitDecode {}
impl<T: BitEncode + BitDecode> BitCodec for T {}

/// Canonically encode a value as bytes.
pub trait ByteEncode {
    /// Return the unique byte representation selected by this implementation.
    fn encode_bytes(&self) -> Vec<u8>;
}

/// Strictly decode a canonical byte representation.
pub trait ByteDecode: Sized {
    /// Parse one value from a cursor.
    fn decode_bytes_from(input: &mut Decoder<'_, u8>) -> Result<Self, DecodeError>;

    /// Parse one value and require the entire input to be consumed.
    fn decode_bytes(input: &[u8]) -> Result<Self, DecodeError> {
        let mut decoder = Decoder::new(input);
        let value = Self::decode_bytes_from(&mut decoder)?;
        decoder.finish()?;
        Ok(value)
    }
}

/// A type with both canonical byte encoding and strict decoding.
pub trait ByteCodec: ByteEncode + ByteDecode {}
impl<T: ByteEncode + ByteDecode> ByteCodec for T {}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Debug, PartialEq, Eq)]
    struct OneBit(bool);

    impl BitDecode for OneBit {
        fn decode_bits_from(input: &mut Decoder<'_, bool>) -> Result<Self, DecodeError> {
            Ok(Self(*input.take()?))
        }
    }

    #[test]
    fn strict_decoder_rejects_a_suffix() {
        assert_eq!(
            OneBit::decode_bits(&[true, false]),
            Err(DecodeError::TrailingInput {
                offset: 1,
                remaining: 1,
            })
        );
    }

    #[test]
    fn cursor_reports_absolute_offsets() {
        let mut decoder = Decoder::new(&[1_u8]);
        assert_eq!(decoder.take(), Ok(&1));
        assert_eq!(
            decoder.take(),
            Err(DecodeError::UnexpectedEnd {
                offset: 1,
                needed: 1,
            })
        );
    }
}
