//! Characters, abstract strings, and concrete Unicode encodings.
//!
//! @covalence-api {"id":"A0014","title":"Characters and strings","status":"experimental","dependsOn":["A0001","A0002","A0003"]}
//!
//! A Unicode scalar value is not a UTF-16 code unit and neither is a raw
//! byte. Abstract character sequences and strings are likewise distinct from
//! their UTF-8 and UTF-16 serializations.

use crate::{BytesSyntax, NatSyntax};
use covalence_logic_api::Logic;

/// A Unicode scalar value: `0..=0x10ffff`, excluding surrogates.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct UnicodeScalar(u32);

impl UnicodeScalar {
    pub const fn new(value: u32) -> Option<Self> {
        if value <= 0x10ffff && !(value >= 0xd800 && value <= 0xdfff) {
            Some(Self(value))
        } else {
            None
        }
    }

    pub const fn value(self) -> u32 {
        self.0
    }
}

impl From<char> for UnicodeScalar {
    fn from(value: char) -> Self {
        Self(value as u32)
    }
}

/// One raw UTF-16 code unit; surrogate units are permitted.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Utf16CodeUnit(pub u16);

/// One raw byte, with no character interpretation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct RawByte(pub u8);

/// Evidence retained when UTF-8 validation fails.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MalformedUtf8 {
    /// Length of the valid prefix.
    pub valid_up_to: usize,
    /// Length of the invalid sequence, or `None` when truncated.
    pub error_len: Option<usize>,
}

/// Why UTF-16 decoding failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MalformedUtf16Kind {
    UnpairedHighSurrogate,
    UnpairedLowSurrogate,
}

/// Evidence retained when UTF-16 validation fails.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MalformedUtf16 {
    pub index: usize,
    pub unit: Utf16CodeUnit,
    pub kind: MalformedUtf16Kind,
}

/// Validate and decode UTF-8 into Unicode scalar values.
pub fn decode_utf8(bytes: &[RawByte]) -> Result<Vec<UnicodeScalar>, MalformedUtf8> {
    let raw: Vec<u8> = bytes.iter().map(|byte| byte.0).collect();
    match std::str::from_utf8(&raw) {
        Ok(text) => Ok(text.chars().map(UnicodeScalar::from).collect()),
        Err(error) => Err(MalformedUtf8 {
            valid_up_to: error.valid_up_to(),
            error_len: error.error_len(),
        }),
    }
}

/// Encode Unicode scalar values as canonical UTF-8.
pub fn encode_utf8(scalars: &[UnicodeScalar]) -> Vec<RawByte> {
    let mut bytes = Vec::new();
    for scalar in scalars {
        let character = char::from_u32(scalar.value()).expect("UnicodeScalar invariant");
        let mut buffer = [0; 4];
        bytes.extend(
            character
                .encode_utf8(&mut buffer)
                .as_bytes()
                .iter()
                .copied()
                .map(RawByte),
        );
    }
    bytes
}

/// Validate and decode UTF-16 into Unicode scalar values.
pub fn decode_utf16(units: &[Utf16CodeUnit]) -> Result<Vec<UnicodeScalar>, MalformedUtf16> {
    let mut scalars = Vec::new();
    let mut index = 0;
    while index < units.len() {
        let unit = units[index].0;
        match unit {
            0xd800..=0xdbff => {
                let Some(next) = units.get(index + 1).copied() else {
                    return Err(MalformedUtf16 {
                        index,
                        unit: units[index],
                        kind: MalformedUtf16Kind::UnpairedHighSurrogate,
                    });
                };
                if !(0xdc00..=0xdfff).contains(&next.0) {
                    return Err(MalformedUtf16 {
                        index,
                        unit: units[index],
                        kind: MalformedUtf16Kind::UnpairedHighSurrogate,
                    });
                }
                let high = u32::from(unit - 0xd800);
                let low = u32::from(next.0 - 0xdc00);
                scalars.push(UnicodeScalar::new(0x10000 + (high << 10) + low).unwrap());
                index += 2;
            }
            0xdc00..=0xdfff => {
                return Err(MalformedUtf16 {
                    index,
                    unit: units[index],
                    kind: MalformedUtf16Kind::UnpairedLowSurrogate,
                });
            }
            _ => {
                scalars.push(UnicodeScalar::new(u32::from(unit)).unwrap());
                index += 1;
            }
        }
    }
    Ok(scalars)
}

/// Encode Unicode scalar values as canonical UTF-16.
pub fn encode_utf16(scalars: &[UnicodeScalar]) -> Vec<Utf16CodeUnit> {
    let mut units = Vec::new();
    for scalar in scalars {
        let character = char::from_u32(scalar.value()).expect("UnicodeScalar invariant");
        let mut buffer = [0; 2];
        units.extend(
            character
                .encode_utf16(&mut buffer)
                .iter()
                .copied()
                .map(Utf16CodeUnit),
        );
    }
    units
}

/// Unicode scalar carrier and closed literals.
pub trait CharacterSyntax: Logic {
    fn character_type(&self) -> Self::Type;
    fn character_literal(&self, scalar: UnicodeScalar) -> Self::Term;
}

/// Finite sequences of abstract characters.
pub trait CharacterSequenceSyntax: CharacterSyntax {
    fn character_sequence_type(&self) -> Self::Type;
    fn character_sequence_empty(&self) -> Self::Term;
    fn character_sequence_literal(&self, scalars: &[UnicodeScalar]) -> Self::Term;
}

/// An abstract string carrier, distinct from encoded bytes/code units.
pub trait StringSyntax: CharacterSequenceSyntax {
    fn string_type(&self) -> Self::Type;
    fn string_empty(&self) -> Self::Term;
    fn string_literal(&self, scalars: &[UnicodeScalar]) -> Self::Term;
    fn string_from_characters(&self, characters: Self::Term) -> Result<Self::Term, Self::Error>;
    fn string_characters(&self, string: Self::Term) -> Result<Self::Term, Self::Error>;
}

pub trait StringConstruction: StringSyntax {
    fn string_singleton(&self, character: Self::Term) -> Result<Self::Term, Self::Error>;
    fn string_prepend(
        &self,
        character: Self::Term,
        tail: Self::Term,
    ) -> Result<Self::Term, Self::Error>;
    fn string_concat(&self, left: Self::Term, right: Self::Term)
    -> Result<Self::Term, Self::Error>;
}

/// Natural-valued observations stay optional until the abstract list API is
/// shared across backends.
pub trait StringObservation: StringSyntax + NatSyntax {
    fn string_length(&self, string: Self::Term) -> Result<Self::Term, Self::Error>;
}

pub trait StringConcatLaws: StringConstruction {
    fn string_concat_left_identity(&self) -> Result<Self::Thm, Self::Error>;
    fn string_concat_right_identity(&self) -> Result<Self::Thm, Self::Error>;
    fn string_concat_associative(&self) -> Result<Self::Thm, Self::Error>;
}

/// UTF-8 encoding, independently usable before a decoder is realized.
pub trait Utf8EncoderSyntax: StringSyntax + BytesSyntax {
    fn utf8_encode(&self, string: Self::Term) -> Result<Self::Term, Self::Error>;
}

/// UTF-8 validation and relational decoding vocabulary.
pub trait Utf8DecodingSyntax: Utf8EncoderSyntax {
    fn valid_utf8(&self, bytes: Self::Term) -> Result<Self::Term, Self::Error>;
    fn utf8_decodes_to(
        &self,
        bytes: Self::Term,
        string: Self::Term,
    ) -> Result<Self::Term, Self::Error>;
}

pub trait Utf8EncodingLaws: Utf8DecodingSyntax {
    fn utf8_encode_valid(&self) -> Result<Self::Thm, Self::Error>;
    fn utf8_decode_encode(&self) -> Result<Self::Thm, Self::Error>;
    fn utf8_decoding_functional(&self) -> Result<Self::Thm, Self::Error>;
}

/// UTF-16 code-unit sequence and encoding vocabulary.
pub trait Utf16EncoderSyntax: StringSyntax {
    fn utf16_code_unit_type(&self) -> Self::Type;
    fn utf16_code_unit_literal(&self, unit: Utf16CodeUnit) -> Self::Term;
    fn utf16_sequence_type(&self) -> Self::Type;
    fn utf16_encode(&self, string: Self::Term) -> Result<Self::Term, Self::Error>;
}

/// UTF-16 validation and relational decoding vocabulary.
pub trait Utf16DecodingSyntax: Utf16EncoderSyntax {
    fn valid_utf16(&self, units: Self::Term) -> Result<Self::Term, Self::Error>;
    fn utf16_decodes_to(
        &self,
        units: Self::Term,
        string: Self::Term,
    ) -> Result<Self::Term, Self::Error>;
}

pub trait Utf16EncodingLaws: Utf16DecodingSyntax {
    fn utf16_encode_valid(&self) -> Result<Self::Thm, Self::Error>;
    fn utf16_decode_encode(&self) -> Result<Self::Thm, Self::Error>;
    fn utf16_decoding_functional(&self) -> Result<Self::Thm, Self::Error>;
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum UnicodeNormalization {
    Nfc,
    Nfd,
    Nfkc,
    Nfkd,
}

pub trait UnicodeNormalizationSyntax: StringSyntax {
    fn normalize(
        &self,
        form: UnicodeNormalization,
        string: Self::Term,
    ) -> Result<Self::Term, Self::Error>;
}

pub trait UnicodeNormalizationLaws: UnicodeNormalizationSyntax {
    fn normalization_idempotent(
        &self,
        form: UnicodeNormalization,
    ) -> Result<Self::Thm, Self::Error>;
    fn normalization_preserves_equivalence(
        &self,
        form: UnicodeNormalization,
    ) -> Result<Self::Thm, Self::Error>;
}

// TODO(cov:text.abstract-list-integration, major): Replace the temporary character-sequence seam with the shared abstract finite-list API once it lands.
// TODO(cov:text.unicode-tables, major): Add versioned Unicode normalization, case, category, and grapheme tables with checked provenance.

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scalar_values_exclude_surrogates_and_out_of_range_values() {
        assert_eq!(UnicodeScalar::new(0x10ffff).unwrap().value(), 0x10ffff);
        assert!(UnicodeScalar::new(0xd800).is_none());
        assert!(UnicodeScalar::new(0xdfff).is_none());
        assert!(UnicodeScalar::new(0x110000).is_none());
    }

    #[test]
    fn utf8_round_trip_and_malformed_evidence() {
        let scalars = ['A', 'é', '𝄞'].map(UnicodeScalar::from);
        let bytes = encode_utf8(&scalars);
        assert_eq!(decode_utf8(&bytes).unwrap(), scalars);
        assert_eq!(
            decode_utf8(&[RawByte(0xf0), RawByte(0x9d)]),
            Err(MalformedUtf8 {
                valid_up_to: 0,
                error_len: None
            })
        );
    }

    #[test]
    fn utf16_round_trip_and_unpaired_surrogate_evidence() {
        let scalars = ['A', '𝄞'].map(UnicodeScalar::from);
        let units = encode_utf16(&scalars);
        assert_eq!(decode_utf16(&units).unwrap(), scalars);
        assert_eq!(
            decode_utf16(&[Utf16CodeUnit(0xd800)]),
            Err(MalformedUtf16 {
                index: 0,
                unit: Utf16CodeUnit(0xd800),
                kind: MalformedUtf16Kind::UnpairedHighSurrogate
            })
        );
        assert_eq!(
            decode_utf16(&[Utf16CodeUnit(0xdc00)]),
            Err(MalformedUtf16 {
                index: 0,
                unit: Utf16CodeUnit(0xdc00),
                kind: MalformedUtf16Kind::UnpairedLowSurrogate
            })
        );
    }
}
