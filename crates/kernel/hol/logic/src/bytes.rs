//! Logic-agnostic capabilities for bytes and byte strings.
//!
//! A [`ByteSyntax`] value is one bounded 8-bit datum. A [`BytesSyntax`] value
//! is a finite sequence of bytes; the two carriers are deliberately distinct.
//! Consumers should require only the construction, observation, law, or
//! encoding capabilities they use.
//!
//! Integer encodings are not presented as an isomorphism. Minimal encodings
//! identify byte strings that differ by redundant leading/trailing zero bytes,
//! while fixed-width encodings require explicit fit and length conditions.
//!
//! @covalence-api {"id":"A0003","title":"Bytes and byte strings","status":"experimental","dependsOn":["A0001","A0002"]}

use crate::{Logic, NatSyntax};

/// Byte order for multi-byte integer encodings.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Endianness {
    Little,
    Big,
}

/// The single-byte carrier and its closed literals.
pub trait ByteSyntax: Logic {
    fn byte_type(&self) -> Self::Type;
    fn byte_literal(&self, value: u8) -> Self::Term;
}

/// The byte-string carrier and its closed literals.
pub trait BytesSyntax: ByteSyntax {
    fn bytes_type(&self) -> Self::Type;
    fn bytes_empty(&self) -> Self::Term;
    fn bytes_literal(&self, value: &[u8]) -> Self::Term;
}

/// Byte-string constructors.
pub trait BytesConstruction: BytesSyntax {
    fn bytes_singleton(&self, byte: Self::Term) -> Result<Self::Term, Self::Error>;
    fn bytes_prepend(&self, byte: Self::Term, tail: Self::Term) -> Result<Self::Term, Self::Error>;
    fn bytes_concat(&self, left: Self::Term, right: Self::Term) -> Result<Self::Term, Self::Error>;
}

/// Observation operations whose results are natural numbers.
pub trait BytesObservation: BytesSyntax + NatSyntax {
    fn bytes_length(&self, bytes: Self::Term) -> Result<Self::Term, Self::Error>;
    /// Totalized numeric observation: return the indexed byte as a natural,
    /// or zero when `index >= length`. This is not a byte-valued safe lookup.
    fn bytes_at_or_zero_nat(
        &self,
        bytes: Self::Term,
        index: Self::Term,
    ) -> Result<Self::Term, Self::Error>;
}

/// Optional laws for the explicitly totalized numeric observation.
pub trait BytesObservationLaws: BytesObservation {
    /// `bytes_at_or_zero_nat bs i < 256`.
    fn bytes_at_nat_in_range(&self) -> Result<Self::Thm, Self::Error>;
    /// `length bs ≤ i ⟹ bytes_at_or_zero_nat bs i = 0`.
    fn bytes_at_nat_out_of_bounds(&self) -> Result<Self::Thm, Self::Error>;
}

/// Optional byte/string algebra laws supplied by a backend.
pub trait BytesConcatLaws: BytesConstruction {
    fn bytes_concat_left_identity(&self) -> Result<Self::Thm, Self::Error>;
    fn bytes_concat_right_identity(&self) -> Result<Self::Thm, Self::Error>;
    fn bytes_concat_associative(&self) -> Result<Self::Thm, Self::Error>;
    fn bytes_length_concat(&self) -> Result<Self::Thm, Self::Error>;
}

/// A representation seam between one byte and a natural-number carrier.
///
/// `byte_from_nat_mod_256` is intentionally named for its many-to-one
/// behavior. It is not an inverse of `byte_to_nat` on arbitrary naturals.
pub trait ByteNatBridge: ByteSyntax + NatSyntax {
    fn byte_to_nat(&self, byte: Self::Term) -> Result<Self::Term, Self::Error>;
    fn byte_from_nat_mod_256(&self, nat: Self::Term) -> Result<Self::Term, Self::Error>;
}

/// Optional laws for the byte-as-natural representation.
pub trait ByteNatBridgeLaws: ByteNatBridge {
    /// `byte_to_nat b < 256`.
    fn byte_to_nat_in_range(&self) -> Result<Self::Thm, Self::Error>;
    /// `byte_from_nat_mod_256 (byte_to_nat b) = b`.
    fn byte_nat_round_trip(&self) -> Result<Self::Thm, Self::Error>;
    /// Characterize conversion from a natural as reduction modulo 256.
    fn nat_byte_modulo_law(&self) -> Result<Self::Thm, Self::Error>;
}

/// Minimal-length natural-number encodings.
///
/// The representation of zero and which zero bytes are redundant are part of
/// this capability's supplied laws, not assumptions made by consumers.
pub trait MinimalNatBytesEncoding: BytesSyntax + NatSyntax {
    fn nat_to_minimal_bytes(
        &self,
        endian: Endianness,
        nat: Self::Term,
    ) -> Result<Self::Term, Self::Error>;
    fn nat_from_bytes(
        &self,
        endian: Endianness,
        bytes: Self::Term,
    ) -> Result<Self::Term, Self::Error>;

    /// `encode (decode bytes)`: a canonical representative, not necessarily
    /// the original string when it contains redundant zero bytes.
    fn canonicalize_nat_bytes(
        &self,
        endian: Endianness,
        bytes: Self::Term,
    ) -> Result<Self::Term, Self::Error> {
        let nat = self.nat_from_bytes(endian, bytes)?;
        self.nat_to_minimal_bytes(endian, nat)
    }
}

pub trait MinimalNatBytesEncodingLaws: MinimalNatBytesEncoding {
    /// `decode endian (encode endian n) = n`.
    fn minimal_decode_encode(&self, endian: Endianness) -> Result<Self::Thm, Self::Error>;
    /// `encode endian (decode endian bs) = canonicalize endian bs`.
    fn minimal_encode_decode_canonical(&self, endian: Endianness)
    -> Result<Self::Thm, Self::Error>;
}

/// Fixed-width natural-number encodings.
pub trait FixedWidthNatBytesEncoding: BytesSyntax + NatSyntax {
    fn nat_to_fixed_width_bytes(
        &self,
        endian: Endianness,
        width: Self::Term,
        nat: Self::Term,
    ) -> Result<Self::Term, Self::Error>;
    fn nat_from_fixed_width_bytes(
        &self,
        endian: Endianness,
        bytes: Self::Term,
    ) -> Result<Self::Term, Self::Error>;
}

/// Width-sensitive encoding laws with their conditions explicit.
pub trait FixedWidthNatBytesEncodingLaws: FixedWidthNatBytesEncoding {
    /// Conditional theorem: when `n < 256^width`, decoding the width-byte
    /// encoding returns `n`.
    fn fixed_width_decode_encode_if_fits(
        &self,
        endian: Endianness,
    ) -> Result<Self::Thm, Self::Error>;
    /// Conditional theorem: when `length bs = width`, encoding its decoded
    /// value at that width returns `bs`.
    fn fixed_width_encode_decode_if_exact_length(
        &self,
        endian: Endianness,
    ) -> Result<Self::Thm, Self::Error>;
}

/// Optional normalization of closed byte and byte-string expressions.
pub trait BytesNormalization: BytesSyntax {
    fn normalize_byte(&self, byte: Self::Term) -> Result<Self::Thm, Self::Error>;
    fn normalize_bytes(&self, bytes: Self::Term) -> Result<Self::Thm, Self::Error>;
}

// TODO(cov:bytes.list-nat-sequence-bridge, major): Once the abstract list API stabilizes, relate bytes to lists of in-range naturals with explicit element-range and round-trip laws.
// TODO(cov:bytes.leb128-encoding, major): Add unsigned/signed LEB128 as variable-length byte relations with canonicality, termination, and bounded-width overflow evidence.

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Clone, Debug, PartialEq, Eq)]
    enum Term {
        Byte(u8),
        Bytes(Vec<u8>),
        Nat(u64),
    }

    #[derive(Clone, Copy, Debug)]
    struct Reference;

    #[derive(Debug)]
    struct Error;

    impl core::fmt::Display for Error {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            f.write_str("wrong reference term")
        }
    }

    impl core::error::Error for Error {}

    impl Logic for Reference {
        type Kind = ();
        type Type = &'static str;
        type Term = Term;
        type Thm = ();
        type Error = Error;
    }

    impl NatSyntax for Reference {
        fn nat_type(&self) -> &'static str {
            "nat"
        }
        fn nat_zero(&self) -> Term {
            Term::Nat(0)
        }
        fn nat_succ(&self, n: Term) -> Result<Term, Error> {
            match n {
                Term::Nat(n) => Ok(Term::Nat(n + 1)),
                _ => Err(Error),
            }
        }
        fn nat_literal(&self, n: u64) -> Term {
            Term::Nat(n)
        }
    }

    impl ByteSyntax for Reference {
        fn byte_type(&self) -> &'static str {
            "byte"
        }
        fn byte_literal(&self, value: u8) -> Term {
            Term::Byte(value)
        }
    }

    impl BytesSyntax for Reference {
        fn bytes_type(&self) -> &'static str {
            "bytes"
        }
        fn bytes_empty(&self) -> Term {
            Term::Bytes(vec![])
        }
        fn bytes_literal(&self, value: &[u8]) -> Term {
            Term::Bytes(value.to_vec())
        }
    }

    impl ByteNatBridge for Reference {
        fn byte_to_nat(&self, byte: Term) -> Result<Term, Error> {
            match byte {
                Term::Byte(byte) => Ok(Term::Nat(byte.into())),
                _ => Err(Error),
            }
        }
        fn byte_from_nat_mod_256(&self, nat: Term) -> Result<Term, Error> {
            match nat {
                Term::Nat(nat) => Ok(Term::Byte(nat as u8)),
                _ => Err(Error),
            }
        }
    }

    impl BytesConstruction for Reference {
        fn bytes_singleton(&self, byte: Term) -> Result<Term, Error> {
            self.bytes_prepend(byte, self.bytes_empty())
        }
        fn bytes_prepend(&self, byte: Term, tail: Term) -> Result<Term, Error> {
            match (byte, tail) {
                (Term::Byte(byte), Term::Bytes(mut tail)) => {
                    tail.insert(0, byte);
                    Ok(Term::Bytes(tail))
                }
                _ => Err(Error),
            }
        }
        fn bytes_concat(&self, left: Term, right: Term) -> Result<Term, Error> {
            match (left, right) {
                (Term::Bytes(mut left), Term::Bytes(right)) => {
                    left.extend(right);
                    Ok(Term::Bytes(left))
                }
                _ => Err(Error),
            }
        }
    }

    impl BytesObservation for Reference {
        fn bytes_length(&self, bytes: Term) -> Result<Term, Error> {
            match bytes {
                Term::Bytes(bytes) => Ok(Term::Nat(bytes.len() as u64)),
                _ => Err(Error),
            }
        }
        fn bytes_at_or_zero_nat(&self, bytes: Term, index: Term) -> Result<Term, Error> {
            match (bytes, index) {
                (Term::Bytes(bytes), Term::Nat(index)) => Ok(Term::Nat(
                    bytes.get(index as usize).copied().unwrap_or(0).into(),
                )),
                _ => Err(Error),
            }
        }
    }

    #[test]
    fn byte_and_byte_string_carriers_are_distinct() {
        let api = Reference;
        assert_eq!(api.byte_type(), "byte");
        assert_eq!(api.bytes_type(), "bytes");
        assert_ne!(api.byte_literal(7), api.bytes_literal(&[7]));
    }

    #[test]
    fn nat_bridge_is_explicitly_modulo_256() {
        let api = Reference;
        assert_eq!(
            api.byte_from_nat_mod_256(api.nat_literal(257)).unwrap(),
            api.byte_literal(1)
        );
        assert_eq!(
            api.byte_to_nat(api.byte_literal(255)).unwrap(),
            api.nat_literal(255)
        );
    }

    #[test]
    fn construction_and_totalized_observation_are_separate_capabilities() {
        let api = Reference;
        let bytes = api
            .bytes_concat(
                api.bytes_literal(&[1, 2]),
                api.bytes_singleton(Term::Byte(3)).unwrap(),
            )
            .unwrap();
        assert_eq!(api.bytes_length(bytes.clone()).unwrap(), Term::Nat(3));
        assert_eq!(
            api.bytes_at_or_zero_nat(bytes, Term::Nat(99)).unwrap(),
            Term::Nat(0)
        );
    }
}
