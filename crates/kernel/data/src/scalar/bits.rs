//! Logic-agnostic capabilities for bits and finite bit strings.
//!
//! `Bit`, finite `Bits`, and fixed-width bit vectors are separate layers.
//! Packing to [`crate::BytesSyntax`] names intra-byte order and partial-byte
//! padding explicitly.
//!
//! @covalence-api {"id":"A0010","title":"Bits and finite bit strings","status":"experimental","dependsOn":["A0001","A0002","A0003"]}

use crate::{BytesSyntax, NatSyntax};
use covalence_logic_api::Logic;

/// Significance order of successive bits within each packed byte.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum IntraByteOrder {
    /// The first bit occupies bit 0, then bit 1, and so on.
    LeastSignificantFirst,
    /// The first bit occupies bit 7, then bit 6, and so on.
    MostSignificantFirst,
}

/// Policy when a bit string's length is not divisible by eight.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PartialByte {
    Reject,
    /// Append false bits at the end of the logical bit sequence.
    PadEndWithZero,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct BytePacking {
    pub intra_byte: IntraByteOrder,
    pub partial_byte: PartialByte,
}

/// One logical bit.
pub trait BitSyntax: Logic {
    fn bit_type(&self) -> Self::Type;
    fn bit_false(&self) -> Self::Term;
    fn bit_true(&self) -> Self::Term;
    fn bit_literal(&self, value: bool) -> Self::Term {
        if value {
            self.bit_true()
        } else {
            self.bit_false()
        }
    }
}

/// A finite sequence of bits.
pub trait BitsSyntax: BitSyntax {
    fn bits_type(&self) -> Self::Type;
    fn bits_empty(&self) -> Self::Term;
    fn bits_literal(&self, bits: &[bool]) -> Result<Self::Term, Self::Error>;
}

pub trait BitsConstruction: BitsSyntax {
    fn bits_singleton(&self, bit: Self::Term) -> Result<Self::Term, Self::Error>;
    fn bits_prepend(&self, bit: Self::Term, tail: Self::Term) -> Result<Self::Term, Self::Error>;
    fn bits_concat(&self, left: Self::Term, right: Self::Term) -> Result<Self::Term, Self::Error>;
}

pub trait BitsObservation: BitsSyntax + NatSyntax {
    fn bits_length(&self, bits: Self::Term) -> Result<Self::Term, Self::Error>;
}

pub trait BitsConcatLaws: BitsConstruction + BitsObservation {
    fn bits_concat_left_identity(&self) -> Result<Self::Thm, Self::Error>;
    fn bits_concat_right_identity(&self) -> Result<Self::Thm, Self::Error>;
    fn bits_concat_associative(&self) -> Result<Self::Thm, Self::Error>;
    fn bits_length_concat(&self) -> Result<Self::Thm, Self::Error>;
}

/// Fixed-width bit-vector formation is conditional on exact length.
pub trait FixedWidthBits: BitsSyntax + NatSyntax {
    fn fixed_bits_type(&self, width: usize) -> Result<Self::Type, Self::Error>;
    /// Proposition `bits_length bits = width`.
    fn bits_have_width(&self, width: usize, bits: Self::Term) -> Result<Self::Term, Self::Error>;
    /// Form a fixed-width value from bits and checked exact-length evidence.
    fn form_fixed_bits(
        &self,
        width: usize,
        bits: Self::Term,
        exact_length: Self::Thm,
    ) -> Result<Self::Term, Self::Error>;
    fn forget_fixed_bits(&self, width: usize, fixed: Self::Term)
    -> Result<Self::Term, Self::Error>;
}

pub trait FixedWidthBitsLaws: FixedWidthBits {
    fn fixed_bits_forget_form(&self, width: usize) -> Result<Self::Thm, Self::Error>;
    fn fixed_bits_form_forget(&self, width: usize) -> Result<Self::Thm, Self::Error>;
}

/// Packing relation between finite bits and A0003 byte strings.
pub trait BitsBytesPacking: BitsSyntax + BytesSyntax {
    fn pack_bits(
        &self,
        convention: BytePacking,
        bits: Self::Term,
    ) -> Result<Self::Term, Self::Error>;
    fn unpack_bytes(
        &self,
        intra_byte: IntraByteOrder,
        bytes: Self::Term,
    ) -> Result<Self::Term, Self::Error>;
    /// Proposition `bits_length bits mod 8 = 0`.
    fn bits_are_byte_aligned(&self, bits: Self::Term) -> Result<Self::Term, Self::Error>;
}

pub trait BitsBytesPackingLaws: BitsBytesPacking {
    /// Unpacking packed aligned bits returns the original bits.
    fn unpack_pack_aligned(&self, intra_byte: IntraByteOrder) -> Result<Self::Thm, Self::Error>;
    /// Packing unpacked bytes returns the original bytes.
    fn pack_unpack_bytes(&self, intra_byte: IntraByteOrder) -> Result<Self::Thm, Self::Error>;
    /// With `PadEndWithZero`, unpacking returns the original prefix followed
    /// by fewer than eight false bits.
    fn unpack_pack_zero_padding(
        &self,
        intra_byte: IntraByteOrder,
    ) -> Result<Self::Thm, Self::Error>;
}

pub trait BitsNormalization: BitsSyntax {
    fn normalize_bit(&self, bit: Self::Term) -> Result<Self::Thm, Self::Error>;
    fn normalize_bits(&self, bits: Self::Term) -> Result<Self::Thm, Self::Error>;
}

// TODO(cov:bits.abstract-bool-list-adapter, major): Replace the initial List<Bool> representation seam with abstract Bool and List capabilities once those carrier APIs stabilize.
// TODO(cov:bits.bytes-packing-backend, major): Implement A0010↔A0003 packing behind BytePacking and prove aligned and padded round-trip laws.

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Clone, Debug, PartialEq, Eq)]
    enum Term {
        Bit(bool),
        Bits(Vec<bool>),
        Nat(u64),
        Bytes(Vec<u8>),
    }

    #[derive(Clone, Copy, Debug)]
    struct ListBool;

    #[derive(Debug)]
    struct Error;

    impl core::fmt::Display for Error {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            f.write_str("wrong test carrier")
        }
    }
    impl core::error::Error for Error {}

    impl Logic for ListBool {
        type Kind = ();
        type Type = &'static str;
        type Term = Term;
        type Thm = ();
        type Error = Error;
    }

    impl NatSyntax for ListBool {
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

    impl BitSyntax for ListBool {
        fn bit_type(&self) -> &'static str {
            "bool"
        }
        fn bit_false(&self) -> Term {
            Term::Bit(false)
        }
        fn bit_true(&self) -> Term {
            Term::Bit(true)
        }
    }

    impl BitsSyntax for ListBool {
        fn bits_type(&self) -> &'static str {
            "list bool"
        }
        fn bits_empty(&self) -> Term {
            Term::Bits(vec![])
        }
        fn bits_literal(&self, bits: &[bool]) -> Result<Term, Error> {
            Ok(Term::Bits(bits.to_vec()))
        }
    }

    impl BitsConstruction for ListBool {
        fn bits_singleton(&self, bit: Term) -> Result<Term, Error> {
            self.bits_prepend(bit, self.bits_empty())
        }
        fn bits_prepend(&self, bit: Term, tail: Term) -> Result<Term, Error> {
            match (bit, tail) {
                (Term::Bit(bit), Term::Bits(mut tail)) => {
                    tail.insert(0, bit);
                    Ok(Term::Bits(tail))
                }
                _ => Err(Error),
            }
        }
        fn bits_concat(&self, left: Term, right: Term) -> Result<Term, Error> {
            match (left, right) {
                (Term::Bits(mut left), Term::Bits(right)) => {
                    left.extend(right);
                    Ok(Term::Bits(left))
                }
                _ => Err(Error),
            }
        }
    }

    impl BitsObservation for ListBool {
        fn bits_length(&self, bits: Term) -> Result<Term, Error> {
            match bits {
                Term::Bits(bits) => Ok(Term::Nat(bits.len() as u64)),
                _ => Err(Error),
            }
        }
    }

    #[test]
    fn bit_and_finite_bits_are_distinct_list_bool_layers() {
        let api = ListBool;
        assert_eq!(api.bit_type(), "bool");
        assert_eq!(api.bits_type(), "list bool");
        assert_ne!(api.bit_literal(true), api.bits_literal(&[true]).unwrap());
    }

    #[test]
    fn generic_list_bool_construction_preserves_order() {
        let api = ListBool;
        let bits = api
            .bits_concat(
                api.bits_literal(&[true, false]).unwrap(),
                api.bits_singleton(api.bit_true()).unwrap(),
            )
            .unwrap();
        assert_eq!(bits, Term::Bits(vec![true, false, true]));
        assert_eq!(api.bits_length(bits).unwrap(), Term::Nat(3));
    }

    #[test]
    fn byte_packing_conventions_are_not_implicit_defaults() {
        let lsb = BytePacking {
            intra_byte: IntraByteOrder::LeastSignificantFirst,
            partial_byte: PartialByte::Reject,
        };
        let msb = BytePacking {
            intra_byte: IntraByteOrder::MostSignificantFirst,
            partial_byte: PartialByte::PadEndWithZero,
        };
        assert_ne!(lsb, msb);
        let _unused_bytes_carrier = Term::Bytes(vec![]);
    }
}
