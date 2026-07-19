//! Computational reference seam for byte strings over a swappable Nat backend.
//!
//! These checked values are useful for testing representations and codecs.
//! They are not object-logic theorems and never implement a proof-law trait.
//!
//! @covalence-api-impl {"api":"A0003","name":"NatBackedBytes<B>","representation":"validated lists of backend Nat values and radix-256 codecs"}

use core::fmt::Debug;

use crate::Endianness;

/// The operations needed to interpret a backend's natural values in radix 256.
pub trait Radix256Nat {
    type Nat: Clone + Eq + Debug;

    fn zero(&self) -> Self::Nat;
    fn is_zero(&self, value: &Self::Nat) -> bool;
    fn lift_byte(&self, byte: u8) -> Self::Nat;
    /// Return a byte exactly when `value < 256`.
    fn as_byte(&self, value: &Self::Nat) -> Option<u8>;
    /// Quotient and remainder by 256.
    fn div_rem_256(&self, value: &Self::Nat) -> (Self::Nat, u8);
    /// `accumulator * 256 + byte`.
    fn mul_256_add(&self, accumulator: &Self::Nat, byte: u8) -> Self::Nat;
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NatByteList<N> {
    elements: Vec<N>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NatByteListError<N> {
    pub index: usize,
    pub value: N,
}

impl<N> NatByteList<N> {
    pub fn elements(&self) -> &[N] {
        &self.elements
    }

    pub fn into_elements(self) -> Vec<N> {
        self.elements
    }
}

/// Radix-256 operations parameterized by the Nat representation.
#[derive(Clone, Debug)]
pub struct NatBackedBytes<B> {
    backend: B,
}

impl<B> NatBackedBytes<B> {
    pub const fn new(backend: B) -> Self {
        Self { backend }
    }

    pub const fn backend(&self) -> &B {
        &self.backend
    }
}

impl<B: Radix256Nat> NatBackedBytes<B> {
    /// Validate the per-element `<256` invariant of a Nat list.
    pub fn validate_nat_list(
        &self,
        elements: Vec<B::Nat>,
    ) -> Result<NatByteList<B::Nat>, NatByteListError<B::Nat>> {
        for (index, value) in elements.iter().enumerate() {
            if self.backend.as_byte(value).is_none() {
                return Err(NatByteListError {
                    index,
                    value: value.clone(),
                });
            }
        }
        Ok(NatByteList { elements })
    }

    pub fn nat_list_from_bytes(&self, bytes: &[u8]) -> NatByteList<B::Nat> {
        NatByteList {
            elements: bytes
                .iter()
                .map(|byte| self.backend.lift_byte(*byte))
                .collect(),
        }
    }

    pub fn bytes_from_nat_list(&self, values: &NatByteList<B::Nat>) -> Vec<u8> {
        values
            .elements
            .iter()
            .map(|value| {
                self.backend
                    .as_byte(value)
                    .expect("NatByteList invariant established by constructors")
            })
            .collect()
    }

    /// Decode every byte string. Distinct strings may have the same result.
    pub fn decode(&self, endian: Endianness, bytes: &[u8]) -> B::Nat {
        let mut value = self.backend.zero();
        match endian {
            Endianness::Big => {
                for byte in bytes {
                    value = self.backend.mul_256_add(&value, *byte);
                }
            }
            Endianness::Little => {
                for byte in bytes.iter().rev() {
                    value = self.backend.mul_256_add(&value, *byte);
                }
            }
        }
        value
    }

    /// Canonical minimal encoding, using `[0]` for zero.
    pub fn encode_canonical(&self, endian: Endianness, value: &B::Nat) -> Vec<u8> {
        if self.backend.is_zero(value) {
            return vec![0];
        }
        let mut quotient = value.clone();
        let mut little = Vec::new();
        while !self.backend.is_zero(&quotient) {
            let (next, byte) = self.backend.div_rem_256(&quotient);
            little.push(byte);
            quotient = next;
        }
        if endian == Endianness::Big {
            little.reverse();
        }
        little
    }

    pub fn canonicalize(&self, endian: Endianness, bytes: &[u8]) -> Vec<u8> {
        self.encode_canonical(endian, &self.decode(endian, bytes))
    }

    /// The equivalence/PER induced by decoding.
    pub fn same_decoded_nat(&self, endian: Endianness, left: &[u8], right: &[u8]) -> bool {
        self.decode(endian, left) == self.decode(endian, right)
    }

    pub fn canonical_class(&self, endian: Endianness, bytes: &[u8]) -> CanonicalNatBytes<B::Nat> {
        let value = self.decode(endian, bytes);
        let bytes = self.encode_canonical(endian, &value);
        CanonicalNatBytes {
            endian,
            value,
            bytes,
        }
    }

    /// Encode exactly `width` bytes, failing precisely when
    /// `value >= 256^width`.
    pub fn encode_fixed_width(
        &self,
        endian: Endianness,
        width: usize,
        value: &B::Nat,
    ) -> Result<Vec<u8>, FixedWidthError<B::Nat>> {
        let mut quotient = value.clone();
        let mut little = Vec::with_capacity(width);
        for _ in 0..width {
            let (next, byte) = self.backend.div_rem_256(&quotient);
            little.push(byte);
            quotient = next;
        }
        if !self.backend.is_zero(&quotient) {
            return Err(FixedWidthError {
                width,
                value: value.clone(),
            });
        }
        if endian == Endianness::Big {
            little.reverse();
        }
        Ok(little)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CanonicalNatBytes<N> {
    endian: Endianness,
    value: N,
    bytes: Vec<u8>,
}

impl<N> CanonicalNatBytes<N> {
    pub fn endian(&self) -> Endianness {
        self.endian
    }

    pub fn value(&self) -> &N {
        &self.value
    }

    pub fn bytes(&self) -> &[u8] {
        &self.bytes
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FixedWidthError<N> {
    pub width: usize,
    pub value: N,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Clone, Copy, Debug)]
    struct U64Nat;

    impl Radix256Nat for U64Nat {
        type Nat = u64;

        fn zero(&self) -> u64 {
            0
        }
        fn is_zero(&self, value: &u64) -> bool {
            *value == 0
        }
        fn lift_byte(&self, byte: u8) -> u64 {
            byte.into()
        }
        fn as_byte(&self, value: &u64) -> Option<u8> {
            (*value).try_into().ok()
        }
        fn div_rem_256(&self, value: &u64) -> (u64, u8) {
            (value / 256, (value % 256) as u8)
        }
        fn mul_256_add(&self, accumulator: &u64, byte: u8) -> u64 {
            accumulator * 256 + u64::from(byte)
        }
    }

    #[test]
    fn nat_lists_require_each_element_to_be_a_byte() {
        let codec = NatBackedBytes::new(U64Nat);
        let valid = codec.validate_nat_list(vec![0, 255]).unwrap();
        assert_eq!(codec.bytes_from_nat_list(&valid), vec![0, 255]);
        assert_eq!(
            codec.validate_nat_list(vec![1, 256]),
            Err(NatByteListError {
                index: 1,
                value: 256,
            })
        );
    }

    #[test]
    fn endian_decoders_induce_padding_equivalence_classes() {
        let codec = NatBackedBytes::new(U64Nat);
        assert!(codec.same_decoded_nat(Endianness::Big, &[1], &[0, 1]));
        assert!(codec.same_decoded_nat(Endianness::Little, &[1], &[1, 0]));
        assert_eq!(codec.canonicalize(Endianness::Big, &[0, 0, 1]), vec![1]);
        assert_eq!(codec.canonicalize(Endianness::Little, &[1, 0, 0]), vec![1]);
    }

    #[test]
    fn canonical_and_fixed_width_round_trips_have_distinct_conditions() {
        let codec = NatBackedBytes::new(U64Nat);
        for endian in [Endianness::Little, Endianness::Big] {
            let canonical = codec.encode_canonical(endian, &65_536);
            assert_eq!(codec.decode(endian, &canonical), 65_536);

            let fixed = codec.encode_fixed_width(endian, 4, &65_536).unwrap();
            assert_eq!(fixed.len(), 4);
            assert_eq!(codec.decode(endian, &fixed), 65_536);
            assert_eq!(
                codec.encode_fixed_width(endian, 1, &256),
                Err(FixedWidthError {
                    width: 1,
                    value: 256,
                })
            );
        }
    }
}
