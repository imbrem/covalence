//! Native HOL leaf adapter for the bytes capabilities.
//!
//! Closed byte strings remain one native blob leaf. Symbolic operations
//! delegate to the existing HOL definitions; this adapter adds no trusted
//! rules or theorem constructors.
//!
//! @covalence-api-impl {"api":"A0003","name":"NativeHol","representation":"HOL u8 and native byte-string leaves"}

use covalence_core::{IntTag, Result, Term, Type};
use covalence_hol_eval::{defs, mk_blob, mk_u8};
use covalence_logic_api::{
    ByteNatBridge, ByteSyntax, BytesConstruction, BytesObservation, BytesSyntax, Endianness,
    MinimalNatBytesEncoding, NatBytesEquivalenceSyntax,
};

use super::hol::{Hol, NativeHol};

impl ByteSyntax for NativeHol {
    fn byte_type(&self) -> Type {
        IntTag::U8.ty()
    }

    fn byte_literal(&self, value: u8) -> Term {
        mk_u8(value)
    }
}

impl BytesSyntax for NativeHol {
    fn bytes_type(&self) -> Type {
        Type::bytes()
    }

    fn bytes_empty(&self) -> Term {
        mk_blob(Vec::<u8>::new())
    }

    fn bytes_literal(&self, value: &[u8]) -> Term {
        mk_blob(value.to_vec())
    }
}

impl ByteNatBridge for NativeHol {
    fn byte_to_nat(&self, byte: Term) -> Result<Term> {
        Hol::app(self, defs::int_to_nat(IntTag::U8), byte)
    }

    fn byte_from_nat_mod_256(&self, nat: Term) -> Result<Term> {
        Hol::app(self, defs::int_from_nat(IntTag::U8), nat)
    }
}

impl BytesConstruction for NativeHol {
    fn bytes_singleton(&self, byte: Term) -> Result<Term> {
        self.bytes_prepend(byte, self.bytes_empty())
    }

    fn bytes_prepend(&self, byte: Term, tail: Term) -> Result<Term> {
        let byte_as_nat = self.byte_to_nat(byte)?;
        Hol::app(
            self,
            Hol::app(self, defs::bytes_cons_nat(), byte_as_nat)?,
            tail,
        )
    }

    fn bytes_concat(&self, left: Term, right: Term) -> Result<Term> {
        Hol::app(self, Hol::app(self, defs::bytes_cat(), left)?, right)
    }
}

impl BytesObservation for NativeHol {
    fn bytes_length(&self, bytes: Term) -> Result<Term> {
        Hol::app(self, defs::bytes_len(), bytes)
    }

    fn bytes_at_or_zero_nat(&self, bytes: Term, index: Term) -> Result<Term> {
        Hol::app(self, Hol::app(self, defs::bytes_at(), bytes)?, index)
    }
}

impl MinimalNatBytesEncoding for NativeHol {
    fn nat_to_minimal_bytes(&self, endian: Endianness, nat: Term) -> Result<Term> {
        let encoder = match endian {
            Endianness::Little => defs::nat_to_bytes_le(),
            Endianness::Big => defs::nat_to_bytes_be(),
        };
        Hol::app(self, encoder, nat)
    }

    fn nat_from_bytes(&self, endian: Endianness, bytes: Term) -> Result<Term> {
        let decoder = match endian {
            Endianness::Little => defs::nat_from_bytes_le(),
            Endianness::Big => defs::nat_from_bytes_be(),
        };
        Hol::app(self, decoder, bytes)
    }
}

impl NatBytesEquivalenceSyntax for NativeHol {
    fn same_decoded_nat(&self, endian: Endianness, left: Term, right: Term) -> Result<Term> {
        let left = self.nat_from_bytes(endian, left)?;
        let right = self.nat_from_bytes(endian, right)?;
        Hol::eq(self, left, right)
    }
}

#[cfg(test)]
mod tests {
    use covalence_hol_eval::as_blob;

    use super::*;
    #[test]
    fn native_literals_keep_byte_and_bytes_distinct() {
        let api = NativeHol;
        assert_eq!(api.byte_type(), IntTag::U8.ty());
        assert_eq!(api.bytes_type(), Type::bytes());
        assert_eq!(api.byte_literal(7), mk_u8(7));
        assert_eq!(
            as_blob(&api.bytes_literal(&[7, 8])).as_deref(),
            Some([7, 8].as_slice())
        );
    }

    #[test]
    fn native_minimal_encodings_select_endianness_explicitly() {
        let api = NativeHol;
        let nat = covalence_logic_api::NatSyntax::nat_literal(&api, 256);
        let little = api
            .nat_to_minimal_bytes(Endianness::Little, nat.clone())
            .unwrap();
        let big = api.nat_to_minimal_bytes(Endianness::Big, nat).unwrap();
        assert_ne!(little, big);
    }
}
