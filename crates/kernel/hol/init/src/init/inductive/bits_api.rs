//! Native HOL adapter for bits and finite bit strings.
//!
//! A bit is the existing HOL boolean type. A finite bit string is the existing
//! HOL `list bool`; construction and observation use the existing list
//! definitions and introduce no new trusted constants or rules.
//!
//! @covalence-api-impl {"api":"A0010","name":"NativeHol","representation":"HOL List<Bool>"}

use covalence_core::{Result, Term, Type, defs as core_defs};
use covalence_hol_eval::{defs, mk_bool};
use covalence_kernel_data::{BitSyntax, BitsConstruction, BitsObservation, BitsSyntax};

use super::hol::{Hol, NativeHol};

impl BitSyntax for NativeHol {
    fn bit_type(&self) -> Type {
        Type::bool()
    }

    fn bit_false(&self) -> Term {
        mk_bool(false)
    }

    fn bit_true(&self) -> Term {
        mk_bool(true)
    }
}

impl BitsSyntax for NativeHol {
    fn bits_type(&self) -> Type {
        core_defs::list(Type::bool())
    }

    fn bits_empty(&self) -> Term {
        core_defs::nil(Type::bool())
    }

    fn bits_literal(&self, bits: &[bool]) -> Result<Term> {
        bits.iter().rev().try_fold(self.bits_empty(), |tail, bit| {
            self.bits_prepend(self.bit_literal(*bit), tail)
        })
    }
}

impl BitsConstruction for NativeHol {
    fn bits_singleton(&self, bit: Term) -> Result<Term> {
        self.bits_prepend(bit, self.bits_empty())
    }

    fn bits_prepend(&self, bit: Term, tail: Term) -> Result<Term> {
        Hol::app(
            self,
            Hol::app(self, core_defs::cons(Type::bool()), bit)?,
            tail,
        )
    }

    fn bits_concat(&self, left: Term, right: Term) -> Result<Term> {
        Hol::app(
            self,
            Hol::app(self, defs::list_cat(Type::bool()), left)?,
            right,
        )
    }
}

impl BitsObservation for NativeHol {
    fn bits_length(&self, bits: Term) -> Result<Term> {
        Hol::app(self, core_defs::list_length(Type::bool()), bits)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn native_carriers_are_bool_and_list_bool() {
        let api = NativeHol;
        assert_eq!(api.bit_type(), Type::bool());
        assert_eq!(api.bits_type(), core_defs::list(Type::bool()));
    }

    #[test]
    fn native_literal_uses_existing_bool_and_list_definitions() {
        let api = NativeHol;
        let literal = api.bits_literal(&[true, false, true]).unwrap();
        let expected = Hol::app(
            &api,
            Hol::app(&api, core_defs::cons(Type::bool()), mk_bool(true)).unwrap(),
            Hol::app(
                &api,
                Hol::app(&api, core_defs::cons(Type::bool()), mk_bool(false)).unwrap(),
                Hol::app(
                    &api,
                    Hol::app(&api, core_defs::cons(Type::bool()), mk_bool(true)).unwrap(),
                    core_defs::nil(Type::bool()),
                )
                .unwrap(),
            )
            .unwrap(),
        )
        .unwrap();
        assert_eq!(literal, expected);
    }
}
