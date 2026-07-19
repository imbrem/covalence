//! Native HOL adapter for A0014 characters and strings.
//!
//! It reuses the existing scalar subtype, list-backed string newtype, and
//! proved UTF encoders. This module constructs terms only and adds no theorem
//! rules or mint sites.
//!
//! @covalence-api-impl {"api":"A0014","name":"NativeHol","representation":"Unicode-scalar subtype and list-backed abstract strings"}

use covalence_core::{IntTag, Result, Term, Type};
use covalence_hol_eval::{defs, mk_u16};
use covalence_kernel_data::{
    CharacterSequenceSyntax, CharacterSyntax, StringConstruction, StringSyntax, UnicodeScalar,
    Utf8EncoderSyntax, Utf16CodeUnit, Utf16EncoderSyntax,
};

use super::hol::{Hol, NativeHol};

fn character_type() -> Type {
    crate::init::char::char_ty()
}

fn character_list_type() -> Type {
    defs::list(character_type())
}

fn string_abs(characters: Term) -> Term {
    Term::app(Term::spec_abs(defs::string_spec(), Vec::new()), characters)
}

fn string_rep(string: Term) -> Term {
    Term::app(Term::spec_rep(defs::string_spec(), Vec::new()), string)
}

fn character_list(scalars: &[UnicodeScalar]) -> Term {
    scalars
        .iter()
        .rev()
        .fold(defs::nil(character_type()), |tail, scalar| {
            Term::app(
                Term::app(
                    defs::cons(character_type()),
                    crate::init::char::char_lit(u64::from(scalar.value())),
                ),
                tail,
            )
        })
}

impl CharacterSyntax for NativeHol {
    fn character_type(&self) -> Type {
        character_type()
    }

    fn character_literal(&self, scalar: UnicodeScalar) -> Term {
        crate::init::char::char_lit(u64::from(scalar.value()))
    }
}

impl CharacterSequenceSyntax for NativeHol {
    fn character_sequence_type(&self) -> Type {
        character_list_type()
    }

    fn character_sequence_empty(&self) -> Term {
        defs::nil(character_type())
    }

    fn character_sequence_literal(&self, scalars: &[UnicodeScalar]) -> Term {
        character_list(scalars)
    }
}

impl StringSyntax for NativeHol {
    fn string_type(&self) -> Type {
        defs::string_ty()
    }

    fn string_empty(&self) -> Term {
        crate::init::string::string_empty()
    }

    fn string_literal(&self, scalars: &[UnicodeScalar]) -> Term {
        string_abs(character_list(scalars))
    }

    fn string_from_characters(&self, characters: Term) -> Result<Term> {
        Hol::app(
            self,
            Term::spec_abs(defs::string_spec(), Vec::new()),
            characters,
        )
    }

    fn string_characters(&self, string: Term) -> Result<Term> {
        Hol::app(
            self,
            Term::spec_rep(defs::string_spec(), Vec::new()),
            string,
        )
    }
}

impl StringConstruction for NativeHol {
    fn string_singleton(&self, character: Term) -> Result<Term> {
        self.string_prepend(character, self.string_empty())
    }

    fn string_prepend(&self, character: Term, tail: Term) -> Result<Term> {
        let tail = string_rep(tail);
        let characters = Hol::app(
            self,
            Hol::app(self, defs::cons(character_type()), character)?,
            tail,
        )?;
        Ok(string_abs(characters))
    }

    fn string_concat(&self, left: Term, right: Term) -> Result<Term> {
        let characters = Hol::app(
            self,
            Hol::app(self, defs::list_cat(character_type()), string_rep(left))?,
            string_rep(right),
        )?;
        Ok(string_abs(characters))
    }
}

impl Utf8EncoderSyntax for NativeHol {
    fn utf8_encode(&self, string: Term) -> Result<Term> {
        Hol::app(self, crate::init::utf8::encode(), string)
    }
}

impl Utf16EncoderSyntax for NativeHol {
    fn utf16_code_unit_type(&self) -> Type {
        IntTag::U16.ty()
    }

    fn utf16_code_unit_literal(&self, unit: Utf16CodeUnit) -> Term {
        mk_u16(unit.0)
    }

    fn utf16_sequence_type(&self) -> Type {
        defs::list(IntTag::U16.ty())
    }

    fn utf16_encode(&self, string: Term) -> Result<Term> {
        Hol::app(self, crate::init::utf16::encode(), string)
    }
}

#[cfg(test)]
mod tests {
    use covalence_kernel_data::{
        BytesSyntax, CharacterSyntax, StringConstruction, StringSyntax, UnicodeScalar,
        Utf8EncoderSyntax, Utf16EncoderSyntax,
    };

    use super::*;

    #[test]
    fn native_literals_and_construction_are_well_typed() {
        let api = NativeHol;
        let a = UnicodeScalar::from('A');
        let character = api.character_literal(a);
        assert_eq!(character.type_of().unwrap(), api.character_type());
        let text = api.string_literal(&[a, UnicodeScalar::from('é')]);
        assert_eq!(text.type_of().unwrap(), api.string_type());
        assert_eq!(
            api.string_concat(api.string_empty(), text.clone())
                .unwrap()
                .type_of()
                .unwrap(),
            api.string_type()
        );
        assert_eq!(
            api.utf8_encode(text.clone()).unwrap().type_of().unwrap(),
            api.bytes_type()
        );
        assert_eq!(
            api.utf16_encode(text).unwrap().type_of().unwrap(),
            api.utf16_sequence_type()
        );
    }
}
