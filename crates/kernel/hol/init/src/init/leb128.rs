//! **LEB128 value decode** — `leb128_decode : list nat → nat`, the unsigned
//! base-128 varint value (atoms.md's "binary: LEB128").
//!
//! A byte list is decoded **least-significant-group first**: each byte
//! contributes its low 7 bits (`b mod 128`), weighted by `128` per position:
//!
//! ```text
//!   leb128_decode = list_foldr (λb acc. (b mod 128) + 128·acc) 0
//! ```
//!
//! Built on the proved `list_foldr` recursion clauses ([`crate::init::list_recursion`])
//! plus computable `nat` arithmetic. [`prove_decode`] computes
//! `⊢ leb128_decode ⌜bytes⌝ = value` for a concrete byte list, hypothesis-free —
//! the kernel re-checks every fold-unfold and arithmetic step.
//!
//! This is the **value** decoder — orthogonal to the recognition-side LEB128
//! ([`crate::grammar::spectec`]), which proves a byte string has the right
//! *shape*. Bytes are represented as `nat` (their `0..256` value), the natural
//! arithmetic domain; a `list u8 → list nat` lift is left to callers (no
//! computable `u8 → nat` cast exists yet).

use covalence_core::{Error, Result, Term, Type};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::{defs, mk_nat};

use crate::init::ext::{TermExt, ThmExt};
use crate::init::list_recursion::{foldr_cons, foldr_nil};

fn nat() -> Type {
    Type::nat()
}

fn nat_list() -> Type {
    defs::list(nat())
}

/// `λname:ty. body` with `name` closed over `body`.
fn abs(name: &str, ty: Type, body: Term) -> Term {
    Term::abs(ty, covalence_core::subst::close(&body, name))
}

/// `128 : nat` — the varint group base (`2^7`).
fn base() -> Term {
    mk_nat(128u32)
}

/// The fold step `λb acc. (b mod 128) + 128·acc`.
pub fn step() -> Term {
    let b = Term::free("b", nat());
    let acc = Term::free("acc", nat());
    let low = Term::app(Term::app(defs::nat_mod(), b), base());
    let hi = Term::app(Term::app(defs::nat_mul(), base()), acc);
    let body = Term::app(Term::app(defs::nat_add(), low), hi);
    abs("b", nat(), abs("acc", nat(), body))
}

/// `leb128_decode : list nat → nat` — `λbytes. list_foldr step 0 bytes`.
pub fn leb128_decode() -> Term {
    let bytes = Term::free("bytes", nat_list());
    let fold = Term::app(
        Term::app(
            Term::app(defs::list_foldr(nat(), nat()), step()),
            mk_nat(0u32),
        ),
        bytes,
    );
    abs("bytes", nat_list(), fold)
}

/// The reified byte list `⌜[b₀, b₁, …]⌝ : list nat`.
pub fn byte_list(bytes: &[u8]) -> Term {
    let mut acc = defs::nil(nat());
    for &b in bytes.iter().rev() {
        acc = Term::app(Term::app(defs::cons(nat()), mk_nat(b as u32)), acc);
    }
    acc
}

fn rhs_of(thm: &Thm) -> Result<Term> {
    Ok(thm.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone())
}

/// `⊢ list_foldr step 0 ⌜bytes⌝ = value` — unfold the fold clause by clause
/// (`foldr_cons` / `foldr_nil`), reducing each `step` application's arithmetic.
fn prove_foldr(bytes: &[u8]) -> Result<Thm> {
    let s = step();
    let z = mk_nat(0u32);
    match bytes {
        [] => foldr_nil(&nat(), &nat(), &s, &z),
        [b, rest @ ..] => {
            let bt = mk_nat(*b as u32);
            let restt = byte_list(rest);
            // foldr s z (cons b rest) = step b (foldr s z rest).
            let fc = foldr_cons(&nat(), &nat(), &s, &z, &bt, &restt)?;
            // foldr s z rest = v_rest  (recursively).
            let rest_eq = prove_foldr(rest)?;
            // step b (foldr s z rest) = step b v_rest  (congruence under `step b`).
            let step_b = Term::app(s.clone(), bt);
            let cong = rest_eq.cong_arg(step_b)?;
            // step b v_rest = value  (β + nat arithmetic).
            let collapse = rhs_of(&cong)?.reduce()?;
            crate::init::eq::trans_chain([fc, cong, collapse])
        }
    }
}

/// `⊢ leb128_decode ⌜bytes⌝ = value` for a concrete unsigned-LEB128 byte list.
/// Hypothesis-free; `value` is the standard unsigned varint the bytes encode.
pub fn prove_decode(bytes: &[u8]) -> Result<Thm> {
    let app = Term::app(leb128_decode(), byte_list(bytes));
    // leb128_decode ⌜bytes⌝ = list_foldr step 0 ⌜bytes⌝  (outer β).
    let beta = Thm::beta_conv(app)?;
    beta.trans(prove_foldr(bytes)?)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `prove_decode` computes the standard unsigned-LEB128 value, kernel-checked.
    #[test]
    fn decodes_known_varints() {
        // (bytes, value) pairs — real WASM unsigned varints.
        for (bytes, value) in [
            (&[0x00u8][..], 0u32),
            (&[0x7F][..], 127),
            (&[0x80, 0x01][..], 128),
            (&[0xE5, 0x8E, 0x26][..], 624485),
            (&[0xFF, 0xFF, 0xFF, 0xFF, 0x0F][..], 0xFFFF_FFFF),
        ] {
            let thm = prove_decode(bytes).unwrap();
            assert!(thm.hyps().is_empty(), "value decode is hypothesis-free");
            let (lhs, rhs) = thm.concl().as_eq().expect("an equation");
            assert_eq!(lhs, &Term::app(leb128_decode(), byte_list(bytes)));
            assert_eq!(rhs, &mk_nat(value), "leb128_decode {bytes:x?} = {value}");
        }
    }

    /// The empty byte list decodes to 0.
    #[test]
    fn decodes_empty() {
        let thm = prove_decode(&[]).unwrap();
        assert!(thm.hyps().is_empty());
        assert_eq!(thm.concl().as_eq().unwrap().1, &mk_nat(0u32));
    }
}
