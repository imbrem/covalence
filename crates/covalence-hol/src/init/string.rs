//! `string` and `bytes` theorems: the two list-backed sequence types
//! re-exported, their newtype `abs`/`rep` seams, and the empty-sequence
//! (`nil`-side) facts the *current* `list` theory supports.
//!
//! ```text
//! bytes  := list u8       string := list char
//! ```
//!
//! Both are **newtypes** over a `list` (so the `abs`/`rep` round-trips
//! are unconditional, premise `λ_. T`), exactly like
//! [`init::rel`](crate::init::rel). Their structural operations bridge
//! through the kernel coercions
//!
//! - `rep : bytes → list u8` / `rep : string → list char` (unwrap),
//! - `abs : list u8 → bytes` / `abs : list char → string` (wrap),
//!
//! down to the corresponding [`init::list`](crate::init::list)
//! operations. **Downstream proofs must not see that** — they reason
//! through the lemmas here.
//!
//! ## What is here (`nil`-side only)
//!
//! - [`bytes_empty`] / [`string_empty`] — the empty sequences,
//!   `abs nil`.
//! - the newtype round-trip `⊢ rep (abs nil) = nil`
//!   ([`bytes_rep_empty`] / [`string_rep_empty`]),
//! - the empty-sequence head fact `⊢ list.head (rep empty) = none`
//!   ([`bytes_head_empty`] / [`string_head_empty`]), built on
//!   [`init::list::head_nil`].
//!
//! ## Not yet here (see `SKELETONS.md`)
//!
//! The cons-side sequence ops (`length`, `cat`, `at`/`index`, `slice`,
//! `consNat`) ride on the now-landed `list` recursion theorem but are not
//! all surfaced through this newtype seam yet (recorded as skeletons). The
//! UTF-8 / UTF-16 codecs over this seam are built in
//! [`init::utf8`](crate::init::utf8) / [`init::utf16`](crate::init::utf16)
//! — encoders + per-character round-trip + the encoder homomorphism are
//! proved; the validating decoders + full string round-trip are deferred
//! (see `init/SKELETONS.md`). The [`string_rep_abs`] / [`bytes_rep_abs`]
//! newtype round-trips below are the seam those codecs cross.

use covalence_core::{Error, Result, Term, Thm, Type};

use crate::init::ext::{TermExt, ThmExt};
use crate::init::list::head_nil;
use crate::init::logic::truth;

pub use covalence_core::defs::{bytes_spec, string_spec, string_ty};

use covalence_core::defs::{TypeSpec, head, nil, u8_ty};

use crate::init::char::char_ty;

// ============================================================================
// Element types of the two sequences.
// ============================================================================

/// `u8` — the element type of `bytes`.
fn byte_elem() -> Type {
    u8_ty()
}

/// `char` — the element type of `string`.
fn char_elem() -> Type {
    char_ty()
}

// ============================================================================
// THE SEAM — the only code aware that `bytes`/`string` are newtypes over
// `list u8` / `list char`.
//
//   abs : list elem → seq        rep : seq → list elem
//
// Newtypes (selector `λ_. T`), so both round-trips are unconditional.
// ============================================================================

/// `rep : bytes → list u8`.
fn bytes_rep(l: Term) -> Term {
    Term::app(Term::spec_rep(bytes_spec(), Vec::new()), l)
}

/// `abs : list u8 → bytes`.
fn bytes_abs(l: Term) -> Term {
    Term::app(Term::spec_abs(bytes_spec(), Vec::new()), l)
}

/// `rep : string → list char`.
fn string_rep(l: Term) -> Term {
    Term::app(Term::spec_rep(string_spec(), Vec::new()), l)
}

/// `abs : list char → string`.
fn string_abs(l: Term) -> Term {
    Term::app(Term::spec_abs(string_spec(), Vec::new()), l)
}

/// `⊢ rep (abs l) = l` for the `string` newtype, given `l : list char`.
/// The unconditional newtype round-trip across the `string`/`list char`
/// seam, exposed for the codec layers ([`init::utf8`](crate::init::utf8) /
/// [`init::utf16`](crate::init::utf16)). Genuine: hypothesis- and
/// oracle-free.
pub fn string_rep_abs(l: &Term) -> Result<Thm> {
    rep_abs_newtype(string_spec(), l)
}

/// `⊢ rep (abs l) = l` for the `bytes` newtype, given `l : list u8`. The
/// unconditional newtype round-trip across the `bytes`/`list u8` seam,
/// exposed for the codec layers. Genuine: hypothesis- and oracle-free.
pub fn bytes_rep_abs(l: &Term) -> Result<Thm> {
    rep_abs_newtype(bytes_spec(), l)
}

/// `⊢ rep (abs l) = l` for a newtype `spec` over `list elem`, discharging
/// the always-true selector premise via β + [`truth`]. Shared by `bytes`
/// and `string` (both newtypes).
fn rep_abs_newtype(spec: TypeSpec, l: &Term) -> Result<Thm> {
    let fwd = Thm::spec_rep_abs_fwd(spec, Vec::new(), l.clone())?;
    // `fwd : ⊢ (λ_. T) l ⟹ (rep (abs l) = l)`; β-reduce the premise to
    // `T` and transport `⊢ T` across it.
    let (imp_p, _eq) = fwd.concl().as_app().ok_or(Error::NotAnEquation)?;
    let (_imp, prem) = imp_p.as_app().ok_or(Error::NotAnEquation)?;
    let prem_thm = Thm::beta_conv(prem.clone())?.sym()?.eq_mp(truth())?;
    fwd.imp_elim(prem_thm)
}

// ============================================================================
// Empty-sequence builders.
// ============================================================================

/// `bytes.empty := abs (list.nil u8) : bytes` — the empty byte string.
pub fn bytes_empty() -> Term {
    bytes_abs(nil(byte_elem()))
}

/// `string.empty := abs (list.nil char) : string` — the empty string.
pub fn string_empty() -> Term {
    string_abs(nil(char_elem()))
}

// ============================================================================
// Empty-sequence facts (`nil`-side).
// ============================================================================

/// `⊢ rep bytes.empty = list.nil u8` — the carrier of the empty byte
/// string is the empty `list u8`. Genuine: hypothesis- and oracle-free.
pub fn bytes_rep_empty() -> Result<Thm> {
    rep_abs_newtype(bytes_spec(), &nil(byte_elem()))
}

/// `⊢ rep string.empty = list.nil char` — the carrier of the empty
/// string is the empty `list char`. Genuine: hypothesis- and
/// oracle-free.
pub fn string_rep_empty() -> Result<Thm> {
    rep_abs_newtype(string_spec(), &nil(char_elem()))
}

/// `⊢ list.head (rep bytes.empty) = none` — the empty byte string has no
/// first element. Built on [`init::list::head_nil`] through the newtype
/// seam. Genuine: hypothesis- and oracle-free.
pub fn bytes_head_empty() -> Result<Thm> {
    let elem = byte_elem();
    // list.head (rep empty) = list.head (rep empty); rewrite
    // `rep empty → nil`, then collapse `head nil → none`.
    let lhs = Term::app(head(elem.clone()), bytes_rep(bytes_abs(nil(elem.clone()))));
    let refl = Thm::refl(lhs)?;
    let rep_empty = bytes_rep_empty()?; // rep empty = nil
    refl.rhs_conv(|t| t.rw_all(&rep_empty))?
        .trans(head_nil(&elem)?)
}

/// `⊢ list.head (rep string.empty) = none` — the empty string has no
/// first character. Built on [`init::list::head_nil`] through the
/// newtype seam. Genuine: hypothesis- and oracle-free.
pub fn string_head_empty() -> Result<Thm> {
    let elem = char_elem();
    let lhs = Term::app(head(elem.clone()), string_rep(string_abs(nil(elem.clone()))));
    let refl = Thm::refl(lhs)?;
    let rep_empty = string_rep_empty()?;
    refl.rhs_conv(|t| t.rw_all(&rep_empty))?
        .trans(head_nil(&elem)?)
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_core::defs::none;

    fn none_byte() -> Term {
        none(byte_elem())
    }

    fn none_char() -> Term {
        none(char_elem())
    }

    #[test]
    fn empties_are_well_typed() {
        assert_eq!(bytes_empty().type_of().unwrap(), Type::bytes());
        assert_eq!(string_empty().type_of().unwrap(), string_ty());
    }

    #[test]
    fn bytes_rep_empty_is_nil() {
        let thm = bytes_rep_empty().unwrap();
        assert!(thm.hyps().is_empty() && thm.has_no_obs());
        assert_eq!(thm.concl().as_eq().unwrap().1, &nil(byte_elem()));
    }

    #[test]
    fn string_rep_empty_is_nil() {
        let thm = string_rep_empty().unwrap();
        assert!(thm.hyps().is_empty() && thm.has_no_obs());
        assert_eq!(thm.concl().as_eq().unwrap().1, &nil(char_elem()));
    }

    #[test]
    fn bytes_head_empty_is_none() {
        let thm = bytes_head_empty().unwrap();
        assert!(
            thm.hyps().is_empty(),
            "bytes_head_empty is proved, not postulated"
        );
        assert!(thm.has_no_obs(), "bytes_head_empty is oracle-free");
        assert_eq!(thm.concl().as_eq().unwrap().1, &none_byte());
    }

    #[test]
    fn literal_coherence_blob_and_u8() {
        // Literal coherence (element level): a `Blob` literal denotes a
        // `bytes` value, and a `u8` literal denotes a `u8` (the element
        // type of `bytes`). These are exactly the types the surface
        // compiler's byte/byte-string literal lifters target.
        assert_eq!(Term::blob(vec![1u8, 2, 3]).type_of().unwrap(), Type::bytes());
        assert_eq!(Term::u8_lit(255).type_of().unwrap(), byte_elem());
        // The empty `Blob` and our `bytes.empty` are both `bytes` (their
        // equality is a `cons`-recursion fact, deferred — see SKELETONS).
        assert_eq!(Term::blob(Vec::<u8>::new()).type_of().unwrap(), Type::bytes());
        assert_eq!(bytes_empty().type_of().unwrap(), Type::bytes());
    }

    #[test]
    fn string_head_empty_is_none() {
        let thm = string_head_empty().unwrap();
        assert!(
            thm.hyps().is_empty(),
            "string_head_empty is proved, not postulated"
        );
        assert!(thm.has_no_obs(), "string_head_empty is oracle-free");
        assert_eq!(thm.concl().as_eq().unwrap().1, &none_char());
    }
}
