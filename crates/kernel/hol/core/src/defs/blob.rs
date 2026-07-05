//! `bytes := list u8`, plus the bytes-operations TermSpec constants
//! `bytesCat`, `bytesConsNat`, `bytesLen`, `bytesAt`, `bytesSlice`.
//!
//! `bytes` is a `newtype` over `list u8`, so the structural ops bridge
//! through the `abs`/`rep` coercions ([`Term::spec_abs`] /
//! [`Term::spec_rep`] at [`bytes_spec`]) down to the corresponding
//! `list` operations: `rep : bytes → list u8` unwraps, `abs : list u8
//! → bytes` wraps back up.
//!
//! `bytesLen`/`bytesCat`/`bytesSlice` are *defined* here that way —
//! their bodies match the literal-level semantics of the certificate
//! path (`list.length` = `blob.len`, `list.cat` = `blob.cat`,
//! `take len ∘ skip start` = the saturating `blob.slice` with its
//! `(start, len)` argument convention).
//!
//! `bytesConsNat`/`bytesAt` stay **declaration-only**: both cross
//! between `nat` and the element type `u8`, and the catalogue does not
//! yet carry a `nat ↔ u8` (i.e. `bits ↔ nat`) conversion. They still
//! **reduce on `Blob` literals** via the certificate path; they just
//! lack open-form definitional bodies until that conversion lands.

use std::sync::LazyLock;

use crate::hol;
use crate::term::{Term, Type};

use super::bits::u8_ty;
use super::canonical::Canonical;
use super::list::{list, list_cat, list_length, list_skip, list_take};
use super::spec::TypeSpec;

/// `bytes := list u8` — the type of `TermKind::Blob` literals.
/// Derived TypeSpec (Canonical::Bytes); was the kernel-primitive
/// `TypeKind::Bytes` before the spec migration.
pub fn bytes_spec() -> TypeSpec {
    static LAZY: LazyLock<TypeSpec> = LazyLock::new(|| {
        let carrier = list(u8_ty());
        TypeSpec::newtype(Canonical::Bytes, carrier)
    });
    LAZY.clone()
}

// ---- The `abs`/`rep` bridge between `bytes` and `list u8` ----

/// `rep b : list u8` — unwrap a `bytes` value to its underlying list.
fn rep(b: Term) -> Term {
    Term::app(Term::spec_rep(bytes_spec(), Vec::new()), b)
}

/// `abs l : bytes` — wrap a `list u8` back into a `bytes` value.
fn abs(l: Term) -> Term {
    Term::app(Term::spec_abs(bytes_spec(), Vec::new()), l)
}

// ---- Bytes operations as TermSpec constants ----

fn bytes_len_body() -> Term {
    // λb. list.length (rep b)
    let b = Term::free("b", Type::bytes());
    let len = Term::app(list_length(u8_ty()), rep(b));
    hol::pub_abs("b", Type::bytes(), len)
}

let_term! {
    /// `bytesLen : bytes → nat` ≡ `λb. list.length (rep b)` — the number
    /// of bytes, via the underlying `list u8`.
    bytes_len_spec, bytes_len, Canonical::BytesLen, bytes_len_body()
}

fn bytes_cat_body() -> Term {
    // λa b. abs (list.cat (rep a) (rep b))
    let a = Term::free("a", Type::bytes());
    let b = Term::free("b", Type::bytes());
    let catted = Term::app(Term::app(list_cat(u8_ty()), rep(a)), rep(b));
    let wrapped = abs(catted);
    let lam_b = hol::pub_abs("b", Type::bytes(), wrapped);
    hol::pub_abs("a", Type::bytes(), lam_b)
}

let_term! {
    /// `bytesCat : bytes → bytes → bytes` ≡
    /// `λa b. abs (list.cat (rep a) (rep b))` — concatenation.
    bytes_cat_spec, bytes_cat, Canonical::BytesCat, bytes_cat_body()
}

fn bytes_slice_body() -> Term {
    // λb start len. abs (list.take len (list.skip start (rep b)))
    let b = Term::free("b", Type::bytes());
    let start = Term::free("start", Type::nat());
    let len = Term::free("len", Type::nat());
    let skipped = Term::app(Term::app(list_skip(u8_ty()), start.clone()), rep(b));
    let taken = Term::app(Term::app(list_take(u8_ty()), len.clone()), skipped);
    let wrapped = abs(taken);
    let lam_len = hol::pub_abs("len", Type::nat(), wrapped);
    let lam_start = hol::pub_abs("start", Type::nat(), lam_len);
    hol::pub_abs("b", Type::bytes(), lam_start)
}

let_term! {
    /// `bytesSlice : bytes → nat → nat → bytes` ≡
    /// `λb start len. abs (list.take len (list.skip start (rep b)))` —
    /// the saturating slice starting at `start` of length `len`
    /// (matching `blob.slice`'s `(start, len)` convention).
    bytes_slice_spec, bytes_slice, Canonical::BytesSlice, bytes_slice_body()
}

term_decl! {
    /// `bytesConsNat : nat → bytes → bytes` — cons a nat (mod 256)
    /// onto the front of a bytes value. **Declaration-only**: needs a
    /// `nat → u8` conversion the catalogue does not yet carry. Closed
    /// forms reduce via the certificate path.
    bytes_cons_nat_spec, bytes_cons_nat, Canonical::BytesConsNat,
    Type::fun(Type::nat(), Type::fun(Type::bytes(), Type::bytes()))
}

term_decl! {
    /// `bytesAt : bytes → nat → nat` — byte at index, 0 if OOB.
    /// **Declaration-only**: needs a `u8 → nat` conversion the
    /// catalogue does not yet carry. Closed forms reduce via the
    /// certificate path.
    bytes_at_spec, bytes_at, Canonical::BytesAt,
    Type::fun(Type::bytes(), Type::fun(Type::nat(), Type::nat()))
}
