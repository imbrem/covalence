//! Characters and strings — the text element/sequence types.
//!
//! ⚠️ **TODO-level definitions** (broadly-correct shapes, not
//! finalized — see the `defs` module docs).
//!
//! ## `char`
//!
//! ```text
//! char := { c : nat | c < 0x110000 }
//! ```
//!
//! A Unicode *codepoint*: the natural numbers carved down to the
//! Unicode codepoint range `0 ..= 0x10FFFF` (`0x110000` values). The
//! bound is **contiguous**, so it *includes* the UTF-16 surrogate gap
//! `0xD800 ..= 0xDFFF`. A strict Unicode *scalar value* would exclude
//! the surrogates, but that needs a disjunctive predicate
//! (`c < 0xD800 ∨ (0xDFFF < c ∧ c < 0x110000)`) which buys nothing at
//! this stage; the contiguous range is the simplest correct carve. (The
//! surrogate carve is recorded as future work — see `SKELETONS.md`.)
//!
//! `char.code : char → nat` and `char.mk : nat → char` are the named
//! `rep` / `abs` coercions across the subtype boundary.
//!
//! ## `string`
//!
//! ```text
//! string := list char
//! ```
//!
//! A string as a sequence of Unicode codepoints — a newtype over
//! `list char`, exactly mirroring `bytes := list u8`. UTF-8-as-bytes is
//! a separate *encoding* concern (a `string ↔ bytes` codec) layered on
//! top, not the logical model.

use std::sync::LazyLock;

use crate::hol;
use crate::term::{Term, Type};

use super::canonical::Canonical;
use super::list::list;
use super::nat::nat_lt;
use super::spec::TypeSpec;

/// The exclusive upper bound on Unicode codepoints: `0x110000`
/// (`1114112`). A codepoint is any `nat` strictly below this.
pub const CHAR_MAX_EXCL: u64 = 0x110000;

// ============================================================================
// `char := { c : nat | c < 0x110000 }`
// ============================================================================

/// `λc:nat. nat.lt c 0x110000` — the selector predicate carving `char`
/// out of `nat` (the Unicode codepoint range).
fn char_predicate() -> Term {
    let c = Term::free("c", Type::nat());
    let in_range = Term::app(
        Term::app(nat_lt(), c.clone()),
        Term::nat_lit(CHAR_MAX_EXCL),
    );
    hol::pub_abs("c", Type::nat(), in_range)
}

/// `char := { c : nat | c < 0x110000 }` — a Unicode codepoint, a subtype
/// of `nat`.
pub fn char_spec() -> TypeSpec {
    static LAZY: LazyLock<TypeSpec> =
        LazyLock::new(|| TypeSpec::subtype(Canonical::Char, Type::nat(), char_predicate()));
    LAZY.clone()
}

/// `char` — the Unicode-codepoint type.
pub fn char_ty() -> Type {
    static LAZY: LazyLock<Type> = LazyLock::new(|| Type::spec(char_spec(), vec![]));
    LAZY.clone()
}

// ---- The `abs`/`rep` bridge between `char` and `nat` ----

fn char_code_body() -> Term {
    // λc:char. rep c   — the codepoint of a character.
    let c = Term::free("c", char_ty());
    let rep_c = Term::app(Term::spec_rep(char_spec(), Vec::new()), c);
    hol::pub_abs("c", char_ty(), rep_c)
}

let_term! {
    /// `char.code : char → nat` ≡ `λc. rep c` — the codepoint of a
    /// character (the named `rep` coercion `char → nat`).
    char_code_spec, char_code, Canonical::CharCode, char_code_body()
}

fn char_mk_body() -> Term {
    // λn:nat. abs n   — the character with codepoint `n`.
    let n = Term::free("n", Type::nat());
    let abs_n = Term::app(Term::spec_abs(char_spec(), Vec::new()), n);
    hol::pub_abs("n", Type::nat(), abs_n)
}

let_term! {
    /// `char.mk : nat → char` ≡ `λn. abs n` — the character with a given
    /// codepoint (the named `abs` coercion `nat → char`). Like any
    /// subtype `abs`, it junk-saturates on out-of-range codepoints; the
    /// `char.code (char.mk n) = n` round-trip is conditional on
    /// `n < 0x110000` (see `init/char.rs`).
    char_mk_spec, char_mk, Canonical::CharMk, char_mk_body()
}

// ============================================================================
// `string := list char`
// ============================================================================

/// `string := list char` — a sequence of Unicode codepoints. A newtype
/// over `list char`, mirroring `bytes := list u8`.
pub fn string_spec() -> TypeSpec {
    static LAZY: LazyLock<TypeSpec> = LazyLock::new(|| {
        let carrier = list(char_ty());
        TypeSpec::newtype(Canonical::String, carrier)
    });
    LAZY.clone()
}

/// `string` — the string type.
pub fn string_ty() -> Type {
    static LAZY: LazyLock<Type> = LazyLock::new(|| Type::spec(string_spec(), vec![]));
    LAZY.clone()
}
