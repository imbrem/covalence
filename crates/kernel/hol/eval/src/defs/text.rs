//! Characters and strings — the text element/sequence types.
//!
//! ⚠️ **TODO-level definitions** (broadly-correct shapes, not
//! finalized — see the `defs` module docs).
//!
//! ## `char`
//!
//! ```text
//! char := { c : nat | c < 0xD800 ∨ (0xDFFF < c ∧ c < 0x110000) }
//! ```
//!
//! A Unicode **scalar value**: the natural numbers carved down to the
//! Unicode scalar range `0 ..= 0x10FFFF` **excluding** the UTF-16
//! surrogate block `0xD800 ..= 0xDFFF` (which are not scalar values).
//! The predicate is disjunctive — below the surrogate block, or above it
//! and within range — matching Rust's `char` / the Unicode definition of
//! a scalar value.
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

use covalence_core::hol;
use covalence_core::term::{Term, Type};

use crate::defs::Canonical;
use crate::defs::TypeSpec;
use crate::defs::list;
use crate::defs::nat_lt;

/// The exclusive upper bound on Unicode scalar values: `0x110000`
/// (`1114112`).
pub const CHAR_MAX_EXCL: u64 = 0x110000;

/// First UTF-16 surrogate codepoint, `0xD800`. The surrogate block
/// `0xD800 ..= 0xDFFF` is **excluded** from `char` (not scalar values).
pub const SURROGATE_LO: u64 = 0xD800;

/// Last UTF-16 surrogate codepoint, `0xDFFF`.
pub const SURROGATE_HI: u64 = 0xDFFF;

// ============================================================================
// `char := { c : nat | c < 0xD800 ∨ (0xDFFF < c ∧ c < 0x110000) }`
// ============================================================================

/// `λc:nat. (c < 0xD800) ∨ (0xDFFF < c ∧ c < 0x110000)` — the selector
/// predicate carving `char` out of `nat`: the Unicode scalar-value range
/// (below the surrogate block, or above it and within `0x110000`).
fn char_predicate() -> Term {
    let c = Term::free("c", Type::nat());
    let lt = |a: Term, b: Term| Term::app(Term::app(nat_lt(), a), b);
    // c < 0xD800
    let below = lt(c.clone(), Term::nat_lit(SURROGATE_LO));
    // 0xDFFF < c  ∧  c < 0x110000
    let above = hol::hol_and(
        lt(Term::nat_lit(SURROGATE_HI), c.clone()),
        lt(c.clone(), Term::nat_lit(CHAR_MAX_EXCL)),
    );
    hol::pub_abs("c", Type::nat(), hol::hol_or(below, above))
}

/// `char := { c : nat | c < 0xD800 ∨ (0xDFFF < c ∧ c < 0x110000) }` — a
/// Unicode scalar value, a subtype of `nat`.
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
    /// subtype `abs`, it junk-saturates on non-scalar codepoints; the
    /// `char.code (char.mk n) = n` round-trip is conditional on `n` being
    /// a Unicode scalar value (`n < 0xD800 ∨ (0xDFFF < n ∧ n < 0x110000)`,
    /// see `init/char.rs`).
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
