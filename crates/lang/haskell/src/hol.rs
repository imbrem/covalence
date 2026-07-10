//! The **HOL backend** (`hol` feature) — realizes the S-expression IR into a
//! *real kernel data structure*: the carved `sexpr` datatype from
//! `covalence-init`
//! ([`carved`](covalence_init::init::inductive::carved)), the exact same
//! untyped Lisp value that the kernel-side `sexpr_parse` reader produces.
//!
//! This is the "different implementation realizing the IR" point made
//! concrete: the SAME interchange IR and the SAME
//! [`realize`](crate::realize::realize) driver that the demo backends use,
//! but a backend targeting genuine kernel `Term`s instead of a `String`. It
//! sits at the SExpr boundary, so it serves the Haskell front end
//! (via [`crate::lower`]) and hand-written S-expression text
//! (via [`crate::sexpr::parse_sexpr`]) identically.
//!
//! # Why the carved `sexpr` datatype (untyped)
//!
//! Full HOL is *typed*, and realizing an arbitrary S-expression as a
//! well-typed HOL term would require type inference we deliberately do not do
//! here. The carved `sexpr` type is **untyped** (`atom bytes | snil | scons
//! sexpr sexpr`), so every IR construct maps to a Lisp S-expression with no
//! inference — yet the result is a bona-fide kernel `Term` in a carved
//! subtype, not a string.
//!
//! # The realization
//!
//! | IR construct       | carved `sexpr` value                          |
//! |--------------------|-----------------------------------------------|
//! | symbol `x`         | `atom "x"`                                     |
//! | nat atom `n`       | `atom "<decimal digits of n>"`                |
//! | string atom `s`    | `atom "<utf-8 bytes of s>"`                   |
//! | list `(e₁ … eₙ)`   | `scons e₁ (scons … (scons eₙ snil))`          |
//! | empty list `()`    | `snil`                                         |
//!
//! where `atom s` is `atom` applied to a bytes literal built via the
//! designated literal facade ([`covalence_hol_eval::mk_blob`] — never the
//! deprecated kernel literal constructors; see the toHOL purge ratchet).
//! The canonical Haskell lowering therefore lands `\x -> x` as
//! `(lambda x x)`, `let n = v in b` as `(let n v b)`, and `l + r` as
//! `(+ l r)` — the shapes are fixed by [`crate::lower`], not here.
//!
//! ## Atom byte conventions (matching `sexpr_parse`)
//!
//! `sexpr_parse` reads an atom as the *raw, uninterpreted run of bytes*
//! between delimiters — a number atom like `12` is simply the ASCII bytes
//! `b"12"`, not a decoded `nat`. This backend matches that:
//! [`HolBackend::nat`](crate::realize::Realize::nat) emits the decimal ASCII
//! digits of the covalence `Nat` (arbitrary precision), so `1` realizes to
//! the same atom the reader would build from the source text `1`.
//!
//! **String escaping choice:**
//! [`HolBackend::string`](crate::realize::Realize::string) realizes a string
//! atom as the atom of its **raw UTF-8 bytes, with no surrounding quotes and
//! no escaping**. This collapses the string/symbol distinction (both become
//! atoms) — a deliberate simplification for this untyped landing; a typed
//! realization would distinguish them. Because the bytes are raw, a string
//! containing whitespace or parentheses would *not* round-trip through the
//! reader as a single atom; that is out of scope here (see `SKELETONS.md`).

use covalence_hol_eval::mk_blob;
use covalence_init::Term;
use covalence_init::init::inductive::carved::{CarvedSExpr, carved};

use covalence_types::Nat;

use crate::realize::{Realize, Unsupported};

/// Errors from the [`HolBackend`].
#[derive(Clone, Debug)]
pub enum HolBackendError {
    /// An IR construct this backend does not realize.
    Unsupported(Unsupported),
    /// The carved `sexpr` kernel theory failed to build (should not happen in
    /// practice — the theory is a process-global constant).
    Carved(String),
}

impl From<Unsupported> for HolBackendError {
    fn from(u: Unsupported) -> Self {
        HolBackendError::Unsupported(u)
    }
}

impl core::fmt::Display for HolBackendError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            HolBackendError::Unsupported(u) => u.fmt(f),
            HolBackendError::Carved(e) => write!(f, "carved sexpr theory unavailable: {e}"),
        }
    }
}

impl std::error::Error for HolBackendError {}

/// A [`Realize`](crate::realize::Realize) backend producing carved `sexpr`
/// kernel [`Term`]s — genuine kernel data, not a string. See the module docs
/// for the realization table.
#[derive(Clone, Copy, Debug, Default)]
pub struct HolBackend;

impl HolBackend {
    /// The process-global carved `sexpr` theory (constructors `atom`/`snil`/
    /// `scons`), or a [`HolBackendError::Carved`] if it failed to build.
    fn theory() -> Result<&'static CarvedSExpr, HolBackendError> {
        carved().map_err(|e| HolBackendError::Carved(e.to_string()))
    }

    /// `atom <bytes>` — the carved `atom` constructor applied to a bytes
    /// literal (built via [`mk_blob`], the designated literal facade),
    /// matching `sexpr_parse`'s uninterpreted-byte-run atoms.
    fn atom(bytes: Vec<u8>) -> Result<Term, HolBackendError> {
        let c = Self::theory()?;
        Ok(Term::app(c.atom.clone(), mk_blob(bytes)))
    }

    /// `snil` — the empty S-expression list.
    fn snil() -> Result<Term, HolBackendError> {
        Ok(Self::theory()?.snil.clone())
    }

    /// `scons h t` — cons `h` onto the list `t`.
    fn scons(h: Term, t: Term) -> Result<Term, HolBackendError> {
        let c = Self::theory()?;
        Ok(Term::app(Term::app(c.scons.clone(), h), t))
    }
}

impl Realize for HolBackend {
    type Out = Term;
    type Error = HolBackendError;

    fn nat(&mut self, n: &Nat) -> Result<Term, HolBackendError> {
        // ASCII decimal digits — the byte run `sexpr_parse` would read.
        Self::atom(n.to_string().into_bytes())
    }

    fn string(&mut self, s: &str) -> Result<Term, HolBackendError> {
        // Raw UTF-8 bytes, unquoted/unescaped (see module docs).
        Self::atom(s.as_bytes().to_vec())
    }

    fn symbol(&mut self, s: &str) -> Result<Term, HolBackendError> {
        Self::atom(s.as_bytes().to_vec())
    }

    fn list(&mut self, items: Vec<Term>) -> Result<Term, HolBackendError> {
        // `(e₁ … eₙ)` — the scons-chain ending in snil (snil itself for `()`).
        let mut acc = Self::snil()?;
        for it in items.into_iter().rev() {
            acc = Self::scons(it, acc)?;
        }
        Ok(acc)
    }
}
