//! The **HOL backend** (`hol` feature) — lowers the parsed Haskell subset into
//! a *real kernel data structure*: the carved `sexpr` datatype from
//! `covalence-init`
//! ([`carved`](covalence_init::init::inductive::carved)), the exact same
//! untyped Lisp value that `sexpr_parse` produces.
//!
//! This is the "different implementation lowering a subset" point made
//! concrete: the SAME parser and the SAME [`Lower`](crate::lower::Lower) driver
//! that the string demo backends use, but a NEW backend targeting genuine
//! kernel `Term`s instead of a `String`.
//!
//! # Why the carved `sexpr` datatype (untyped)
//!
//! Full HOL is *typed*, and lowering a Haskell expression to a well-typed HOL
//! term would require type inference we deliberately do not do here. The carved
//! `sexpr` type is **untyped** (`atom bytes | snil | scons sexpr sexpr`), so
//! every Haskell construct maps to a Lisp S-expression with no inference — yet
//! the result is a bona-fide kernel `Term` in a carved subtype, not a string.
//!
//! # The lowering (Lisp S-expressions)
//!
//! | Haskell            | S-expression                                  |
//! |--------------------|-----------------------------------------------|
//! | `var x`            | `atom "x"`                                     |
//! | `nat_lit n`        | `atom "<decimal digits of n>"`                |
//! | `str_lit s`        | `atom "<utf-8 bytes of s>"`                   |
//! | `app f x`          | `(f x)`                                        |
//! | `lam p b`          | `(lambda p b)`                                 |
//! | `let n v b`        | `(let n v b)`                                  |
//! | `binop op l r`     | `(op l r)`                                     |
//!
//! where a list `(e₁ … eₙ)` is the `scons`-chain
//! `scons e₁ (scons … (scons eₙ snil))` and `atom s` is `atom` applied to a
//! byte literal (built via the `covalence_init::lit` facade).
//!
//! ## Atom byte conventions (matching `sexpr_parse`)
//!
//! `sexpr_parse` reads an atom as the *raw, uninterpreted run of bytes* between
//! delimiters — a number atom like `12` is simply the ASCII bytes `b"12"`, not
//! a decoded `nat`. This backend matches that: [`HolLower::nat_lit`] emits the
//! decimal ASCII digits, so `1` lowers to the same atom the reader would build
//! from the source text `1`.
//!
//! **String escaping choice:** [`HolLower::str_lit`] lowers a string literal to
//! the atom of its **raw UTF-8 bytes, with no surrounding quotes and no
//! escaping**. This collapses the Haskell string/identifier distinction (both
//! become atoms) — a deliberate simplification for this untyped landing; a
//! typed lowering would distinguish them. Because the bytes are raw, a string
//! containing whitespace or parentheses would *not* round-trip through the
//! reader as a single atom; that is out of scope here (see `SKELETONS.md`).

use covalence_init::Term;
use covalence_init::init::inductive::carved::{CarvedSExpr, carved};

use crate::lower::{Lower, Unsupported};

/// Errors from the [`HolLower`] backend.
#[derive(Clone, Debug)]
pub enum HolLowerError {
    /// A Haskell construct this backend does not lower.
    Unsupported(Unsupported),
    /// The carved `sexpr` kernel theory failed to build (should not happen in
    /// practice — the theory is a process-global constant).
    Carved(String),
}

impl From<Unsupported> for HolLowerError {
    fn from(u: Unsupported) -> Self {
        HolLowerError::Unsupported(u)
    }
}

impl core::fmt::Display for HolLowerError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            HolLowerError::Unsupported(u) => u.fmt(f),
            HolLowerError::Carved(e) => write!(f, "carved sexpr theory unavailable: {e}"),
        }
    }
}

impl std::error::Error for HolLowerError {}

/// A [`Lower`](crate::lower::Lower) backend producing carved `sexpr` kernel
/// [`Term`]s — genuine kernel data, not a string. See the module docs for the
/// lowering table.
#[derive(Clone, Copy, Debug, Default)]
pub struct HolLower;

impl HolLower {
    /// The process-global carved `sexpr` theory (constructors `atom`/`snil`/
    /// `scons`), or a [`HolLowerError::Carved`] if it failed to build.
    fn theory() -> Result<&'static CarvedSExpr, HolLowerError> {
        carved().map_err(|e| HolLowerError::Carved(e.to_string()))
    }

    /// `atom <bytes>` — the carved `atom` constructor applied to a byte
    /// literal (built via the `covalence_init::lit` facade, the sanctioned
    /// literal chokepoint), matching `sexpr_parse`'s uninterpreted-byte-run
    /// atoms.
    fn atom(bytes: Vec<u8>) -> Result<Term, HolLowerError> {
        let c = Self::theory()?;
        Ok(Term::app(
            c.atom.clone(),
            covalence_init::lit::mk_blob(bytes),
        ))
    }

    /// `snil` — the empty S-expression list.
    fn snil() -> Result<Term, HolLowerError> {
        Ok(Self::theory()?.snil.clone())
    }

    /// `scons h t` — cons `h` onto the list `t`.
    fn scons(h: Term, t: Term) -> Result<Term, HolLowerError> {
        let c = Self::theory()?;
        Ok(Term::app(Term::app(c.scons.clone(), h), t))
    }

    /// Build the proper list `(e₁ … eₙ)` as the `scons`-chain ending in `snil`.
    fn list(items: Vec<Term>) -> Result<Term, HolLowerError> {
        let mut acc = Self::snil()?;
        for it in items.into_iter().rev() {
            acc = Self::scons(it, acc)?;
        }
        Ok(acc)
    }
}

impl Lower for HolLower {
    type Out = Term;
    type Error = HolLowerError;

    fn nat_lit(&mut self, n: u128) -> Result<Term, HolLowerError> {
        // ASCII decimal digits — the byte run `sexpr_parse` would read.
        Self::atom(n.to_string().into_bytes())
    }

    fn str_lit(&mut self, s: &str) -> Result<Term, HolLowerError> {
        // Raw UTF-8 bytes, unquoted/unescaped (see module docs).
        Self::atom(s.as_bytes().to_vec())
    }

    fn var(&mut self, name: &str) -> Result<Term, HolLowerError> {
        Self::atom(name.as_bytes().to_vec())
    }

    fn app(&mut self, f: Term, x: Term) -> Result<Term, HolLowerError> {
        // (f x)
        Self::list(vec![f, x])
    }

    fn lam(&mut self, param: &str, body: Term) -> Result<Term, HolLowerError> {
        // (lambda <param> <body>)
        let kw = Self::atom(b"lambda".to_vec())?;
        let p = Self::atom(param.as_bytes().to_vec())?;
        Self::list(vec![kw, p, body])
    }

    fn let_(&mut self, name: &str, val: Term, body: Term) -> Result<Term, HolLowerError> {
        // (let <name> <val> <body>)
        let kw = Self::atom(b"let".to_vec())?;
        let nm = Self::atom(name.as_bytes().to_vec())?;
        Self::list(vec![kw, nm, val, body])
    }

    fn binop(&mut self, op: &str, l: Term, r: Term) -> Result<Term, HolLowerError> {
        // (<op> l r)
        let o = Self::atom(op.as_bytes().to_vec())?;
        Self::list(vec![o, l, r])
    }
}
