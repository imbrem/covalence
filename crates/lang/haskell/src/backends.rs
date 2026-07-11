//! Demonstration [`Realize`] backends showing the pluggability of the
//! SExpr ⇒ backend seam.
//!
//! - [`TextBackend`] realizes the whole IR back to canonical S-expression
//!   text — it agrees exactly with [`SExpr::to_text`](crate::sexpr::SExpr::to_text).
//! - [`PeanoBackend`] is an IR ⇒ IR transform that is the identity *except*
//!   on natural-number atoms, which it realizes as Peano numerals — the same
//!   IR, a different numeric strategy.
//! - [`NoLitBackend`] leaves [`Realize::nat`] at its default, so any form
//!   containing a natural-number atom fails to realize while literal-free
//!   ones succeed — a backend supporting a strict subset.
//! - [`DesugarBackend`] is an IR ⇒ IR transform that rewrites the *sugar
//!   heads* (`list` / `unit`) into a smaller cons/nil core — the structural
//!   analogue of [`PeanoBackend`]'s numeral rewrite, showing the IR is a real
//!   interchange point where a backend can restructure, not just relabel atoms.

use covalence_types::Nat;

use crate::realize::{Realize, Unsupported};
use crate::sexpr::{SExpr, quote_string};

/// The error type shared by the demo backends.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BackendError(pub Unsupported);

impl From<Unsupported> for BackendError {
    fn from(u: Unsupported) -> Self {
        BackendError(u)
    }
}

impl core::fmt::Display for BackendError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.0.fmt(f)
    }
}

impl std::error::Error for BackendError {}

/// Realizes the entire IR to canonical S-expression text (the same text
/// [`SExpr::to_text`](crate::sexpr::SExpr::to_text) prints).
#[derive(Clone, Copy, Debug, Default)]
pub struct TextBackend;

impl Realize for TextBackend {
    type Out = String;
    type Error = BackendError;

    fn nat(&mut self, n: &Nat) -> Result<String, BackendError> {
        Ok(n.to_string())
    }

    fn string(&mut self, s: &str) -> Result<String, BackendError> {
        Ok(quote_string(s))
    }

    fn symbol(&mut self, s: &str) -> Result<String, BackendError> {
        Ok(s.to_string())
    }

    fn list(&mut self, items: Vec<String>) -> Result<String, BackendError> {
        Ok(format!("({})", items.join(" ")))
    }
}

/// An IR ⇒ IR backend: the identity except that natural-number atoms are
/// realized as Peano numerals — `0` ⇝ `Z`, `n` ⇝ `(S (S … Z))` with `n`
/// applications of `S`. Print the result with
/// [`SExpr::to_text`](crate::sexpr::SExpr::to_text).
#[derive(Clone, Copy, Debug, Default)]
pub struct PeanoBackend;

impl Realize for PeanoBackend {
    type Out = SExpr;
    type Error = BackendError;

    fn nat(&mut self, n: &Nat) -> Result<SExpr, BackendError> {
        let mut acc = SExpr::sym("Z");
        let mut i = n.clone();
        // Arbitrary precision: count down the covalence Nat itself.
        while !i.is_zero() {
            acc = SExpr::list(vec![SExpr::sym("S"), acc]);
            i -= Nat::one();
        }
        Ok(acc)
    }

    fn string(&mut self, s: &str) -> Result<SExpr, BackendError> {
        Ok(SExpr::string(s))
    }

    fn symbol(&mut self, s: &str) -> Result<SExpr, BackendError> {
        Ok(SExpr::sym(s))
    }

    fn list(&mut self, items: Vec<SExpr>) -> Result<SExpr, BackendError> {
        Ok(SExpr::List(items))
    }
}

/// A strict-subset backend: it realizes everything *except* natural-number
/// atoms, leaving [`Realize::nat`] at its failing default. Realizing a form
/// that mentions a nat atom returns [`Unsupported`]; literal-free forms
/// realize fine (to canonical text, like [`TextBackend`]).
#[derive(Clone, Copy, Debug, Default)]
pub struct NoLitBackend;

impl Realize for NoLitBackend {
    type Out = String;
    type Error = BackendError;

    // Note: `nat` deliberately NOT overridden — it keeps the default error.

    fn string(&mut self, s: &str) -> Result<String, BackendError> {
        TextBackend.string(s)
    }

    fn symbol(&mut self, s: &str) -> Result<String, BackendError> {
        TextBackend.symbol(s)
    }

    fn list(&mut self, items: Vec<String>) -> Result<String, BackendError> {
        TextBackend.list(items)
    }
}

/// An IR ⇒ IR backend that **desugars structural heads**: it is the identity
/// except that it rewrites the sugar lists produced by the canonical lowering
/// into a smaller cons/nil core —
///
/// - `(list e1 … en)` ⇝ `(cons e1 (cons … (cons en nil)))` (`(list)` ⇝ `nil`);
/// - `(unit)` ⇝ the symbol `unit`.
///
/// Everything else (including `if` / `tuple` lists, applications, lambdas) is
/// passed through unchanged. This is the structural counterpart to
/// [`PeanoBackend`]'s numeral rewrite: the shared IR is a genuine interchange
/// point at which a backend may *restructure* forms, not merely relabel atoms.
/// Print the result with
/// [`SExpr::to_text`](crate::sexpr::SExpr::to_text).
#[derive(Clone, Copy, Debug, Default)]
pub struct DesugarBackend;

impl Realize for DesugarBackend {
    type Out = SExpr;
    type Error = BackendError;

    fn nat(&mut self, n: &Nat) -> Result<SExpr, BackendError> {
        Ok(SExpr::Nat(n.clone()))
    }

    fn string(&mut self, s: &str) -> Result<SExpr, BackendError> {
        Ok(SExpr::string(s))
    }

    fn symbol(&mut self, s: &str) -> Result<SExpr, BackendError> {
        Ok(SExpr::sym(s))
    }

    fn list(&mut self, items: Vec<SExpr>) -> Result<SExpr, BackendError> {
        // The items are already desugared; inspect the head symbol.
        match items.first() {
            Some(SExpr::Sym(h)) if h == "list" => {
                // Fold the (already-desugared) elements into a cons/nil chain.
                let mut acc = SExpr::sym("nil");
                for it in items.into_iter().skip(1).rev() {
                    acc = SExpr::list(vec![SExpr::sym("cons"), it, acc]);
                }
                Ok(acc)
            }
            Some(SExpr::Sym(h)) if h == "unit" && items.len() == 1 => Ok(SExpr::sym("unit")),
            _ => Ok(SExpr::List(items)),
        }
    }
}
