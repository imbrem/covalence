//! The **covalence `/lisp` demo** — a clear Lisp whose reductions are kernel
//! theorems.
//!
//! Layers:
//!
//! - [`Lisp`] — the surface trait. It fixes the Forth-style atom-resolution
//!   order (dictionary → numeral → symbol) as three methods
//!   ([`resolve_symbol`](Lisp::resolve_symbol) /
//!   [`resolve_number`](Lisp::resolve_number) /
//!   [`resolve_string`](Lisp::resolve_string)) plus an
//!   [`eval`](Lisp::eval) entry point, and provides a default
//!   [`lower`](Lisp::lower) folding a parsed [`SExpr`] into a
//!   [`Term`](Lisp::Term) via those three. Kernel-agnostic.
//!
//! - [`reader`] — a thin wrapper over [`covalence_sexp::parse`].
//!
//! - [`hol`] (feature `hol`) — the concrete kernel instance:
//!   [`hol::LispHol`] implements [`Lisp`] by lowering S-expressions to carved
//!   `sexpr` kernel [`covalence_init::Term`]s, and [`hol::SymbolicStrategy`]
//!   is a [`covalence_repl_core::ReductionStrategy`] proving reductions like
//!   `⊢ (car (cons a b)) = a` by composing the carved carrier's computation
//!   laws — no new trusted kernel rules.
//!
//! The REPL only ever prints a value read off a genuine kernel theorem: the
//! reduction path returns `Result<Thm, _>` and the printed term is the
//! theorem's right-hand side. See `notes/vibes/lisp/initial-ideas/` for the
//! design, and `SKELETONS.md` for deferred work (notably the aspirational
//! `Reduces` *relation*, of which the shipped `⊢ input = output` is the
//! deterministic special case).

#![forbid(unsafe_code)]

pub mod reader;

#[cfg(feature = "hol")]
pub mod hol;

#[cfg(feature = "hol")]
pub mod carrier;

#[cfg(feature = "hol")]
pub mod defs;

#[cfg(feature = "hol")]
pub mod semantics;

#[cfg(feature = "hol")]
pub mod int_backend;

#[cfg(feature = "hol")]
pub mod relation;

#[cfg(feature = "hol")]
pub mod session;

#[cfg(feature = "hol")]
pub mod acl2;

#[cfg(feature = "hol")]
pub mod book;

use covalence_sexp::SExpr;

/// The clear-Lisp surface: Forth-style atom resolution + an eval entry.
///
/// Atom resolution is a fixed three-step fallthrough (dictionary → numeral →
/// bare symbol), each a method here; the default [`lower`](Lisp::lower) folds
/// a parsed [`SExpr`] tree into a [`Term`](Lisp::Term) by applying it at
/// every atom and building lists via [`nil`](Lisp::nil) / [`cons`](Lisp::cons).
pub trait Lisp {
    /// The lowered term type (a kernel term, or a small AST).
    type Term;
    /// A lowering failure (e.g. an unbuildable kernel term).
    type Error;

    /// Step 1: a symbol found in the dictionary, or a bare symbol atom.
    ///
    /// The minimal instance treats every non-numeral atom as a bare symbol;
    /// a richer dialect looks the head up in a `defun` dictionary first.
    fn resolve_symbol(&self, name: &str) -> Result<Self::Term, Self::Error>;

    /// Step 2: a numeral, if `text` is one under this dialect's numeral
    /// policy. `None` falls through to [`resolve_symbol`](Lisp::resolve_symbol).
    fn resolve_number(&self, text: &str) -> Option<Result<Self::Term, Self::Error>>;

    /// A string / bytes literal atom (`"..."`, `b"..."`, `json"..."`, …).
    fn resolve_string(&self, format: &str, bytes: &[u8]) -> Result<Self::Term, Self::Error>;

    /// The empty list `()`.
    fn nil(&self) -> Result<Self::Term, Self::Error>;

    /// `cons head tail` — prepend `head` onto the list `tail`.
    fn cons(&self, head: Self::Term, tail: Self::Term) -> Result<Self::Term, Self::Error>;

    /// Evaluate a lowered term to its result form.
    fn eval(&self, term: &Self::Term) -> Result<Self::Eval, Self::EvalError>;

    /// The evaluation result (for the kernel instance, a reduction theorem).
    type Eval;
    /// An evaluation failure.
    type EvalError;

    /// Resolve one atom via the Forth fallthrough: numeral, then symbol.
    fn resolve_atom(&self, atom: &covalence_sexp::Atom) -> Result<Self::Term, Self::Error> {
        match atom {
            covalence_sexp::Atom::Symbol(s) => match self.resolve_number(s) {
                Some(r) => r,
                None => self.resolve_symbol(s),
            },
            covalence_sexp::Atom::Str { format, bytes } => self.resolve_string(format, bytes),
        }
    }

    /// Fold a parsed [`SExpr`] into a [`Term`](Lisp::Term): atoms resolve via
    /// [`resolve_atom`](Lisp::resolve_atom), lists build a `cons`-spine ending
    /// in [`nil`](Lisp::nil).
    fn lower(&self, sexpr: &SExpr) -> Result<Self::Term, Self::Error> {
        match sexpr {
            SExpr::Atom(a) => self.resolve_atom(a),
            SExpr::List(items) => {
                let mut acc = self.nil()?;
                for it in items.iter().rev() {
                    let head = self.lower(it)?;
                    acc = self.cons(head, acc)?;
                }
                Ok(acc)
            }
        }
    }
}
