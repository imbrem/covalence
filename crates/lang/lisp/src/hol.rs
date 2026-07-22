//! The **HOL backend** (`hol` feature): the concrete kernel instance of the
//! Lisp surface + the symbolic reduction strategy.
//!
//! - [`LispHol`] implements [`crate::LispDatumSyntax`], lowering S-expressions to carved
//!   `sexpr` kernel [`Term`]s (atoms via `atom (mk_blob …)`, lists via the
//!   carved `scons`/`snil`) — the same untyped Lisp value the kernel-side
//!   `sexpr_parse` reader produces, and the same realization
//!   `covalence-haskell`'s `HolBackend` uses.
//!
//! - [`SymbolicStrategy`] implements
//!   [`covalence_repl_core::ReductionStrategy`], proving reductions like
//!   `⊢ (car (cons a b)) = a` by **composing** the carved carrier's proved
//!   computation laws (`CarvedSExpr::proj_scons`). It mints **no new trusted
//!   kernel rules** — every theorem is derived from existing ones.
//!
//! Note on term shape: `LispHol::lower` builds Lisp *data* (`scons`-trees).
//! [`SymbolicStrategy`] operates on Lisp *operator applications* — the head
//! `car`/`cdr` applied to `cons h t` — which is the `⊢ input = output`
//! equational special case of the aspirational `Reduces` relation (see
//! the generated open-work index). Building the operator-application form from data (an
//! `eval` that walks a `scons`-tree and applies the `car`/`cdr`/`cons`
//! operators) is future work.

use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::mk_blob;
use covalence_init::Term;
use covalence_init::init::inductive::carved::{CarvedSExpr, carved};
use covalence_init::init::lisp::{Lisp as KernelLisp, lisp};

use covalence_repl_core::ReductionStrategy;
use covalence_sexpr_api::SExprSyntax;

use crate::LispDatumSyntax;

/// Errors from the HOL backend.
#[derive(Debug, thiserror::Error)]
pub enum HolError {
    /// A process-global kernel theory (`carved` / `lisp`) failed to build.
    #[error("kernel theory unavailable: {0}")]
    Theory(String),
    /// A kernel operation (term construction, a proof step) failed.
    #[error("kernel error: {0}")]
    Kernel(String),
    /// The term is not a reducible redex this strategy handles. The payload is
    /// a **complete, self-contained message** (e.g. "no reduction for `…`",
    /// "unbound variable `x`") — the `Display` impl adds only the `stuck:`
    /// prefix, never a second wrapping layer.
    #[error("stuck: {0}")]
    Stuck(String),
}

fn theory_err(e: impl core::fmt::Display) -> HolError {
    HolError::Theory(e.to_string())
}
fn kernel_err(e: impl core::fmt::Display) -> HolError {
    HolError::Kernel(e.to_string())
}
/// A `Stuck` error for a non-redex `term` — the payload is the full message
/// (the `Stuck` display adds only the `stuck:` prefix).
fn stuck(term: &Term) -> HolError {
    HolError::Stuck(format!("no reduction for `{term}`"))
}

/// The HOL Lisp instance — lowers S-expressions to carved `sexpr` kernel
/// [`Term`]s.
#[derive(Clone, Copy, Debug, Default)]
pub struct LispHol;

impl LispHol {
    fn carved(&self) -> Result<&'static CarvedSExpr, HolError> {
        carved().map_err(theory_err)
    }

    /// `atom <bytes>` — the carved `atom` constructor applied to a bytes
    /// literal (via [`mk_blob`], the designated facade).
    fn atom_term(&self, bytes: Vec<u8>) -> Result<Term, HolError> {
        Ok(Term::app(self.carved()?.atom.clone(), mk_blob(bytes)))
    }

    /// Prove one symbolic reduction of an operator term.
    pub fn eval(&self, term: &Term) -> Result<Thm, HolError> {
        SymbolicStrategy.reduce(term)
    }
}

impl SExprSyntax for LispHol {
    type Payload = Vec<u8>;
    type Value = Term;
    type Error = HolError;

    fn atom(&self, payload: Self::Payload) -> Result<Self::Value, Self::Error> {
        self.atom_term(payload)
    }

    fn nil(&self) -> Self::Value {
        self.carved()
            .expect("process-global carved theory")
            .snil
            .clone()
    }

    fn cons(&self, head: Self::Value, tail: Self::Value) -> Result<Self::Value, Self::Error> {
        let c = self.carved()?;
        Ok(Term::app(Term::app(c.scons.clone(), head), tail))
    }
}

impl LispDatumSyntax for LispHol {
    fn symbol_payload(&self, name: &str) -> Result<Self::Payload, Self::Error> {
        Ok(name.as_bytes().to_vec())
    }

    fn number_payload(&self, text: &str) -> Option<Result<Self::Payload, Self::Error>> {
        // Numerals are the ASCII decimal digit run, atomized like any other
        // token — matching `sexpr_parse`'s uninterpreted-byte-run atoms. We
        // only treat all-ASCII-digit tokens as numerals; everything else
        // falls through to `symbol_payload` (same atom either way, so the
        // distinction is cosmetic today — see source-local TODO markers).
        if !text.is_empty() && text.bytes().all(|b| b.is_ascii_digit()) {
            Some(Ok(text.as_bytes().to_vec()))
        } else {
            None
        }
    }

    fn string_payload(&self, _format: &str, bytes: &[u8]) -> Result<Self::Payload, Self::Error> {
        // Raw bytes, unquoted/unescaped (the untyped landing collapses the
        // string/symbol distinction; see source-local TODO markers).
        Ok(bytes.to_vec())
    }
}

/// **The symbolic reduction strategy** — proves `⊢ redex = value` by
/// composing the carved carrier's proved computation laws.
///
/// It is a [`ReductionStrategy`]: the swappable seam where a future
/// proven-WASM-interpreter strategy would plug in, returning a theorem of the
/// same shape. This one handles the single-step Lisp projections
/// `car (cons h t)` and `cdr (cons h t)` via [`CarvedSExpr::proj_scons`].
#[derive(Clone, Copy, Debug, Default)]
pub struct SymbolicStrategy;

impl SymbolicStrategy {
    fn lisp(&self) -> Result<&'static KernelLisp, HolError> {
        lisp().map_err(theory_err)
    }

    /// Match `op (cons h t)` where `op` is the carved `car`/`cdr` operator,
    /// returning `(take_cdr, h, t)`.
    fn as_projection(&self, term: &Term) -> Result<(bool, Term, Term), HolError> {
        let l = self.lisp()?;
        let (op, arg) = term.as_app().ok_or_else(|| stuck(term))?;
        let take_cdr = if op == l.car() {
            false
        } else if op == l.cdr() {
            true
        } else {
            return Err(stuck(term));
        };
        // arg must be `cons h t` = `scons h t` = App(App(cons, h), t).
        let (inner, t) = arg.as_app().ok_or_else(|| stuck(term))?;
        let (cons_op, h) = inner.as_app().ok_or_else(|| stuck(term))?;
        if cons_op != l.cons() {
            return Err(stuck(term));
        }
        Ok((take_cdr, h.clone(), t.clone()))
    }
}

impl ReductionStrategy for SymbolicStrategy {
    type Term = Term;
    type Thm = Thm;
    type Error = HolError;

    /// Prove `⊢ car (cons h t) = h` (or `cdr … = t`) via the carrier's
    /// `proj_scons` computation law.
    fn reduce(&self, term: &Term) -> Result<Thm, HolError> {
        let (take_cdr, h, t) = self.as_projection(term)?;
        let cs = carved().map_err(theory_err)?;
        cs.proj_scons(take_cdr, &h, &t).map_err(kernel_err)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn surface_data_lowers_through_shared_sexpr_constructors() {
        let backend = LispHol;
        let parsed = crate::reader::read_one("(alpha 12)").unwrap();
        let lowered = backend.lower_syntax(&parsed).unwrap();
        let alpha = backend.atom_term(b"alpha".to_vec()).unwrap();
        let twelve = backend.atom_term(b"12".to_vec()).unwrap();
        let expected = backend
            .cons(
                alpha,
                backend.cons(twelve, SExprSyntax::nil(&backend)).unwrap(),
            )
            .unwrap();
        assert_eq!(lowered, expected);
    }

    /// The de-risking proof: build the operator application `car (cons x y)`
    /// over two atom terms, run the symbolic strategy, and check the returned
    /// `Thm` is hyps-free with conclusion `car (cons x y) = x`. This is a
    /// genuine kernel theorem, composed from the carved carrier's proved
    /// computation law — nothing prints a value without a theorem.
    #[test]
    fn car_cons_reduces_to_head_with_a_kernel_theorem() {
        let backend = LispHol;
        let l = lisp().expect("lisp theory");

        // <atom x>, <atom y> — carved `sexpr` atoms via the Lisp lowering.
        let x = backend
            .atom(backend.symbol_payload("x").unwrap())
            .expect("atom x");
        let y = backend
            .atom(backend.symbol_payload("y").unwrap())
            .expect("atom y");

        // The redex `car (cons x y)` = App(car, App(App(cons, x), y)).
        let cons_xy = Term::app(Term::app(l.cons().clone(), x.clone()), y.clone());
        let redex = Term::app(l.car().clone(), cons_xy.clone());

        // Reduce — this returns Result<Thm, _>; the value is read off the Thm.
        let thm = SymbolicStrategy
            .reduce(&redex)
            .expect("reduce car(cons x y)");

        // Hyps-free.
        assert!(thm.hyps().is_empty(), "expected a hyps-free theorem");

        // Conclusion is `car (cons x y) = x`.
        let (lhs, rhs) = thm.concl().as_eq().expect("conclusion is an equation");
        assert_eq!(lhs, &redex, "lhs should be the redex `car (cons x y)`");
        assert_eq!(rhs, &x, "rhs should be the head atom `x`");
    }

    /// The dual: `cdr (cons x y) = y`, same mechanism.
    #[test]
    fn cdr_cons_reduces_to_tail() {
        let backend = LispHol;
        let l = lisp().expect("lisp theory");
        let x = backend
            .atom(backend.symbol_payload("x").unwrap())
            .expect("atom x");
        let y = backend
            .atom(backend.symbol_payload("y").unwrap())
            .expect("atom y");
        let cons_xy = Term::app(Term::app(l.cons().clone(), x.clone()), y.clone());
        let redex = Term::app(l.cdr().clone(), cons_xy);
        let thm = SymbolicStrategy
            .reduce(&redex)
            .expect("reduce cdr(cons x y)");
        assert!(thm.hyps().is_empty());
        let (_, rhs) = thm.concl().as_eq().expect("equation");
        assert_eq!(rhs, &y);
    }

    /// A non-redex is `Stuck`, not silently accepted.
    #[test]
    fn stuck_on_non_redex() {
        let backend = LispHol;
        let x = backend
            .atom(backend.symbol_payload("x").unwrap())
            .expect("atom x");
        assert!(matches!(
            SymbolicStrategy.reduce(&x),
            Err(HolError::Stuck(_))
        ));
    }
}
