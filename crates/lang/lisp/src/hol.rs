//! The **HOL backend** (`hol` feature): the concrete kernel instance of the
//! Lisp surface + the symbolic reduction strategy.
//!
//! - [`LispHol`] implements [`crate::Lisp`], lowering S-expressions to carved
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
//! `SKELETONS.md`). Building the operator-application form from data (an
//! `eval` that walks a `scons`-tree and applies the `car`/`cdr`/`cons`
//! operators) is future work.

use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::mk_blob;
use covalence_init::Term;
use covalence_init::init::inductive::carved::{CarvedSExpr, carved};
use covalence_init::init::lisp::{Lisp as KernelLisp, lisp};

use covalence_repl_core::ReductionStrategy;

use crate::Lisp;

/// Errors from the HOL backend.
#[derive(Debug, thiserror::Error)]
pub enum HolError {
    /// A process-global kernel theory (`carved` / `lisp`) failed to build.
    #[error("kernel theory unavailable: {0}")]
    Theory(String),
    /// A kernel operation (term construction, a proof step) failed.
    #[error("kernel error: {0}")]
    Kernel(String),
    /// The term is not a reducible redex this strategy handles.
    #[error("stuck: no reduction for `{0}`")]
    Stuck(String),
}

fn theory_err(e: impl core::fmt::Display) -> HolError {
    HolError::Theory(e.to_string())
}
fn kernel_err(e: impl core::fmt::Display) -> HolError {
    HolError::Kernel(e.to_string())
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
    fn atom(&self, bytes: Vec<u8>) -> Result<Term, HolError> {
        Ok(Term::app(self.carved()?.atom.clone(), mk_blob(bytes)))
    }
}

impl Lisp for LispHol {
    type Term = Term;
    type Error = HolError;
    type Eval = Thm;
    type EvalError = HolError;

    fn resolve_symbol(&self, name: &str) -> Result<Term, HolError> {
        // Every symbol is a bare atom of its UTF-8 bytes (matching
        // `sexpr_parse`). A dictionary lookup would go here first.
        self.atom(name.as_bytes().to_vec())
    }

    fn resolve_number(&self, text: &str) -> Option<Result<Term, HolError>> {
        // Numerals are the ASCII decimal digit run, atomized like any other
        // token — matching `sexpr_parse`'s uninterpreted-byte-run atoms. We
        // only treat all-ASCII-digit tokens as numerals; everything else
        // falls through to `resolve_symbol` (same atom either way, so the
        // distinction is cosmetic today — see SKELETONS.md).
        if !text.is_empty() && text.bytes().all(|b| b.is_ascii_digit()) {
            Some(self.atom(text.as_bytes().to_vec()))
        } else {
            None
        }
    }

    fn resolve_string(&self, _format: &str, bytes: &[u8]) -> Result<Term, HolError> {
        // Raw bytes, unquoted/unescaped (the untyped landing collapses the
        // string/symbol distinction; see SKELETONS.md).
        self.atom(bytes.to_vec())
    }

    fn nil(&self) -> Result<Term, HolError> {
        Ok(self.carved()?.snil.clone())
    }

    fn cons(&self, head: Term, tail: Term) -> Result<Term, HolError> {
        let c = self.carved()?;
        Ok(Term::app(Term::app(c.scons.clone(), head), tail))
    }

    fn eval(&self, term: &Term) -> Result<Thm, HolError> {
        SymbolicStrategy.reduce(term)
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
        let (op, arg) = term
            .as_app()
            .ok_or_else(|| HolError::Stuck(term.to_string()))?;
        let take_cdr = if op == l.car() {
            false
        } else if op == l.cdr() {
            true
        } else {
            return Err(HolError::Stuck(term.to_string()));
        };
        // arg must be `cons h t` = `scons h t` = App(App(cons, h), t).
        let (inner, t) = arg
            .as_app()
            .ok_or_else(|| HolError::Stuck(term.to_string()))?;
        let (cons_op, h) = inner
            .as_app()
            .ok_or_else(|| HolError::Stuck(term.to_string()))?;
        if cons_op != l.cons() {
            return Err(HolError::Stuck(term.to_string()));
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
        let x = backend.resolve_symbol("x").expect("atom x");
        let y = backend.resolve_symbol("y").expect("atom y");

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
        let x = backend.resolve_symbol("x").expect("atom x");
        let y = backend.resolve_symbol("y").expect("atom y");
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
        let x = backend.resolve_symbol("x").expect("atom x");
        assert!(matches!(
            SymbolicStrategy.reduce(&x),
            Err(HolError::Stuck(_))
        ));
    }
}
