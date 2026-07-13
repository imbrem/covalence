//! The **`Session` REPL** (`hol` feature) — a concrete
//! [`covalence_repl_core::Repl`] over the kernel-backed Lisp [`Evaluator`].
//!
//! A cell's lifecycle is `parse` (text → [`SExpr`]) → `eval` (→ a
//! [`Reduction`], i.e. a kernel `⊢ program = value` theorem) → `show`
//! (render the value **off the theorem's conclusion**). The
//! [`Session::eval_cell`] convenience runs the whole pipeline.
//!
//! # The honesty invariant
//!
//! `show` renders **only** the value carried in a [`Reduction`], which is by
//! construction the RHS of a genuine kernel theorem
//! ([`Reduction::thm`]). There is no code path that prints a value that did
//! not come off a theorem: [`eval`](Session::eval) returns `Result<Reduction,
//! _>`, and a `Reduction` cannot be built without a `Thm` (the field is
//! populated only by [`Evaluator`], which chains kernel rules). A caller can
//! independently audit [`Reduction::thm`] — it is hypothesis-free for every
//! closed program.
//!
//! # Directives
//!
//! A line beginning with `#` is a [directive](Directive), not a Lisp form:
//! `#help` prints the primitive list, `#show EXPR` prints the full
//! `⊢ lhs = rhs` theorem behind `EXPR`. The directive table is extensible;
//! other directives are deferred (see `SKELETONS.md`).

use covalence_init::Term;
use covalence_repl_core::Repl;

use crate::eval::{Evaluator, Reduction, ValueKind};
use crate::hol::HolError;
use crate::reader::{ReadError, read_one};

/// A REPL session over the kernel-backed Lisp evaluator.
///
/// The `Repl` machinery is stateless here (the carved + Lisp theories are
/// process-global), so [`State`] is a unit — but the trait shape leaves room
/// for a future `defun` dictionary (see `SKELETONS.md`).
pub struct Session {
    eval: Evaluator,
}

/// The (currently empty) per-session state.
#[derive(Clone, Copy, Debug, Default)]
pub struct State;

impl Session {
    /// Build a session, binding the process-global kernel theories.
    pub fn new() -> Result<Self, HolError> {
        Ok(Session {
            eval: Evaluator::new()?,
        })
    }

    /// Parse → evaluate → render, for one cell of source. The returned string
    /// is read **off the reduction theorem's conclusion**.
    ///
    /// A leading `#` selects a [directive](Directive) instead of a Lisp form.
    pub fn eval_cell(&mut self, src: &str) -> Result<String, CellError> {
        let src = src.trim();
        if let Some(rest) = src.strip_prefix('#') {
            return self.run_directive(rest).map_err(CellError::Directive);
        }
        let form = read_one(src).map_err(CellError::Read)?;
        let r = self.eval.eval(&form).map_err(CellError::Eval)?;
        Ok(self.render(&r))
    }

    /// Evaluate one already-parsed form to its [`Reduction`] (the kernel
    /// theorem + value).
    pub fn reduce(&self, form: &covalence_sexp::SExpr) -> Result<Reduction, HolError> {
        self.eval.eval(form)
    }

    /// Render a reduction's value to Little-Schemer text — **off the value
    /// term only** (the theorem's RHS).
    pub fn render(&self, r: &Reduction) -> String {
        match r.kind {
            ValueKind::Bool => self.render_bool(&r.value),
            ValueKind::Data => self.render_data(&r.value),
        }
    }

    /// A `bool` literal → `t` (true) / `nil` (false).
    fn render_bool(&self, v: &Term) -> String {
        match v.as_bool() {
            Some(true) => "t".to_string(),
            Some(false) => "nil".to_string(),
            None => format!("{v}"), // not a literal — surface the raw term
        }
    }

    /// A carved `sexpr` datum → Lisp text (`atom` → its bytes as text,
    /// `snil` → `()`, `scons` chains → `(e₁ e₂ …)`).
    fn render_data(&self, v: &Term) -> String {
        if self.eval.is_snil(v) {
            return "()".to_string();
        }
        if let Some(bytes) = self.eval.atom_bytes(v) {
            return String::from_utf8_lossy(&bytes).into_owned();
        }
        if let Some((_, _)) = self.eval.as_scons(v) {
            let mut out = String::from("(");
            let mut cur = v.clone();
            let mut first = true;
            loop {
                if let Some((h, t)) = self.eval.as_scons(&cur) {
                    if !first {
                        out.push(' ');
                    }
                    first = false;
                    out.push_str(&self.render_data(&h));
                    if self.eval.is_snil(&t) {
                        break;
                    }
                    // Improper list (dotted): a non-snil, non-scons tail.
                    if self.eval.as_scons(&t).is_none() {
                        out.push_str(" . ");
                        out.push_str(&self.render_data(&t));
                        break;
                    }
                    cur = t;
                } else {
                    break;
                }
            }
            out.push(')');
            return out;
        }
        format!("{v}") // unknown shape — surface the raw term
    }

    // ---- directives -----------------------------------------------------

    fn run_directive(&mut self, rest: &str) -> Result<String, DirectiveError> {
        let rest = rest.trim();
        let (name, arg) = match rest.split_once(char::is_whitespace) {
            Some((n, a)) => (n, a.trim()),
            None => (rest, ""),
        };
        match name {
            "help" => Ok(HELP.to_string()),
            "show" => {
                if arg.is_empty() {
                    return Err(DirectiveError::Usage("#show EXPR".into()));
                }
                let form = read_one(arg).map_err(DirectiveError::Read)?;
                let r = self.eval.eval(&form).map_err(DirectiveError::Eval)?;
                // The full `⊢ lhs = rhs` theorem.
                Ok(format!("{}", r.thm.concl()))
            }
            other => Err(DirectiveError::Unknown(other.to_string())),
        }
    }
}

/// The `#help` text — the primitive set this REPL backs with kernel theorems.
const HELP: &str = "\
covalence /lisp — every value is backed by a kernel theorem.
Little Schemer ch1 primitives:
  (quote D)        data literal D (atoms and lists)
  (car E)          head of a cons
  (cdr E)          tail of a cons
  (cons E1 E2)     prepend E1 onto list E2
  (atom? E)        t if E is an atom, else nil
  (consp E)        t if E is a cons, else nil     (alias pair?)
  (null? E)        t if E is the empty list, else nil
  (eq? E1 E2)      t if two atoms are equal, else nil
Directives:
  #help            this text
  #show EXPR       print the full `|- lhs = rhs` theorem behind EXPR";

/// A `#`-directive error.
#[derive(Debug, thiserror::Error)]
pub enum DirectiveError {
    /// Unknown directive name.
    #[error("unknown directive `#{0}` (try #help)")]
    Unknown(String),
    /// Bad usage; the string is the expected form.
    #[error("usage: {0}")]
    Usage(String),
    /// The directive's argument failed to parse.
    #[error("read error: {0}")]
    Read(ReadError),
    /// Evaluating the directive's argument failed.
    #[error("eval error: {0}")]
    Eval(HolError),
}

/// A cell-level error (a directive, a read, or an eval failure).
#[derive(Debug, thiserror::Error)]
pub enum CellError {
    /// A `#`-directive failed.
    #[error(transparent)]
    Directive(DirectiveError),
    /// The cell text failed to parse as one S-expression.
    #[error(transparent)]
    Read(ReadError),
    /// The program failed to evaluate to a value.
    #[error(transparent)]
    Eval(HolError),
}

/// A parsed directive (currently only the two built-ins; the table is
/// extensible — see `SKELETONS.md`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Directive {
    /// `#help`.
    Help,
    /// `#show EXPR`.
    Show(String),
}

// ---- the Repl trait instance -------------------------------------------

impl Repl for Session {
    type State = State;
    type Term = covalence_sexp::SExpr;
    type Eval = Reduction;
    type StartError = HolError;
    type ParseError = ReadError;
    type EvalError = HolError;

    fn start(&mut self) -> Result<State, HolError> {
        Ok(State)
    }

    fn parse(&mut self, _state: &State, src: &str) -> Result<Self::Term, ReadError> {
        read_one(src)
    }

    fn eval(&mut self, _state: &mut State, term: Self::Term) -> Result<Reduction, HolError> {
        self.eval.eval(&term)
    }

    fn show(&self, _state: &State, eval: &Reduction) -> String {
        self.render(eval)
    }
}
