//! The **`Session` REPL** (`hol` feature) — a concrete
//! [`covalence_repl_core::Repl`] that drives the Lisp
//! [`LispSemantics`](crate::semantics::LispSemantics) reduction relation
//! through the [`RunToValue`] strategy.
//!
//! A cell's lifecycle is `parse` (text → [`SExpr`]) → `reduce` (drive the
//! step-relation to a normal form, yielding a kernel `⊢ input = value`
//! theorem) → `render` (print the value **off the theorem's RHS**). The
//! [`Session::eval_cell`] convenience runs the whole pipeline.
//!
//! # The honesty invariant
//!
//! `render` prints **only** the value term carried in an [`Outcome`], which is
//! by construction the RHS of a genuine kernel theorem (`Outcome::thm`). There
//! is no code path that prints a value that did not come off a theorem:
//! [`reduce`](Session::reduce) returns `Result<Outcome, _>`, the `Outcome`'s
//! `value` is `Reduction::cur` after driving, and its `thm` is the
//! trans-composed `⊢ input = value` (reflexivity when the input was already a
//! value). A caller can independently audit `Outcome::thm` — it is
//! hypothesis-free for every closed program.
//!
//! # Streaming / non-termination
//!
//! [`reduce`](Session::reduce) drives with [`Fuel::UNBOUNDED`] (ch1 programs
//! terminate). [`drive_fueled`](Session::drive_fueled) exposes the raw
//! [`Reduction`] under a step bound, so a caller can pull a partial certified
//! reduction (`Status::Diverging`) instead of hanging — the seam a
//! non-terminating recursive program (ch2) will use.
//!
//! # Directives
//!
//! A line beginning with `#` is a [directive](Directive), not a Lisp form:
//! `#help` prints the primitive list, `#show EXPR` prints the full
//! `⊢ lhs = rhs` theorem behind `EXPR`. The directive table is extensible;
//! other directives are deferred (see `SKELETONS.md`).

use covalence_hol_eval::EvalThm as Thm;
use covalence_init::Term;
use covalence_repl_core::{Fuel, Reduction, Repl, RunToValue, Status, Strategy};

use crate::hol::HolError;
use crate::reader::{ReadError, read_one};
use crate::semantics::{LispRepr, LispSemantics, ValueKind};

/// The reduction of one form: the value term, the composite kernel theorem
/// `⊢ input = value`, its value-kind, and the streaming status/step count.
#[derive(Clone)]
pub struct Outcome {
    /// The normal-form value term (the theorem's RHS).
    pub value: Term,
    /// `⊢ input = value` — the trans-composed step chain (reflexivity when the
    /// input was already a value).
    pub thm: Thm,
    /// Whether `value` is a `sexpr` datum or a `bool` literal (for printing).
    pub kind: ValueKind,
    /// The reduction status (always [`Status::Value`] for a completed `reduce`).
    pub status: Status,
    /// How many certified steps the reduction took.
    pub steps: u64,
}

/// A REPL session driving the Lisp reduction relation.
///
/// The `Repl` machinery is stateless here (the `sexpr` + Lisp theories are
/// process-global), so [`State`] is a unit — but the trait shape leaves room
/// for a future `defun` dictionary (see `SKELETONS.md`).
pub struct Session {
    sem: LispSemantics,
}

/// The (currently empty) per-session state.
#[derive(Clone, Copy, Debug, Default)]
pub struct State;

impl Session {
    /// Build a session, binding the process-global kernel theories.
    pub fn new() -> Result<Self, HolError> {
        Ok(Session {
            sem: LispSemantics::new()?,
        })
    }

    /// Reduce a parsed form to a value (run to normal form), returning the
    /// [`Outcome`] (value + `⊢ input = value` theorem).
    pub fn reduce(&self, form: &covalence_sexp::SExpr) -> Result<Outcome, HolError> {
        let red = self.drive_fueled(form, Fuel::UNBOUNDED)?;
        self.outcome(red)
    }

    /// Drive a form under a step `fuel` bound and return the raw streaming
    /// [`Reduction`] — for inspecting partial, certified reductions
    /// ([`Status::Diverging`]) without running to a value. The composite
    /// `⊢ input = cur` certifies the steps taken so far.
    pub fn drive_fueled(
        &self,
        form: &covalence_sexp::SExpr,
        fuel: Fuel,
    ) -> Result<Reduction<LispRepr, LispSemantics>, HolError> {
        let term = self.sem.compile(form)?;
        let mut red = Reduction::start(term);
        RunToValue.drive(&self.sem, &mut red, fuel)?;
        Ok(red)
    }

    /// Package a completed [`Reduction`] into an [`Outcome`], reading the value
    /// kind off the normal-form term and minting reflexivity when zero steps
    /// were taken.
    fn outcome(&self, red: Reduction<LispRepr, LispSemantics>) -> Result<Outcome, HolError> {
        let status = red.status();
        let steps = red.steps();
        let (value, composite) = red.into_parts();
        let kind = self.sem.value_kind(&value).ok_or_else(|| {
            HolError::Stuck(format!(
                "reduction did not reach a value (status {status:?})"
            ))
        })?;
        let thm = match composite {
            Some(t) => t,
            // Zero steps: the input already was the value — `⊢ value = value`.
            None => Thm::refl(value.clone()).map_err(|e| HolError::Kernel(e.to_string()))?,
        };
        Ok(Outcome {
            value,
            thm,
            kind,
            status,
            steps,
        })
    }

    /// Parse → reduce → render, for one cell of source. The returned string is
    /// read **off the reduction theorem's conclusion**.
    ///
    /// A leading `#` selects a [directive](Directive) instead of a Lisp form.
    pub fn eval_cell(&mut self, src: &str) -> Result<String, CellError> {
        let src = src.trim();
        if let Some(rest) = src.strip_prefix('#') {
            return self.run_directive(rest).map_err(CellError::Directive);
        }
        let form = read_one(src).map_err(CellError::Read)?;
        let out = self.reduce(&form).map_err(CellError::Eval)?;
        Ok(self.render(&out))
    }

    /// Render an outcome's value to Little-Schemer text — **off the value term
    /// only** (the theorem's RHS).
    pub fn render(&self, out: &Outcome) -> String {
        match out.kind {
            ValueKind::Bool => self.render_bool(&out.value),
            ValueKind::Data => self.render_data(&out.value),
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

    /// A `sexpr` datum → Lisp text (`atom` → its bytes as text, `snil` → `()`,
    /// `scons` chains → `(e₁ e₂ …)`).
    fn render_data(&self, v: &Term) -> String {
        if self.sem.is_snil(v) {
            return "()".to_string();
        }
        if let Some(bytes) = self.sem.atom_bytes(v) {
            return String::from_utf8_lossy(&bytes).into_owned();
        }
        if self.sem.as_scons(v).is_some() {
            let mut out = String::from("(");
            let mut cur = v.clone();
            let mut first = true;
            loop {
                if let Some((h, t)) = self.sem.as_scons(&cur) {
                    if !first {
                        out.push(' ');
                    }
                    first = false;
                    out.push_str(&self.render_data(&h));
                    if self.sem.is_snil(&t) {
                        break;
                    }
                    // Improper list (dotted): a non-snil, non-scons tail.
                    if self.sem.as_scons(&t).is_none() {
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
                let out = self.reduce(&form).map_err(DirectiveError::Eval)?;
                // The full `⊢ lhs = rhs` composite theorem.
                Ok(format!("{}", out.thm.concl()))
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
    type Eval = Outcome;
    type StartError = HolError;
    type ParseError = ReadError;
    type EvalError = HolError;

    fn start(&mut self) -> Result<State, HolError> {
        Ok(State)
    }

    fn parse(&mut self, _state: &State, src: &str) -> Result<Self::Term, ReadError> {
        read_one(src)
    }

    fn eval(&mut self, _state: &mut State, term: Self::Term) -> Result<Outcome, HolError> {
        self.reduce(&term)
    }

    fn show(&self, _state: &State, eval: &Outcome) -> String {
        self.render(eval)
    }
}
