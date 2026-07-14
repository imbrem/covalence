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
use covalence_init::{Term, Type};
use covalence_repl_core::{Fuel, Reduction, Repl, RunToValue, Status, Strategy};
use covalence_sexp::SExpr;

use crate::defs::{Defs, build_def, build_def_with_ret};
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
/// The `sexpr` + Lisp theories are process-global; the session's mutable state
/// is its **`defun` dictionary** ([`State`]) — user function definitions
/// entered as kernel *hypotheses* (see [`crate::defs`]). Each cell rebuilds a
/// [`LispSemantics`] over the current dictionary so `(f args)` calls unfold
/// against their assumed equations.
pub struct Session {
    defs: Defs,
    /// A definition-free semantics used only for its **structural** render
    /// helpers (`is_snil` / `as_scons` / `atom_bytes`), which are independent
    /// of the `defun` dictionary.
    render_sem: LispSemantics,
}

/// The per-session state: the `defun` dictionary.
#[derive(Clone, Default)]
pub struct State {
    /// The user function definitions (each an assumed `f = λ…` equation).
    pub defs: Defs,
}

impl Session {
    /// Build a session, binding the process-global kernel theories, with no
    /// user definitions.
    pub fn new() -> Result<Self, HolError> {
        Ok(Session {
            defs: Defs::new(),
            render_sem: LispSemantics::new()?,
        })
    }

    /// The current `defun` dictionary.
    pub fn defs(&self) -> &Defs {
        &self.defs
    }

    /// Build a semantics over the current definition dictionary.
    fn semantics(&self) -> Result<LispSemantics, HolError> {
        LispSemantics::with_defs(self.defs.clone())
    }

    /// Reduce a parsed form to a value (run to normal form), returning the
    /// [`Outcome`] (value + `definitions ⊢ input = value` theorem — the
    /// theorem's hypotheses are exactly the `defun` equations used).
    pub fn reduce(&self, form: &SExpr) -> Result<Outcome, HolError> {
        let sem = self.semantics()?;
        let red = self.drive_fueled_with(&sem, form, Fuel::UNBOUNDED)?;
        self.outcome(&sem, red)
    }

    /// Drive a form under a step `fuel` bound and return the raw streaming
    /// [`Reduction`] — for inspecting partial, certified reductions
    /// ([`Status::Diverging`]) without running to a value. The composite
    /// `⊢ input = cur` certifies the steps taken so far.
    pub fn drive_fueled(
        &self,
        form: &SExpr,
        fuel: Fuel,
    ) -> Result<Reduction<LispRepr, LispSemantics>, HolError> {
        let sem = self.semantics()?;
        self.drive_fueled_with(&sem, form, fuel)
    }

    fn drive_fueled_with(
        &self,
        sem: &LispSemantics,
        form: &SExpr,
        fuel: Fuel,
    ) -> Result<Reduction<LispRepr, LispSemantics>, HolError> {
        let term = sem.compile(form)?;
        let mut red = Reduction::start(term);
        RunToValue.drive(sem, &mut red, fuel)?;
        Ok(red)
    }

    /// Is this form a `(defun f (params) body)` / `(define f (lambda …))`
    /// definition? If so, add the assumed equation to the dictionary and
    /// return the function name (for the ack), else `Ok(None)`.
    pub fn try_define(&mut self, form: &SExpr) -> Result<Option<String>, HolError> {
        let SExpr::List(items) = form else {
            return Ok(None);
        };
        let Some(op) = items.first().and_then(SExpr::as_symbol) else {
            return Ok(None);
        };
        match op {
            // `(defun f (p₁ … pₙ) body)`.
            "defun" if items.len() == 4 => {
                let name = items[1]
                    .as_symbol()
                    .ok_or_else(|| HolError::Stuck("defun name is not a symbol".into()))?;
                let params = self.param_names(&items[2])?;
                self.install(name, &params, &items[3])?;
                Ok(Some(name.to_string()))
            }
            // `(define f (lambda (p…) body))` — the metacircular `label`/`define`.
            "define" | "label" if items.len() == 3 => {
                let name = items[1]
                    .as_symbol()
                    .ok_or_else(|| HolError::Stuck("define name is not a symbol".into()))?;
                let (params, body) = self.as_lambda(&items[2])?;
                self.install(name, &params, body)?;
                Ok(Some(name.to_string()))
            }
            _ => Ok(None),
        }
    }

    /// Install `(name, params, body)` as an assumed `defun` equation. The body
    /// is compiled with `name` **already in scope** (so recursion resolves to
    /// the def's own free-variable head).
    ///
    /// Because HOL is typed but Lisp is not, the recursive head's *return type*
    /// (`bool` for a predicate, `sexpr` for a list-valued function) must be
    /// fixed **before** the body compiles. We try `bool` first, and on a type
    /// error retry with `sexpr` — covering both `lat?`/`member?` (predicates,
    /// whose `t`/`nil` must render as booleans) and `rember` (data). A
    /// predicate's body only types under a `bool` head; a data function's
    /// recursive call only fits its data context under a `sexpr` head, so the
    /// two are disambiguated by which attempt type-checks.
    fn install(&mut self, name: &str, params: &[String], body: &SExpr) -> Result<(), HolError> {
        let tau = LispSemantics::new()?.tau();
        let candidates = [Type::bool(), tau.clone()];
        let mut last_err = None;
        for ret in candidates {
            match self.try_install_with_ret(name, params, body, &ret) {
                Ok(()) => return Ok(()),
                Err(e) => last_err = Some(e),
            }
        }
        Err(last_err.unwrap_or_else(|| HolError::Stuck(format!("cannot type `defun {name}`"))))
    }

    /// Attempt to install `name` with a chosen recursive return type `ret`.
    /// The whole attempt is transactional: `self.defs` is only mutated on
    /// success.
    fn try_install_with_ret(
        &mut self,
        name: &str,
        params: &[String],
        body: &SExpr,
        ret: &Type,
    ) -> Result<(), HolError> {
        // Pre-register a placeholder head (typed `sexpr… → ret`) so the body
        // compiles its recursive calls against `name`.
        let placeholder = build_def_with_ret(name, params, dummy_of(ret)?, ret)?;
        let staged = self.defs.with(placeholder);
        let sem = LispSemantics::with_defs(staged)?;
        let body_term = sem.compile(body)?;
        // The real def, whose head type is inferred from the compiled body — it
        // must match `ret`, or `assume` (which type-checks `f = λ…`) rejects it.
        let def = build_def(name, params, body_term)?;
        self.defs = self.defs.with(def);
        Ok(())
    }

    fn param_names(&self, params: &SExpr) -> Result<Vec<String>, HolError> {
        let SExpr::List(items) = params else {
            return Err(HolError::Stuck("parameter list is not a list".into()));
        };
        items
            .iter()
            .map(|p| {
                p.as_symbol()
                    .map(str::to_string)
                    .ok_or_else(|| HolError::Stuck("parameter is not a symbol".into()))
            })
            .collect()
    }

    /// Destructure a `(lambda (params) body)` form.
    fn as_lambda<'a>(&self, form: &'a SExpr) -> Result<(Vec<String>, &'a SExpr), HolError> {
        let SExpr::List(items) = form else {
            return Err(HolError::Stuck("define value is not a lambda".into()));
        };
        if items.len() != 3 || items[0].as_symbol() != Some("lambda") {
            return Err(HolError::Stuck("define value is not a lambda".into()));
        }
        let params = self.param_names(&items[1])?;
        Ok((params, &items[2]))
    }

    /// An acknowledgement [`Outcome`] for a definition cell: the function name
    /// as a `sexpr` atom value, backed by a reflexivity theorem. (A definition
    /// installs a hypothesis; it produces no reduction.)
    fn ack(&self, name: &str) -> Result<Outcome, HolError> {
        let value = self.render_sem.symbol_value(name);
        let thm = Thm::refl(value.clone()).map_err(|e| HolError::Kernel(e.to_string()))?;
        Ok(Outcome {
            value,
            thm,
            kind: ValueKind::Data,
            status: Status::Value,
            steps: 0,
        })
    }

    /// Package a completed [`Reduction`] into an [`Outcome`], reading the value
    /// kind off the normal-form term and minting reflexivity when zero steps
    /// were taken.
    fn outcome(
        &self,
        sem: &LispSemantics,
        red: Reduction<LispRepr, LispSemantics>,
    ) -> Result<Outcome, HolError> {
        let status = red.status();
        let steps = red.steps();
        let (value, composite) = red.into_parts();
        let kind = sem.value_kind(&value).ok_or_else(|| {
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
        // A `defun` / `define` adds an assumption and returns an ack (no value).
        if let Some(name) = self.try_define(&form).map_err(CellError::Eval)? {
            return Ok(name);
        }
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
        if self.render_sem.is_snil(v) {
            return "()".to_string();
        }
        if let Some(bytes) = self.render_sem.atom_bytes(v) {
            return String::from_utf8_lossy(&bytes).into_owned();
        }
        if self.render_sem.as_scons(v).is_some() {
            let mut out = String::from("(");
            let mut cur = v.clone();
            let mut first = true;
            while let Some((h, t)) = self.render_sem.as_scons(&cur) {
                if !first {
                    out.push(' ');
                }
                first = false;
                out.push_str(&self.render_data(&h));
                if self.render_sem.is_snil(&t) {
                    break;
                }
                // Improper list (dotted): a non-snil, non-scons tail.
                if self.render_sem.as_scons(&t).is_none() {
                    out.push_str(" . ");
                    out.push_str(&self.render_data(&t));
                    break;
                }
                cur = t;
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
Chapter 2 (recursion via kernel hypotheses):
  (if C A B)       A if C is true, else B
  (cond (T E)...)  first clause whose test T holds
  (lambda (x) E)   an anonymous function (beta-reduces when applied)
  (defun f (x) E)  define f; calls of f unfold against the ASSUMED equation
                   f = (lambda (x) E), which rides the result theorem as a
                   hypothesis (never an axiom)
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

/// A trivial term of type `ret`, used as a placeholder body while compiling a
/// recursive definition: `nil` for `sexpr`, `F` for `bool`.
fn dummy_of(ret: &Type) -> Result<Term, HolError> {
    let sem = LispSemantics::new()?;
    if *ret == Type::bool() {
        Ok(covalence_hol_eval::mk_bool(false))
    } else {
        Ok(sem.tau_nil())
    }
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
        Ok(State {
            defs: self.defs.clone(),
        })
    }

    fn parse(&mut self, _state: &State, src: &str) -> Result<Self::Term, ReadError> {
        read_one(src)
    }

    fn eval(&mut self, state: &mut State, term: Self::Term) -> Result<Outcome, HolError> {
        // A `defun` / `define` installs an assumption and acks; otherwise reduce.
        if let Some(name) = self.try_define(&term)? {
            state.defs = self.defs.clone();
            return self.ack(&name);
        }
        self.reduce(&term)
    }

    fn show(&self, _state: &State, eval: &Outcome) -> String {
        self.render(eval)
    }
}

#[cfg(test)]
mod send_sync {
    // The server holds `Session` across threads (`/api/lisp` persistent-session
    // demo), so it must be `Send + Sync` — guaranteed by `Arc` (not `Rc`) in `Defs`.
    const _: fn() = || {
        fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<super::Session>();
    };
}
