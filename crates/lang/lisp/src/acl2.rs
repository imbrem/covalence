//! An honest **ACL2-flavoured dialect** (`hol` feature) — the first slice of
//! the `SExpr ⇒ Reduction ⇒ Lisp ⇒ ACL2` tower's top layer.
//!
//! ACL2 is an applicative, first-order Lisp with a definitional principle
//! (`defun` admitted only when it terminates) and a theorem event (`defthm`).
//! This module ships the *honest demo slice* of that discipline over the
//! existing value semantics ([`LispSemantics`], defun-as-hypothesis
//! recursion — see [`crate::defs`]):
//!
//! - **Primitives** — ACL2 spellings over the existing machinery: ternary
//!   `if` (no `cond`), `equal`, `consp` / `atom` / `endp`, `car` / `cdr` /
//!   `cons`, plus **ground** integer arithmetic `+` `-` `*` `<=` `=` `zp`
//!   `natp` (see below).
//! - **`defun`** — accepted only when it passes a *syntactic
//!   structural-recursion check* (every recursive call descends a `car`/`cdr`
//!   chain of the same formal; §admissibility below). This is a stated
//!   discipline, **not** a termination proof — no measures, no ordinals.
//!   Soundness never rests on it: an admitted `defun` still enters the kernel
//!   only as the *assumption* `{f = λ…} ⊢ f = λ…`, so even a wrongly-admitted
//!   non-terminating definition cannot mint a hypothesis-free falsehood.
//! - **`defthm`** — only what is genuinely provable *today*: **ground,
//!   decidable goals**, discharged by kernel reduction. `(defthm four (equal
//!   (+ 2 2) 4))` mints a real kernel theorem (the certified step-relation
//!   drive to `T`, then `eqt_elim`); a goal with free variables is
//!   **rejected** with a message naming what is missing (induction — future
//!   work). Nothing is ever faked.
//!
//! # The honesty invariant
//!
//! Exactly the [`crate::session`] contract: every value printed by
//! [`Acl2Session::eval_cell`] is read off the right-hand side of a genuine
//! kernel theorem carried in the [`Acl2Outcome`]; every stored `defthm` is a
//! genuine kernel [`Thm`] whose hypotheses (if any) are exactly the `defun`
//! equations the proof used. Anything unprovable returns a clean `Err`.
//!
//! # Admissibility (the demo criterion, stated exactly)
//!
//! `(defun f (x₁ … xₙ) body)` is admitted iff:
//!
//! 1. every form in `body` is a known primitive, a previously admitted
//!    `defun`, or `f` itself, applied at the right arity (definition before
//!    use — no forward references);
//! 2. every atom in `body` (outside `quote`) is `t`, `nil`, or a formal; and
//! 3. if `body` calls `f`, there is a formal position `i` such that **every**
//!    recursive call passes, in position `i`, a non-empty `car`/`cdr` chain
//!    applied to the formal `xᵢ` (e.g. `(app (cdr x) y)` descends `x`).
//!
//! This accepts the Little-Schemer staples (`app`, `member?`, …) and rejects
//! `(defun bad (x) (bad x))` and `(defun grow (x) (grow (cons x x)))` with a
//! clear message. It is deliberately weaker than ACL2's measure-based
//! definitional principle (e.g. it does not verify the `endp`/`consp` guard);
//! termination *proofs* are future work — see `SKELETONS.md` and
//! `notes/vibes/lisp/acl2-dialect.md`.
//!
//! # Integers (on the value semantics' [`IntBackend`] integration)
//!
//! Integers ride the value semantics' integer support (the
//! [`crate::int_backend::IntBackend`] seam, wired by default in
//! [`LispSemantics`]): numerals compile to kernel `int` literals and
//! `+ - * <= =` to the kernel `int.add` / `int.sub` / `int.mul` / `int.le` /
//! `(=):int` operators, whose reductions are **kernel-proved** computation
//! equations (never asserted). `zp` / `natp` are compiled as their integer
//! meanings (`zp n` ⇔ `n ≤ 0`, `natp n` ⇔ `0 ≤ n` — on `int`-typed terms
//! `integerp` is `t` by typing), and `equal` routes to integer `=` when
//! either side is syntactically arithmetic.
//!
//! One honest limitation: kernel integers are **typed `int` terms, not
//! `sexpr` data**, so mixed structures (`(cons 1 nil)`, an integer passed to
//! a list-typed formal) are not expressible — they are rejected with a clear
//! message, never mis-evaluated. Integer-*valued* recursion over lists
//! (e.g. `len`) works: the recursive head's return type is inferred as
//! `int`.

use std::collections::BTreeMap;

use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::{as_bool, as_int, mk_bool, mk_int};
use covalence_init::init::ext::ThmExt;
use covalence_init::{Term, Type};
use covalence_repl_core::{Fuel, Reduction, RunToValue, Strategy};
use covalence_sexp::{Atom, SExpr};
use covalence_types::Int;

use crate::defs::{Defs, build_def, build_def_with_ret};
use crate::hol::HolError;
use crate::reader::{ReadError, read_one};
use crate::semantics::{LispRepr, LispSemantics, ValueKind};

/// Step budget for a value reduction — recursion is admitted by a *syntactic*
/// check, not a proof, so the driver must stay fuel-bounded (divergence is a
/// clean error, never a hang).
const FUEL: u64 = 100_000;

// ============================================================================
// Errors
// ============================================================================

/// An ACL2-cell error: read, evaluation, admissibility, or proof failure.
#[derive(Debug, thiserror::Error)]
pub enum Acl2Error {
    /// The cell text failed to parse as one S-expression.
    #[error(transparent)]
    Read(ReadError),
    /// Evaluation failed (stuck term, kernel error, fuel exhausted).
    #[error(transparent)]
    Eval(HolError),
    /// A `defun` failed the admissibility check.
    #[error("defun `{name}` not admitted: {reason}")]
    Inadmissible {
        /// The function name.
        name: String,
        /// Why it was rejected.
        reason: String,
    },
    /// A `defthm` goal could not be proved (and was NOT faked).
    #[error("defthm `{name}` rejected: {reason}")]
    Unprovable {
        /// The theorem name.
        name: String,
        /// Why it was rejected (what is missing).
        reason: String,
    },
    /// A malformed event or unsupported form.
    #[error("{0}")]
    Malformed(String),
}

impl From<HolError> for Acl2Error {
    fn from(e: HolError) -> Self {
        Acl2Error::Eval(e)
    }
}

fn kernel_err(e: impl core::fmt::Display) -> Acl2Error {
    Acl2Error::Eval(HolError::Kernel(e.to_string()))
}

// ============================================================================
// Outcomes
// ============================================================================

/// The value-kind of an ACL2 outcome, for printing.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Acl2ValueKind {
    /// A `sexpr` datum (`atom` / `snil` / `scons` chains).
    Data,
    /// A `bool` literal (predicate / `equal` result) — printed `t` / `nil`.
    Bool,
    /// A kernel `int` literal (ground arithmetic) — printed as a decimal.
    Int,
}

/// The result of evaluating one ACL2 expression: the value term and the
/// kernel theorem backing it. The value is **always** the theorem's RHS.
#[derive(Clone, Debug)]
pub struct Acl2Outcome {
    /// The normal-form value term (the theorem's RHS).
    pub value: Term,
    /// `hyps ⊢ input = value` — the composite kernel theorem. The hypotheses,
    /// if any, are exactly the `defun` equations the reduction unfolded.
    pub thm: Thm,
    /// How to print `value`.
    pub kind: Acl2ValueKind,
}

// ============================================================================
// The session
// ============================================================================

/// An ACL2-dialect REPL session, mirroring [`crate::session::Session`]'s
/// `eval_cell` / `render` shape (phase-2 integration into the `#lang`
/// dispatch is a thin wrapper around this).
///
/// State: the admitted `defun` dictionary (kernel *hypotheses*, never axioms
/// — [`crate::defs`]) and the proved `defthm` table (genuine kernel
/// theorems, retrievable via [`theorem`](Acl2Session::theorem)).
pub struct Acl2Session {
    defs: Defs,
    thms: BTreeMap<String, Thm>,
    /// A definition-free semantics for structural helpers (`tau`, renderers).
    sem0: LispSemantics,
}

impl Acl2Session {
    /// Build a session over the process-global kernel theories, with no
    /// definitions and no theorems.
    pub fn new() -> Result<Self, Acl2Error> {
        Ok(Acl2Session {
            defs: Defs::new(),
            thms: BTreeMap::new(),
            sem0: LispSemantics::new()?,
        })
    }

    /// The admitted `defun` dictionary.
    pub fn defs(&self) -> &Defs {
        &self.defs
    }

    /// A proved `defthm` by name — the genuine kernel theorem (its hypotheses
    /// are the `defun` equations the proof used; empty for pure-arithmetic
    /// goals).
    pub fn theorem(&self, name: &str) -> Option<&Thm> {
        self.thms.get(name)
    }

    /// Parse → dispatch (event or expression) → render, for one cell of
    /// source. `defun` / `defthm` events return their name on success (the
    /// ACL2 convention); an expression returns its value, read off the
    /// backing theorem's RHS.
    pub fn eval_cell(&mut self, src: &str) -> Result<String, Acl2Error> {
        let form = read_one(src.trim()).map_err(Acl2Error::Read)?;
        if let Some(name) = self.try_event(&form)? {
            return Ok(name);
        }
        let out = self.reduce(&form)?;
        Ok(self.render(&out))
    }

    /// Is this form an ACL2 **event** (`defun` / `defthm`)? If so, admit it
    /// and return its name (the ACL2 convention), else `Ok(None)` — the
    /// caller evaluates the form as an expression. This is the seam the
    /// `#lang acl2` [`session::Session`](crate::session::Session) dispatch
    /// uses.
    pub fn try_event(&mut self, form: &SExpr) -> Result<Option<String>, Acl2Error> {
        if let SExpr::List(items) = form {
            match items.first().and_then(SExpr::as_symbol) {
                Some("defun") => return self.admit_defun(items).map(Some),
                Some("defthm") => return self.admit_defthm(items).map(Some),
                _ => {}
            }
        }
        Ok(None)
    }

    /// Drop all session state (the `defun` dictionary and the `defthm`
    /// table) — infallible, used by the `#lang` switch reset.
    pub fn reset(&mut self) {
        self.defs = Defs::new();
        self.thms = BTreeMap::new();
    }

    // ------------------------------------------------------------------
    // Expression evaluation
    // ------------------------------------------------------------------

    /// Evaluate one ACL2 expression to an [`Acl2Outcome`]: translate the
    /// ACL2 spellings and drive the value semantics (which carries the
    /// integer backend). A top-level non-arithmetic `equal` additionally
    /// gets the structural fallback ([`reduce_equal`](Self::reduce_equal)).
    pub fn reduce(&self, form: &SExpr) -> Result<Acl2Outcome, Acl2Error> {
        if let SExpr::List(items) = form
            && items.len() == 3
            && items[0].as_symbol() == Some("equal")
            && !is_int_form(&items[1])
            && !is_int_form(&items[2])
        {
            return self.reduce_equal(&items[1], &items[2]);
        }
        let translated = self.translate(form, &[], None)?;
        self.reduce_value(&translated)
    }

    /// Drive a (translated) form through the value semantics to a normal
    /// form, fuel-bounded, packaging the composite theorem.
    fn reduce_value(&self, form: &SExpr) -> Result<Acl2Outcome, Acl2Error> {
        let sem = LispSemantics::with_defs(self.defs.clone())?;
        let term = sem.compile(form)?;
        let mut red: Reduction<LispRepr, LispSemantics> = Reduction::start(term);
        RunToValue.drive(&sem, &mut red, Fuel::steps(FUEL))?;
        let status = red.status();
        let (value, composite) = red.into_parts();
        let kind = match sem.value_kind(&value) {
            Some(ValueKind::Data) => Acl2ValueKind::Data,
            Some(ValueKind::Bool) => Acl2ValueKind::Bool,
            Some(ValueKind::Int) => Acl2ValueKind::Int,
            None => {
                return Err(Acl2Error::Eval(HolError::Stuck(format!(
                    "did not reach a value in {FUEL} steps (status {status:?}) — \
                     the definition may not terminate"
                ))));
            }
        };
        let thm = match composite {
            Some(t) => t,
            None => Thm::refl(value.clone()).map_err(kernel_err)?,
        };
        Ok(Acl2Outcome { value, thm, kind })
    }

    /// `(equal a b)` outside arithmetic: first try the `eq?` reduction (which
    /// genuinely decides atom (dis)equality); if that gets stuck (composite
    /// operands), fall back to reducing both operands and — **only when the
    /// value terms are syntactically identical** — minting
    /// `hyps ⊢ (a = b) = T` by `trans`/`sym` + `eqt_intro`. Distinct
    /// composite values are a clean error (deciding their *dis*equality needs
    /// the `scons` discrimination laws — future work, see `SKELETONS.md`).
    fn reduce_equal(&self, a: &SExpr, b: &SExpr) -> Result<Acl2Outcome, Acl2Error> {
        let eq_form = SExpr::List(vec![
            SExpr::Atom(Atom::Symbol("eq?".into())),
            self.translate(a, &[], None)?,
            self.translate(b, &[], None)?,
        ]);
        match self.reduce_value(&eq_form) {
            Ok(out) => Ok(out),
            Err(first) => self.reduce_equal_structural(a, b).map_err(|e| {
                // Prefer the structural path's message when it is the honest
                // "cannot decide" one; else surface the original failure.
                match e {
                    Acl2Error::Malformed(_) => e,
                    _ => first,
                }
            }),
        }
    }

    /// The structural-identity `equal` fallback (values must coincide).
    fn reduce_equal_structural(&self, a: &SExpr, b: &SExpr) -> Result<Acl2Outcome, Acl2Error> {
        let oa = self.reduce_value(&self.translate(a, &[], None)?)?;
        let ob = self.reduce_value(&self.translate(b, &[], None)?)?;
        if oa.value != ob.value {
            return Err(Acl2Error::Malformed(
                "equal: cannot decide disequality of composite values in this slice \
                 (only atom disequality is decidable — `scons` discrimination laws \
                 are future work)"
                    .into(),
            ));
        }
        // oa.thm : H₁ ⊢ a = v ; ob.thm : H₂ ⊢ b = v ; so H₁∪H₂ ⊢ a = b, and
        // eqt_intro gives H₁∪H₂ ⊢ (a = b) = T.
        let eq = oa
            .thm
            .trans(ob.thm.sym().map_err(kernel_err)?)
            .map_err(kernel_err)?;
        let thm = eq.eqt_intro().map_err(kernel_err)?;
        let value = rhs_of(&thm)?;
        Ok(Acl2Outcome {
            value,
            thm,
            kind: Acl2ValueKind::Bool,
        })
    }

    /// Render an outcome's value — **off the theorem's RHS only**.
    pub fn render(&self, out: &Acl2Outcome) -> String {
        match out.kind {
            Acl2ValueKind::Bool => match as_bool(&out.value) {
                Some(true) => "t".into(),
                Some(false) => "nil".into(),
                None => format!("{}", out.value),
            },
            Acl2ValueKind::Int => match as_int(&out.value) {
                Some(n) => n.to_string(),
                None => format!("{}", out.value),
            },
            Acl2ValueKind::Data => self.render_data(&out.value),
        }
    }

    /// A `sexpr` datum → Lisp text (mirrors `session::Session::render_data`).
    fn render_data(&self, v: &Term) -> String {
        if self.sem0.is_snil(v) {
            return "()".into();
        }
        if let Some(bytes) = self.sem0.atom_bytes(v) {
            return String::from_utf8_lossy(&bytes).into_owned();
        }
        if self.sem0.as_scons(v).is_some() {
            let mut out = String::from("(");
            let mut cur = v.clone();
            let mut first = true;
            while let Some((h, t)) = self.sem0.as_scons(&cur) {
                if !first {
                    out.push(' ');
                }
                first = false;
                out.push_str(&self.render_data(&h));
                if self.sem0.is_snil(&t) {
                    break;
                }
                if self.sem0.as_scons(&t).is_none() {
                    out.push_str(" . ");
                    out.push_str(&self.render_data(&t));
                    break;
                }
                cur = t;
            }
            out.push(')');
            return out;
        }
        format!("{v}")
    }

    // ------------------------------------------------------------------
    // defun — admissibility + install
    // ------------------------------------------------------------------

    /// `(defun name (params) body)`: run the admissibility check, then
    /// install the definition as an assumed equation (never an axiom).
    fn admit_defun(&mut self, items: &[SExpr]) -> Result<String, Acl2Error> {
        if items.len() != 4 {
            return Err(Acl2Error::Malformed(
                "defun: expected (defun name (params) body)".into(),
            ));
        }
        let name = items[1]
            .as_symbol()
            .ok_or_else(|| Acl2Error::Malformed("defun: name is not a symbol".into()))?
            .to_string();
        let inadmissible = |reason: String| Acl2Error::Inadmissible {
            name: name.clone(),
            reason,
        };
        if reserved_head(&name).is_some() || matches!(name.as_str(), "t" | "nil") {
            return Err(inadmissible("the name is a reserved primitive".into()));
        }
        let params = param_names(&items[2]).map_err(&inadmissible)?;
        self.check_admissible(&name, &params, &items[3])
            .map_err(&inadmissible)?;
        let body = self.translate(&items[3], &params, Some(&name))?;
        self.install(&name, &params, &body)?;
        Ok(name)
    }

    /// The syntactic admissibility check (see the module docs for the exact
    /// criterion). Errors carry a human-readable reason.
    fn check_admissible(&self, name: &str, params: &[String], body: &SExpr) -> Result<(), String> {
        let mut calls: Vec<&[SExpr]> = Vec::new();
        self.check_body(name, params, body, &mut calls)?;
        if calls.is_empty() {
            return Ok(()); // non-recursive: nothing to justify
        }
        let decreasing = (0..params.len()).any(|i| {
            calls
                .iter()
                .all(|args| is_proper_projection(&args[i], &params[i]))
        });
        if decreasing {
            Ok(())
        } else {
            Err(format!(
                "not structurally recursive: no formal position decreases — every \
                 recursive call to `{name}` must pass a car/cdr-projection of the \
                 same formal in that formal's position (general measures / \
                 termination proofs are future work)"
            ))
        }
    }

    /// Walk a `defun` body: validate every head and atom, collecting the
    /// argument lists of recursive calls.
    fn check_body<'a>(
        &self,
        name: &str,
        params: &[String],
        e: &'a SExpr,
        calls: &mut Vec<&'a [SExpr]>,
    ) -> Result<(), String> {
        match e {
            SExpr::Atom(Atom::Str { .. }) => Ok(()),
            SExpr::Atom(Atom::Symbol(s)) => {
                let s = s.as_str();
                if s == "t"
                    || s == "nil"
                    || params.iter().any(|p| p == s)
                    || s.parse::<Int>().is_ok()
                {
                    Ok(())
                } else {
                    Err(format!("unbound variable `{s}` in the body"))
                }
            }
            SExpr::List(items) => {
                let Some((head, args)) = items.split_first() else {
                    return Err("empty application `()`".into());
                };
                let Some(h) = head.as_symbol() else {
                    return Err("application head is not a symbol (no higher-order \
                                forms in the ACL2 slice)"
                        .into());
                };
                if h == "quote" {
                    return if args.len() == 1 {
                        Ok(()) // quoted data: no code inside
                    } else {
                        Err("quote takes exactly one argument".into())
                    };
                }
                let expected = if let Some(arity) = int_op_arity(h) {
                    arity
                } else if let Some(arity) = reserved_head(h) {
                    arity
                } else if h == name {
                    calls.push(args);
                    params.len()
                } else if let Some(def) = self.defs.get(h) {
                    def.params.len()
                } else {
                    return Err(format!(
                        "call to undefined function `{h}` — ACL2 requires \
                         definition before use"
                    ));
                };
                if args.len() != expected {
                    return Err(format!(
                        "`{h}` expects {expected} argument(s), got {}",
                        args.len()
                    ));
                }
                for a in args {
                    self.check_body(name, params, a, calls)?;
                }
                Ok(())
            }
        }
    }

    /// Install an admissible definition: compile the (translated) body with
    /// the recursive head pre-registered, and enter `{f = λ…} ⊢ f = λ…` into
    /// the dictionary. Return-type disambiguation extends
    /// `session::Session::install`'s trick: try `bool` (predicates), then
    /// `sexpr` (data functions), then `int` (integer-valued functions, e.g.
    /// `len`); the wrong choices fail to type-check.
    fn install(&mut self, name: &str, params: &[String], body: &SExpr) -> Result<(), Acl2Error> {
        let tau = self.sem0.tau();
        let mut last: Option<HolError> = None;
        for ret in [Type::bool(), tau, Type::int()] {
            let dummy = if ret == Type::bool() {
                mk_bool(false)
            } else if ret == Type::int() {
                mk_int(0i128)
            } else {
                self.sem0.tau_nil()
            };
            match self.try_install(name, params, body, &ret, dummy) {
                Ok(()) => return Ok(()),
                Err(e) => last = Some(e),
            }
        }
        Err(Acl2Error::Inadmissible {
            name: name.to_string(),
            reason: match last {
                Some(e) => format!("body does not type-check: {e}"),
                None => "cannot type the definition".into(),
            },
        })
    }

    /// One return-type attempt; `self.defs` is only mutated on success.
    fn try_install(
        &mut self,
        name: &str,
        params: &[String],
        body: &SExpr,
        ret: &Type,
        dummy: Term,
    ) -> Result<(), HolError> {
        let placeholder = build_def_with_ret(name, params, dummy, ret)?;
        let staged = self.defs.with(placeholder);
        let sem = LispSemantics::with_defs(staged)?;
        let body_term = sem.compile(body)?;
        let def = build_def(name, params, body_term)?;
        self.defs = self.defs.with(def);
        Ok(())
    }

    // ------------------------------------------------------------------
    // defthm — ground decidable goals only
    // ------------------------------------------------------------------

    /// `(defthm name goal)`: prove `goal` by kernel reduction, or reject.
    /// Only **ground** goals are accepted; a goal with free variables is a
    /// universally quantified claim this slice cannot prove (induction is not
    /// implemented) and is rejected saying so.
    fn admit_defthm(&mut self, items: &[SExpr]) -> Result<String, Acl2Error> {
        if items.len() != 3 {
            return Err(Acl2Error::Malformed(
                "defthm: expected (defthm name goal)".into(),
            ));
        }
        let name = items[1]
            .as_symbol()
            .ok_or_else(|| Acl2Error::Malformed("defthm: name is not a symbol".into()))?
            .to_string();
        let thm = self.prove_ground(&name, &items[2])?;
        self.thms.insert(name.clone(), thm);
        Ok(name)
    }

    /// Prove a ground goal: reduce it to a boolean literal by the kernel and
    /// conclude `hyps ⊢ goal` when (and only when) it lands on `T`.
    fn prove_ground(&self, name: &str, goal: &SExpr) -> Result<Thm, Acl2Error> {
        let unprovable = |reason: String| Acl2Error::Unprovable {
            name: name.to_string(),
            reason,
        };
        // Groundness first, for the honest rejection message.
        let mut vars = Vec::new();
        self.scan_free(goal, &mut vars);
        if !vars.is_empty() {
            vars.sort();
            vars.dedup();
            return Err(unprovable(format!(
                "the goal has free variables ({}) — a universally quantified claim \
                 needs induction, which this slice does not implement; only ground \
                 decidable goals are accepted",
                vars.join(", ")
            )));
        }
        let out = self.reduce(goal).map_err(|e| match e {
            Acl2Error::Unprovable { .. } | Acl2Error::Inadmissible { .. } => e,
            other => unprovable(format!("the goal did not reduce: {other}")),
        })?;
        if out.kind == Acl2ValueKind::Data || out.kind == Acl2ValueKind::Int {
            return Err(unprovable(
                "the goal is not a boolean form (it reduces to data, not t/nil)".into(),
            ));
        }
        match as_bool(&out.value) {
            // out.thm : hyps ⊢ goal = T ; eqt_elim : hyps ⊢ goal.
            Some(true) => out.thm.eqt_elim().map_err(kernel_err),
            Some(false) => Err(unprovable(
                "the goal is FALSE: it reduces to nil (refuted by computation)".into(),
            )),
            None => Err(unprovable(
                "the goal did not decide to a boolean literal".into(),
            )),
        }
    }

    /// Collect the free variables of a form: non-`t`/`nil`, non-numeral
    /// symbols in operand position, outside `quote` (function heads are
    /// validated separately by [`translate`](Self::translate)).
    fn scan_free(&self, e: &SExpr, vars: &mut Vec<String>) {
        match e {
            SExpr::Atom(Atom::Str { .. }) => {}
            SExpr::Atom(Atom::Symbol(s)) => {
                let s = s.as_str();
                if s != "t" && s != "nil" && s.parse::<Int>().is_err() {
                    vars.push(s.to_string());
                }
            }
            SExpr::List(items) => {
                if items.first().and_then(SExpr::as_symbol) == Some("quote") {
                    return;
                }
                for a in items.iter().skip(1) {
                    self.scan_free(a, vars);
                }
            }
        }
    }

    // ------------------------------------------------------------------
    // Surface translation (ACL2 spellings → the value-semantics dialect)
    // ------------------------------------------------------------------

    /// Rewrite an ACL2 form into the value-semantics dialect (`equal` →
    /// integer `=` or `eq?`, `endp` → `null?`, `atom` → `atom?`, `zp n` →
    /// `(<= n 0)`, `natp n` → `(<= 0 n)`), validating heads, arities, and
    /// variable scope as it goes. `vars` are the in-scope formals; `self_name`
    /// is the function being defined (its recursive calls are legal).
    fn translate(
        &self,
        e: &SExpr,
        vars: &[String],
        self_name: Option<&str>,
    ) -> Result<SExpr, Acl2Error> {
        match e {
            SExpr::Atom(Atom::Str { .. }) => Ok(e.clone()),
            SExpr::Atom(Atom::Symbol(s)) => {
                let s = s.as_str();
                if s == "t" || s == "nil" || vars.iter().any(|p| p == s) || s.parse::<Int>().is_ok()
                {
                    Ok(e.clone())
                } else {
                    Err(Acl2Error::Malformed(format!("unbound variable `{s}`")))
                }
            }
            SExpr::List(items) => {
                let Some((head, args)) = items.split_first() else {
                    return Err(Acl2Error::Malformed("empty application `()`".into()));
                };
                let Some(h) = head.as_symbol() else {
                    return Err(Acl2Error::Malformed(
                        "application head is not a symbol (no higher-order forms in \
                         the ACL2 slice)"
                            .into(),
                    ));
                };
                if h == "quote" {
                    if args.len() != 1 {
                        return Err(Acl2Error::Malformed(
                            "quote takes exactly one argument".into(),
                        ));
                    }
                    return Ok(e.clone()); // data — no translation inside
                }
                if h == "cond" {
                    return Err(Acl2Error::Malformed(
                        "the ACL2 slice uses ternary `if`, not `cond`".into(),
                    ));
                }
                // `zp n` / `natp n` — integer sugar for `n ≤ 0` / `0 ≤ n`
                // (on `int`-typed terms `integerp` is `t` by typing).
                if h == "zp" || h == "natp" {
                    if args.len() != 1 {
                        return Err(Acl2Error::Malformed(format!(
                            "`{h}` expects 1 argument, got {}",
                            args.len()
                        )));
                    }
                    let n = self.translate(&args[0], vars, self_name)?;
                    let zero = SExpr::Atom(Atom::Symbol("0".into()));
                    let (a, b) = if h == "zp" { (n, zero) } else { (zero, n) };
                    return Ok(SExpr::List(vec![
                        SExpr::Atom(Atom::Symbol("<=".into())),
                        a,
                        b,
                    ]));
                }
                let (new_head, expected) = if let Some(arity) = int_op_arity(h) {
                    (h.to_string(), arity)
                } else if let Some(arity) = reserved_head(h) {
                    let renamed = match h {
                        // `equal` is generic in ACL2: route it to integer `=`
                        // when either side is syntactically arithmetic, else
                        // to the sexpr `eq?` (atoms, plus the structural
                        // fallback in `reduce_equal`).
                        "equal" if args.iter().any(is_int_form) => "=",
                        "equal" => "eq?",
                        "endp" => "null?",
                        "atom" => "atom?",
                        other => other,
                    };
                    (renamed.to_string(), arity)
                } else if Some(h) == self_name {
                    (h.to_string(), vars.len())
                } else if let Some(def) = self.defs.get(h) {
                    (h.to_string(), def.params.len())
                } else {
                    return Err(Acl2Error::Malformed(format!(
                        "call to undefined function `{h}` — ACL2 requires definition \
                         before use"
                    )));
                };
                if args.len() != expected {
                    return Err(Acl2Error::Malformed(format!(
                        "`{h}` expects {expected} argument(s), got {}",
                        args.len()
                    )));
                }
                // Kernel integers are typed `int` terms, not sexpr data — an
                // arithmetic form in a list-typed position is rejected with a
                // clear message (instead of leaving a stuck ill-typed term).
                if sexpr_positions(&new_head)
                    && let Some(bad) = args.iter().find(|a| is_int_form(a))
                {
                    return Err(Acl2Error::Malformed(format!(
                        "integer `{bad:?}` in a list position of `{h}` — kernel \
                         integers are typed `int` terms, not sexpr data; mixed \
                         integer/list structure is not supported in this slice"
                    )));
                }
                let mut out = Vec::with_capacity(items.len());
                out.push(SExpr::Atom(Atom::Symbol(new_head.into())));
                for a in args {
                    out.push(self.translate(a, vars, self_name)?);
                }
                Ok(SExpr::List(out))
            }
        }
    }
}

// ============================================================================
// The ACL2 surface tables
// ============================================================================

/// The non-arithmetic primitive heads and their arities. (Note ternary `if`;
/// there is no `cond` in this dialect.)
fn reserved_head(name: &str) -> Option<usize> {
    match name {
        "car" | "cdr" | "consp" | "atom" | "endp" => Some(1),
        "cons" | "equal" => Some(2),
        "if" => Some(3),
        _ => None,
    }
}

/// The ground-arithmetic operator heads.
const INT_OPS: [&str; 7] = ["+", "-", "*", "<=", "=", "zp", "natp"];

/// The arity of a ground-arithmetic operator head (`+ - * <= =` binary,
/// `zp` / `natp` unary); `None` for non-arithmetic heads.
fn int_op_arity(name: &str) -> Option<usize> {
    match name {
        "+" | "-" | "*" | "<=" | "=" => Some(2),
        "zp" | "natp" => Some(1),
        _ => None,
    }
}

/// Is a form **syntactically arithmetic**: a numeral, an arithmetic-op form,
/// or an `equal` with an arithmetic side? Used to route `equal` (integer `=`
/// vs sexpr `eq?`) and to reject integers in list-typed positions. Syntactic
/// on purpose — a user call is never classified arithmetic, even if it
/// returns an integer.
fn is_int_form(e: &SExpr) -> bool {
    match e {
        SExpr::Atom(Atom::Symbol(s)) => s.parse::<Int>().is_ok(),
        SExpr::Atom(_) => false,
        SExpr::List(items) => match items.first().and_then(SExpr::as_symbol) {
            Some(h) if int_op_arity(h).is_some() => true,
            Some("equal") if items.len() == 3 => is_int_form(&items[1]) || is_int_form(&items[2]),
            _ => false,
        },
    }
}

/// Do this (translated) head's arguments sit in `sexpr`-typed positions?
/// True for the list primitives, `eq?`, and user calls (whose formals are
/// always `sexpr`-typed); false for the arithmetic operators and `if` (whose
/// branches may legitimately be integers).
fn sexpr_positions(head: &str) -> bool {
    head != "if" && int_op_arity(head).is_none()
}

// ============================================================================
// Small helpers
// ============================================================================

/// The RHS of an equational conclusion.
fn rhs_of(thm: &Thm) -> Result<Term, Acl2Error> {
    thm.concl()
        .as_eq()
        .map(|(_, r)| r.clone())
        .ok_or_else(|| kernel_err("theorem conclusion is not an equation"))
}

/// The parameter names of a `(p₁ … pₙ)` formal list — distinct plain symbols.
fn param_names(params: &SExpr) -> Result<Vec<String>, String> {
    let SExpr::List(items) = params else {
        return Err("parameter list is not a list".into());
    };
    let mut out = Vec::with_capacity(items.len());
    for p in items {
        let Some(s) = p.as_symbol() else {
            return Err("parameter is not a symbol".into());
        };
        if matches!(s, "t" | "nil") || reserved_head(s).is_some() || INT_OPS.contains(&s) {
            return Err(format!("parameter `{s}` shadows a primitive"));
        }
        if s.parse::<Int>().is_ok() {
            return Err(format!("parameter `{s}` is a numeral"));
        }
        if out.iter().any(|q| q == s) {
            return Err(format!("duplicate parameter `{s}`"));
        }
        out.push(s.to_string());
    }
    Ok(out)
}

/// Is `e` a **non-empty** `car`/`cdr` chain applied to exactly the formal
/// `formal`? (`(cdr x)`, `(car (cdr x))`, … — the structural-descent shape.)
fn is_proper_projection(e: &SExpr, formal: &str) -> bool {
    fn depth(e: &SExpr, formal: &str) -> Option<usize> {
        match e {
            SExpr::Atom(Atom::Symbol(s)) if s.as_str() == formal => Some(0),
            SExpr::List(items) if items.len() == 2 => match items[0].as_symbol() {
                Some("car") | Some("cdr") => depth(&items[1], formal).map(|d| d + 1),
                _ => None,
            },
            _ => None,
        }
    }
    depth(e, formal).is_some_and(|d| d >= 1)
}
