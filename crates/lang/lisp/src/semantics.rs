//! The Lisp **reduction relation as a [`Semantics`]** (`hol` feature).
//!
//! [`LispSemantics`] is the middle axis of the parametric reduction API: it
//! *is* the small-step reduction relation on carved `sexpr` operator terms.
//! Each [`step`](Semantics::step) finds the leftmost-innermost redex, applies
//! **one** computation law (a `proj_scons` / `consp` / `atom?` / `not`-fold
//! kernel theorem — the same laws the big-step the big-step evaluator
//! composed), and congruence-lifts it to a `⊢ term = term'` over the whole
//! term. [`compose`](Semantics::compose) is [`Thm::trans`], so a `drive` to a
//! normal form yields one composite `⊢ input = value`.
//!
//! A term is a **value** (normal form; `step` → `None`) when it is a carved
//! `sexpr` datum (`atom` / `snil` / `scons` chains) or a `bool` literal.
//!
//! Reduction runs over a **compiled program term**: [`LispSemantics::compile`]
//! lowers a parsed [`SExpr`] to the operator-application form (`quote` → data;
//! `car` / `cdr` / `cons` / `atom?` / `consp` → carved/Lisp operators applied
//! to compiled arguments; `null? E` → `¬ (consp E)`; `eq?` → a HOL equation at
//! `sexpr`; `if` / `cond` → the kernel `cond`; `lambda` → an abstraction; and a
//! call `(f args)` to a user [`defun`](crate::defs) → the def's free-variable
//! head applied to compiled args). This is the "data → operator application"
//! bridge the plain [`crate::Lisp::lower`] does not build.
//!
//! Two redexes are non-congruential:
//! - **`eq?`** on two atom values decides the HOL equation `atom b₁ = atom b₂`
//!   to `T`/`F` — the blob (dis)equality lifted through `atom` injectivity +
//!   congruence, a single self-contained step whose LHS *is* the redex, so it
//!   composes anywhere (not only at the top level).
//! - **`cond α c x y`** reduces only its condition `c` to a `bool` literal, then
//!   fires the selected `cond_true`/`cond_false` clause — the unselected branch
//!   is discarded, never reduced (the divergence guard for recursion).
//!
//! A **`defun` call** unfolds against the function's *assumed* equation
//! `{f = λ…} ⊢ f = λ…` (congruence to rewrite the head, then β), so the
//! `defun` equations ride the composite as **hypotheses** — sound recursion in
//! a total HOL without any new axiom. See [`crate::defs`].
//!
//! The value read off a normal form is always the RHS of a genuine kernel
//! theorem; nothing here mints new trusted rules.

use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::derived::DerivedRules;
use covalence_hol_eval::hol::hol_not;
use covalence_hol_eval::mk_blob;
use covalence_init::init::cond::{cond_false, cond_true};
use covalence_init::init::ext::{TermExt, ThmExt};
use covalence_init::init::inductive::carved::{CarvedSExpr, LeafKind, carved};
use covalence_init::init::lisp::{Lisp as KernelLisp, lisp};
use covalence_init::init::logic::simp;
use covalence_init::{Term, Type};

use covalence_repl_core::{Repr, Semantics, StepCert};
use covalence_sexp::{Atom, SExpr};

use crate::defs::Defs;
use crate::hol::HolError;

fn theory_err(e: impl core::fmt::Display) -> HolError {
    HolError::Theory(e.to_string())
}
fn kernel_err(e: impl core::fmt::Display) -> HolError {
    HolError::Kernel(e.to_string())
}

/// The value-kind of a normal form, for printing (mirrors the big-step
/// evaluator's `ValueKind`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ValueKind {
    /// A carved `sexpr` datum (`atom` / `snil` / `scons`).
    Data,
    /// A `bool` literal (a predicate / `eq?` result).
    Bool,
}

// ============================================================================
// Repr — the kernel S-expression term encoding
// ============================================================================

/// The Lisp representation axis: reduction is over the kernel carved `sexpr`
/// operator [`Term`].
#[derive(Clone, Copy, Debug, Default)]
pub struct LispRepr;

impl Repr for LispRepr {
    type Term = Term;
}

// ============================================================================
// StepCert — one certified step
// ============================================================================

/// A single certified reduction step: the reduct term plus `⊢ from = to`.
#[derive(Clone, Debug)]
pub struct LispStep {
    to: Term,
    thm: Thm,
}

impl StepCert<LispRepr> for LispStep {
    type Thm = Thm;
    fn to(&self) -> &Term {
        &self.to
    }
    fn thm(&self) -> &Thm {
        &self.thm
    }
    fn into_parts(self) -> (Term, Thm) {
        (self.to, self.thm)
    }
}

// ============================================================================
// Semantics — THE small-step relation
// ============================================================================

/// The Lisp small-step reduction relation over the process-global carved +
/// Lisp theories, plus the session's user-`defun` dictionary
/// ([`Defs`]) — consulted to unfold `(f args)` calls against their assumed
/// equations (see [`crate::defs`]).
pub struct LispSemantics {
    cs: &'static CarvedSExpr,
    l: &'static KernelLisp,
    defs: Defs,
}

/// What a `t` / `nil` literal should compile to in a given position: a `bool`
/// literal (test / bool-valued branch) or a `sexpr` datum (data-valued branch).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Hint {
    /// Prefer a `bool` literal (`t` → `T`, `nil` → `F`).
    Bool,
    /// Prefer a `sexpr` datum (`t` → `atom t`, `nil` → `snil`).
    Data,
}

impl LispSemantics {
    /// Bind the process-global carved `sexpr` + Lisp theories, with no
    /// user definitions.
    pub fn new() -> Result<Self, HolError> {
        Self::with_defs(Defs::new())
    }

    /// Bind the theories with a user-`defun` dictionary — the calls in a
    /// compiled program unfold against these assumed equations.
    pub fn with_defs(defs: Defs) -> Result<Self, HolError> {
        Ok(LispSemantics {
            cs: carved().map_err(theory_err)?,
            l: lisp().map_err(theory_err)?,
            defs,
        })
    }

    /// The definition dictionary this semantics reduces against.
    pub fn defs(&self) -> &Defs {
        &self.defs
    }

    /// The `sexpr` carrier type.
    pub(crate) fn tau(&self) -> Type {
        self.cs.tau.clone()
    }

    /// Compile a parsed [`SExpr`] into the operator-application program term.
    /// A bare `t` / `nil` compiles as *data* by default (top level).
    pub fn compile(&self, e: &SExpr) -> Result<Term, HolError> {
        self.compile_h(e, Hint::Data)
    }

    fn compile_h(&self, e: &SExpr, hint: Hint) -> Result<Term, HolError> {
        match e {
            SExpr::Atom(a) => self.atom_or_var(a, hint),
            SExpr::List(items) => self.compile_form(items),
        }
    }

    /// An atom in operand position: a `t`/`nil` literal (per `hint`), an
    /// in-scope user variable / function-as-value (a free var from a `defun`),
    /// or a bare symbol datum.
    fn atom_or_var(&self, a: &Atom, hint: Hint) -> Result<Term, HolError> {
        if let Atom::Symbol(s) = a {
            match s.as_str() {
                "t" => {
                    return Ok(match hint {
                        Hint::Bool => covalence_hol_eval::mk_bool(true),
                        Hint::Data => self.symbol_atom("t"),
                    });
                }
                "nil" => {
                    return Ok(match hint {
                        Hint::Bool => covalence_hol_eval::mk_bool(false),
                        Hint::Data => self.cs.snil.clone(),
                    });
                }
                // A parameter / bound variable of a surrounding `defun` /
                // `lambda` compiles to a `sexpr`-typed free variable.
                other => {
                    return Ok(Term::free(other, self.cs.tau.clone()));
                }
            }
        }
        self.atom_data(a)
    }

    fn symbol_atom(&self, s: &str) -> Term {
        Term::app(self.cs.atom.clone(), mk_blob(s.as_bytes().to_vec()))
    }

    /// A `sexpr` atom datum for the symbol `s` — the public [`symbol_atom`]
    /// (used by the session to build definition-ack values).
    ///
    /// [`symbol_atom`]: Self::symbol_atom
    pub fn symbol_value(&self, s: &str) -> Term {
        self.symbol_atom(s)
    }

    /// The empty-list datum `snil : sexpr`.
    pub fn tau_nil(&self) -> Term {
        self.cs.snil.clone()
    }

    fn compile_form(&self, items: &[SExpr]) -> Result<Term, HolError> {
        let (head, args) = items
            .split_first()
            .ok_or_else(|| HolError::Stuck("()".into()))?;
        // A `((lambda …) …)` application: the head is itself a form.
        if let SExpr::List(_) = head {
            return self.compile_app(head, args);
        }
        let op = head
            .as_symbol()
            .ok_or_else(|| HolError::Stuck("application head is not a symbol".into()))?;
        match (op, args.len()) {
            // `quote` is the special form: its argument is *data*.
            ("quote", 1) => self.data(&args[0]),
            ("car", 1) => Ok(Term::app(self.cs.car.clone(), self.compile(&args[0])?)),
            ("cdr", 1) => Ok(Term::app(self.cs.cdr.clone(), self.compile(&args[0])?)),
            ("cons", 2) => {
                let h = self.compile(&args[0])?;
                let t = self.compile(&args[1])?;
                Ok(Term::app(Term::app(self.cs.scons.clone(), h), t))
            }
            ("atom?" | "atom", 1) => Ok(Term::app(self.l.atom_p.clone(), self.compile(&args[0])?)),
            ("consp" | "pair?", 1) => Ok(Term::app(self.l.consp.clone(), self.compile(&args[0])?)),
            // `null? E` compiles to `¬ (consp E)` — congruential: `consp v`
            // fires to a literal, then `¬ literal` folds via `simp`.
            ("null?" | "null", 1) => Ok(hol_not(Term::app(
                self.l.consp.clone(),
                self.compile(&args[0])?,
            ))),
            // `eq?` compiles to the **real HOL equation** `a = b : bool` at
            // element type `sexpr`. It is congruential (operands reduce to atom
            // values first); once both are atoms, the leaf step
            // ([`eval_eq_leaf`]) decides it to `T`/`F`.
            ("eq?" | "eq", 2) => {
                let a = self.compile(&args[0])?;
                let b = self.compile(&args[1])?;
                Ok(Term::app(Term::app(Term::eq_op(self.cs.tau.clone()), a), b))
            }
            // `if` — sugar for a two-clause `cond`.
            ("if", 3) => self.compile_cond_clauses(&[
                (self.compile_h(&args[0], Hint::Bool)?, &args[1]),
                (covalence_hol_eval::mk_bool(true), &args[2]),
            ]),
            // `cond` — a chain of `(test branch)` clauses.
            ("cond", _) => self.compile_cond(args),
            // `lambda` — an anonymous abstraction (β-reducible when applied).
            ("lambda", 2) => self.compile_lambda(&args[0], &args[1]),
            // A call to a user-defined function `f` (an assumed `defun`), or a
            // **forward reference** to one not yet defined — mutual recursion in
            // the metacircular interpreter needs this. Either way it compiles to
            // a free-variable head (the def's, if present; else a fresh
            // `sexpr… → sexpr` head that a later `defun` will match by
            // name+type). Reserved special-form / builtin names are excluded so
            // a misspelled primitive is still an error.
            (name, n) if !is_reserved(name) => self.compile_user_call(name, args, n),
            (other, n) => Err(HolError::Stuck(format!(
                "unknown or misapplied operator `{other}` (arity {n})"
            ))),
        }
    }

    /// Compile a `lambda` `(lambda (p₁ … pₙ) body)` into `λp₁ … pₙ. body`.
    fn compile_lambda(&self, params: &SExpr, body: &SExpr) -> Result<Term, HolError> {
        let ps = self.param_names(params)?;
        let mut lam = self.compile(body)?;
        for p in ps.iter().rev() {
            let closed = covalence_core::subst::close(&lam, p);
            lam = Term::abs(self.cs.tau.clone(), closed);
        }
        Ok(lam)
    }

    /// Compile an application whose head is itself a form (e.g. a `lambda`):
    /// `(head a₁ … aₙ)` → `App(… App(head, a₁) …, aₙ)`.
    fn compile_app(&self, head: &SExpr, args: &[SExpr]) -> Result<Term, HolError> {
        let mut t = self.compile(head)?;
        for a in args {
            t = Term::app(t, self.compile(a)?);
        }
        Ok(t)
    }

    /// Compile a call to a user-defined function `name` applied to `args`. Uses
    /// the def's stored head if present; otherwise (a forward reference)
    /// synthesizes a `sexpr… → sexpr` free-variable head — a later `defun` of
    /// `name` with the same signature installs the matching assumption, and the
    /// unfold then fires by name+type.
    fn compile_user_call(
        &self,
        name: &str,
        args: &[SExpr],
        arity: usize,
    ) -> Result<Term, HolError> {
        let head = match self.defs.get(name) {
            Some(def) => def.head.clone(),
            None => Term::free(name, self.forward_head_ty(arity)),
        };
        let mut t = head;
        for a in args {
            t = Term::app(t, self.compile(a)?);
        }
        Ok(t)
    }

    /// `sexpr → … → sexpr` (`arity` arrows) — the default type of a
    /// forward-referenced function's head.
    fn forward_head_ty(&self, arity: usize) -> Type {
        let mut ty = self.cs.tau.clone();
        for _ in 0..arity {
            ty = Type::fun(self.cs.tau.clone(), ty);
        }
        ty
    }

    /// Compile a `cond` from its `(test branch)` clause list.
    fn compile_cond(&self, clauses: &[SExpr]) -> Result<Term, HolError> {
        let mut parsed: Vec<(Term, &SExpr)> = Vec::with_capacity(clauses.len());
        for c in clauses {
            let SExpr::List(items) = c else {
                return Err(HolError::Stuck("cond clause is not a list".into()));
            };
            if items.len() != 2 {
                return Err(HolError::Stuck("cond clause must be (test branch)".into()));
            }
            let test = self.compile_h(&items[0], Hint::Bool)?;
            parsed.push((test, &items[1]));
        }
        self.compile_cond_clauses(&parsed)
    }

    /// Build the nested `cond τ` term from compiled `(test, branch-expr)`
    /// clauses. The branch element type `α` is inferred from the first branch
    /// that is not a bare `t`/`nil`; bare `t`/`nil` branches then compile to
    /// that type (bool → `T`/`F`, data → `atom t`/`snil`).
    fn compile_cond_clauses(&self, clauses: &[(Term, &SExpr)]) -> Result<Term, HolError> {
        // Infer α from the first non-`t`/`nil` branch (default: data).
        let mut alpha: Option<Type> = None;
        for (_, e) in clauses {
            if !is_bare_bool_lit(e) {
                let probe = self.compile_h(e, Hint::Data)?;
                alpha = Some(probe.type_of().map_err(kernel_err)?);
                break;
            }
        }
        let alpha = alpha.unwrap_or_else(|| self.cs.tau.clone());
        let hint = if alpha == Type::bool() {
            Hint::Bool
        } else {
            Hint::Data
        };
        // Default (no clause matched): `nil` in the inferred type.
        let mut acc = match hint {
            Hint::Bool => covalence_hol_eval::mk_bool(false),
            Hint::Data => self.cs.snil.clone(),
        };
        for (test, e) in clauses.iter().rev() {
            let branch = self.compile_h(e, hint)?;
            acc = self.mk_cond(&alpha, test.clone(), branch, acc)?;
        }
        Ok(acc)
    }

    /// `cond α c x y` from the kernel `cond` operator at element type `α`.
    fn mk_cond(&self, alpha: &Type, c: Term, x: Term, y: Term) -> Result<Term, HolError> {
        let op = covalence_hol_eval::defs::cond(alpha.clone());
        Ok(Term::app(Term::app(Term::app(op, c), x), y))
    }

    /// The parameter names of a `(p₁ … pₙ)` formal list.
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

    // ---- data compilation (the `quote` payload) -------------------------

    fn data(&self, e: &SExpr) -> Result<Term, HolError> {
        match e {
            SExpr::Atom(a) => self.atom_data(a),
            SExpr::List(items) => {
                let mut acc = self.cs.snil.clone();
                for it in items.iter().rev() {
                    let h = self.data(it)?;
                    acc = Term::app(Term::app(self.cs.scons.clone(), h), acc);
                }
                Ok(acc)
            }
        }
    }

    fn atom_data(&self, a: &Atom) -> Result<Term, HolError> {
        let bytes: Vec<u8> = match a {
            Atom::Symbol(s) => s.as_bytes().to_vec(),
            Atom::Str { bytes, .. } => bytes.to_vec(),
        };
        Ok(Term::app(self.cs.atom.clone(), mk_blob(bytes)))
    }

    // ---- value classification -------------------------------------------

    /// The value-kind of a normal form, or `None` if `t` is not a value.
    pub fn value_kind(&self, t: &Term) -> Option<ValueKind> {
        if self.is_data_value(t) {
            Some(ValueKind::Data)
        } else if t.as_bool().is_some() {
            Some(ValueKind::Bool)
        } else {
            None
        }
    }

    /// Is `t` a fully-evaluated `sexpr` datum (`atom` / `snil` / `scons` chain)?
    fn is_data_value(&self, t: &Term) -> bool {
        if *t == self.cs.snil {
            return true;
        }
        if self.as_atom(t).is_some() {
            return true;
        }
        if let Some((h, tl)) = self.as_scons(t) {
            return self.is_data_value(&h) && self.is_data_value(&tl);
        }
        false
    }

    // ---- the redex reducer (one leftmost-innermost step) ----------------

    /// Reduce the leftmost-innermost redex of `t` by **one** law, returning
    /// `⊢ t = t'` congruence-lifted, or `None` if `t` is a value.
    fn step_term(&self, t: &Term) -> Result<Option<LispStep>, HolError> {
        if self.value_kind(t).is_some() {
            return Ok(None);
        }
        // A `cond α c x y` — reduce ONLY the condition, then select a branch.
        // Handled before the generic congruence so the *unselected* branch is
        // never reduced (call-by-name on the branches; the divergence guard for
        // recursive definitions).
        if let Some((alpha, c, x, y)) = self.as_cond(t) {
            return self.step_cond(&alpha, &c, &x, &y).map(Some);
        }
        // An `eq?` redex `a = b : sexpr` whose operands are **both atom
        // values** — decide it to `T`/`F` (a self-contained leaf step). If the
        // operands are not yet values, fall through to the generic congruence,
        // which reduces them first.
        if let Some((a, b)) = self.as_eq_redex(t)
            && self.as_atom(&a).is_some()
            && self.as_atom(&b).is_some()
        {
            return self.eval_eq_leaf(&a, &b).map(Some);
        }
        // `not p` — a unary spine on the `not` head.
        if let Some(p) = self.as_not(t) {
            return self.step_not(t, &p);
        }
        // General application: `App(f, arg)`.
        let Some((f, arg)) = t.as_app() else {
            return Err(HolError::Stuck(format!("no reduction for `{t}`")));
        };
        // 1. Reduce inside the argument (innermost).
        if let Some(inner) = self.step_term(arg)? {
            let lifted = inner.thm.clone().cong_arg(f.clone()).map_err(kernel_err)?;
            let to = Term::app(f.clone(), inner.to.clone());
            return Ok(Some(LispStep { to, thm: lifted }));
        }
        // 2. Reduce inside the function position ONLY when it is itself an
        //    application (a curried spine, e.g. `App(scons, h)` in a `cons`); a
        //    bare operator head (`car`/`cdr`/`consp`/`atom_p`) is irreducible
        //    and is handled by `fire` below. A **partial user-call spine**
        //    (`App(f, a)` with `f` a `defun` head) is NOT reduced here — it is
        //    fired whole by `fire` once the outer application supplies the last
        //    argument, so recursing would strand it at the wrong arity.
        if f.as_app().is_some()
            && !self.is_user_spine(f)
            && let Some(inner) = self.step_term(f)?
        {
            let lifted = inner.thm.clone().cong_fn(arg.clone()).map_err(kernel_err)?;
            let to = Term::app(inner.to.clone(), arg.clone());
            return Ok(Some(LispStep { to, thm: lifted }));
        }
        // 3. Redex head with value sub-terms — fire the law.
        self.fire(t, f, arg)
    }

    /// Is `t`'s application-spine head a user `defun` free variable? Such a
    /// spine must be fired whole (at full arity) by [`fire`], not reduced
    /// piecewise in the function position.
    fn is_user_spine(&self, t: &Term) -> bool {
        let (head, _) = unwind_app(t);
        head.as_free()
            .map(|v| self.defs.contains(v.name()))
            .unwrap_or(false)
    }

    /// Fire the head computation law of a redex `t = App(f, v)` whose argument
    /// `v` is a value and whose head `f` is a value/operator.
    fn fire(&self, t: &Term, f: &Term, v: &Term) -> Result<Option<LispStep>, HolError> {
        if *f == self.cs.car {
            return self.fire_proj(t, false, v).map(Some);
        }
        if *f == self.cs.cdr {
            return self.fire_proj(t, true, v).map(Some);
        }
        if *f == self.l.atom_p {
            return self.fire_pred(t, Pred::Atom, v).map(Some);
        }
        if *f == self.l.consp {
            return self.fire_pred(t, Pred::Consp, v).map(Some);
        }
        // A β-redex `(λ. body) v` — fire one β step.
        if f.as_abs().is_some() {
            return self.fire_beta(t).map(Some);
        }
        // A fully-applied user-defined function `(g a₁ … aₙ)` whose spine head
        // is a `defun` free variable — unfold against its assumed equation,
        // then β-reduce the arguments in.
        if let Some(step) = self.try_unfold_user_call(t)? {
            return Ok(Some(step));
        }
        Err(HolError::Stuck(format!("no reduction for `{t}`")))
    }

    /// One β-contraction of a redex `(λ:τ. body) v` — the kernel
    /// [`Thm::beta_conv`] equation, packaged as a step.
    fn fire_beta(&self, redex: &Term) -> Result<LispStep, HolError> {
        let thm = Thm::beta_conv(redex.clone()).map_err(kernel_err)?;
        let to = self.rhs(&thm)?;
        Ok(LispStep { to, thm })
    }

    /// If `t`'s application spine head is a user `defun` free variable applied
    /// to exactly its arity of (value) arguments, unfold it: rewrite the head
    /// against the assumed equation `f = λparams. body` (congruence), then
    /// β-reduce each argument. Returns the composite `{f=λ} ⊢ (f a…) = body[a…]`.
    fn try_unfold_user_call(&self, t: &Term) -> Result<Option<LispStep>, HolError> {
        // Unwind the spine `((f a₁) a₂) … aₙ`.
        let (head, args) = unwind_app(t);
        let Some(var) = head.as_free() else {
            return Ok(None);
        };
        let Some(def) = self.defs.get(var.name()) else {
            return Ok(None);
        };
        if args.len() != def.params.len() || def.params.is_empty() {
            // Partial application / arity mismatch — not a redex here.
            return Ok(None);
        }
        // Step A: rewrite the head `f` to `λparams. body` under the argument
        // spine, carrying the `{f=λ}` hypothesis: `⊢ (f a…) = ((λ…) a…)`.
        let mut thm = def.assumption.clone(); // {f=λ} ⊢ f = λ…
        for a in &args {
            thm = thm.cong_fn(a.clone()).map_err(kernel_err)?;
        }
        // Step B: β-reduce the spine `((λparams. body) a₁ … aₙ)` argument by
        // argument (outermost binder first), firing the leftmost redex each
        // time and composing via trans.
        for _ in 0..args.len() {
            let cur = self.rhs(&thm)?;
            let beta = self.beta_leftmost(&cur)?;
            thm = thm.trans(beta).map_err(kernel_err)?;
        }
        let to = self.rhs(&thm)?;
        Ok(Some(LispStep { to, thm }))
    }

    /// `⊢ spine = spine'` firing the **leftmost** β-redex of an
    /// application spine `((λ. body) a₁) … aₙ` — congruence-lifted over the
    /// trailing arguments.
    fn beta_leftmost(&self, t: &Term) -> Result<Thm, HolError> {
        // Descend the function spine to the innermost `App(Abs, arg)`.
        let (f, arg) = t
            .as_app()
            .ok_or_else(|| HolError::Kernel("beta_leftmost: not an application".into()))?;
        if f.as_abs().is_some() {
            // `t = (λ. body) arg` — fire it directly.
            return Thm::beta_conv(t.clone()).map_err(kernel_err);
        }
        // Otherwise the redex is deeper in the function position; recurse and
        // lift under the trailing argument.
        let inner = self.beta_leftmost(f)?;
        inner.cong_fn(arg.clone()).map_err(kernel_err)
    }

    /// `⊢ car v = h` (or `cdr v = t`) for a value `v`.
    fn fire_proj(&self, redex: &Term, take_cdr: bool, v: &Term) -> Result<LispStep, HolError> {
        let law = if let Some((h, tl)) = self.as_scons(v) {
            self.cs.proj_scons(take_cdr, &h, &tl).map_err(kernel_err)?
        } else if let Some(b) = self.as_atom(v) {
            self.cs
                .proj_leaf(take_cdr, LeafKind::Atom(&b))
                .map_err(kernel_err)?
        } else if *v == self.cs.snil {
            self.cs
                .proj_leaf(take_cdr, LeafKind::Nil)
                .map_err(kernel_err)?
        } else {
            return Err(HolError::Stuck(format!("car/cdr of non-`sexpr` `{v}`")));
        };
        self.package(redex, law)
    }

    /// `⊢ pred v = T/F` for a value `v`.
    fn fire_pred(&self, redex: &Term, pred: Pred, v: &Term) -> Result<LispStep, HolError> {
        let law = match pred {
            Pred::Atom => {
                if let Some((h, t)) = self.as_scons(v) {
                    self.l.atom_scons(&h, &t).map_err(kernel_err)?
                } else if let Some(b) = self.as_atom(v) {
                    self.l.atom_atom(&b).map_err(kernel_err)?
                } else if *v == self.cs.snil {
                    self.l.atom_nil().map_err(kernel_err)?
                } else {
                    return Err(HolError::Stuck(format!("atom? of non-`sexpr` `{v}`")));
                }
            }
            Pred::Consp => {
                if let Some((h, t)) = self.as_scons(v) {
                    self.l.consp_scons(&h, &t).map_err(kernel_err)?
                } else if let Some(b) = self.as_atom(v) {
                    self.l.consp_atom(&b).map_err(kernel_err)?
                } else if *v == self.cs.snil {
                    self.l.consp_nil().map_err(kernel_err)?
                } else {
                    return Err(HolError::Stuck(format!("consp of non-`sexpr` `{v}`")));
                }
            }
        };
        self.package(redex, law)
    }

    /// `¬ p`: if `p` is a bool literal, fold `¬ literal` to a literal via
    /// `simp`; otherwise step inside `p`.
    fn step_not(&self, t: &Term, p: &Term) -> Result<Option<LispStep>, HolError> {
        if p.as_bool().is_some() {
            // ⊢ ¬ p = T/F  (a single fold).
            let thm = Thm::refl(t.clone())
                .map_err(kernel_err)?
                .rhs_conv(simp)
                .map_err(kernel_err)?;
            let to = self.rhs(&thm)?;
            return Ok(Some(LispStep { to, thm }));
        }
        // Step inside `p`, lift under `not`.
        if let Some(inner) = self.step_term(p)? {
            let lifted = inner
                .thm
                .clone()
                .cong_arg(self.not_head())
                .map_err(kernel_err)?;
            let to = hol_not(inner.to.clone());
            return Ok(Some(LispStep { to, thm: lifted }));
        }
        Err(HolError::Stuck(format!("no reduction for `{t}`")))
    }

    /// A `cond α c x y` step: reduce the condition `c` to a `bool` literal
    /// (congruence-lifting the step under `cond α · x y`); once `c` is a
    /// literal, fire the [`cond_true`] / [`cond_false`] clause to select a
    /// branch (the unselected branch is discarded, never reduced).
    fn step_cond(&self, alpha: &Type, c: &Term, x: &Term, y: &Term) -> Result<LispStep, HolError> {
        if let Some(b) = c.as_bool() {
            // ⊢ cond α (T|F) x y = (x|y).
            let clause = if b {
                cond_true(alpha, x, y).map_err(kernel_err)?
            } else {
                cond_false(alpha, x, y).map_err(kernel_err)?
            };
            let to = self.rhs(&clause)?;
            return Ok(LispStep { to, thm: clause });
        }
        // Step inside the condition, lifting under `cond α · x y`.
        let inner = self
            .step_term(c)?
            .ok_or_else(|| HolError::Stuck(format!("cond condition is stuck: `{c}`")))?;
        // `cond α c x y = App(App(App(cond α, c), x), y)`; the step is on `c`,
        // so lift it under the head `cond α` then over the trailing `x`, `y`.
        let cond_head = covalence_hol_eval::defs::cond(alpha.clone());
        let lifted = inner
            .thm
            .clone()
            .cong_arg(cond_head) // ⊢ (cond α) c = (cond α) c'
            .map_err(kernel_err)?
            .cong_fn(x.clone()) // ⊢ (cond α c) x = (cond α c') x
            .map_err(kernel_err)?
            .cong_fn(y.clone()) // ⊢ (cond α c x) y = (cond α c' x) y
            .map_err(kernel_err)?;
        let to = self.mk_cond(alpha, inner.to.clone(), x.clone(), y.clone())?;
        Ok(LispStep { to, thm: lifted })
    }

    /// `eq?` on two atom-value operands `atom b₁`, `atom b₂` — decide the HOL
    /// equation `(atom b₁ = atom b₂)` to `T`/`F`, as the self-contained step
    /// `⊢ (atom b₁ = atom b₂) = ⌜b₁ == b₂⌝`. Composes into the reduction chain
    /// (the step's LHS is the actual redex term).
    ///
    /// Both the equal and distinct cases use only sound, hypothesis-free
    /// derived facts: `⊢ (atom b₁ = atom b₂) = (b₁ = b₂)` (the carved `atom`
    /// injectivity `(atom b₁ = atom b₂) ⟹ (b₁ = b₂)` and the congruence
    /// converse, combined by `deduct_antisym`), chained with the decided blob
    /// equality `⊢ (b₁ = b₂) = T|F` (from `reduce_consts`).
    fn eval_eq_leaf(&self, a: &Term, b: &Term) -> Result<LispStep, HolError> {
        let b1 = self
            .as_atom(a)
            .ok_or_else(|| HolError::Stuck("eq? left operand is not an atom".into()))?;
        let b2 = self
            .as_atom(b)
            .ok_or_else(|| HolError::Stuck("eq? right operand is not an atom".into()))?;
        // Decide the underlying blob equality `⊢ (b₁ = b₂) = T|F`.
        let blob_eq = b1.clone().equals(b2.clone()).map_err(kernel_err)?;
        let blob_thm = blob_eq.reduce_consts().map_err(kernel_err)?;
        let decided = self.rhs(&blob_thm)?;
        let thm = match decided.as_bool() {
            // Equal atoms: `⊢ atom b = atom b` (refl), then `⊢ (…) = T`
            // (`eqt_intro`). (Injectivity self-simplifies `b = b` to `T`, so the
            // general iff route degenerates here — this direct form is cleaner.)
            Some(true) => Thm::refl(a.clone())
                .map_err(kernel_err)?
                .eqt_intro()
                .map_err(kernel_err)?,
            // Distinct atoms: `⊢ (atom b₁ = atom b₂) = (b₁ = b₂)` via injectivity
            // + congruence, then chain the decided disequality `= F`.
            Some(false) => self
                .atom_eq_iff_blob(a, b, &b1, &b2)?
                .trans(blob_thm)
                .map_err(kernel_err)?,
            None => {
                return Err(HolError::Kernel(
                    "eq?: blob equality did not decide to a literal".into(),
                ));
            }
        };
        let to = self.rhs(&thm)?;
        Ok(LispStep { to, thm })
    }

    /// `⊢ (atom b₁ = atom b₂) = (b₁ = b₂)` — `atom` injectivity (forward) and
    /// congruence (backward) combined by [`Thm::deduct_antisym`]. Genuine
    /// (hypothesis-free): both directions discharge their assumptions.
    fn atom_eq_iff_blob(&self, a: &Term, b: &Term, b1: &Term, b2: &Term) -> Result<Thm, HolError> {
        let atom_eq = a.clone().equals(b.clone()).map_err(kernel_err)?;
        let blob_eq = b1.clone().equals(b2.clone()).map_err(kernel_err)?;
        // Forward: {atom b₁ = atom b₂} ⊢ (b₁ = b₂) — injectivity + MP.
        let inj = self.cs.inj_atom(b1, b2).map_err(kernel_err)?;
        let fwd = inj
            .imp_elim(Thm::assume(atom_eq.clone()).map_err(kernel_err)?)
            .map_err(kernel_err)?;
        // Backward: {b₁ = b₂} ⊢ (atom b₁ = atom b₂) — congruence under `atom`.
        let bwd = Thm::assume(blob_eq)
            .map_err(kernel_err)?
            .cong_arg(self.cs.atom.clone())
            .map_err(kernel_err)?;
        // deduct_antisym(fwd, bwd) : ⊢ (b₁ = b₂) = (atom b₁ = atom b₂); flip.
        fwd.deduct_antisym(bwd)
            .map_err(kernel_err)?
            .sym()
            .map_err(kernel_err)
    }

    /// Wrap a head law `⊢ redex = rhs` into a [`LispStep`].
    fn package(&self, _redex: &Term, law: Thm) -> Result<LispStep, HolError> {
        let to = self.rhs(&law)?;
        Ok(LispStep { to, thm: law })
    }

    fn rhs(&self, thm: &Thm) -> Result<Term, HolError> {
        thm.concl()
            .as_eq()
            .map(|(_, r)| r.clone())
            .ok_or_else(|| HolError::Kernel("theorem conclusion is not an equation".into()))
    }

    // ---- term inspection ------------------------------------------------

    fn not_head(&self) -> Term {
        // `¬ p = App(not, p)`; recover the `not` head from a fresh `¬ p`.
        // Build `¬ <snil>` once and take its function side.
        let sample = hol_not(self.cs.snil.clone());
        sample.as_app().map(|(f, _)| f.clone()).unwrap_or(sample)
    }

    fn as_not(&self, t: &Term) -> Option<Term> {
        let (f, p) = t.as_app()?;
        (*f == self.not_head()).then(|| p.clone())
    }

    /// Match a HOL equation `a = b : sexpr` (the compiled `eq?` redex),
    /// returning `(a, b)`. Only `sexpr`-typed equations qualify (so an internal
    /// `bool` equation, e.g. inside a decided `cond`, is not treated as `eq?`).
    fn as_eq_redex(&self, t: &Term) -> Option<(Term, Term)> {
        use covalence_core::TermKind;
        let (inner, b) = t.as_app()?;
        let (head, a) = inner.as_app()?;
        match head.kind() {
            TermKind::Eq(alpha) if *alpha == self.cs.tau => Some((a.clone(), b.clone())),
            _ => None,
        }
    }

    /// Match `cond α c x y`, returning `(α, c, x, y)`.
    fn as_cond(&self, t: &Term) -> Option<(Type, Term, Term, Term)> {
        use covalence_core::TypeKind;
        let (cxy, y) = t.as_app()?;
        let (cx, x) = cxy.as_app()?;
        let (head, c) = cx.as_app()?;
        let (spec, _args) = head.as_spec()?;
        if spec.symbol().label() != covalence_hol_eval::defs::cond_spec().symbol().label() {
            return None;
        }
        // Recover α from the head `cond α : bool → α → α → α`.
        let alpha = match head.type_of().ok()?.kind() {
            // `bool → (α → α → α)` — descend one arrow to get `α`.
            TypeKind::Fun(_, rest) => match rest.kind() {
                TypeKind::Fun(a, _) => a.clone(),
                _ => return None,
            },
            _ => return None,
        };
        Some((alpha, c.clone(), x.clone(), y.clone()))
    }

    pub(crate) fn as_scons(&self, v: &Term) -> Option<(Term, Term)> {
        let (inner, t) = v.as_app()?;
        let (op, h) = inner.as_app()?;
        (*op == self.cs.scons).then(|| (h.clone(), t.clone()))
    }

    pub(crate) fn as_atom(&self, v: &Term) -> Option<Term> {
        let (op, b) = v.as_app()?;
        (*op == self.cs.atom).then(|| b.clone())
    }

    pub(crate) fn is_snil(&self, v: &Term) -> bool {
        *v == self.cs.snil
    }

    pub(crate) fn atom_bytes(&self, v: &Term) -> Option<Vec<u8>> {
        let b = self.as_atom(v)?;
        blob_bytes(&b)
    }
}

impl Semantics<LispRepr> for LispSemantics {
    type StepCert = LispStep;
    type Thm = Thm;
    type Error = HolError;

    fn step(&self, term: &Term) -> Result<Option<LispStep>, HolError> {
        self.step_term(term)
    }

    fn compose(&self, prev: Option<Thm>, step_thm: Thm) -> Result<Thm, HolError> {
        match prev {
            None => Ok(step_thm),
            Some(p) => p.trans(step_thm).map_err(kernel_err),
        }
    }
}

#[derive(Clone, Copy, Debug)]
enum Pred {
    Atom,
    Consp,
}

/// Extract the bytes of a blob literal term, via the designated [`Lit`] facade.
fn blob_bytes(t: &Term) -> Option<Vec<u8>> {
    use covalence_core::seam::Lit;
    match Lit::from_term(t)? {
        Lit::Bytes(b) => Some(b.to_vec()),
        _ => None,
    }
}

/// Unwind an application spine `((f a₁) a₂) … aₙ ↦ (f, [a₁, …, aₙ])`.
fn unwind_app(t: &Term) -> (Term, Vec<Term>) {
    let mut args = Vec::new();
    let mut cur = t.clone();
    while let Some((f, a)) = cur.as_app() {
        args.push(a.clone());
        cur = f.clone();
    }
    args.reverse();
    (cur, args)
}

/// A bare `t` / `nil` symbol — the ambiguous atom that compiles to either a
/// `bool` literal or a `sexpr` datum depending on the surrounding `cond`'s
/// inferred branch type.
fn is_bare_bool_lit(e: &SExpr) -> bool {
    matches!(e.as_symbol(), Some("t") | Some("nil"))
}

/// The reserved special-form / builtin operator names — a symbol head that is
/// **not** one of these is a user function call (a `defun` or a forward
/// reference), never an "unknown operator" error.
fn is_reserved(name: &str) -> bool {
    matches!(
        name,
        "quote"
            | "car"
            | "cdr"
            | "cons"
            | "atom?"
            | "atom"
            | "consp"
            | "pair?"
            | "null?"
            | "null"
            | "eq?"
            | "eq"
            | "if"
            | "cond"
            | "lambda"
            | "defun"
            | "define"
            | "label"
    )
}
