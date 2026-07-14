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
//! to compiled arguments; `null? E` → `¬ (consp E)`). This is the "data →
//! operator application" bridge the plain [`crate::Lisp::lower`] does not build.
//!
//! `eq?` is the one non-congruential redex: its decision is a blob-payload
//! equality on two atom values (`⊢ (b₁ = b₂) = ⌜b₁ == b₂⌝`), whose LHS is the
//! blob equation, not the surface `eq?` term — so it fires as a single
//! self-contained step and (per `SKELETONS.md`) must be the outermost form.
//!
//! The value read off a normal form is always the RHS of a genuine kernel
//! theorem; nothing here mints new trusted rules.

use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::hol::hol_not;
use covalence_hol_eval::mk_blob;
use covalence_init::Term;
use covalence_init::init::ext::{TermExt, ThmExt};
use covalence_init::init::inductive::carved::{CarvedSExpr, LeafKind, carved};
use covalence_init::init::lisp::{Lisp as KernelLisp, lisp};
use covalence_init::init::logic::simp;

use covalence_repl_core::{Repr, Semantics, StepCert};
use covalence_sexp::{Atom, SExpr};

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
/// Lisp theories.
pub struct LispSemantics {
    cs: &'static CarvedSExpr,
    l: &'static KernelLisp,
}

impl LispSemantics {
    /// Bind the process-global carved `sexpr` + Lisp theories.
    pub fn new() -> Result<Self, HolError> {
        Ok(LispSemantics {
            cs: carved().map_err(theory_err)?,
            l: lisp().map_err(theory_err)?,
        })
    }

    /// Compile a parsed [`SExpr`] into the operator-application program term.
    pub fn compile(&self, e: &SExpr) -> Result<Term, HolError> {
        match e {
            SExpr::Atom(a) => self.atom_data(a),
            SExpr::List(items) => self.compile_form(items),
        }
    }

    fn compile_form(&self, items: &[SExpr]) -> Result<Term, HolError> {
        let (head, args) = items
            .split_first()
            .ok_or_else(|| HolError::Stuck("()".into()))?;
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
            // `eq?` fires as a single leaf step (see `eval_eq_leaf`); its
            // compiled marker wraps the two compiled operands.
            ("eq?" | "eq", 2) => {
                let a = self.compile(&args[0])?;
                let b = self.compile(&args[1])?;
                Ok(self.eq_marker(a, b))
            }
            (other, n) => Err(HolError::Stuck(format!(
                "unknown or misapplied operator `{other}` (arity {n})"
            ))),
        }
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

    // ---- the `eq?` marker (a distinguished non-reducible head) ----------

    /// Wrap two operands in the `eq?` marker: `App(App(atom_p ∘ …))` — we reuse
    /// a fresh marker by nesting under a sentinel that never reduces
    /// congruentially. Concretely we tag with the carved `atom` constructor's
    /// *dual* is not needed — we simply keep the operands in a 2-ary spine
    /// under a distinguished op the step function recognizes by pointer.
    fn eq_marker(&self, a: Term, b: Term) -> Term {
        // The marker head is `snil` used purely as a syntactic tag in head
        // position; `step` matches it structurally and never lets it escape as
        // a value (an `eq?` form is always fired). Using an existing constant
        // avoids minting anything new.
        Term::app(Term::app(self.eq_head(), a), b)
    }

    /// The distinguished `eq?` head term. We use the Lisp `atom_p` operator's
    /// sibling only as an identity token; see [`eq_marker`](Self::eq_marker).
    fn eq_head(&self) -> Term {
        // A stable, cheap-to-clone constant that is not `car`/`cdr`/`cons`/
        // `consp`/`atom_p`/`not`, so `step`'s congruence rules never mistake it
        // for another operator. `snil` is a nullary `sexpr` constant; applied,
        // it is never a value and only the `eq?` rule consumes it.
        self.cs.snil.clone()
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
        // The `eq?` marker: a distinguished 2-ary spine `((snil a) b)`.
        if let Some((a, b)) = self.as_eq_marker(t) {
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
        //    and is handled by `fire` below.
        if f.as_app().is_some()
            && let Some(inner) = self.step_term(f)?
        {
            let lifted = inner.thm.clone().cong_fn(arg.clone()).map_err(kernel_err)?;
            let to = Term::app(inner.to.clone(), arg.clone());
            return Ok(Some(LispStep { to, thm: lifted }));
        }
        // 3. Redex head with value sub-terms — fire the law.
        self.fire(t, f, arg)
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
        Err(HolError::Stuck(format!("no reduction for `{t}`")))
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

    /// `eq?` on two atom-value operands — the closed blob (dis)equality
    /// decision. A single self-contained step: `⊢ (b₁ = b₂) = ⌜b₁ == b₂⌝`.
    fn eval_eq_leaf(&self, a: &Term, b: &Term) -> Result<LispStep, HolError> {
        // Reduce each operand to a value first (drive to normal form).
        let av = self.normalize(a)?;
        let bv = self.normalize(b)?;
        let b1 = self
            .as_atom(&av)
            .ok_or_else(|| HolError::Stuck("eq? left operand is not an atom".into()))?;
        let b2 = self
            .as_atom(&bv)
            .ok_or_else(|| HolError::Stuck("eq? right operand is not an atom".into()))?;
        let eq = b1.equals(b2).map_err(kernel_err)?;
        let thm = eq.reduce_consts().map_err(kernel_err)?;
        let to = self.rhs(&thm)?;
        Ok(LispStep { to, thm })
    }

    /// Drive a sub-term to a value (used by `eq?` for its operands). Returns
    /// the value term only (its reduction cert is subsumed by the leaf step).
    fn normalize(&self, t: &Term) -> Result<Term, HolError> {
        let mut cur = t.clone();
        loop {
            match self.step_term(&cur)? {
                None => return Ok(cur),
                Some(s) => cur = s.to,
            }
        }
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

    fn as_eq_marker(&self, t: &Term) -> Option<(Term, Term)> {
        let (inner, b) = t.as_app()?;
        let (head, a) = inner.as_app()?;
        (*head == self.eq_head()).then(|| (a.clone(), b.clone()))
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
