//! The **multi-step Lisp evaluator** (`hol` feature) — normalizes a nested
//! closed Lisp program to its value, every step backed by a kernel theorem.
//!
//! # What this is
//!
//! [`Evaluator`] takes a *program* — a parsed [`SExpr`] built from the
//! Little-Schemer ch1 primitives (`car`, `cdr`, `cons`, `atom?`, `null?`,
//! `eq?`, `consp`, `quote`, and quoted list/atom data) — and returns a
//! [`Reduction`]: the value in **weak normal form** (a closed carved `sexpr`
//! data term, or a `bool` literal for predicates) *and* a single kernel
//! [`Thm`] whose conclusion is `⊢ lhs = value`, chained from the carved
//! carrier's proved computation laws with [`Thm::trans`] + congruence. It
//! mints **no new trusted kernel rules** — only composes existing ones.
//!
//! # The two term shapes and how they relate (the data→application bridge)
//!
//! Evaluation lowers a program *evaluation-directed* — this is the bridge the
//! plain [`crate::Lisp::lower`] does not build (it produces pure `scons`
//! *data*):
//!
//! - `(quote D)` compiles the argument `D` as pure `sexpr` **data**
//!   (`atom`/`snil`/`scons` literals) — `quote` is the special form that
//!   suppresses evaluation.
//! - `(car E)` / `(cdr E)` / `(cons E₁ E₂)` compile to genuine kernel
//!   **operator applications** whose arguments are the *recursively
//!   evaluated* values. The carved carrier's `proj_scons` law then proves
//!   `⊢ car (scons h t) = h`, and [`Thm::trans`] + congruence stitch the
//!   argument reductions to the projection.
//! - `(atom? E)` / `(consp E)` evaluate `E` to a value and read the kernel
//!   Lisp theory's `consp`/`atom?` catamorphism laws — the value is a `bool`
//!   literal.
//! - `(null? E)` is the ACL2 complement of `consp` on lists: `⊢ ¬ consp v`
//!   folded through boolean simplification to `T`/`F`.
//! - `(eq? E₁ E₂)` on two **atom** values `atom b₁` / `atom b₂` decides the
//!   payload (dis)equality `⊢ (b₁ = b₂) = ⌜b₁ == b₂⌝` via the kernel's closed
//!   literal-equality reducer ([`TermExt::reduce_consts`]).
//!
//! The value is always read off a real theorem's conclusion — there is no
//! path that yields a value without one. Non-atom `eq?`, unbound symbols, and
//! ill-formed applications are [`HolError::Stuck`].

use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::mk_blob;
use covalence_init::Term;
use covalence_init::init::ext::{TermExt, ThmExt};
use covalence_init::init::inductive::carved::{CarvedSExpr, LeafKind, carved};
use covalence_init::init::lisp::{Lisp as KernelLisp, lisp};
use covalence_init::init::logic::simp;

use covalence_sexp::{Atom, SExpr};

use crate::hol::HolError;

fn theory_err(e: impl core::fmt::Display) -> HolError {
    HolError::Theory(e.to_string())
}
fn kernel_err(e: impl core::fmt::Display) -> HolError {
    HolError::Kernel(e.to_string())
}

/// A completed reduction: the value in weak-normal form together with the
/// single kernel theorem `⊢ lhs = value` that justifies it.
#[derive(Clone, Debug)]
pub struct Reduction {
    /// `⊢ lhs = value` — the whole reduction, one theorem.
    pub thm: Thm,
    /// The value term (the theorem's RHS): a closed carved `sexpr` datum, or
    /// a `bool` literal for predicate results.
    pub value: Term,
    /// How to print the value.
    pub kind: ValueKind,
}

/// The kind of value a [`Reduction`] produced, for printing.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ValueKind {
    /// A carved `sexpr` datum (`atom`/`snil`/`scons`).
    Data,
    /// A `bool` literal (a predicate / `eq?` result) — printed `t` / `nil`.
    Bool,
}

/// The multi-step evaluator over the process-global carved + Lisp theories.
pub struct Evaluator {
    cs: &'static CarvedSExpr,
    l: &'static KernelLisp,
}

impl Evaluator {
    /// Bind the process-global carved `sexpr` + Lisp theories.
    pub fn new() -> Result<Self, HolError> {
        Ok(Evaluator {
            cs: carved().map_err(theory_err)?,
            l: lisp().map_err(theory_err)?,
        })
    }

    // ---- data compilation (the `quote` payload) -------------------------

    /// Compile an [`SExpr`] as **pure `sexpr` data** — the `atom`/`snil`/
    /// `scons` literal tree. No evaluation; this is what `quote` suppresses to.
    fn data(&self, e: &SExpr) -> Result<Term, HolError> {
        match e {
            SExpr::Atom(a) => self.atom_data(a),
            SExpr::List(items) => {
                let mut acc = self.cs.snil.clone();
                for it in items.iter().rev() {
                    let h = self.data(it)?;
                    acc = self.scons(h, acc)?;
                }
                Ok(acc)
            }
        }
    }

    /// `atom <bytes>` — an atom of a symbol/number/string token's raw bytes.
    fn atom_data(&self, a: &Atom) -> Result<Term, HolError> {
        let bytes: Vec<u8> = match a {
            Atom::Symbol(s) => s.as_bytes().to_vec(),
            Atom::Str { bytes, .. } => bytes.to_vec(),
        };
        Ok(Term::app(self.cs.atom.clone(), mk_blob(bytes)))
    }

    fn scons(&self, h: Term, t: Term) -> Result<Term, HolError> {
        Ok(Term::app(Term::app(self.cs.scons.clone(), h), t))
    }

    // ---- the evaluator --------------------------------------------------

    /// Evaluate a program to a [`Reduction`] (`⊢ program = value`).
    ///
    /// The returned theorem's LHS is a genuine kernel term (an operator
    /// application, or the datum itself for `quote`/atoms) and its RHS is the
    /// value.
    pub fn eval(&self, e: &SExpr) -> Result<Reduction, HolError> {
        match e {
            // A bare atom is self-evaluating data (`⊢ atom b = atom b`).
            SExpr::Atom(a) => {
                let v = self.atom_data(a)?;
                self.refl(v, ValueKind::Data)
            }
            SExpr::List(items) => self.eval_form(items),
        }
    }

    /// `⊢ v = v` — a reflexive reduction.
    fn refl(&self, v: Term, kind: ValueKind) -> Result<Reduction, HolError> {
        let thm = Thm::refl(v.clone()).map_err(kernel_err)?;
        Ok(Reduction {
            thm,
            value: v,
            kind,
        })
    }

    /// Evaluate an application form `(op arg…)`.
    fn eval_form(&self, items: &[SExpr]) -> Result<Reduction, HolError> {
        let (head, args) = items
            .split_first()
            .ok_or_else(|| HolError::Stuck("()".into()))?;
        let op = head
            .as_symbol()
            .ok_or_else(|| HolError::Stuck("application head is not a symbol".into()))?;
        match (op, args.len()) {
            ("quote", 1) => {
                let v = self.data(&args[0])?;
                self.refl(v, ValueKind::Data)
            }
            ("car", 1) => self.eval_proj(false, &args[0]),
            ("cdr", 1) => self.eval_proj(true, &args[0]),
            ("cons", 2) => self.eval_cons(&args[0], &args[1]),
            ("atom?" | "atom", 1) => self.eval_pred(Pred::Atom, &args[0]),
            ("consp" | "pair?", 1) => self.eval_pred(Pred::Consp, &args[0]),
            ("null?" | "null", 1) => self.eval_null(&args[0]),
            ("eq?" | "eq", 2) => self.eval_eq(&args[0], &args[1]),
            (other, n) => Err(HolError::Stuck(format!(
                "unknown or misapplied operator `{other}` (arity {n})"
            ))),
        }
    }

    // ---- car / cdr ------------------------------------------------------

    /// `(car|cdr E)` — evaluate `E` to a value `v`, then project.
    fn eval_proj(&self, take_cdr: bool, arg: &SExpr) -> Result<Reduction, HolError> {
        let r = self.eval(arg)?;
        let op = if take_cdr {
            self.cs.cdr.clone()
        } else {
            self.cs.car.clone()
        };
        // ⊢ op argₗ = op v  (congruence on the argument reduction).
        let lifted = r.thm.cong_arg(op).map_err(kernel_err)?;
        // The projection law on the value `v`.
        let proj = self.project(take_cdr, &r.value)?;
        let thm = lifted.trans(proj).map_err(kernel_err)?;
        self.data_reduction(thm)
    }

    /// `⊢ op v = …` for a *value* `v`: `proj_scons` when `v = scons h t`,
    /// otherwise the ACL2-default leaf law (`car (atom b) = snil`).
    fn project(&self, take_cdr: bool, v: &Term) -> Result<Thm, HolError> {
        if let Some((h, t)) = self.as_scons(v) {
            self.cs.proj_scons(take_cdr, &h, &t).map_err(kernel_err)
        } else if let Some(b) = self.as_atom(v) {
            self.cs
                .proj_leaf(take_cdr, LeafKind::Atom(&b))
                .map_err(kernel_err)
        } else if *v == self.cs.snil {
            self.cs
                .proj_leaf(take_cdr, LeafKind::Nil)
                .map_err(kernel_err)
        } else {
            Err(HolError::Stuck(format!(
                "car/cdr of a non-`sexpr` value `{v}`"
            )))
        }
    }

    // ---- cons -----------------------------------------------------------

    /// `(cons E₁ E₂)` — evaluate both, then `⊢ scons e₁ e₂ = scons v₁ v₂` by
    /// double congruence ([`Thm::cong_app`]) over the argument reductions.
    fn eval_cons(&self, a: &SExpr, b: &SExpr) -> Result<Reduction, HolError> {
        let ra = self.eval(a)?;
        let rb = self.eval(b)?;
        // ⊢ scons e₁ = scons v₁   (congruence on the head reduction).
        let head_eq = ra.thm.cong_arg(self.cs.scons.clone()).map_err(kernel_err)?;
        // ⊢ (scons e₁) e₂ = (scons v₁) v₂   (cong_app with the tail reduction).
        let thm = head_eq.cong_app(rb.thm).map_err(kernel_err)?;
        self.data_reduction(thm)
    }

    // ---- predicates -----------------------------------------------------

    /// `(atom?|consp E)` — evaluate `E`, then read the kernel Lisp theory's
    /// catamorphism law on the value.
    fn eval_pred(&self, pred: Pred, arg: &SExpr) -> Result<Reduction, HolError> {
        let r = self.eval(arg)?;
        let op = match pred {
            Pred::Atom => self.l.atom_p.clone(),
            Pred::Consp => self.l.consp.clone(),
        };
        let comp = self.pred_on_value(pred, &r.value)?; // ⊢ pred v = T/F
        // ⊢ pred argₗ = pred v  (congruence), then chain the value law.
        let lifted = r.thm.cong_arg(op).map_err(kernel_err)?;
        let thm = lifted.trans(comp).map_err(kernel_err)?;
        self.bool_reduction(thm)
    }

    /// The kernel computation law `⊢ pred v = T/F` for a value `v`.
    fn pred_on_value(&self, pred: Pred, v: &Term) -> Result<Thm, HolError> {
        match pred {
            Pred::Atom => {
                if let Some((h, t)) = self.as_scons(v) {
                    self.l.atom_scons(&h, &t).map_err(kernel_err)
                } else if let Some(b) = self.as_atom(v) {
                    self.l.atom_atom(&b).map_err(kernel_err)
                } else if *v == self.cs.snil {
                    self.l.atom_nil().map_err(kernel_err)
                } else {
                    Err(HolError::Stuck(format!("atom? of non-`sexpr` `{v}`")))
                }
            }
            Pred::Consp => {
                if let Some((h, t)) = self.as_scons(v) {
                    self.l.consp_scons(&h, &t).map_err(kernel_err)
                } else if let Some(b) = self.as_atom(v) {
                    self.l.consp_atom(&b).map_err(kernel_err)
                } else if *v == self.cs.snil {
                    self.l.consp_nil().map_err(kernel_err)
                } else {
                    Err(HolError::Stuck(format!("consp of non-`sexpr` `{v}`")))
                }
            }
        }
    }

    // ---- null? ----------------------------------------------------------

    /// `(null? E)` — the ACL2 complement of `consp` on lists: evaluate `E`,
    /// take `⊢ consp v = bl`, lift it under `¬`, and fold `¬ bl` through
    /// boolean simplification to a literal. `⊢ ¬ consp v = ⌜v is snil⌝`.
    fn eval_null(&self, arg: &SExpr) -> Result<Reduction, HolError> {
        let r = self.eval(arg)?;
        let consp_v = self.pred_on_value(Pred::Consp, &r.value)?; // ⊢ consp v = bl
        // ⊢ consp argₗ = consp v   (lift the argument reduction under consp).
        let consp_lifted = r
            .thm
            .clone()
            .cong_arg(self.l.consp.clone())
            .map_err(kernel_err)?
            .trans(consp_v)
            .map_err(kernel_err)?; // ⊢ consp argₗ = bl
        // Build ¬ (consp argₗ) and rewrite `consp argₗ` to `bl`, then fold.
        let neg = consp_lifted
            .concl()
            .as_eq()
            .ok_or_else(|| HolError::Kernel("not an equation".into()))?
            .0
            .clone()
            .not()
            .map_err(kernel_err)?;
        let thm = Thm::refl(neg)
            .map_err(kernel_err)?
            .rewrite(&consp_lifted)
            .map_err(kernel_err)? // ⊢ ¬ consp argₗ = ¬ bl
            .rhs_conv(|t| simp(t))
            .map_err(kernel_err)?; // ⊢ ¬ consp argₗ = T/F
        self.bool_reduction(thm)
    }

    // ---- eq? ------------------------------------------------------------

    /// `(eq? E₁ E₂)` on two **atom** values — decide payload (dis)equality via
    /// the kernel's closed literal-equality reducer.
    fn eval_eq(&self, a: &SExpr, b: &SExpr) -> Result<Reduction, HolError> {
        let ra = self.eval(a)?;
        let rb = self.eval(b)?;
        let b1 = self
            .as_atom(&ra.value)
            .ok_or_else(|| HolError::Stuck("eq? left operand is not an atom".into()))?;
        let b2 = self
            .as_atom(&rb.value)
            .ok_or_else(|| HolError::Stuck("eq? right operand is not an atom".into()))?;
        // ⊢ (b₁ = b₂) = ⌜b₁ == b₂⌝ — the closed literal-equality decision.
        let eq = b1.equals(b2).map_err(kernel_err)?;
        let thm = eq.reduce_consts().map_err(kernel_err)?;
        self.bool_reduction(thm)
    }

    // ---- reduction packaging -------------------------------------------

    fn data_reduction(&self, thm: Thm) -> Result<Reduction, HolError> {
        let value = rhs(&thm)?;
        Ok(Reduction {
            thm,
            value,
            kind: ValueKind::Data,
        })
    }

    fn bool_reduction(&self, thm: Thm) -> Result<Reduction, HolError> {
        let value = rhs(&thm)?;
        Ok(Reduction {
            thm,
            value,
            kind: ValueKind::Bool,
        })
    }

    // ---- value inspection ----------------------------------------------

    /// Match a value `scons h t`, returning `(h, t)`.
    pub(crate) fn as_scons(&self, v: &Term) -> Option<(Term, Term)> {
        let (inner, t) = v.as_app()?;
        let (op, h) = inner.as_app()?;
        (*op == self.cs.scons).then(|| (h.clone(), t.clone()))
    }

    /// Match a value `atom b`, returning the blob payload term `b`.
    pub(crate) fn as_atom(&self, v: &Term) -> Option<Term> {
        let (op, b) = v.as_app()?;
        (*op == self.cs.atom).then(|| b.clone())
    }

    /// Is `v` the empty list `snil`?
    pub(crate) fn is_snil(&self, v: &Term) -> bool {
        *v == self.cs.snil
    }

    /// The blob payload bytes of an `atom b` value, if `b` is a blob literal.
    pub(crate) fn atom_bytes(&self, v: &Term) -> Option<Vec<u8>> {
        let b = self.as_atom(v)?;
        blob_bytes(&b)
    }
}

/// The predicate kind.
#[derive(Clone, Copy, Debug)]
enum Pred {
    Atom,
    Consp,
}

/// The RHS of an equational theorem.
fn rhs(thm: &Thm) -> Result<Term, HolError> {
    thm.concl()
        .as_eq()
        .map(|(_, r)| r.clone())
        .ok_or_else(|| HolError::Kernel("theorem conclusion is not an equation".into()))
}

/// Extract the bytes of a blob literal term (`mk_blob`), if it is one — via
/// the designated [`Lit`](covalence_core::seam::Lit) facade (the inverse of
/// `mk_blob`), so no `TermKind` literal is matched in this crate.
fn blob_bytes(t: &Term) -> Option<Vec<u8>> {
    use covalence_core::seam::Lit;
    match Lit::from_term(t)? {
        Lit::Bytes(b) => Some(b.to_vec()),
        _ => None,
    }
}
