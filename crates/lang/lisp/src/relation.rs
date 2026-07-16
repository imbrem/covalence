//! The Lisp **reduction relation** — a genuine small-step operational semantics
//! and its reflexive-transitive closure, built on the kernel's binary
//! inductive-relation engine ([`covalence_init::metalogic::binary`]) rather than
//! as chained equations (`hol` feature).
//!
//! This is the relational twin of [`crate::semantics`]: where `LispSemantics`
//! composes each step into one big-step `⊢ from = to` *equation*, here each step
//! is a **membership theorem** `⊢ Step from to` in a defined relation, and a run
//! is a `⊢ Reduces input value` chain in the reflexive-transitive closure. No new
//! trusted kernel rules: both relations are *defined* via the engine's
//! impredicative least-fixpoint (`Derives_L n w := ∀d. Closed_L d ⟹ d n w`), so a
//! closed program's `⊢ Reduces …` is hypothesis-free.
//!
//! ## The two relations
//!
//! - [`step_rule_set`] — `Step : sexpr → sexpr → bool`, one clause per reduction
//!   rule. Redex clauses (car/cdr/predicates/eq?/cond) are base clauses; each
//!   elimination-context **congruence** clause carries one [`Premise::Derivation`]
//!   (a `Step` sub-derivation).
//! - [`reduces_rule_set`] — `Reduces = Step*`, two clauses: `refl : ∀t. Reduces t t`
//!   and `step : ∀a b c. Step a b ⟹ Reduces b c ⟹ Reduces a c` (the `Step`
//!   antecedent is a [`Premise::Side`], the `Reduces` antecedent a
//!   [`Premise::Derivation`]).
//!
//! ## Unifying the value kinds
//!
//! The predicate / `eq?` results are **sexpr atoms** `t` / `nil` (not HOL `bool`),
//! and `cond` tests sexpr *truthiness* (`nil` = false, any other value = true).
//! This dissolves the `Bool`-vs-`Data` split (and the "truthy-data `cond`" wall)
//! the equational value semantics hit: every value is an sexpr datum.
//!
//! ## Scope
//!
//! The **primitive fragment** is solid: `car`/`cdr`/`cons` projections,
//! `atom?`/`consp`/`null?` predicates, `eq?` on *equal* atoms, `cond` (truthy /
//! falsy clause selection), one congruence clause per unary elimination
//! context, and — in the `sector+int` dialect — left/right congruence into the
//! integer-op operands (so `(+ 1 (+ 2 3))` reduces). β/λ, δ/`defun`, `eq?` on
//! distinct atoms, and congruence *into* `eq?` operands and `cond` tests are
//! the next phase (see `SKELETONS.md` and
//! `notes/vibes/lisp/relational-recursion.md`).

use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::mk_blob;
use covalence_init::init::ext::{TermExt, ThmExt};
use covalence_init::init::inductive::carved::{CarvedSExpr, carved};
use covalence_init::metalogic::binary::{Premise, RuleSet2, derivable2, derive_mixed};
use covalence_init::{Term, Type};
use covalence_sexp::{Atom, SExpr};
use covalence_types::Int;

use covalence_sexp::abstract_sexpr::{AbstractSExpr, PayloadLit};

use crate::carrier::CarvedCarrier;
use crate::hol::HolError;
use crate::int_backend::{IntBackend, IntOp, IntVariant, NatVariant};

fn theory_err(e: impl core::fmt::Display) -> HolError {
    HolError::Theory(e.to_string())
}
fn kernel_err(e: impl core::fmt::Display) -> HolError {
    HolError::Kernel(e.to_string())
}

// ============================================================================
// Operator heads
// ============================================================================
//
// The relation is *defined* by its clauses, so the operator heads need only be
// distinct, well-typed sexpr terms — they carry no kernel computation laws (the
// `Step` clauses supply all their behaviour). The structural constructors
// (`car`/`cdr`/`scons`/`atom`/`snil`) are reused from the carved carrier; the
// sexpr-**valued** predicates / `eq?` / `cond`-cell heads (which the bool-valued
// `lisp` theory constants cannot serve) are fresh, stable free-variable heads.

/// Which Lisp **dialect** a [`LispRel`] realises. The two form the refinement
/// order `sector ⊑ sector+int`: every `sector` program reduces identically in
/// `sector+int`, which additionally reduces integer literals + arithmetic.
///
/// The dialect is exactly a *clause subset* of the `Step` `RuleSet2`:
/// [`Sector`](Dialect::Sector) omits the integer clauses (so `(+ 2 2)` is
/// **stuck** — no step), [`SectorInt`](Dialect::SectorInt) includes them.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Dialect {
    /// The pure McCarthy fragment — no integer literals or arithmetic.
    Sector,
    /// `sector` plus integer literals + arithmetic, over the chosen
    /// [`IntFlavour`] (signed `int` or non-negative `nat`).
    SectorInt(IntFlavour),
}

/// The integer flavour of the `sector+int` dialect: honest signed integers, or
/// naturals (which error on a negative literal / difference).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IntFlavour {
    /// Signed integers — `-` may go negative.
    Int,
    /// Naturals — negative literals / differences are errors.
    Nat,
}

/// The set of operator heads + the sexpr carrier, built once from [`carved`].
pub struct LispRel {
    cs: &'static CarvedSExpr,
    /// The shared abstract-sexpr adapter over `cs` (structural build/observe
    /// helpers — `as_scons`/`as_atom`/`is_snil`/`data` delegate here).
    carrier: CarvedCarrier,
    /// The sexpr `t` atom (`atom "t"`) — the truthy value predicates return.
    t: Term,
    /// The sexpr `nil` atom (`atom "nil"`) — the falsy value; distinct from
    /// `snil` so `null?`/truthiness are decidable on either representation.
    nil: Term,
    /// `atom? : sexpr → sexpr`.
    atom_p: Term,
    /// `consp : sexpr → sexpr`.
    consp: Term,
    /// `null? : sexpr → sexpr`.
    null_p: Term,
    /// `eq? : sexpr → sexpr → sexpr`.
    eq_p: Term,
    /// `cond : sexpr → sexpr` (over a cond-cell-list argument).
    cond: Term,
    /// The active dialect (which integer clauses, if any, are installed).
    dialect: Dialect,
    /// The integer backend for the `sector+int` dialect (`None` for `sector`).
    /// Boxed so the two variants share one field; drives both the extra `Step`
    /// clauses and the driver's integer-redex reduction.
    int_be: Option<Box<dyn IntBackend>>,
}

/// A stable, sexpr-valued operator head named `name` with `arity` sexpr inputs.
fn op_head(name: &str, arity: usize, tau: &Type) -> Term {
    let mut ty = tau.clone();
    for _ in 0..arity {
        ty = Type::fun(tau.clone(), ty);
    }
    Term::free(name, ty)
}

impl LispRel {
    /// Bind the process-global carved sexpr carrier and the operator heads, in
    /// the pure [`Sector`](Dialect::Sector) dialect (no integer clauses).
    pub fn new() -> Result<Self, HolError> {
        Self::with_dialect(Dialect::Sector)
    }

    /// Build a [`LispRel`] in the given [`Dialect`]. For
    /// [`SectorInt`](Dialect::SectorInt) this installs the integer backend and
    /// the extra integer `Step` clauses; [`Sector`](Dialect::Sector) has
    /// neither (so `(+ 2 2)` is stuck).
    pub fn with_dialect(dialect: Dialect) -> Result<Self, HolError> {
        let cs = carved().map_err(theory_err)?;
        let tau = &cs.tau;
        let atom_c = |s: &str| Term::app(cs.atom.clone(), mk_blob(s.as_bytes().to_vec()));
        let t = atom_c("t");
        let nil = atom_c("nil");
        let int_be: Option<Box<dyn IntBackend>> = match dialect {
            Dialect::Sector => None,
            Dialect::SectorInt(IntFlavour::Int) => Some(Box::new(IntVariant::new(
                tau.clone(),
                t.clone(),
                nil.clone(),
            ))),
            Dialect::SectorInt(IntFlavour::Nat) => Some(Box::new(NatVariant::new(
                tau.clone(),
                t.clone(),
                nil.clone(),
            ))),
        };
        Ok(LispRel {
            cs,
            carrier: CarvedCarrier::over(cs),
            t,
            nil,
            atom_p: op_head("lisp.rel.atom?", 1, tau),
            consp: op_head("lisp.rel.consp", 1, tau),
            null_p: op_head("lisp.rel.null?", 1, tau),
            eq_p: op_head("lisp.rel.eq?", 2, tau),
            cond: op_head("lisp.rel.cond", 1, tau),
            dialect,
            int_be,
        })
    }

    /// The active dialect.
    pub fn dialect(&self) -> Dialect {
        self.dialect
    }

    /// The integer backend, if the dialect is `sector+int`.
    pub fn int_backend(&self) -> Option<&dyn IntBackend> {
        self.int_be.as_deref()
    }

    /// Build the sexpr value `(int n)` via the active backend. Errors in
    /// `sector` (no integer backend) and — in the `nat` flavour — for `n < 0`.
    pub fn int_lit(&self, n: &Int) -> Result<Term, HolError> {
        self.int_be
            .as_ref()
            .ok_or_else(|| HolError::Theory("integer literals need the sector+int dialect".into()))?
            .lit(n)
    }

    /// Build an integer op application `(op a b)` (`a`, `b` already sexpr
    /// terms). In `sector`, the op heads still *exist* as fresh free variables
    /// — this builds the (stuck) application — but no `Step` fires on it.
    pub fn int_op_term(&self, op: IntOp, a: Term, b: Term) -> Result<Term, HolError> {
        match self.int_be.as_deref() {
            Some(be) => be.op_term(op, a, b),
            None => crate::int_backend::op_head(op, &self.cs.tau)
                .apply(a)
                .map_err(kernel_err)?
                .apply(b)
                .map_err(kernel_err),
        }
    }

    /// The sexpr carrier type.
    pub fn tau(&self) -> Type {
        self.cs.tau.clone()
    }

    /// The sexpr `t` atom.
    pub fn t(&self) -> Term {
        self.t.clone()
    }

    /// The sexpr `nil` atom.
    pub fn nil(&self) -> Term {
        self.nil.clone()
    }

    // -- term constructors (untrusted; just build sexpr terms) ---------------

    fn car(&self, x: Term) -> Result<Term, HolError> {
        self.cs.car.clone().apply(x).map_err(kernel_err)
    }
    fn cdr(&self, x: Term) -> Result<Term, HolError> {
        self.cs.cdr.clone().apply(x).map_err(kernel_err)
    }
    /// `scons h t`.
    pub fn scons(&self, h: Term, t: Term) -> Result<Term, HolError> {
        self.cs
            .scons
            .clone()
            .apply(h)
            .map_err(kernel_err)?
            .apply(t)
            .map_err(kernel_err)
    }
    /// `atom "s"` — a symbol atom.
    pub fn sym(&self, s: &str) -> Term {
        Term::app(self.cs.atom.clone(), mk_blob(s.as_bytes().to_vec()))
    }
    /// `atom? x`.
    pub fn atom_p_of(&self, x: Term) -> Result<Term, HolError> {
        self.atom_p.clone().apply(x).map_err(kernel_err)
    }
    /// `consp x`.
    pub fn consp_of(&self, x: Term) -> Result<Term, HolError> {
        self.consp.clone().apply(x).map_err(kernel_err)
    }
    /// `null? x`.
    pub fn null_p_of(&self, x: Term) -> Result<Term, HolError> {
        self.null_p.clone().apply(x).map_err(kernel_err)
    }
    /// `eq? a b`.
    pub fn eq_of(&self, a: Term, b: Term) -> Result<Term, HolError> {
        self.eq_p
            .clone()
            .apply(a)
            .map_err(kernel_err)?
            .apply(b)
            .map_err(kernel_err)
    }
    /// `cond cells` — a `cond` over a `scons`-chain of clauses. Each clause is
    /// a pair `scons test body` (`test` = car, `body` = cdr); the clause list
    /// is a `scons`-chain terminated by `snil`.
    pub fn cond_of(&self, cells: Term) -> Result<Term, HolError> {
        self.cond.clone().apply(cells).map_err(kernel_err)
    }

    // ------------------------------------------------------------------
    // Step : sexpr → sexpr → bool
    // ------------------------------------------------------------------

    /// The `Step` rule set. Clause order (STABLE — the driver indexes it):
    ///
    /// | idx | clause |
    /// |----:|--------|
    /// | 0 | `∀h t. Step (car (scons h t)) h` |
    /// | 1 | `∀h t. Step (cdr (scons h t)) t` |
    /// | 2 | `∀h t. Step (atom? (scons h t)) nil` |
    /// | 3 | `∀b.   Step (atom? (atom b)) t` |
    /// | 4 | `       Step (atom? snil) t` |
    /// | 5 | `∀h t. Step (consp (scons h t)) t` |
    /// | 6 | `∀b.   Step (consp (atom b)) nil` |
    /// | 7 | `       Step (consp snil) nil` |
    /// | 8 | `       Step (null? snil) t` |
    /// | 9 | `∀h t. Step (null? (scons h t)) nil` |
    /// | 10 | `∀b.  Step (null? (atom b)) nil` |
    /// | 11 | `∀a.  Step (eq? (atom a) (atom a)) t`  (equal atoms) |
    /// | 12 | congruence: `∀a a'. Step a a' ⟹ Step (car a) (car a')` |
    /// | 13 | congruence: cdr |
    /// | 14 | congruence: atom? arg |
    /// | 15 | congruence: consp arg |
    /// | 16 | congruence: null? arg |
    /// | 17 | `Step (cond snil) nil` |
    /// | 18 | `∀body rest. Step (cond ((nil . body) . rest)) (cond rest)` |
    /// | 19 | `∀body rest. Step (cond ((t . body) . rest)) body` |
    ///
    /// In the [`SectorInt`](Dialect::SectorInt) dialect, five more integer
    /// redex clauses follow (indices 20–24, in [`IntOp::ALL`] order):
    ///
    /// | idx | clause |
    /// |----:|--------|
    /// | 20 | `∀a b:int. Step (+ (int a)(int b)) (int (int.add a b))` |
    /// | 21 | `∀a b:int. Step (- (int a)(int b)) (int (int.sub a b))` |
    /// | 22 | `∀a b:int. Step (* (int a)(int b)) (int (int.mul a b))` |
    /// | 23 | `∀a b:int. Step (<= (int a)(int b)) (cond (int.le a b) t nil)` |
    /// | 24 | `∀a b:int. Step (= (int a)(int b)) (cond ((=:int) a b) t nil)` |
    ///
    /// then ten integer **congruence** clauses (indices 25–34), a left/right
    /// pair per op in [`IntOp::ALL`] order, so operands reduce in place:
    ///
    /// | idx | clause |
    /// |----:|--------|
    /// | 25 + 2·op | `∀a a2 b. Step a a2 ⟹ Step (op a b) (op a2 b)` |
    /// | 26 + 2·op | `∀a b b2. Step b b2 ⟹ Step (op a b) (op a b2)` |
    ///
    /// (`eq?` on *distinct* atoms is future work — see the builder / SKELETONS.)
    pub fn step_rule_set(&self) -> RuleSet2<'_> {
        let tau = self.cs.tau.clone();
        RuleSet2::new(tau.clone(), tau.clone(), move |d| {
            let tau = &self.cs.tau;
            let h = Term::free("h", tau.clone());
            let t = Term::free("t", tau.clone());
            let b = Term::free("b", Type::bytes());
            let scons_ht = self.scons(h.clone(), t.clone()).map_err(to_core)?;
            let atom_b = Term::app(self.cs.atom.clone(), b.clone());
            let snil = self.cs.snil.clone();

            let mut cs = Vec::new();

            // 0: car projection.
            cs.push(
                d(&self.car(scons_ht.clone()).map_err(to_core)?, &h)?
                    .forall("t", tau.clone())?
                    .forall("h", tau.clone())?,
            );
            // 1: cdr projection.
            cs.push(
                d(&self.cdr(scons_ht.clone()).map_err(to_core)?, &t)?
                    .forall("t", tau.clone())?
                    .forall("h", tau.clone())?,
            );
            // 2: atom? (scons h t) = nil.
            cs.push(
                d(
                    &self.atom_p_of(scons_ht.clone()).map_err(to_core)?,
                    &self.nil,
                )?
                .forall("t", tau.clone())?
                .forall("h", tau.clone())?,
            );
            // 3: atom? (atom b) = t.
            cs.push(
                d(&self.atom_p_of(atom_b.clone()).map_err(to_core)?, &self.t)?
                    .forall("b", Type::bytes())?,
            );
            // 4: atom? snil = t.
            cs.push(d(&self.atom_p_of(snil.clone()).map_err(to_core)?, &self.t)?);
            // 5: consp (scons h t) = t.
            cs.push(
                d(&self.consp_of(scons_ht.clone()).map_err(to_core)?, &self.t)?
                    .forall("t", tau.clone())?
                    .forall("h", tau.clone())?,
            );
            // 6: consp (atom b) = nil.
            cs.push(
                d(&self.consp_of(atom_b.clone()).map_err(to_core)?, &self.nil)?
                    .forall("b", Type::bytes())?,
            );
            // 7: consp snil = nil.
            cs.push(d(
                &self.consp_of(snil.clone()).map_err(to_core)?,
                &self.nil,
            )?);
            // 8: null? snil = t.
            cs.push(d(&self.null_p_of(snil.clone()).map_err(to_core)?, &self.t)?);
            // 9: null? (scons h t) = nil.
            cs.push(
                d(
                    &self.null_p_of(scons_ht.clone()).map_err(to_core)?,
                    &self.nil,
                )?
                .forall("t", tau.clone())?
                .forall("h", tau.clone())?,
            );
            // 10: null? (atom b) = nil.
            cs.push(
                d(&self.null_p_of(atom_b.clone()).map_err(to_core)?, &self.nil)?
                    .forall("b", Type::bytes())?,
            );
            // 11: eq? (atom a) (atom a) = t  (equal atoms).
            {
                let ab = Term::free("a", Type::bytes());
                let atom_a = Term::app(self.cs.atom.clone(), ab.clone());
                cs.push(
                    d(
                        &self
                            .eq_of(atom_a.clone(), atom_a.clone())
                            .map_err(to_core)?,
                        &self.t,
                    )?
                    .forall("a", Type::bytes())?,
                );
            }

            // 12–16: congruence clauses, one per elimination context.
            // ∀a a'. d a a' ⟹ d (K a) (K a').
            let cong =
                |mk: &dyn Fn(Term) -> Result<Term, HolError>| -> covalence_core::Result<Term> {
                    let a = Term::free("a", tau.clone());
                    let a2 = Term::free("a2", tau.clone());
                    let concl = d(
                        &mk(a.clone()).map_err(to_core)?,
                        &mk(a2.clone()).map_err(to_core)?,
                    )?;
                    d(&a, &a2)?
                        .imp(concl)?
                        .forall("a2", tau.clone())?
                        .forall("a", tau.clone())
                };
            cs.push(cong(&|x| self.car(x))?); // 12
            cs.push(cong(&|x| self.cdr(x))?); // 13
            cs.push(cong(&|x| self.atom_p_of(x))?); // 14
            cs.push(cong(&|x| self.consp_of(x))?); // 15
            cs.push(cong(&|x| self.null_p_of(x))?); // 16

            // --- cond clauses ---------------------------------------------
            // A cond-cell list is a `scons`-chain of clauses; each clause is a
            // pair `scons test body` (test = car, body = cdr). `cond` tests
            // sexpr truthiness: the falsy value is `nil`, and the canonical
            // truthy value is `t` (exactly what the predicate clauses produce).

            // 17: no clause matched — `Step (cond snil) nil`.
            cs.push(d(&self.cond_of(snil.clone()).map_err(to_core)?, &self.nil)?);

            let body = Term::free("body", tau.clone());
            let rest = Term::free("rest", tau.clone());
            // 18: falsy head — `∀body rest. Step (cond ((nil . body) . rest)) (cond rest)`.
            {
                let clause = self
                    .scons(self.nil.clone(), body.clone())
                    .map_err(to_core)?;
                let cells = self.scons(clause, rest.clone()).map_err(to_core)?;
                cs.push(
                    d(
                        &self.cond_of(cells).map_err(to_core)?,
                        &self.cond_of(rest.clone()).map_err(to_core)?,
                    )?
                    .forall("rest", tau.clone())?
                    .forall("body", tau.clone())?,
                );
            }
            // 19: truthy head — `∀body rest. Step (cond ((t . body) . rest)) body`.
            {
                let clause = self.scons(self.t.clone(), body.clone()).map_err(to_core)?;
                let cells = self.scons(clause, rest.clone()).map_err(to_core)?;
                cs.push(
                    d(&self.cond_of(cells).map_err(to_core)?, &body)?
                        .forall("rest", tau.clone())?
                        .forall("body", tau.clone())?,
                );
            }

            // --- integer clauses (the `sector+int` dialect only) -----------
            // One ∀-quantified clause per op:
            //   ∀a b:int. Step (op (int a)(int b)) (TARGET a b)
            // where TARGET is the sexpr injection of the kernel int result
            // (ring) or `cond sexpr (int.<cmp> a b) t nil` (comparison). On
            // concrete literals the driver instantiates a,b and normalises
            // TARGET via the kernel int-computation equation (see `step_int`).
            // `Sector` installs NONE of these (integers are stuck there).
            if let Some(be) = self.int_be.as_deref() {
                for &op in &IntOp::ALL {
                    let a = Term::free("a", Type::int());
                    let b = Term::free("b", Type::int());
                    let ia = be.lit_var(&a).map_err(to_core)?; // (int a)
                    let ib = be.lit_var(&b).map_err(to_core)?; // (int b)
                    let from = be.op_term(op, ia, ib).map_err(to_core)?;
                    let target = be.clause_target(op, &a, &b).map_err(to_core)?;
                    cs.push(
                        d(&from, &target)?
                            .forall("b", Type::int())?
                            .forall("a", Type::int())?,
                    );
                }

                // 25–34: congruence into the int-op operands (a left/right
                // pair per op, in IntOp::ALL order), so nested expressions
                // like `(+ 1 (+ 2 3))` reduce their operands in place:
                //   left:  ∀a a2 b. Step a a2 ⟹ Step (op a b) (op a2 b)
                //   right: ∀a b b2. Step b b2 ⟹ Step (op a b) (op a b2)
                for &op in &IntOp::ALL {
                    let a = Term::free("a", tau.clone());
                    let a2 = Term::free("a2", tau.clone());
                    let b = Term::free("b", tau.clone());
                    let b2 = Term::free("b2", tau.clone());
                    // left congruence.
                    let concl = d(
                        &be.op_term(op, a.clone(), b.clone()).map_err(to_core)?,
                        &be.op_term(op, a2.clone(), b.clone()).map_err(to_core)?,
                    )?;
                    cs.push(
                        d(&a, &a2)?
                            .imp(concl)?
                            .forall("b", tau.clone())?
                            .forall("a2", tau.clone())?
                            .forall("a", tau.clone())?,
                    );
                    // right congruence.
                    let concl = d(
                        &be.op_term(op, a.clone(), b.clone()).map_err(to_core)?,
                        &be.op_term(op, a.clone(), b2.clone()).map_err(to_core)?,
                    )?;
                    cs.push(
                        d(&b, &b2)?
                            .imp(concl)?
                            .forall("b2", tau.clone())?
                            .forall("b", tau.clone())?
                            .forall("a", tau.clone())?,
                    );
                }
            }

            Ok(cs)
        })
    }

    /// The clause index of int op `op` in the `sector+int` `Step` rule set
    /// (the integer clauses follow the 20 primitive-fragment clauses, in
    /// [`IntOp::ALL`] order). Only meaningful when a backend is installed.
    fn int_clause_idx(op: IntOp) -> usize {
        20 + IntOp::ALL.iter().position(|&o| o == op).expect("op in ALL")
    }

    /// The clause index of int op `op`'s **congruence** clause (left = reduce
    /// the first operand, right = the second) in the `sector+int` `Step` rule
    /// set: the pairs follow the five redex clauses, in [`IntOp::ALL`] order.
    fn int_cong_idx(op: IntOp, right: bool) -> usize {
        let p = IntOp::ALL.iter().position(|&o| o == op).expect("op in ALL");
        25 + 2 * p + usize::from(right)
    }

    /// The number of `Step` clauses.
    pub fn step_n_clauses(&self) -> Result<usize, HolError> {
        self.step_rule_set().n_clauses().map_err(kernel_err)
    }

    /// `⊢ Step from to` via base clause `idx` (a redex rule), peeling its
    /// `∀`s with `word_args` (outermost first). No premises.
    fn step_base(&self, idx: usize, word_args: &[Term]) -> Result<Thm, HolError> {
        let n = self.step_n_clauses()?;
        derive_mixed(&self.step_rule_set(), idx, n, word_args, vec![]).map_err(kernel_err)
    }

    /// `⊢ Step (K a) (K a')` from a sub-step `⊢ Step a a'` via congruence
    /// clause `idx` (word args `[a, a']`).
    fn step_cong(&self, idx: usize, a: Term, a2: Term, sub: Thm) -> Result<Thm, HolError> {
        let n = self.step_n_clauses()?;
        derive_mixed(
            &self.step_rule_set(),
            idx,
            n,
            &[a, a2],
            vec![Premise::Derivation(sub)],
        )
        .map_err(kernel_err)
    }

    /// `Step from to` (the proposition).
    pub fn step_prop(&self, from: &Term, to: &Term) -> Result<Term, HolError> {
        derivable2(&self.step_rule_set(), from, to).map_err(kernel_err)
    }

    // ------------------------------------------------------------------
    // Reduces = Step*
    // ------------------------------------------------------------------

    /// The `Reduces` rule set: `refl` (clause 0) + `step` (clause 1).
    pub fn reduces_rule_set(&self) -> RuleSet2<'_> {
        let tau = self.cs.tau.clone();
        let step_rs = self.step_rule_set();
        RuleSet2::new(tau.clone(), tau.clone(), move |d| {
            let tau = &self.cs.tau;
            // clause 0: ∀t. d t t.
            let tv = Term::free("t", tau.clone());
            let refl = d(&tv, &tv)?.forall("t", tau.clone())?;
            // clause 1: ∀a b c. Step a b ⟹ d b c ⟹ d a c.
            let a = Term::free("a", tau.clone());
            let b = Term::free("b", tau.clone());
            let c = Term::free("c", tau.clone());
            let step_ab = derivable2(&step_rs, &a, &b)?;
            let body = step_ab.imp(d(&b, &c)?.imp(d(&a, &c)?)?)?;
            let step = body
                .forall("c", tau.clone())?
                .forall("b", tau.clone())?
                .forall("a", tau.clone())?;
            Ok(vec![refl, step])
        })
    }

    /// `Reduces from to` (the proposition).
    pub fn reduces_prop(&self, from: &Term, to: &Term) -> Result<Term, HolError> {
        derivable2(&self.reduces_rule_set(), from, to).map_err(kernel_err)
    }

    /// `⊢ Reduces t t` (the `refl` clause).
    pub fn reduces_refl(&self, t: &Term) -> Result<Thm, HolError> {
        derive_mixed(&self.reduces_rule_set(), 0, 2, &[t.clone()], vec![]).map_err(kernel_err)
    }

    /// `⊢ Reduces a c` from `⊢ Step a b` and `⊢ Reduces b c` (the `step`
    /// clause): word args `[a, b, c]`, premises `[Side(step), Derivation(rest)]`.
    pub fn reduces_step(
        &self,
        a: &Term,
        b: &Term,
        c: &Term,
        step: Thm,
        rest: Thm,
    ) -> Result<Thm, HolError> {
        derive_mixed(
            &self.reduces_rule_set(),
            1,
            2,
            &[a.clone(), b.clone(), c.clone()],
            vec![Premise::Side(step), Premise::Derivation(rest)],
        )
        .map_err(kernel_err)
    }

    // ------------------------------------------------------------------
    // Driver: leftmost-innermost redex search
    // ------------------------------------------------------------------

    /// One leftmost-innermost step: find the redex, prove `⊢ Step term to`,
    /// lifting through congruence clauses. `None` if `term` is a normal form.
    pub fn prove_step(&self, term: &Term) -> Result<Option<(Term, Thm)>, HolError> {
        // Structural redices at the head, after reducing arguments (innermost).
        // Each unary elimination form: try to reduce its argument first
        // (congruence), else fire the head rule.

        // car / cdr.
        if let Some(arg) = self.match_unary(term, &self.cs.car) {
            return self.step_unary(term, &arg, |x| self.car(x), 12, RedHead::CarCdr(false));
        }
        if let Some(arg) = self.match_unary(term, &self.cs.cdr) {
            return self.step_unary(term, &arg, |x| self.cdr(x), 13, RedHead::CarCdr(true));
        }
        if let Some(arg) = self.match_unary(term, &self.atom_p) {
            return self.step_unary(term, &arg, |x| self.atom_p_of(x), 14, RedHead::AtomP);
        }
        if let Some(arg) = self.match_unary(term, &self.consp) {
            return self.step_unary(term, &arg, |x| self.consp_of(x), 15, RedHead::Consp);
        }
        if let Some(arg) = self.match_unary(term, &self.null_p) {
            return self.step_unary(term, &arg, |x| self.null_p_of(x), 16, RedHead::NullP);
        }
        // eq? a b — reduce a, then b, then fire (equal-atoms clause 11).
        if let Some((a, b)) = self.match_eq(term) {
            return self.step_eq(term, &a, &b);
        }
        // cond cells — the cond driver (below) handles scrutiny + selection.
        if let Some(cells) = self.match_cond(term) {
            return self.step_cond(term, &cells);
        }
        // Integer op `(op a b)` — the `sector+int` dialect only. In `sector`
        // (no backend) this match never fires, so `(+ 2 2)` is stuck (as an
        // sexpr free-variable application, no step).
        if let Some((op, a, b)) = self.match_int_app(term) {
            return self.step_int_app(op, &a, &b);
        }
        Ok(None)
    }

    /// Match an integer-op application `(op a b)` (operands arbitrary sexpr
    /// terms), returning the op and the two operand terms. `None` in `sector`.
    fn match_int_app(&self, t: &Term) -> Option<(IntOp, Term, Term)> {
        let be = self.int_be.as_deref()?;
        let (inner, b_arg) = t.as_app()?;
        let (head, a_arg) = inner.as_app()?;
        let op = IntOp::ALL
            .iter()
            .copied()
            .find(|&op| *head == be.op_head(op))?;
        Some((op, a_arg.clone(), b_arg.clone()))
    }

    /// Step an integer-op application `(op a b)`: reduce the left operand
    /// (left congruence clause), else the right (right congruence clause),
    /// else — with both operands normal — fire the redex clause if both are
    /// `(int n)` literals. Anything else is stuck (no step).
    fn step_int_app(&self, op: IntOp, a: &Term, b: &Term) -> Result<Option<(Term, Thm)>, HolError> {
        let be = self
            .int_be
            .as_deref()
            .ok_or_else(|| HolError::Theory("step_int_app without an int backend".into()))?;
        let n = self.step_n_clauses()?;
        // Left operand steps → left congruence (word args [a, a2, b]).
        if let Some((a2, sub)) = self.prove_step(a)? {
            let to = be.op_term(op, a2.clone(), b.clone())?;
            let thm = derive_mixed(
                &self.step_rule_set(),
                Self::int_cong_idx(op, false),
                n,
                &[a.clone(), a2, b.clone()],
                vec![Premise::Derivation(sub)],
            )
            .map_err(kernel_err)?;
            return Ok(Some((to, thm)));
        }
        // Right operand steps → right congruence (word args [a, b, b2]).
        if let Some((b2, sub)) = self.prove_step(b)? {
            let to = be.op_term(op, a.clone(), b2.clone())?;
            let thm = derive_mixed(
                &self.step_rule_set(),
                Self::int_cong_idx(op, true),
                n,
                &[a.clone(), b.clone(), b2],
                vec![Premise::Derivation(sub)],
            )
            .map_err(kernel_err)?;
            return Ok(Some((to, thm)));
        }
        // Both operands normal — fire the redex clause on two literals.
        if let (Some(ia), Some(ib)) = (be.as_lit(a), be.as_lit(b)) {
            return self.step_int(op, &ia, &ib);
        }
        Ok(None)
    }

    /// `⊢ Step (op (int a)(int b)) to` for two integer literals: instantiate
    /// the op's `∀a b`-clause at `a`, `b` (giving `⊢ Step … (TARGET a b)`),
    /// then rewrite `TARGET a b` down to the reduced value with the backend's
    /// **kernel** equations (`int.<op> a b = c`, and for a comparison the
    /// `cond` clause). The result is genuine — every rewrite is kernel-checked.
    ///
    /// Errors (nat flavour) if the op's result is negative — no step is
    /// produced, so a negative subtraction is *stuck* rather than reduced.
    fn step_int(&self, op: IntOp, a: &Int, b: &Int) -> Result<Option<(Term, Thm)>, HolError> {
        let be = self
            .int_be
            .as_deref()
            .ok_or_else(|| HolError::Theory("step_int without an int backend".into()))?;
        // Nat-flavour negativity: a negative result is stuck (no step), not an
        // error propagated up (the redex simply has no rule for it here).
        let proof = match be.prove_reduce(op, a, b) {
            Ok(p) => p,
            Err(_) => return Ok(None),
        };
        // Instantiate the generic clause at the two int literals.
        let a_lit = covalence_hol_eval::mk_int(a.clone());
        let b_lit = covalence_hol_eval::mk_int(b.clone());
        let n = self.step_n_clauses()?;
        let idx = Self::int_clause_idx(op);
        let mut thm = derive_mixed(&self.step_rule_set(), idx, n, &[a_lit, b_lit], vec![])
            .map_err(kernel_err)?; // ⊢ Step (op (int a)(int b)) (TARGET a b)
        // Normalise TARGET in the conclusion via the backend's kernel eqns.
        for eq in &proof.eqs {
            thm = thm.rewrite(eq).map_err(kernel_err)?;
        }
        Ok(Some((proof.to, thm)))
    }

    /// A unary elimination `K arg`: reduce `arg` (congruence, clause `cong_idx`)
    /// if it steps, else fire the head redex rule for `head`.
    fn step_unary(
        &self,
        _term: &Term,
        arg: &Term,
        mk: impl Fn(Term) -> Result<Term, HolError>,
        cong_idx: usize,
        head: RedHead,
    ) -> Result<Option<(Term, Thm)>, HolError> {
        if let Some((arg2, sub)) = self.prove_step(arg)? {
            let to = mk(arg2.clone())?;
            let thm = self.step_cong(cong_idx, arg.clone(), arg2, sub)?;
            return Ok(Some((to, thm)));
        }
        // Argument is a normal form — fire the head rule if `arg` is a value.
        self.fire_head(head, arg)
    }

    /// Fire a head redex rule on a value argument.
    fn fire_head(&self, head: RedHead, v: &Term) -> Result<Option<(Term, Thm)>, HolError> {
        match head {
            RedHead::CarCdr(take_cdr) => {
                let Some((h, t)) = self.as_scons(v) else {
                    return Ok(None); // car/cdr of atom/nil: stuck (no rule)
                };
                let (to, idx) = if take_cdr {
                    (t.clone(), 1)
                } else {
                    (h.clone(), 0)
                };
                let thm = self.step_base(idx, &[h, t])?;
                Ok(Some((to, thm)))
            }
            RedHead::AtomP => {
                if let Some((h, t)) = self.as_scons(v) {
                    Ok(Some((self.nil(), self.step_base(2, &[h, t])?)))
                } else if let Some(b) = self.as_atom(v) {
                    Ok(Some((self.t(), self.step_base(3, &[b])?)))
                } else if self.is_snil(v) {
                    Ok(Some((self.t(), self.step_base(4, &[])?)))
                } else {
                    Ok(None)
                }
            }
            RedHead::Consp => {
                if let Some((h, t)) = self.as_scons(v) {
                    Ok(Some((self.t(), self.step_base(5, &[h, t])?)))
                } else if let Some(b) = self.as_atom(v) {
                    Ok(Some((self.nil(), self.step_base(6, &[b])?)))
                } else if self.is_snil(v) {
                    Ok(Some((self.nil(), self.step_base(7, &[])?)))
                } else {
                    Ok(None)
                }
            }
            RedHead::NullP => {
                if self.is_snil(v) {
                    Ok(Some((self.t(), self.step_base(8, &[])?)))
                } else if let Some((h, t)) = self.as_scons(v) {
                    Ok(Some((self.nil(), self.step_base(9, &[h, t])?)))
                } else if let Some(b) = self.as_atom(v) {
                    Ok(Some((self.nil(), self.step_base(10, &[b])?)))
                } else {
                    Ok(None)
                }
            }
        }
    }

    /// `eq? a b`: reduce `a`, then `b` (no dedicated congruence clauses yet —
    /// see SKELETONS), else fire the equal-atoms rule (clause 11). Distinct
    /// atoms are currently stuck (the distinct-atom clause is future work).
    fn step_eq(&self, _term: &Term, a: &Term, b: &Term) -> Result<Option<(Term, Thm)>, HolError> {
        // Operands are not reduced through congruence yet (would need eq?-arg
        // congruence clauses); require both already values.
        let (Some(ba), Some(bb)) = (self.as_atom(a), self.as_atom(b)) else {
            return Ok(None);
        };
        if ba == bb {
            return Ok(Some((self.t(), self.step_base(11, &[ba])?)));
        }
        // Distinct atoms — no clause yet.
        Ok(None)
    }

    /// `cond cells`: the clause-list scrutiny. Empty (`snil`) → `nil`
    /// (clause 17); a leading clause `(nil . body)` → drop it (`cond rest`,
    /// clause 18); a leading clause `(t . body)` → select `body` (clause 19).
    /// A leading clause whose test is not yet a `t`/`nil` value is stuck here
    /// (test-reduction congruence for cond is future work — see SKELETONS).
    fn step_cond(&self, _term: &Term, cells: &Term) -> Result<Option<(Term, Thm)>, HolError> {
        if self.is_snil(cells) {
            return Ok(Some((self.nil(), self.step_base(17, &[])?)));
        }
        // cells = scons clause rest ; clause = scons test body.
        let Some((clause, rest)) = self.as_scons(cells) else {
            return Ok(None);
        };
        let Some((test, body)) = self.as_scons(&clause) else {
            return Ok(None);
        };
        if test == self.nil {
            let to = self.cond_of(rest.clone())?;
            return Ok(Some((to, self.step_base(18, &[body, rest])?)));
        }
        if test == self.t {
            return Ok(Some((body.clone(), self.step_base(19, &[body, rest])?)));
        }
        // Test is not yet a canonical value — no rule (would need congruence).
        Ok(None)
    }

    /// Multi-step reduction to a normal form (fuel-bounded). Returns the value
    /// and `⊢ Reduces term value`, hypothesis-free for a closed program.
    ///
    /// Builds the chain right-nested from the value back: collect the step
    /// certs `t₀ →t₁ →…→ tₙ` (each `⊢ Step tᵢ tᵢ₊₁`), seed with
    /// `⊢ Reduces tₙ tₙ` (refl), then fold each step on with the `step` clause,
    /// yielding `⊢ Reduces t₀ tₙ`.
    pub fn prove_reduces(&self, term: &Term, fuel: usize) -> Result<(Term, Thm), HolError> {
        let mut cur = term.clone();
        // Collect (from, to, step-thm) triples.
        let mut steps: Vec<(Term, Term, Thm)> = Vec::new();
        for _ in 0..fuel {
            match self.prove_step(&cur)? {
                Some((to, thm)) => {
                    steps.push((cur.clone(), to.clone(), thm));
                    cur = to;
                }
                None => break,
            }
        }
        // Seed with refl at the final term, then fold right-to-left.
        let value = cur.clone();
        let mut acc = self.reduces_refl(&value)?; // ⊢ Reduces value value
        for (from, to, step) in steps.into_iter().rev() {
            // acc : ⊢ Reduces to value ; step : ⊢ Step from to
            acc = self.reduces_step(&from, &to, &value, step, acc)?;
        }
        Ok((value, acc))
    }

    // ------------------------------------------------------------------
    // Term inspection (untrusted matchers)
    // ------------------------------------------------------------------

    fn match_unary(&self, t: &Term, head: &Term) -> Option<Term> {
        let (f, a) = t.as_app()?;
        (*f == *head).then(|| a.clone())
    }

    fn match_eq(&self, t: &Term) -> Option<(Term, Term)> {
        let (inner, b) = t.as_app()?;
        let (f, a) = inner.as_app()?;
        (*f == self.eq_p).then(|| (a.clone(), b.clone()))
    }

    fn match_cond(&self, t: &Term) -> Option<Term> {
        let (f, cells) = t.as_app()?;
        (*f == self.cond).then(|| cells.clone())
    }

    fn as_scons(&self, v: &Term) -> Option<(Term, Term)> {
        self.carrier.as_cons(v)
    }

    fn as_atom(&self, v: &Term) -> Option<Term> {
        self.carrier.as_atom_term(v)
    }

    fn is_snil(&self, v: &Term) -> bool {
        self.carrier.is_nil(v)
    }

    // ------------------------------------------------------------------
    // Surface compiler + driver + renderer (the relational REPL path)
    // ------------------------------------------------------------------

    /// Lower a surface [`SExpr`] into the relational operator-application term.
    ///
    /// Handles `quote` → data, the McCarthy primitives (`car`/`cdr`/`cons`/
    /// `atom?`/`consp`/`null?`/`eq?`/`cond`/`if`), and — when the dialect has an
    /// [`IntBackend`] — numeral atoms → `(int n)` and the int-op symbols
    /// `+ - * <= =` → their relational op heads. In [`Sector`](Dialect::Sector)
    /// (no backend) numerals stay symbol atoms and the int ops stay stuck free
    /// applications.
    pub fn compile_surface(&self, e: &SExpr) -> Result<Term, HolError> {
        match e {
            SExpr::Atom(a) => self.surface_atom(a),
            SExpr::List(items) => self.surface_form(items),
        }
    }

    /// An atom in operand position: a numeral (int dialect only), else a
    /// symbol atom.
    fn surface_atom(&self, a: &Atom) -> Result<Term, HolError> {
        if let Atom::Symbol(s) = a
            && self.int_be.is_some()
            && let Ok(n) = s.parse::<Int>()
        {
            return self.int_lit(&n);
        }
        self.data_atom(a)
    }

    /// A symbol/string atom → the `atom "…"` datum (numerals-as-symbols too).
    fn data_atom(&self, a: &Atom) -> Result<Term, HolError> {
        let bytes: &[u8] = match a {
            Atom::Symbol(s) => s.as_bytes(),
            Atom::Str { bytes, .. } => bytes,
        };
        self.carrier.atom(PayloadLit::Sym(bytes))
    }

    /// `quote` payload → nested `scons`/`atom`/`snil` data (the carrier's
    /// `quote` fold; numerals-in-data stay symbol atoms).
    fn data(&self, e: &SExpr) -> Result<Term, HolError> {
        self.carrier.quote(e)
    }

    fn surface_form(&self, items: &[SExpr]) -> Result<Term, HolError> {
        let (head, args) = items
            .split_first()
            .ok_or_else(|| HolError::Stuck("`()` is an empty application (no operator)".into()))?;
        let op = head
            .as_symbol()
            .ok_or_else(|| HolError::Stuck("application head is not a symbol".into()))?;
        // An int-op symbol `+ - * <= =`. In `sector+int` this builds a genuine
        // integer redex; in `sector` (no backend) it still builds the op-head
        // application — but with symbol-atom operands and no `Step` clause, so
        // `(+ 2 2)` is **stuck** (reduces to itself) rather than erroring.
        if let Some(iop) = IntOp::ALL.iter().copied().find(|o| o.symbol() == op) {
            if args.len() != 2 {
                return Err(HolError::Stuck(format!("`{op}` takes 2 arguments")));
            }
            let a = self.compile_surface(&args[0])?;
            let b = self.compile_surface(&args[1])?;
            return self.int_op_term(iop, a, b);
        }
        match (op, args.len()) {
            ("quote", 1) => self.data(&args[0]),
            ("car", 1) => self.car(self.compile_surface(&args[0])?),
            ("cdr", 1) => self.cdr(self.compile_surface(&args[0])?),
            ("cons", 2) => {
                let h = self.compile_surface(&args[0])?;
                let t = self.compile_surface(&args[1])?;
                self.scons(h, t)
            }
            ("atom?" | "atom", 1) => self.atom_p_of(self.compile_surface(&args[0])?),
            ("consp" | "pair?", 1) => self.consp_of(self.compile_surface(&args[0])?),
            ("null?" | "null", 1) => self.null_p_of(self.compile_surface(&args[0])?),
            ("eq?" | "eq", 2) => {
                let a = self.compile_surface(&args[0])?;
                let b = self.compile_surface(&args[1])?;
                self.eq_of(a, b)
            }
            // `if C A B` → a two-clause `cond`.
            ("if", 3) => {
                let c = self.compile_surface(&args[0])?;
                let a = self.compile_surface(&args[1])?;
                let b = self.compile_surface(&args[2])?;
                let else_cell = self.scons(self.t.clone(), b)?;
                let then_cell = self.scons(c, a)?;
                let rest = self.scons(else_cell, self.cs.snil.clone())?;
                let cells = self.scons(then_cell, rest)?;
                self.cond_of(cells)
            }
            // `cond (T E)...` → the relational `cond` over a scons-chain of
            // `(test . body)` cells.
            ("cond", _) => {
                let mut cells = self.cs.snil.clone();
                for clause in args.iter().rev() {
                    let SExpr::List(parts) = clause else {
                        return Err(HolError::Stuck("cond clause is not a list".into()));
                    };
                    if parts.len() != 2 {
                        return Err(HolError::Stuck("cond clause must be (test body)".into()));
                    }
                    let test = self.compile_surface(&parts[0])?;
                    let body = self.compile_surface(&parts[1])?;
                    let cell = self.scons(test, body)?;
                    cells = self.scons(cell, cells)?;
                }
                self.cond_of(cells)
            }
            // Function definition / abstraction forms: honestly unsupported
            // here — the relational dialects have no β/δ clauses yet.
            ("defun" | "define" | "label" | "lambda", _) => Err(HolError::Stuck(format!(
                "`{op}` needs recursion, which this relational dialect does not \
                 support yet — switch dialects with `#lang scheme`"
            ))),
            (other, n) => {
                let ints = if self.int_be.is_some() {
                    " + - * <= ="
                } else {
                    ""
                };
                Err(HolError::Stuck(format!(
                    "unknown or misapplied operator `{other}` (applied to {n} argument{}) — \
                     this dialect supports: quote car cdr cons atom? consp null? eq? cond \
                     if{ints}; `defun`/`lambda` need `#lang scheme`",
                    if n == 1 { "" } else { "s" }
                )))
            }
        }
    }

    /// Is `t` a **value** of the relation: an `(int n)` literal (int dialect),
    /// an atom, `snil`/`nil`, or a cons of values?
    pub fn is_value(&self, t: &Term) -> bool {
        if let Some(be) = self.int_be.as_deref()
            && be.as_lit(t).is_some()
        {
            return true;
        }
        if self.is_snil(t) || self.as_atom(t).is_some() {
            return true;
        }
        if let Some((h, tl)) = self.as_scons(t) {
            return self.is_value(&h) && self.is_value(&tl);
        }
        false
    }

    /// Drive a surface form to a **value**: compile it, run the step relation
    /// (fuel-bounded), and return the value term and `⊢ Reduces input value`
    /// (hypothesis-free for a closed program).
    ///
    /// **Honesty guard:** if the fuel runs out, or the final term is *not* a
    /// value (see [`is_value`](Self::is_value)) — a stuck non-redex — this
    /// returns a clean `Err` instead of surfacing the raw kernel term as if it
    /// were a result. (The partial `⊢ Reduces` theorem is still genuine; it
    /// just does not end at a value, so nothing is printed.)
    pub fn reduce_surface(&self, e: &SExpr, fuel: usize) -> Result<(Term, Thm), HolError> {
        let input = self.compile_surface(e)?;
        let (value, thm) = self.prove_reduces(&input, fuel)?;
        if self.is_value(&value) {
            return Ok((value, thm));
        }
        if self.prove_step(&value)?.is_some() {
            // Still steps — the fuel ran out before a value was reached.
            return Err(HolError::Stuck(format!(
                "`{}` ran out of fuel ({fuel} steps) before reaching a value",
                surface_text(e)
            )));
        }
        let hint = match self.dialect {
            Dialect::Sector => " (integer arithmetic needs `#lang lisp`)",
            Dialect::SectorInt(_) => "",
        };
        Err(HolError::Stuck(format!(
            "`{}` does not reduce to a value: a subterm has no reduction rule in this dialect{hint}",
            surface_text(e)
        )))
    }

    /// Render a relational value term to Lisp text: `(int n)` → decimal `n`,
    /// `atom "…"` → its text, `snil` → `()`, `scons` chains → `(e₁ e₂ …)`.
    pub fn render_value(&self, v: &Term) -> String {
        if let Some(be) = self.int_be.as_deref()
            && let Some(n) = be.as_lit(v)
        {
            return n.to_string();
        }
        if self.is_snil(v) {
            return "()".to_string();
        }
        if let Some(b) = self.as_atom(v)
            && let Some(bytes) = blob_bytes(&b)
        {
            return String::from_utf8_lossy(&bytes).into_owned();
        }
        if self.as_scons(v).is_some() {
            let mut out = String::from("(");
            let mut cur = v.clone();
            let mut first = true;
            while let Some((h, t)) = self.as_scons(&cur) {
                if !first {
                    out.push(' ');
                }
                first = false;
                out.push_str(&self.render_value(&h));
                if self.is_snil(&t) {
                    break;
                }
                if self.as_scons(&t).is_none() {
                    out.push_str(" . ");
                    out.push_str(&self.render_value(&t));
                    break;
                }
                cur = t;
            }
            out.push(')');
            return out;
        }
        format!("{v}") // unknown / stuck shape — surface the raw term
    }
}

/// Render a surface [`SExpr`] back to Lisp text — for **error messages** only
/// (never as a value; values print via [`LispRel::render_value`] off a theorem).
fn surface_text(e: &SExpr) -> String {
    match e {
        SExpr::Atom(Atom::Symbol(s)) => s.to_string(),
        SExpr::Atom(Atom::Str { bytes, .. }) => {
            format!("\"{}\"", String::from_utf8_lossy(bytes))
        }
        SExpr::List(items) => {
            let inner: Vec<String> = items.iter().map(surface_text).collect();
            format!("({})", inner.join(" "))
        }
    }
}

/// Extract the bytes of a blob literal term, via the designated `Lit` facade.
fn blob_bytes(t: &Term) -> Option<Vec<u8>> {
    use covalence_core::seam::Lit;
    match Lit::from_term(t)? {
        Lit::Bytes(b) => Some(b.to_vec()),
        _ => None,
    }
}

/// The head redex family a unary elimination fires.
#[derive(Clone, Copy)]
enum RedHead {
    /// `car` (false) / `cdr` (true).
    CarCdr(bool),
    AtomP,
    Consp,
    NullP,
}

/// Map a [`HolError`] back into a `covalence_core::Error` inside a clause
/// builder (whose closure returns `covalence_core::Result`).
fn to_core(e: HolError) -> covalence_core::Error {
    covalence_core::Error::ConnectiveRule(e.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rel() -> LispRel {
        LispRel::new().unwrap()
    }

    /// `⊢ Reduces (car (cons (atom a) (atom b))) (atom a)`, hyps-free, and equal
    /// to `derivable2(Reduces, input, value)`.
    #[test]
    fn car_cons_reduces() {
        let r = rel();
        let a = r.sym("a");
        let b = r.sym("b");
        let input = r.car(r.scons(a.clone(), b.clone()).unwrap()).unwrap();

        let (value, thm) = r.prove_reduces(&input, 16).unwrap();
        assert_eq!(value, a);
        assert!(thm.hyps().is_empty(), "closed reduction must be hyps-free");
        assert_eq!(thm.concl(), &r.reduces_prop(&input, &a).unwrap());
    }

    /// A multi-step nested reduction:
    /// `⊢ Reduces (car (cdr (quote (a b c)))) (atom b)`.
    /// `(quote (a b c))` = `scons a (scons b (scons c snil))`.
    #[test]
    fn car_cdr_nested_reduces() {
        let r = rel();
        let a = r.sym("a");
        let b = r.sym("b");
        let c = r.sym("c");
        let snil = r.cs.snil.clone();
        let list = r
            .scons(
                a.clone(),
                r.scons(b.clone(), r.scons(c.clone(), snil).unwrap())
                    .unwrap(),
            )
            .unwrap();
        // car (cdr list) : cdr list → (scons b (scons c snil)); car → b.
        let input = r.car(r.cdr(list.clone()).unwrap()).unwrap();

        let (value, thm) = r.prove_reduces(&input, 16).unwrap();
        assert_eq!(value, b);
        assert!(thm.hyps().is_empty());
        assert_eq!(thm.concl(), &r.reduces_prop(&input, &b).unwrap());
    }

    /// `atom?` reduces to the sexpr `t` / `nil` atom.
    #[test]
    fn atom_p_reduces_to_sexpr_bool() {
        let r = rel();
        let a = r.sym("a");
        // atom? (atom a) → t.
        let in1 = r.atom_p_of(a.clone()).unwrap();
        let (v1, th1) = r.prove_reduces(&in1, 8).unwrap();
        assert_eq!(v1, r.t());
        assert!(th1.hyps().is_empty());
        assert_eq!(th1.concl(), &r.reduces_prop(&in1, &r.t()).unwrap());

        // atom? (cons a a) → nil.
        let cons = r.scons(a.clone(), a.clone()).unwrap();
        let in2 = r.atom_p_of(cons).unwrap();
        let (v2, _) = r.prove_reduces(&in2, 8).unwrap();
        assert_eq!(v2, r.nil());
    }

    /// `consp` / `null?` reduce to the sexpr booleans.
    #[test]
    fn consp_null_reduce() {
        let r = rel();
        let a = r.sym("a");
        let cons = r.scons(a.clone(), a.clone()).unwrap();

        let (v, _) = r
            .prove_reduces(&r.consp_of(cons.clone()).unwrap(), 8)
            .unwrap();
        assert_eq!(v, r.t());
        let (v, _) = r.prove_reduces(&r.null_p_of(cons).unwrap(), 8).unwrap();
        assert_eq!(v, r.nil());
        let (v, _) = r
            .prove_reduces(&r.null_p_of(r.cs.snil.clone()).unwrap(), 8)
            .unwrap();
        assert_eq!(v, r.t());
    }

    /// `eq?` on equal atoms reduces to `t`; distinct atoms are stuck (no rule).
    #[test]
    fn eq_atoms() {
        let r = rel();
        let a = r.sym("a");
        let b = r.sym("b");
        // eq? a a → t.
        let (v, th) = r
            .prove_reduces(&r.eq_of(a.clone(), a.clone()).unwrap(), 4)
            .unwrap();
        assert_eq!(v, r.t());
        assert!(th.hyps().is_empty());
        // eq? a b: stuck — no step, so Reduces input input (refl).
        let input = r.eq_of(a.clone(), b.clone()).unwrap();
        let (v, _) = r.prove_reduces(&input, 4).unwrap();
        assert_eq!(v, input);
    }

    /// `cond` selects the first truthy clause, skipping falsy ones, and
    /// reduces to the sexpr `t` / `nil` truthiness values.
    #[test]
    fn cond_selects_truthy_clause() {
        let r = rel();
        let win = r.sym("win");
        let lose = r.sym("lose");
        // cond ((nil . lose) (t . win)) → skip → select → win.
        // clause2 = (t . win) ; rest = scons clause2 snil.
        let c2 = r.scons(r.t(), win.clone()).unwrap();
        let rest = r.scons(c2, r.cs.snil.clone()).unwrap();
        let c1 = r.scons(r.nil(), lose.clone()).unwrap();
        let cells = r.scons(c1, rest).unwrap();
        let input = r.cond_of(cells).unwrap();

        let (value, thm) = r.prove_reduces(&input, 8).unwrap();
        assert_eq!(value, win);
        assert!(thm.hyps().is_empty());
        assert_eq!(thm.concl(), &r.reduces_prop(&input, &win).unwrap());

        // An empty cond → nil.
        let (v, _) = r
            .prove_reduces(&r.cond_of(r.cs.snil.clone()).unwrap(), 4)
            .unwrap();
        assert_eq!(v, r.nil());
    }

    /// A value / stuck term yields no step.
    #[test]
    fn value_has_no_step() {
        let r = rel();
        let a = r.sym("a");
        assert!(r.prove_step(&a).unwrap().is_none()); // atom value
        assert!(r.prove_step(&r.cs.snil.clone()).unwrap().is_none()); // snil value
        // car of an atom (no projection rule) is stuck.
        assert!(r.prove_step(&r.car(a).unwrap()).unwrap().is_none());
    }

    /// The rule sets have the expected clause counts. `sector` has 20 `Step`
    /// clauses; `sector+int` adds the 5 integer redex clauses and the 10
    /// integer congruence clauses (35 total).
    #[test]
    fn clause_counts() {
        let r = rel();
        assert_eq!(r.step_n_clauses().unwrap(), 20);
        assert_eq!(r.reduces_rule_set().n_clauses().unwrap(), 2);

        let ri = LispRel::with_dialect(Dialect::SectorInt(IntFlavour::Int)).unwrap();
        assert_eq!(ri.step_n_clauses().unwrap(), 35);
    }

    // ---- integer dialect (sector+int) ------------------------------------

    fn int_rel() -> LispRel {
        LispRel::with_dialect(Dialect::SectorInt(IntFlavour::Int)).unwrap()
    }
    fn nat_rel() -> LispRel {
        LispRel::with_dialect(Dialect::SectorInt(IntFlavour::Nat)).unwrap()
    }
    fn i(n: i128) -> Int {
        Int::from(n)
    }

    /// `sector+int`: `⊢ Reduces (+ (int 2)(int 2)) (int 4)`, hyps-free, equal
    /// to `derivable2(Reduces, input, value)`.
    #[test]
    fn int_add_reduces() {
        let r = int_rel();
        let a = r.int_lit(&i(2)).unwrap();
        let b = r.int_lit(&i(2)).unwrap();
        let input = r.int_op_term(IntOp::Add, a, b).unwrap();

        let (value, thm) = r.prove_reduces(&input, 8).unwrap();
        assert_eq!(value, r.int_lit(&i(4)).unwrap());
        assert!(thm.hyps().is_empty(), "closed reduction must be hyps-free");
        assert_eq!(thm.concl(), &r.reduces_prop(&input, &value).unwrap());
    }

    /// `(- (int 5)(int 3)) ⇒ (int 2)` and `(* (int 3)(int 4)) ⇒ (int 12)`.
    #[test]
    fn int_sub_mul_reduce() {
        let r = int_rel();
        let sub = r
            .int_op_term(
                IntOp::Sub,
                r.int_lit(&i(5)).unwrap(),
                r.int_lit(&i(3)).unwrap(),
            )
            .unwrap();
        let (v, th) = r.prove_reduces(&sub, 8).unwrap();
        assert_eq!(v, r.int_lit(&i(2)).unwrap());
        assert!(th.hyps().is_empty());

        let mul = r
            .int_op_term(
                IntOp::Mul,
                r.int_lit(&i(3)).unwrap(),
                r.int_lit(&i(4)).unwrap(),
            )
            .unwrap();
        let (v, _) = r.prove_reduces(&mul, 8).unwrap();
        assert_eq!(v, r.int_lit(&i(12)).unwrap());
    }

    /// A negative subtraction is fine in the `int` dialect: `(- (int 3)(int 5))
    /// ⇒ (int -2)`.
    #[test]
    fn int_sub_may_go_negative() {
        let r = int_rel();
        let sub = r
            .int_op_term(
                IntOp::Sub,
                r.int_lit(&i(3)).unwrap(),
                r.int_lit(&i(5)).unwrap(),
            )
            .unwrap();
        let (v, th) = r.prove_reduces(&sub, 8).unwrap();
        assert_eq!(v, r.int_lit(&i(-2)).unwrap());
        assert!(th.hyps().is_empty());
    }

    /// Comparisons reduce to the sexpr `t` / `nil` truthiness values.
    #[test]
    fn int_comparisons_reduce_to_sexpr_bool() {
        let r = int_rel();
        // 2 <= 5 → t.
        let le = r
            .int_op_term(
                IntOp::Le,
                r.int_lit(&i(2)).unwrap(),
                r.int_lit(&i(5)).unwrap(),
            )
            .unwrap();
        let (v, th) = r.prove_reduces(&le, 8).unwrap();
        assert_eq!(v, r.t());
        assert!(th.hyps().is_empty());
        assert_eq!(th.concl(), &r.reduces_prop(&le, &r.t()).unwrap());

        // 5 <= 2 → nil.
        let le2 = r
            .int_op_term(
                IntOp::Le,
                r.int_lit(&i(5)).unwrap(),
                r.int_lit(&i(2)).unwrap(),
            )
            .unwrap();
        let (v, _) = r.prove_reduces(&le2, 8).unwrap();
        assert_eq!(v, r.nil());

        // 4 = 4 → t ; 4 = 5 → nil.
        let eq = r
            .int_op_term(
                IntOp::Eq,
                r.int_lit(&i(4)).unwrap(),
                r.int_lit(&i(4)).unwrap(),
            )
            .unwrap();
        let (v, _) = r.prove_reduces(&eq, 8).unwrap();
        assert_eq!(v, r.t());
        let neq = r
            .int_op_term(
                IntOp::Eq,
                r.int_lit(&i(4)).unwrap(),
                r.int_lit(&i(5)).unwrap(),
            )
            .unwrap();
        let (v, _) = r.prove_reduces(&neq, 8).unwrap();
        assert_eq!(v, r.nil());
    }

    /// **`sector` has no integer clauses**: `(+ (int 2)(int 2))` is STUCK.
    /// We build the same op application (the heads exist as free variables in
    /// `sector` too) and confirm `prove_step` yields nothing — so `Reduces`
    /// is just reflexivity at the input.
    #[test]
    fn sector_has_no_int_step() {
        let sector = rel(); // Dialect::Sector
        let intd = int_rel();
        // Build `(+ (int 2)(int 2))` — a genuine sexpr application in both
        // dialects (the `int`/`+` heads are the same free variables).
        let a = intd.int_lit(&i(2)).unwrap();
        let b = intd.int_lit(&i(2)).unwrap();
        let input = sector.int_op_term(IntOp::Add, a, b).unwrap();

        assert!(
            sector.prove_step(&input).unwrap().is_none(),
            "`(+ 2 2)` must be stuck in `sector`"
        );
        // In `sector`, Reduces input input (refl only).
        let (v, _) = sector.prove_reduces(&input, 8).unwrap();
        assert_eq!(v, input);

        // The same input DOES step in `sector+int`.
        assert!(intd.prove_step(&input).unwrap().is_some());
    }

    /// **`nat` variant**: `(+ 2 2) ⇒ 4`, but `(- 3 5)` is stuck (negative
    /// difference), and building `lit(-1)` errors.
    #[test]
    fn nat_variant_rejects_negatives() {
        let r = nat_rel();
        // 2 + 2 → 4 (fine in nat).
        let add = r
            .int_op_term(
                IntOp::Add,
                r.int_lit(&i(2)).unwrap(),
                r.int_lit(&i(2)).unwrap(),
            )
            .unwrap();
        let (v, _) = r.prove_reduces(&add, 8).unwrap();
        assert_eq!(v, r.int_lit(&i(4)).unwrap());

        // 3 - 5 would be -2 → the nat dialect has no step here (stuck).
        let sub = r
            .int_op_term(
                IntOp::Sub,
                r.int_lit(&i(3)).unwrap(),
                r.int_lit(&i(5)).unwrap(),
            )
            .unwrap();
        assert!(
            r.prove_step(&sub).unwrap().is_none(),
            "negative subtraction is stuck in the nat dialect"
        );
        let (v, _) = r.prove_reduces(&sub, 8).unwrap();
        assert_eq!(v, sub, "stuck → Reduces is reflexivity");

        // Constructing a negative literal errors.
        assert!(
            r.int_lit(&i(-1)).is_err(),
            "the nat dialect must refuse a negative literal"
        );
    }

    /// **Congruence into int operands**: `(+ (int 1) (+ (int 2)(int 3)))`
    /// reduces the nested operand in place (right congruence) and then fires
    /// the redex — a genuine hyps-free `⊢ Reduces input (int 6)`.
    #[test]
    fn nested_int_congruence_reduces() {
        let r = int_rel();
        let inner = r
            .int_op_term(
                IntOp::Add,
                r.int_lit(&i(2)).unwrap(),
                r.int_lit(&i(3)).unwrap(),
            )
            .unwrap();
        let input = r
            .int_op_term(IntOp::Add, r.int_lit(&i(1)).unwrap(), inner)
            .unwrap();
        let (v, thm) = r.prove_reduces(&input, 16).unwrap();
        assert_eq!(v, r.int_lit(&i(6)).unwrap());
        assert!(thm.hyps().is_empty(), "closed reduction must be hyps-free");
        assert_eq!(thm.concl(), &r.reduces_prop(&input, &v).unwrap());

        // Left congruence too: `(* (+ 1 2) (- 5 1)) ⇒ 12`.
        let left = r
            .int_op_term(
                IntOp::Add,
                r.int_lit(&i(1)).unwrap(),
                r.int_lit(&i(2)).unwrap(),
            )
            .unwrap();
        let right = r
            .int_op_term(
                IntOp::Sub,
                r.int_lit(&i(5)).unwrap(),
                r.int_lit(&i(1)).unwrap(),
            )
            .unwrap();
        let input = r.int_op_term(IntOp::Mul, left, right).unwrap();
        let (v, thm) = r.prove_reduces(&input, 16).unwrap();
        assert_eq!(v, r.int_lit(&i(12)).unwrap());
        assert!(thm.hyps().is_empty());
        assert_eq!(thm.concl(), &r.reduces_prop(&input, &v).unwrap());
    }

    /// A single congruence step is itself a genuine membership theorem:
    /// `⊢ Step (+ (+ 1 1) 2) (+ 2 2)`.
    #[test]
    fn int_cong_step_is_a_membership_theorem() {
        let r = int_rel();
        let inner = r
            .int_op_term(
                IntOp::Add,
                r.int_lit(&i(1)).unwrap(),
                r.int_lit(&i(1)).unwrap(),
            )
            .unwrap();
        let from = r
            .int_op_term(IntOp::Add, inner, r.int_lit(&i(2)).unwrap())
            .unwrap();
        let (to, thm) = r.prove_step(&from).unwrap().unwrap();
        let expected = r
            .int_op_term(
                IntOp::Add,
                r.int_lit(&i(2)).unwrap(),
                r.int_lit(&i(2)).unwrap(),
            )
            .unwrap();
        assert_eq!(to, expected);
        assert!(thm.hyps().is_empty());
        assert_eq!(thm.concl(), &r.step_prop(&from, &to).unwrap());
    }

    /// The produced `⊢ Step (+ (int a)(int b)) (int c)` is a genuine membership
    /// theorem: it equals `derivable2(Step, from, to)`, hyps-free.
    #[test]
    fn int_step_is_a_membership_theorem() {
        let r = int_rel();
        let a = r.int_lit(&i(7)).unwrap();
        let b = r.int_lit(&i(5)).unwrap();
        let from = r.int_op_term(IntOp::Add, a, b).unwrap();
        let (to, thm) = r.prove_step(&from).unwrap().unwrap();
        assert_eq!(to, r.int_lit(&i(12)).unwrap());
        assert!(thm.hyps().is_empty());
        assert_eq!(thm.concl(), &r.step_prop(&from, &to).unwrap());
    }
}
