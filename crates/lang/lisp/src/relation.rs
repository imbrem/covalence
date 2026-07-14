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
//! falsy clause selection), and one congruence clause per unary elimination
//! context. β/λ, δ/`defun`, integer literals, `eq?` on distinct atoms, and
//! congruence *into* `eq?` operands and `cond` tests are the next phase (see
//! `SKELETONS.md`).

use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::mk_blob;
use covalence_init::init::ext::TermExt;
use covalence_init::init::inductive::carved::{CarvedSExpr, carved};
use covalence_init::metalogic::binary::{Premise, RuleSet2, derivable2, derive_mixed};
use covalence_init::{Term, Type};

use crate::hol::HolError;

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

/// The set of operator heads + the sexpr carrier, built once from [`carved`].
pub struct LispRel {
    cs: &'static CarvedSExpr,
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
    /// Bind the process-global carved sexpr carrier and the operator heads.
    pub fn new() -> Result<Self, HolError> {
        let cs = carved().map_err(theory_err)?;
        let tau = &cs.tau;
        let atom_c = |s: &str| Term::app(cs.atom.clone(), mk_blob(s.as_bytes().to_vec()));
        Ok(LispRel {
            cs,
            t: atom_c("t"),
            nil: atom_c("nil"),
            atom_p: op_head("lisp.rel.atom?", 1, tau),
            consp: op_head("lisp.rel.consp", 1, tau),
            null_p: op_head("lisp.rel.null?", 1, tau),
            eq_p: op_head("lisp.rel.eq?", 2, tau),
            cond: op_head("lisp.rel.cond", 1, tau),
        })
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

            Ok(cs)
        })
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
        Ok(None)
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
        let (inner, t) = v.as_app()?;
        let (op, h) = inner.as_app()?;
        (*op == self.cs.scons).then(|| (h.clone(), t.clone()))
    }

    fn as_atom(&self, v: &Term) -> Option<Term> {
        let (op, b) = v.as_app()?;
        (*op == self.cs.atom).then(|| b.clone())
    }

    fn is_snil(&self, v: &Term) -> bool {
        *v == self.cs.snil
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

    /// The rule sets have the expected clause counts.
    #[test]
    fn clause_counts() {
        let r = rel();
        assert_eq!(r.step_n_clauses().unwrap(), 20);
        assert_eq!(r.reduces_rule_set().n_clauses().unwrap(), 2);
    }
}
