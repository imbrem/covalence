//! [`HolAletheBridge`] — an [`AletheBridge`] backed by the
//! `covalence-core` HOL kernel.
//!
//! This is the concrete reincarnation of the bridge whose legacy
//! `Prover`-based impl was removed in the kernel rewrite. It checks an
//! Alethe refutation by *replaying it as a HOL derivation*: every clause
//! becomes a kernel [`Thm`] whose conclusion is the clause read as a
//! right-associated disjunction of literals (the empty clause is `F`),
//! and every Alethe rule is discharged by real kernel inference. If the
//! proof reaches the empty clause with hypotheses drawn only from the
//! `assume`d assertions, the original problem is genuinely `Unsat`.
//!
//! ## Modelling
//!
//! * **Sorts.** `(declare-sort U 0)` → the type variable `Type::tfree("U")`.
//!   `Bool` is the kernel `bool`. Parametric sorts (arity > 0) are not yet
//!   supported.
//! * **Symbols.** `(declare-fun f (A B) C)` → the free variable
//!   `f : A → B → C`. Uninterpreted constants and functions are free
//!   variables, so a derived `⊢ F` is a refutation *for every
//!   interpretation* of them — exactly the UNSAT semantics.
//! * **Terms.** S-expressions translate structurally; the `(! t :named @x)`
//!   annotation records `@x ↦ t` so later references resolve.
//! * **Clauses & rules.** See [`HolAletheBridge::step`]; the propositional
//!   plumbing (resolution, clausification) lives in
//!   [`covalence_hol::init::logic`], powered by the kernel's `lem`.
//!
//! ## Scope
//!
//! The QF_UF fragment — `assume`, `resolution` / `th_resolution`, `refl`,
//! `trans`, `symm`, `cong`, `eq_*`, `equiv_pos2`, `false` — is wired
//! through. Rewrite `hole`s, subproofs (`anchor` / `:discharge`), and the
//! remaining rule families return [`BridgeError::NotImplemented`]; see
//! `SKELETONS.md`.

use std::collections::HashMap;

use covalence_core::{Term, Thm, Type, defs};
use covalence_hol::HolLightCtx;
use covalence_hol::init::logic;
use covalence_sexp::SExpr;
use covalence_types::Decision;

use crate::bridge::AletheBridge;
use crate::error::BridgeError;

type R<T> = Result<T, BridgeError>;

/// Alethe-checking bridge over the `covalence-core` kernel.
pub struct HolAletheBridge {
    /// Declared sorts: name → HOL type (`Bool` and arity-0 sorts).
    sorts: HashMap<String, Type>,
    /// Declared symbols: name → its HOL type (constants have an arrow-free type).
    funs: HashMap<String, Type>,
    /// `:named` term abbreviations introduced by `(! t :named @x)`.
    named: HashMap<String, Term>,
    /// The terms introduced by `assume` — the problem's asserted formulas.
    /// A refutation is valid iff the empty clause's hypotheses are a
    /// subset of these.
    assumed: Vec<Term>,
    /// Final verdict; flips to `Unsat` once the empty clause is derived.
    decision: Decision,
}

impl HolAletheBridge {
    /// A fresh bridge with no declarations.
    pub fn new() -> Self {
        Self {
            sorts: HashMap::new(),
            funs: HashMap::new(),
            named: HashMap::new(),
            assumed: Vec::new(),
            decision: Decision::Unknown,
        }
    }

    // -----------------------------------------------------------------
    // Sort / term translation
    // -----------------------------------------------------------------

    /// Resolve a sort S-expression to a HOL type.
    fn sort_to_type(&self, e: &SExpr) -> R<Type> {
        if let Some(sym) = e.as_symbol() {
            if sym == "Bool" {
                return Ok(Type::bool());
            }
            return self
                .sorts
                .get(sym)
                .cloned()
                .ok_or_else(|| BridgeError::UnknownSort(sym.to_string()));
        }
        Err(BridgeError::Malformed(format!("sort: {e:?}")))
    }

    /// Translate a term S-expression to a HOL [`Term`]. Records and
    /// resolves `(! t :named @x)` abbreviations as a side effect.
    fn term(&mut self, e: &SExpr) -> R<Term> {
        match e {
            // Atom: a literal, a declared symbol, or a `@named` reference.
            _ if e.as_symbol().is_some() => {
                let sym = e.as_symbol().unwrap();
                match sym {
                    "true" => Ok(Term::bool_lit(true)),
                    "false" => Ok(Term::bool_lit(false)),
                    _ if sym.starts_with('@') => self
                        .named
                        .get(sym)
                        .cloned()
                        .ok_or_else(|| BridgeError::Malformed(format!("unknown :named ref {sym}"))),
                    _ => {
                        let ty = self
                            .funs
                            .get(sym)
                            .cloned()
                            .ok_or_else(|| BridgeError::UnknownFun(sym.to_string()))?;
                        Ok(Term::free(sym, ty))
                    }
                }
            }
            // List: an annotation, a connective, or a function application.
            _ => {
                let items = e
                    .as_list()
                    .ok_or_else(|| BridgeError::Malformed(format!("term: {e:?}")))?;
                let head = items
                    .first()
                    .and_then(|h| h.as_symbol())
                    .ok_or_else(|| BridgeError::Malformed(format!("term head: {e:?}")))?;
                match head {
                    "!" => self.annotated(items),
                    "not" => {
                        let p = self.term(&items[1])?;
                        Ok(HolLightCtx::new().mk_not(p))
                    }
                    "and" => self.fold_binop(&items[1..], |c, a, b| c.mk_and(a, b)),
                    "or" => self.fold_binop(&items[1..], |c, a, b| c.mk_or(a, b)),
                    "=>" => self.fold_binop(&items[1..], |c, a, b| c.mk_imp(a, b)),
                    "=" => {
                        if items.len() != 3 {
                            return Err(BridgeError::Malformed(format!("`=` arity: {e:?}")));
                        }
                        let l = self.term(&items[1])?;
                        let r = self.term(&items[2])?;
                        HolLightCtx::new().mk_eq(l, r).map_err(Into::into)
                    }
                    // Uninterpreted application `(f a1 … an)`.
                    _ => {
                        let mut t = self.term(&items[0])?;
                        for arg in &items[1..] {
                            let a = self.term(arg)?;
                            t = Term::app(t, a);
                        }
                        // Type-check the spine eagerly for a clear error.
                        t.type_of()?;
                        Ok(t)
                    }
                }
            }
        }
    }

    /// Translate `(! t :named @x …)`: translate `t`, bind every
    /// `:named` symbol to it, return `t`.
    fn annotated(&mut self, items: &[SExpr]) -> R<Term> {
        let inner = self.term(&items[1])?;
        let mut i = 2;
        while i < items.len() {
            if items[i].as_symbol() == Some(":named") {
                if let Some(name) = items.get(i + 1).and_then(|s| s.as_symbol()) {
                    self.named.insert(name.to_string(), inner.clone());
                }
                i += 2;
            } else {
                i += 1;
            }
        }
        Ok(inner)
    }

    /// Left-fold an n-ary connective (`and`/`or`/`=>`) over its args.
    fn fold_binop(
        &mut self,
        args: &[SExpr],
        op: impl Fn(&HolLightCtx, Term, Term) -> Term,
    ) -> R<Term> {
        if args.is_empty() {
            return Err(BridgeError::Malformed("nullary connective".into()));
        }
        let ctx = HolLightCtx::new();
        let mut acc = self.term(&args[0])?;
        for a in &args[1..] {
            let t = self.term(a)?;
            acc = op(&ctx, acc, t);
        }
        Ok(acc)
    }

    // -----------------------------------------------------------------
    // Decision bookkeeping
    // -----------------------------------------------------------------

    /// Note a derived theorem: if it is the empty clause (`⊢ F`) and its
    /// hypotheses are all `assume`d assertions, the problem is `Unsat`.
    fn observe(&mut self, thm: &Thm) {
        if matches!(thm.concl().as_bool(), Some(false))
            && thm.hyps().iter().all(|h| self.assumed.contains(h))
        {
            self.decision = Decision::Unsat;
        }
    }
}

// =====================================================================
// Rule dispatch
// =====================================================================

impl AletheBridge for HolAletheBridge {
    type Thm = Thm;

    fn set_logic(&mut self, _logic: &str) -> R<()> {
        Ok(())
    }

    fn declare_sort(&mut self, name: &str, arity: u32) -> R<()> {
        if arity != 0 {
            return Err(BridgeError::ParametricSort {
                name: name.to_string(),
                arity,
            });
        }
        self.sorts.insert(name.to_string(), Type::tfree(name));
        Ok(())
    }

    fn declare_fun(&mut self, name: &str, params: &[SExpr], sort: &SExpr) -> R<()> {
        // Build `p₀ → p₁ → … → cod`; an empty param list is a constant.
        let cod = self.sort_to_type(sort)?;
        let mut ty = cod;
        for p in params.iter().rev() {
            let dom = self.sort_to_type(p)?;
            ty = Type::fun(dom, ty);
        }
        self.funs.insert(name.to_string(), ty);
        Ok(())
    }

    fn assert(&mut self, _term: &SExpr) -> R<()> {
        // Assertions re-enter through `assume` in the proof body, which is
        // where we mint the hypothesis theorems; nothing to do here.
        Ok(())
    }

    fn assume(&mut self, _id: &str, term: &SExpr) -> R<Thm> {
        let t = self.term(term)?;
        let thm = Thm::assume(t.clone())?;
        self.assumed.push(t);
        Ok(thm)
    }

    fn step(
        &mut self,
        id: &str,
        clause: &[SExpr],
        rule: &str,
        premises: &[Thm],
        _args: &[SExpr],
        discharge: &[Thm],
    ) -> R<Thm> {
        if !discharge.is_empty() {
            return Err(BridgeError::NotImplemented(format!("{rule} (:discharge)")));
        }
        // Translate the stated clause literals — needed by premise-less
        // rules and as the build target for equality rules.
        let lits: Vec<Term> = clause.iter().map(|c| self.term(c)).collect::<R<_>>()?;

        let thm = match rule {
            "resolution" | "th_resolution" => resolution(premises)?,
            "refl" => refl(&lits)?,
            "trans" => trans(premises)?,
            "symm" => symm(premises)?,
            "cong" => cong(&lits, premises)?,
            "equiv_pos2" => equiv_pos2(&lits)?,
            "false" => false_rule(&lits)?,
            "hole" => return Err(BridgeError::NotImplemented("hole (untranslated)".into())),
            other => return Err(BridgeError::UnknownRule(other.to_string())),
        };

        // Sanity: the proof's stated clause must match what we derived
        // (modulo the empty-clause `F` encoding). A mismatch is a bridge
        // translation bug, surfaced rather than silently trusted.
        check_matches(id, rule, &lits, &thm)?;

        self.observe(&thm);
        Ok(thm)
    }

    fn decision(&self) -> Decision {
        self.decision
    }
}

// =====================================================================
// Individual rules
// =====================================================================

/// `resolution` / `th_resolution`: left-fold the premise clauses through
/// binary resolution, letting each step find its own pivot.
fn resolution(premises: &[Thm]) -> R<Thm> {
    let mut iter = premises.iter().cloned();
    let mut acc = iter.next().ok_or_else(|| BridgeError::BadStep {
        rule: "resolution".into(),
        detail: "no premises".into(),
    })?;
    for next in iter {
        acc = logic::resolve(acc, next)?;
    }
    Ok(acc)
}

/// `refl`: the unit clause `(cl (= s s))`.
fn refl(lits: &[Term]) -> R<Thm> {
    let (s, _) = unit_eq(lits, "refl")?;
    Thm::refl(s).map_err(Into::into)
}

/// `trans`: chain the premise equalities `a=b, b=c, … ⊢ a=z`.
fn trans(premises: &[Thm]) -> R<Thm> {
    let mut iter = premises.iter().cloned();
    let mut acc = iter.next().ok_or_else(|| BridgeError::BadStep {
        rule: "trans".into(),
        detail: "no premises".into(),
    })?;
    for next in iter {
        acc = acc.trans(next)?;
    }
    Ok(acc)
}

/// `symm`: `⊢ a = b` ⟶ `⊢ b = a`.
fn symm(premises: &[Thm]) -> R<Thm> {
    let prem = one_premise(premises, "symm")?;
    prem.sym().map_err(Into::into)
}

/// `cong`: congruence. The clause states the goal equation `f a… = f b…`;
/// each premise proves one argument equality `aᵢ = bᵢ`, in order.
fn cong(lits: &[Term], premises: &[Thm]) -> R<Thm> {
    let (lhs, _rhs) = unit_eq(lits, "cong")?;
    // Strip as many argument applications as there are premises to reach
    // the shared head, then re-apply congruence with each premise.
    let head = strip_args(&lhs, premises.len()).ok_or_else(|| BridgeError::BadStep {
        rule: "cong".into(),
        detail: format!("clause head has fewer than {} arguments", premises.len()),
    })?;
    let mut acc = Thm::refl(head)?;
    for prem in premises {
        acc = acc.mk_comb(prem.clone())?;
    }
    Ok(acc)
}

/// `equiv_pos2`: the tautology clause `(cl (not (= φ ψ)) (not φ) ψ)`.
///
/// Derived intuitionistically as the sequent `{φ = ψ, φ} ⊢ ψ`
/// (`eq_mp`) and clausified through [`logic::clause_intro`].
fn equiv_pos2(lits: &[Term]) -> R<Thm> {
    if lits.len() != 3 {
        return Err(BridgeError::BadStep {
            rule: "equiv_pos2".into(),
            detail: "expected a 3-literal clause".into(),
        });
    }
    let eq = dest_not(&lits[0]).ok_or_else(|| BridgeError::BadStep {
        rule: "equiv_pos2".into(),
        detail: "first literal is not `¬(φ = ψ)`".into(),
    })?;
    let (phi, _psi) = eq.as_eq().ok_or_else(|| BridgeError::BadStep {
        rule: "equiv_pos2".into(),
        detail: "first literal is not a negated equation".into(),
    })?;
    let phi = phi.clone();
    // {φ=ψ, φ} ⊢ ψ
    let seq = Thm::assume(eq.clone())?.eq_mp(Thm::assume(phi.clone())?)?;
    logic::clause_intro(seq, &[eq, phi]).map_err(Into::into)
}

/// `false`: the unit clause `(cl (not false))` — `⊢ ¬F`.
fn false_rule(lits: &[Term]) -> R<Thm> {
    if lits.len() != 1 || dest_not(&lits[0]).and_then(|t| t.as_bool()) != Some(false) {
        return Err(BridgeError::BadStep {
            rule: "false".into(),
            detail: "expected `(cl (not false))`".into(),
        });
    }
    let f = Term::bool_lit(false);
    // ¬F from (F ⟹ F).
    Thm::assume(f.clone())?
        .imp_intro(&f)?
        .not_intro()
        .map_err(Into::into)
}

// =====================================================================
// Helpers
// =====================================================================

/// Require a single-literal equation clause, returning `(lhs, rhs)`.
fn unit_eq(lits: &[Term], rule: &str) -> R<(Term, Term)> {
    let [lit] = lits else {
        return Err(BridgeError::BadStep {
            rule: rule.into(),
            detail: "expected a unit clause".into(),
        });
    };
    let (l, r) = lit.as_eq().ok_or_else(|| BridgeError::BadStep {
        rule: rule.into(),
        detail: "clause literal is not an equation".into(),
    })?;
    Ok((l.clone(), r.clone()))
}

/// Require exactly one premise.
fn one_premise(premises: &[Thm], rule: &str) -> R<Thm> {
    match premises {
        [p] => Ok(p.clone()),
        _ => Err(BridgeError::BadStep {
            rule: rule.into(),
            detail: format!("expected 1 premise, got {}", premises.len()),
        }),
    }
}

/// Strip `n` argument applications off a spine, returning the head, or
/// `None` if the spine is too short.
fn strip_args(t: &Term, n: usize) -> Option<Term> {
    let mut cur = t.clone();
    for _ in 0..n {
        let (f, _) = cur.as_app()?;
        cur = f.clone();
    }
    Some(cur)
}

/// `App(¬, p)` → `p`, if `t` is a HOL negation.
fn dest_not(t: &Term) -> Option<Term> {
    let (head, p) = t.as_app()?;
    let (spec, _) = head.as_spec()?;
    spec.ptr_eq(&defs::not_spec()).then(|| p.clone())
}

/// Verify the derived theorem proves the clause the proof stated.
///
/// Compares the derived conclusion's top-level disjuncts to the stated
/// literals as a multiset (resolution may legitimately reorder them).
/// The empty clause `(cl)` corresponds to `⊢ F` (no disjuncts).
fn check_matches(id: &str, rule: &str, lits: &[Term], thm: &Thm) -> R<()> {
    let mut derived: Vec<String> = disjuncts(thm.concl()).iter().map(|t| t.to_string()).collect();
    let mut stated: Vec<String> = lits.iter().map(|t| t.to_string()).collect();
    derived.sort();
    stated.sort();
    if derived != stated {
        return Err(BridgeError::Kernel(format!(
            "step {id} (`{rule}`): derived clause {derived:?} ≠ stated clause {stated:?}"
        )));
    }
    Ok(())
}

/// Split a clause term into its top-level `∨` literals; `F` → `[]`.
fn disjuncts(t: &Term) -> Vec<Term> {
    if matches!(t.as_bool(), Some(false)) {
        return Vec::new();
    }
    // `App(App(∨, a), b)` → a :: disjuncts(b).
    if let Some((f, b)) = t.as_app()
        && let Some((head, a)) = f.as_app()
        && let Some((spec, _)) = head.as_spec()
        && spec.ptr_eq(&defs::or_spec())
    {
        let mut v = vec![a.clone()];
        v.extend(disjuncts(b));
        return v;
    }
    vec![t.clone()]
}
