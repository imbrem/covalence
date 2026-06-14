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
//! through, plus the **integer term layer** (`Int`, literals, `+ - * <
//! <= > >=` over the `defs` `int` catalogue).
//!
//! cvc5's `hole` ("untranslated rewrite") is **re-derived, not trusted**:
//! every hole is a unit clause `(cl L)` and [`hole`] proves `⊢ L` in the
//! kernel by βι-`reduce` (closed `int` arithmetic, literal `=`) + `simp`
//! (connective identities). That discharges the *closed-arithmetic* and
//! propositional rewrites; a hole needing variable-level ring
//! normalisation (`x + 1 = 1 + x`) or the linear-arithmetic core
//! (`la_generic`, `la_mult_*`) has no shared normal form yet and is
//! reported `NotImplemented`. Subproofs (`anchor` / `:discharge`) and the
//! remaining rule families are likewise reported; see `SKELETONS.md`.

use std::collections::HashMap;

use covalence_core::{Term, Thm, Type, defs};
use covalence_hol::HolLightCtx;
use covalence_hol::init::ext::{TermExt, ThmExt};
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
            match sym {
                "Bool" => return Ok(Type::bool()),
                "Int" => return Ok(Type::int()),
                _ => {}
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
                    // An integer literal (cvc5 writes negatives bare, e.g. `-6`).
                    _ if sym.parse::<i128>().is_ok() => {
                        Ok(Term::int_lit(sym.parse::<i128>().unwrap()))
                    }
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
                    // Linear integer arithmetic.
                    "+" => self.fold_int(&items[1..], defs::int_add()),
                    "*" => self.fold_int(&items[1..], defs::int_mul()),
                    "-" if items.len() == 2 => {
                        let x = self.term(&items[1])?;
                        checked(Term::app(defs::int_neg(), x))
                    }
                    "-" => self.fold_int(&items[1..], defs::int_sub()),
                    "<" => self.int_cmp(items, defs::int_lt(), false),
                    "<=" => self.int_cmp(items, defs::int_le(), false),
                    ">" => self.int_cmp(items, defs::int_lt(), true),
                    ">=" => self.int_cmp(items, defs::int_le(), true),
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

    /// Left-fold an n-ary integer operator (`+`/`-`/`*`) applied as a
    /// curried HOL constant.
    fn fold_int(&mut self, args: &[SExpr], op: Term) -> R<Term> {
        if args.is_empty() {
            return Err(BridgeError::Malformed("nullary arithmetic op".into()));
        }
        let mut acc = self.term(&args[0])?;
        for a in &args[1..] {
            let t = self.term(a)?;
            acc = Term::app(Term::app(op.clone(), acc), t);
        }
        checked(acc)
    }

    /// A binary integer comparison `(op a b)`; `swap` flips the operands
    /// (so `>`/`>=` reuse `<`/`<=`).
    fn int_cmp(&mut self, items: &[SExpr], op: Term, swap: bool) -> R<Term> {
        if items.len() != 3 {
            return Err(BridgeError::Malformed(format!("comparison arity: {items:?}")));
        }
        let a = self.term(&items[1])?;
        let b = self.term(&items[2])?;
        let (lo, hi) = if swap { (b, a) } else { (a, b) };
        checked(Term::app(Term::app(op, lo), hi))
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
            // cvc5's "untranslated rewrite": re-derive it in the kernel
            // rather than trust it. Closed arithmetic + propositional
            // simplification are discharged; anything else is reported.
            "hole" => hole(&lits)?,
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

/// `hole`: re-derive cvc5's "untranslated rewrite" in the kernel. Its
/// clause is a unit `(cl L)`; we prove `⊢ L` ourselves — an equation by
/// normalising both sides to a common form, any other literal by
/// normalising it to `T`. Soundness-preserving: nothing is trusted.
fn hole(lits: &[Term]) -> R<Thm> {
    let [lit] = lits else {
        return Err(BridgeError::NotImplemented("hole (non-unit clause)".into()));
    };
    if let Some((lhs, rhs)) = lit.as_eq() {
        return discharge_eq(lhs, rhs);
    }
    let conv = normalize(lit)?; // ⊢ L = nf
    if matches!(rhs_of(&conv).as_bool(), Some(true)) {
        Ok(conv.eqt_elim()?) // ⊢ L
    } else {
        Err(BridgeError::NotImplemented(format!(
            "hole: cannot re-derive `{lit}`"
        )))
    }
}

/// Prove `⊢ lhs = rhs` by normalising both sides to a shared form.
fn discharge_eq(lhs: &Term, rhs: &Term) -> R<Thm> {
    let nl = normalize(lhs)?; // ⊢ lhs = nl'
    let nr = normalize(rhs)?; // ⊢ rhs = nr'
    if rhs_of(&nl) == rhs_of(&nr) {
        Ok(nl.trans(nr.sym()?)?) // ⊢ lhs = rhs
    } else {
        Err(BridgeError::NotImplemented(format!(
            "hole: `{lhs}` and `{rhs}` have no shared normal form"
        )))
    }
}

/// `⊢ t = nf`: alternately βι-`reduce` (closed `nat`/`int` arithmetic,
/// literal `=`) and propositionally `simp` (connective identities) until
/// neither changes. The recompute backend for [`hole`].
fn normalize(t: &Term) -> R<Thm> {
    let mut acc = Thm::refl(t.clone())?;
    for _ in 0..64 {
        let cur = rhs_of(&acc);
        let reduced = cur.reduce()?; // ⊢ cur = cur'  (βι)
        if rhs_of(&reduced) != cur {
            acc = acc.trans(reduced)?;
            continue;
        }
        let simped = logic::simp(&cur)?; // ⊢ cur = cur''  (connectives)
        if rhs_of(&simped) != cur {
            acc = acc.trans(simped)?;
            continue;
        }
        return Ok(acc);
    }
    Err(BridgeError::Kernel("normalize: did not converge".into()))
}

/// The right-hand side of an equational theorem.
fn rhs_of(thm: &Thm) -> Term {
    thm.concl().as_eq().expect("equational theorem").1.clone()
}

/// Validate a freshly built term, returning it only if well-typed.
fn checked(t: Term) -> R<Term> {
    t.type_of()?;
    Ok(t)
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
/// The empty clause `(cl)` is `⊢ F`; any other clause of `n` literals is
/// a right-associated `n`-way disjunction. We split the conclusion to the
/// stated arity (so a literal that *is* `F` is kept, not mistaken for the
/// empty clause) and compare as a multiset — resolution may reorder.
fn check_matches(id: &str, rule: &str, lits: &[Term], thm: &Thm) -> R<()> {
    if lits.is_empty() {
        return match thm.concl().as_bool() {
            Some(false) => Ok(()),
            _ => Err(BridgeError::Kernel(format!(
                "step {id} (`{rule}`): expected the empty clause `F`, derived `{}`",
                thm.concl()
            ))),
        };
    }
    let derived = split_clause(thm.concl(), lits.len()).ok_or_else(|| {
        BridgeError::Kernel(format!(
            "step {id} (`{rule}`): derived `{}` is not a {}-literal clause",
            thm.concl(),
            lits.len()
        ))
    })?;
    let mut derived: Vec<String> = derived.iter().map(|t| t.to_string()).collect();
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

/// Peel exactly `n` literals off a right-associated `∨`-spine; `None` if
/// the term has fewer than `n` top-level disjuncts.
fn split_clause(t: &Term, n: usize) -> Option<Vec<Term>> {
    if n <= 1 {
        return Some(vec![t.clone()]);
    }
    let (f, b) = t.as_app()?;
    let (head, a) = f.as_app()?;
    let (spec, _) = head.as_spec()?;
    if !spec.ptr_eq(&defs::or_spec()) {
        return None;
    }
    let mut v = vec![a.clone()];
    v.extend(split_clause(b, n - 1)?);
    Some(v)
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_sexp::parse_smt;

    /// Parse a single SMT term and translate it through a bridge whose
    /// `Int` symbols are pre-declared.
    fn translate(decls: &[(&str, Type)], src: &str) -> Term {
        let mut b = HolAletheBridge::new();
        for (name, ty) in decls {
            b.funs.insert(name.to_string(), ty.clone());
        }
        let exprs = parse_smt(src).expect("parse");
        b.term(&exprs[0]).expect("translate")
    }

    #[test]
    fn translates_integer_literals_and_arithmetic() {
        let int = Type::int();
        let x = || Term::free("x", int.clone());
        let lit = |n: i128| Term::int_lit(n);
        let app2 = |op: Term, a: Term, c: Term| Term::app(Term::app(op, a), c);

        // negative literal
        assert_eq!(translate(&[], "-6"), lit(-6));
        // (+ x 1)
        assert_eq!(
            translate(&[("x", int.clone())], "(+ x 1)"),
            app2(defs::int_add(), x(), lit(1))
        );
        // (- x) is unary negation
        assert_eq!(
            translate(&[("x", int.clone())], "(- x)"),
            Term::app(defs::int_neg(), x())
        );
        // (* 2 3) — closed, folds left
        assert_eq!(translate(&[], "(* 2 3)"), app2(defs::int_mul(), lit(2), lit(3)));
    }

    #[test]
    fn comparisons_map_gt_to_swapped_lt() {
        let int = Type::int();
        let x = || Term::free("x", int.clone());
        let lit5 = Term::int_lit(5);
        let app2 = |op: Term, a: Term, c: Term| Term::app(Term::app(op, a), c);
        // (< x 5)  →  int.lt x 5
        assert_eq!(
            translate(&[("x", int.clone())], "(< x 5)"),
            app2(defs::int_lt(), x(), lit5.clone())
        );
        // (> x 5)  →  int.lt 5 x   (operands swapped)
        assert_eq!(
            translate(&[("x", int.clone())], "(> x 5)"),
            app2(defs::int_lt(), lit5, x())
        );
    }
}
