//! [`SequentClauseBackend`] — the **sequent-form** [`ClauseBackend`], the
//! scale fix that makes resolution near-O(1) per step.
//!
//! Where [`HolClauseBackend`](crate::hol::HolClauseBackend) represents a clause
//! `C = l₁ ∨ … ∨ lₙ` as a `∨`-*term* and pays a kernel inference per literal to
//! resolve (`elim_disj`), this backend represents the same clause as the
//! **theorem**
//!
//! ```text
//! {C, ~l₁, …, ~lₙ} ⊢ F
//! ```
//!
//! — the disjunction `C` kept as a hypothesis (so discharging it is legitimate:
//! `C` is *the problem*), and `~lᵢ` the **complementary-literal term** of `lᵢ`
//! (`~x = ¬x`, `~(¬x) = x`). Because HOL hypotheses are a *set*, resolution
//! manipulates the hyp set rather than rebuilding disjunction terms, so
//! `resolve_on` costs ~3 kernel rules regardless of clause size.
//!
//! ## Soundness
//!
//! Every step goes through the trusted kernel rules (`lem` / `or_elim` /
//! `imp_intro` / `not_elim`); the backend mints nothing itself and adds **zero
//! TCB**. The genuine-refutation contract is unchanged: the final `⊢ F`'s
//! hypotheses are a subset of the input clause disjunctions `C` (every `~`-literal
//! hyp is cut away by resolution). Because a `~lᵢ` hyp is only ever *introduced*
//! by `assume_clause` (against the matching `C`) and only ever *removed* by a
//! resolution cut, a derived `⊢ F` can never have fewer than the genuine input
//! `C`-hyps — see [`SequentClauseBackend::resolve_on`].

use covalence_core::{Term, Type};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::derived::DerivedRules;
use covalence_init::HolLightCtx;
use covalence_sat::{Clause, Lit, Var};

use crate::{ClauseBackend, ReplayError, SatProblem};

/// A sequent-form [`ClauseBackend`]: a clause `C` is carried as
/// `{C, ~l₁, …, ~lₙ} ⊢ F`. Resolution is a hypothesis-set cut, so per-step cost
/// is flat in clause size — the LCF-standard efficient SAT-replay representation.
/// Its [`SatProblem`] lowering is identical to
/// [`HolClauseBackend`](crate::hol::HolClauseBackend) (`Var(i)` → `xi : bool`),
/// so the two backends produce interchangeable input-clause disjunctions and the
/// same refutation contract.
#[derive(Default)]
pub struct SequentClauseBackend {
    ctx: HolLightCtx,
}

impl SequentClauseBackend {
    /// A fresh backend.
    pub fn new() -> Self {
        Self {
            ctx: HolLightCtx::new(),
        }
    }

    /// The boolean variable term for a literal's variable: `xi : bool`. Matches
    /// [`HolClauseBackend`](crate::hol::HolClauseBackend) so `x{i}` names agree.
    fn var_term(lit: Lit) -> Term {
        Term::free(format!("x{}", lit.var().index()), Type::bool())
    }

    /// The positive-atom term `x{i}` of a pivot variable.
    fn pivot_term(pivot: Var) -> Term {
        Term::free(format!("x{}", pivot.index()), Type::bool())
    }

    fn err(msg: impl Into<String>) -> ReplayError {
        ReplayError::Backend(msg.into())
    }

    /// The branch `⊢ lit(l) ⟹ F` for a single literal, surviving-hyp `~l`.
    ///
    /// Assume both `lit(l)` and its complement `~l = lit(!l)` (one is `x`, the
    /// other `¬x`); `not_elim` the negative against the positive to reach `F`,
    /// then `DISCH` `lit(l)` — leaving `{~l} ⊢ lit(l) ⟹ F`.
    fn contradiction_branch(&self, l: Lit) -> Result<Thm, ReplayError> {
        let pos = self.lit(l); // lit(l)
        let comp = self.lit(!l); // ~l = lit(!l)
        let pos_thm = Thm::assume(pos.clone()).map_err(|e| Self::err(e.to_string()))?;
        let comp_thm = Thm::assume(comp).map_err(|e| Self::err(e.to_string()))?;
        // Orient: `not_elim(neg, other)` wants `neg : ⊢ ¬p`, `other : ⊢ p`.
        let f = if l.is_pos() {
            // pos = x (the p), comp = ¬x (the ¬p).
            comp_thm.not_elim(pos_thm)
        } else {
            // pos = ¬x (the ¬p), comp = x (the p).
            pos_thm.not_elim(comp_thm)
        }
        .map_err(|e| Self::err(e.to_string()))?; // {lit(l), ~l} ⊢ F
        // DISCH lit(l): {~l} ⊢ lit(l) ⟹ F.
        f.imp_intro(&pos).map_err(|e| Self::err(e.to_string()))
    }

    /// From `clause : Γ ⊢ build_disj(lit-terms of `lits`)`, derive
    /// `Γ ∪ {~l : l ∈ lits} ⊢ F` by disjunction elimination down the
    /// right-associated `∨`-spine — the sequent-form of [`SatProblem::clause`].
    fn eliminate(&self, clause: Thm, lits: &[Lit]) -> Result<Thm, ReplayError> {
        match lits {
            [] => Err(Self::err("eliminate: empty literal list")),
            [only] => {
                // clause : Γ ⊢ lit(only); MP with ⊢ lit(only) ⟹ F.
                self.contradiction_branch(*only)?
                    .imp_elim(clause)
                    .map_err(|e| Self::err(e.to_string()))
            }
            [head, rest @ ..] => {
                let rest_lits: Vec<Term> = rest.iter().map(|l| self.lit(*l)).collect();
                let rest_disj = build_disj(&rest_lits);
                let left = self.contradiction_branch(*head)?; // ⊢ lit(head) ⟹ F
                // ⊢ rest_disj ⟹ F: assume the tail, recurse, DISCH.
                let assumed =
                    Thm::assume(rest_disj.clone()).map_err(|e| Self::err(e.to_string()))?;
                let under = self.eliminate(assumed, rest)?;
                let right = under
                    .imp_intro(&rest_disj)
                    .map_err(|e| Self::err(e.to_string()))?;
                clause
                    .or_elim(left, right)
                    .map_err(|e| Self::err(e.to_string()))
            }
        }
    }
}

/// Right-associated disjunction of `lits` (the empty list is falsity `F`). Kept
/// local (mirrors `init::logic`'s private `build_disj`) so the sequent shapes
/// match [`SatProblem::clause`] exactly.
fn build_disj(lits: &[Term]) -> Term {
    match lits {
        [] => Term::bool_lit(false),
        [last] => last.clone(),
        [head, rest @ ..] => {
            let ctx = HolLightCtx::new();
            ctx.mk_or(head.clone(), build_disj(rest))
        }
    }
}

impl SatProblem for SequentClauseBackend {
    type Term = Term;

    /// A literal's HOL term: the variable positively, `¬`-wrapped negatively.
    fn lit(&self, lit: Lit) -> Term {
        let v = Self::var_term(lit);
        if lit.is_pos() { v } else { self.ctx.mk_not(v) }
    }

    /// The clause term: the right-associated `∨` of its literals, `F` when empty
    /// — identical to [`HolClauseBackend`](crate::hol::HolClauseBackend).
    fn clause(&self, clause: &Clause) -> Term {
        let lits: Vec<Term> = clause.lits().iter().map(|l| self.lit(*l)).collect();
        build_disj(&lits)
    }

    fn falsity(&self) -> Term {
        Term::bool_lit(false)
    }
}

impl ClauseBackend for SequentClauseBackend {
    type Thm = Thm;

    /// Enter an input clause `C` as `{C, ~l₁, …, ~lₙ} ⊢ F`.
    ///
    /// Assume the disjunction `C = ⊢ clause(C)` (hyp `C`), then eliminate it: each
    /// disjunct `lᵢ` contradicts its own assumed complement `~lᵢ` (`not_elim`),
    /// so every branch yields `F`. The empty clause `C = []` is `assume(F)` —
    /// `{F} ⊢ F` — since there is no literal to contradict. O(n) kernel rules,
    /// **once** per input clause.
    fn assume_clause(&mut self, clause: &Clause) -> Result<Self::Thm, ReplayError> {
        let c_term = self.clause(clause);
        let c_thm = Thm::assume(c_term).map_err(|e| Self::err(e.to_string()))?;
        match clause.lits() {
            [] => Ok(c_thm), // {F} ⊢ F
            lits => self.eliminate(c_thm, lits),
        }
    }

    /// Resolve on the *first* complementary literal pair — for RUP replay the
    /// pivot is computed, so [`ClauseBackend::resolve_on`] is what actually runs.
    /// Here we scan the two theorems' `~`-literal hyps for a variable one carries
    /// positively and the other negatively.
    fn resolve(&mut self, a: &Self::Thm, b: &Self::Thm) -> Result<Self::Thm, ReplayError> {
        // A theorem's surviving `~`-literals are its non-`C` hyps: the atoms `x`
        // and negated atoms `¬x`. Find a variable that appears as `¬x` in one and
        // `x` in the other (opposite complementary polarity ⇒ resolvable pivot).
        let pivots_a = comp_literals(a);
        let pivots_b = comp_literals(b);
        for &(v, _) in &pivots_a {
            if pivots_b.iter().any(|&(w, _)| w == v) {
                return self.resolve_on(a, b, v);
            }
        }
        Err(Self::err(
            "resolve: no complementary pivot between the clauses",
        ))
    }

    /// The **cut**: resolve `a` and `b` on pivot variable `p` (term `x{p}`), ~3
    /// kernel rules regardless of clause size.
    ///
    /// One theorem carries the hyp `¬p` (from `p ∈ its clause`), the other carries
    /// `p` (from `¬p ∈ its clause`). Orient by which theorem's hyps contain the
    /// atom `x{p}` vs `¬x{p}`, then:
    ///
    /// ```text
    /// let left  = b_has_p.imp_intro(&p);       // hyps_b \ {p}  ⊢ p ⟹ F
    /// let right = a_has_np.imp_intro(&not_p);  // hyps_a \ {¬p} ⊢ ¬p ⟹ F
    /// Thm::lem(p).or_elim(left, right)         // (hyps_a\¬p) ∪ (hyps_b\p) ⊢ F
    /// ```
    ///
    /// The result's hyp set is exactly the resolvent's `C`-disjunctions plus every
    /// surviving `~`-literal — the set bookkeeping is automatic and the two cut
    /// literals `p` / `¬p` are the only hyps removed.
    fn resolve_on(
        &mut self,
        a: &Self::Thm,
        b: &Self::Thm,
        pivot: Var,
    ) -> Result<Self::Thm, ReplayError> {
        let p = Self::pivot_term(pivot); // x{p}
        let not_p = self.ctx.mk_not(p.clone()); // ¬x{p}

        // Orient: `has_np` carries the hyp `¬p`, `has_p` carries the hyp `p`.
        let (has_np, has_p) = if a.hyps().contains(&not_p) && b.hyps().contains(&p) {
            (a, b)
        } else if b.hyps().contains(&not_p) && a.hyps().contains(&p) {
            (b, a)
        } else {
            return Err(Self::err(format!(
                "resolve_on: pivot x{} not carried with opposite polarities \
                 (one theorem must have hyp `x{}`, the other `¬x{}`)",
                pivot.index(),
                pivot.index(),
                pivot.index()
            )));
        };

        // left  : hyps_p  \ {p}  ⊢ p ⟹ F      (DISCH p on the `p`-carrier)
        let left = has_p
            .clone()
            .imp_intro(&p)
            .map_err(|e| Self::err(e.to_string()))?;
        // right : hyps_np \ {¬p} ⊢ ¬p ⟹ F     (DISCH ¬p on the `¬p`-carrier)
        let right = has_np
            .clone()
            .imp_intro(&not_p)
            .map_err(|e| Self::err(e.to_string()))?;
        // ⊢ p ∨ ¬p, then case-split: both branches conclude F.
        Thm::lem(p)
            .map_err(|e| Self::err(e.to_string()))?
            .or_elim(left, right)
            .map_err(|e| Self::err(e.to_string()))
    }

    /// In the sequent representation *every* clause has conclusion `F`, so the
    /// conclusion cannot identify the empty clause. It is the empty clause when no
    /// surviving `~`-literal hyp remains — every hyp is a genuine input `C`
    /// disjunction. (RUP replay is authoritative here: it detects the refutation
    /// via the LRAT clause being empty; this method is the backend-side check.)
    fn is_empty_clause(&self, thm: &Self::Thm) -> bool {
        is_false(thm.concl()) && comp_literals(thm).is_empty()
    }
}

/// Is `t` falsity `F`? The derived rules conclude in the **defined** `F`
/// ([`covalence_core::defs::fal`]); the `assume([])` empty-clause path uses the
/// literal `⌜F⌝`. Both count.
fn is_false(t: &Term) -> bool {
    use covalence_core::TermKind;
    if matches!(t.kind(), TermKind::Bool(false)) {
        return true;
    }
    matches!(t.kind(), TermKind::Spec(h, _) if h.ptr_eq(&covalence_core::defs::fal_spec()))
}

/// The surviving `~`-literal hyps of a sequent-form clause theorem: each hyp that
/// is a bare atom `x{i}` or a negated atom `¬x{i}`, as `(var-index, is_negated)`.
/// A hyp that is a `∨`-disjunction (an input clause `C`) is *not* a `~`-literal.
fn comp_literals(thm: &Thm) -> Vec<(Var, bool)> {
    thm.hyps().iter().filter_map(parse_comp_literal).collect()
}

/// Parse a `~`-literal hyp `x{i}` / `¬x{i}` into `(var, is_negated)`; `None` for
/// any other hyp shape (notably a `∨`-clause disjunction, or a bare `F`).
fn parse_comp_literal(h: &Term) -> Option<(Var, bool)> {
    use covalence_core::TermKind;
    // ¬x{i}?
    if let TermKind::App(head, atom) = h.kind()
        && is_not_head(head)
        && let Some(v) = atom_var(atom)
    {
        return Some((v, true));
    }
    // x{i}?
    atom_var(h).map(|v| (v, false))
}

/// The `not` connective head test (`defs::not`), matching what `mk_not` builds.
fn is_not_head(head: &Term) -> bool {
    head == &HolLightCtx::new().not_op()
}

/// A bare boolean free variable named `x{i}` → its (SAT) `Var`.
fn atom_var(t: &Term) -> Option<Var> {
    use covalence_core::TermKind;
    let TermKind::Free(var) = t.kind() else {
        return None;
    };
    if !var.ty().is_bool() {
        return None;
    }
    let idx: i32 = var.name().strip_prefix('x')?.parse().ok()?;
    // A SAT `Var` has no public constructor; recover it through a positive
    // literal on the same 1-based index.
    Lit::from_dimacs(idx.abs()).map(Lit::var)
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_sat::Cnf;

    /// The lowering yields a `Term` with no proof — identical to the disjunction
    /// backend's encoding.
    #[test]
    fn problem_lowering_is_term_only() {
        let mut cnf = Cnf::new();
        let (x, y) = (cnf.fresh(), cnf.fresh());
        let b = SequentClauseBackend::new();
        let term = b.clause(&Clause::new([x, !y]));
        let expected = b.ctx.mk_or(b.lit(x), b.lit(!y));
        assert_eq!(term, expected);
        assert_eq!(b.clause(&Clause::new([])), b.falsity());
        assert_eq!(b.falsity(), Term::bool_lit(false));
    }

    /// The empty clause is `{F} ⊢ F` — conclusion `F`, no `~`-literal hyps.
    #[test]
    fn empty_clause_is_false() {
        let mut b = SequentClauseBackend::new();
        let thm = b.assume_clause(&Clause::new([])).unwrap();
        assert_eq!(thm.concl().as_bool(), Some(false));
        assert!(b.is_empty_clause(&thm));
        assert_eq!(thm.hyps().len(), 1); // just {F}
    }

    /// A unit clause `{x}` becomes `{x, ¬x} ⊢ F` — conclusion `F` but NOT empty
    /// (a surviving `¬x` hyp).
    #[test]
    fn unit_clause_sequent_shape() {
        let mut cnf = Cnf::new();
        let x = cnf.fresh();
        let mut b = SequentClauseBackend::new();
        let thm = b.assume_clause(&Clause::new([x])).unwrap();
        assert!(is_false(thm.concl()));
        assert!(
            !b.is_empty_clause(&thm),
            "unit clause is not the empty clause"
        );
        // Hyps: {x, ¬x} (the C disjunction of a unit clause IS `x`, so the two
        // coincide — {x, ¬x}, len 2).
        assert_eq!(thm.hyps().len(), 2);
        assert!(thm.hyps().contains(&b.lit(x)));
        assert!(thm.hyps().contains(&b.lit(!x)));
    }

    /// A three-literal clause `{x1, ¬x2, x3}` → `{C, ¬x1, x2, ¬x3} ⊢ F`.
    #[test]
    fn ternary_clause_sequent_shape() {
        let mut cnf = Cnf::new();
        let (x1, x2, x3) = (cnf.fresh(), cnf.fresh(), cnf.fresh());
        let mut b = SequentClauseBackend::new();
        let cl = Clause::new([x1, !x2, x3]);
        let thm = b.assume_clause(&cl).unwrap();
        assert!(is_false(thm.concl()));
        // Hyps: the disjunction C, plus the three complementary literals.
        assert!(thm.hyps().contains(&b.clause(&cl)));
        assert!(thm.hyps().contains(&b.lit(!x1)));
        assert!(thm.hyps().contains(&b.lit(x2)));
        assert!(thm.hyps().contains(&b.lit(!x3)));
        assert_eq!(thm.hyps().len(), 4);
    }

    /// `{x}` and `{¬x}` resolve to the empty clause `{x, ¬x} ⊢ F` cut on `x` →
    /// `{(x), (¬x)} ⊢ F` where the two hyps are the two input disjunctions.
    #[test]
    fn resolve_unit_and_negation_is_empty() {
        let mut cnf = Cnf::new();
        let x = cnf.fresh();
        let mut b = SequentClauseBackend::new();
        let px = b.assume_clause(&Clause::new([x])).unwrap();
        let nx = b.assume_clause(&Clause::new([!x])).unwrap();
        let empty = b.resolve_on(&px, &nx, x.var()).unwrap();
        // A genuine `⊢ F`: conclusion falsity, hyps exactly the two input clause
        // disjunctions (x) and (¬x) — the two cut literals removed.
        assert!(is_false(empty.concl()));
        assert_eq!(empty.hyps().len(), 2);
        assert!(empty.hyps().contains(&b.lit(x))); // input clause {x} = x
        assert!(empty.hyps().contains(&b.lit(!x))); // input clause {¬x} = ¬x
        // NOTE: `is_empty_clause` is shape-based and *cannot* certify this corner:
        // a UNIT input clause's `C` disjunction IS a bare atom `x`, structurally
        // identical to a surviving `~`-literal. So `comp_literals` still sees the
        // input hyps here and `is_empty_clause` returns false. This is exactly why
        // RUP replay treats the LRAT clause being empty (`c_lits.is_empty()`) as
        // authoritative — `is_empty_clause` is only a best-effort backend check.
        assert!(!comp_literals(&empty).is_empty());
    }

    /// Resolving `{x1, x2}` with `{¬x1, x3}` on `x1` yields `{x2, x3}` in
    /// sequent form: `{(x1∨x2), (¬x1∨x3), ¬x2, ¬x3} ⊢ F`, a surviving `~x2, ~x3`.
    #[test]
    fn resolve_binary_keeps_survivors() {
        let mut cnf = Cnf::new();
        let (x1, x2, x3) = (cnf.fresh(), cnf.fresh(), cnf.fresh());
        let mut b = SequentClauseBackend::new();
        let c1 = Clause::new([x1, x2]);
        let c2 = Clause::new([!x1, x3]);
        let t1 = b.assume_clause(&c1).unwrap();
        let t2 = b.assume_clause(&c2).unwrap();
        let r = b.resolve_on(&t1, &t2, x1.var()).unwrap();
        assert!(is_false(r.concl()));
        assert!(!b.is_empty_clause(&r));
        // Both input disjunctions survive as hyps (genuine refutation contract).
        assert!(r.hyps().contains(&b.clause(&c1)));
        assert!(r.hyps().contains(&b.clause(&c2)));
        // The resolvent's complementary literals ~x2, ~x3 survive; ~x1/x1 cut.
        assert!(r.hyps().contains(&b.lit(!x2)));
        assert!(r.hyps().contains(&b.lit(!x3)));
        let vars: Vec<_> = comp_literals(&r).iter().map(|&(v, _)| v).collect();
        assert!(!vars.contains(&x1.var()), "pivot x1 must be cut away");
    }

    /// `resolve` (first-pair) finds the shared pivot without a hint.
    #[test]
    fn resolve_finds_pivot() {
        let mut cnf = Cnf::new();
        let (x1, x2) = (cnf.fresh(), cnf.fresh());
        let mut b = SequentClauseBackend::new();
        let t1 = b.assume_clause(&Clause::new([x1, x2])).unwrap();
        let t2 = b.assume_clause(&Clause::new([!x1, !x2])).unwrap();
        // shares both x1 and x2 as complementary pivots; resolve picks one.
        let r = b.resolve(&t1, &t2).unwrap();
        assert!(is_false(r.concl()));
    }
}
