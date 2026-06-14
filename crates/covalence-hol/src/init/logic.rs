//! The propositional connectives: the `defs/logic.rs` *definitions*
//! re-exported, plus the *proved* properties the kernel deliberately
//! omits.
//!
//! `covalence_core::defs::logic` only **defines** `∧ ∨ ¬ ⟹ ⟺ ∀ ∃`
//! (each as a `TermSpec` body); the kernel-separation discipline
//! forbids it from proving anything. This is where the expected facts
//! — `⊢ T`, commutativity of `∧` / `∨`, … — get **derived**, using the
//! high-level [`TermExt`] / [`ThmExt`] API so the proofs survive churn
//! in `covalence-core`.
//!
//! The intro / elim rules themselves are already kernel primitives
//! ([`Thm::and_intro`], [`Thm::or_elim`], …) — call them directly. The
//! derived *rules* here ([`and_sym`], [`or_sym`]) return [`Result`] and
//! thread errors with `?`. The closed *theorems* ([`truth`],
//! [`and_comm`], [`or_comm`]) are `init` proofs: they return [`Thm`]
//! and `expect` on failure, since a failure is a build-time bug. See
//! [`crate::proofs::bool`] for the *derivations* witnessing the
//! connective primitives' soundness.

pub use covalence_core::defs::{
    and, and_spec, exists, exists_spec, forall, forall_spec, iff, iff_spec, imp, imp_spec, not,
    not_spec, or, or_spec,
};

use covalence_core::{Error, Result, Term, Thm, Type};

use crate::init::ext::{TermExt, ThmExt};

// ============================================================================
// Truth
// ============================================================================

/// `⊢ T`. Derived (no postulate): [`Thm::reduce_prim`] decides
/// `(T = T) = T` on the closed literals, and `refl T : ⊢ T = T`
/// discharges the antecedent via [`Thm::eq_mp`].
pub fn truth() -> Thm {
    let t = Term::bool_lit(true);
    let refl_t = Thm::refl(t).expect("truth: refl T");
    let t_eq_t = refl_t.concl().clone();
    let reduced = Thm::reduce_prim(t_eq_t).expect("truth: reduce_prim (T=T)");
    reduced.eq_mp(refl_t).expect("truth: eq_mp")
}

// ============================================================================
// Conjunction
// ============================================================================

/// `⊢ p ∧ q` → `⊢ q ∧ p`. The hypotheses of the input carry through.
pub fn and_sym(pq: Thm) -> Result<Thm> {
    let (p, q) = pq.conjuncts()?;
    q.and_intro(p)
}

/// `⊢ (p ∧ q) ⟹ (q ∧ p)` for free `p`, `q : bool` — commutativity of
/// `∧` as a closed, hypothesis-free theorem. Assume `p ∧ q`, swap with
/// [`and_sym`], discharge.
pub fn and_comm() -> Thm {
    let p = Term::free("p", Type::bool());
    let q = Term::free("q", Type::bool());
    let pq = p.and(q).expect("and_comm: build p ∧ q");
    let assumed = Thm::assume(pq.clone()).expect("and_comm: assume p ∧ q");
    and_sym(assumed)
        .and_then(|swapped| swapped.imp_intro(&pq))
        .expect("and_comm: discharge into (p∧q) ⟹ (q∧p)")
}

// ============================================================================
// Disjunction
// ============================================================================

/// `⊢ p ∨ q` → `⊢ q ∨ p`. The hypotheses of the input carry through.
///
/// Eliminate the disjunction into the goal `q ∨ p`: the `p` branch
/// re-injects on the right ([`Thm::or_intro_r`]), the `q` branch on the
/// left ([`Thm::or_intro_l`]).
pub fn or_sym(pq: Thm) -> Result<Thm> {
    let (p, q) = parse_or(pq.concl()).ok_or_else(|| {
        Error::ConnectiveRule(format!("or_sym: conclusion is not `p ∨ q`: {}", pq.concl()))
    })?;
    let left = Thm::assume(p.clone())?.or_intro_r(q.clone())?.imp_intro(&p)?;
    let right = Thm::assume(q.clone())?.or_intro_l(p.clone())?.imp_intro(&q)?;
    pq.or_elim(left, right)
}

/// `⊢ (p ∨ q) ⟹ (q ∨ p)` for free `p`, `q : bool` — commutativity of
/// `∨` as a closed, hypothesis-free theorem.
pub fn or_comm() -> Thm {
    let p = Term::free("p", Type::bool());
    let q = Term::free("q", Type::bool());
    let pq = p.or(q).expect("or_comm: build p ∨ q");
    let assumed = Thm::assume(pq.clone()).expect("or_comm: assume p ∨ q");
    or_sym(assumed)
        .and_then(|swapped| swapped.imp_intro(&pq))
        .expect("or_comm: discharge into (p∨q) ⟹ (q∨p)")
}

/// Parse `App(App(\/, p), q)` → `(p, q)`. Returns `None` unless the
/// head is the `or` connective spec. Uses the [`Term`] structural
/// accessors rather than matching `TermKind`.
fn parse_or(t: &Term) -> Option<(Term, Term)> {
    let (f, q) = t.as_app()?;
    let (head, p) = f.as_app()?;
    let (spec, _) = head.as_spec()?;
    spec.ptr_eq(&or_spec()).then(|| (p.clone(), q.clone()))
}

/// Parse `App(¬, p)` → `p`. Returns `None` unless the head is the `not`
/// connective spec.
fn parse_not(t: &Term) -> Option<Term> {
    let (head, p) = t.as_app()?;
    let (spec, _) = head.as_spec()?;
    spec.ptr_eq(&not_spec()).then(|| p.clone())
}

// ============================================================================
// Clause reasoning — resolution and clausification
// ============================================================================
//
// A *clause* here is a `bool`-typed term read as a right-associated
// disjunction of *literals* — `l₀ ∨ (l₁ ∨ … ∨ lₙ)` — with the empty
// clause being `F`. This is the propositional skeleton an SMT proof
// format (Alethe, DRAT, …) manipulates: `resolve` is binary
// resolution, `clause_intro` turns a sequent into a clause by pushing
// hypotheses across as negated literals.
//
// ⚠️ **Naive split.** The helpers below split a clause into literals by
// fully walking its `∨`-spine, so a literal that is *itself* `∨`-headed
// (e.g. the clause `(l₀ ∨ l₁) ∨ l₂` meaning the two literals
// `[l₀ ∨ l₁, l₂]`) is over-split. Callers that build clauses out of
// disjunctive literals must track the literal boundaries themselves and
// drive [`resolve_on`] with explicit pivots. For the propositional /
// equality-literal fragment (atoms, negations, equations) the split is
// exact.

/// Build the right-associated disjunction of `lits`; the empty list
/// yields `F` (the empty clause). Always returns a `bool`-typed term
/// when the literals are `bool`-typed.
fn build_disj(lits: &[Term]) -> Result<Term> {
    match lits {
        [] => Ok(Term::bool_lit(false)),
        [last] => Ok(last.clone()),
        [head, rest @ ..] => head.clone().or(build_disj(rest)?),
    }
}

/// Split a clause into its literals by fully walking the `∨`-spine
/// (see the module-level ⚠️ note on naive splitting). `F` (the empty
/// clause) splits to `[]`.
fn disjuncts(t: &Term) -> Vec<Term> {
    if matches!(t.as_bool(), Some(false)) {
        return Vec::new();
    }
    match parse_or(t) {
        Some((a, b)) => {
            let mut v = vec![a];
            v.extend(disjuncts(&b));
            v
        }
        None => vec![t.clone()],
    }
}

/// The literal complementary to `l`: `¬x` for a positive `l = x`, and
/// `x` for a negative `l = ¬x`.
fn complement(l: &Term) -> Result<Term> {
    match parse_not(l) {
        Some(inner) => Ok(inner),
        None => l.clone().not(),
    }
}

/// `⊢ build_disj(target)` from `⊢ l` where `l == target[idx]`, by
/// `or_intro` chaining along the right-associated disjunction.
fn inject(lit: Thm, target: &[Term], idx: usize) -> Result<Thm> {
    if idx == 0 {
        if target.len() == 1 {
            return Ok(lit); // the clause is exactly its single literal
        }
        return lit.or_intro_l(build_disj(&target[1..])?);
    }
    let rest = inject(lit, &target[1..], idx - 1)?;
    rest.or_intro_r(target[0].clone())
}

/// Eliminate a disjunction-form clause into a single `goal`.
///
/// Given `clause : Γ ⊢ build_disj(lits)` and a `branch` builder that,
/// for each literal `l`, returns `Δ_l ⊢ l ⟹ goal`, returns
/// `Γ ∪ ⋃ Δ_l ⊢ goal`. The recursion mirrors the right-associated
/// `∨`-spine: peel the head literal, recurse under the assumed tail.
fn elim_disj(
    clause: Thm,
    lits: &[Term],
    goal: &Term,
    branch: &impl Fn(&Term) -> Result<Thm>,
) -> Result<Thm> {
    match lits {
        [] => Err(Error::ConnectiveRule("elim_disj: empty clause".into())),
        [only] => {
            // `clause : Γ ⊢ only`; modus ponens with `⊢ only ⟹ goal`.
            branch(only)?.imp_elim(clause)
        }
        [head, rest @ ..] => {
            let rest_disj = build_disj(rest)?;
            let left = branch(head)?; // ⊢ head ⟹ goal
            // ⊢ rest_disj ⟹ goal: assume the tail, recurse, discharge.
            let assumed = Thm::assume(rest_disj.clone())?;
            let under = elim_disj(assumed, rest, goal, branch)?;
            let right = under.imp_intro(&rest_disj)?;
            clause.or_elim(left, right)
        }
    }
}

/// Binary propositional resolution with an explicit pivot.
///
/// `left : Γ ⊢ C₁` and `right : Δ ⊢ C₂` are disjunction-form clauses
/// (see the module ⚠️ note). `pivot` is the *positive* resolved atom: it
/// must be a top-level disjunct of one clause and its negation `¬pivot`
/// a top-level disjunct of the other. Returns `Γ ∪ Δ ⊢ R`, where the
/// resolvent `R` is the disjunction of every remaining literal —
/// `(C₁ without pivot) ++ (C₂ without ¬pivot)` — and is `F` (the empty
/// clause) when nothing remains. Every occurrence of the pivot literal
/// is dropped from each side. Errors if the pivot/negation are not
/// present with opposite polarities.
pub fn resolve_on(left: Thm, right: Thm, pivot: &Term) -> Result<Thm> {
    let not_pivot = pivot.clone().not()?;
    let left_lits = disjuncts(left.concl());
    let right_lits = disjuncts(right.concl());

    // Orient: `cp` carries the pivot positively, `cn` carries ¬pivot.
    let (cp, pl, cn, nl) = if left_lits.contains(pivot) && right_lits.contains(&not_pivot) {
        (left, left_lits, right, right_lits)
    } else if right_lits.contains(pivot) && left_lits.contains(&not_pivot) {
        (right, right_lits, left, left_lits)
    } else {
        return Err(Error::ConnectiveRule(format!(
            "resolve_on: pivot `{pivot}` / `¬{pivot}` not present with opposite polarities"
        )));
    };

    let resolvent: Vec<Term> = pl
        .iter()
        .filter(|l| *l != pivot)
        .chain(nl.iter().filter(|m| *m != &not_pivot))
        .cloned()
        .collect();
    let goal = build_disj(&resolvent)?;

    // Pivot side: each literal `l` becomes `⊢ l ⟹ goal`. A non-pivot
    // literal re-injects into the resolvent; the pivot literal opens the
    // ¬pivot clause under an in-scope `⊢ pivot`.
    let p_branch = |l: &Term| -> Result<Thm> {
        if l == pivot {
            let p_assumed = Thm::assume(pivot.clone())?; // {pivot} ⊢ pivot
            let n_branch = |m: &Term| n_branch(m, &not_pivot, &p_assumed, &goal, &resolvent);
            let under = elim_disj(cn.clone(), &nl, &goal, &n_branch)?;
            under.imp_intro(pivot) // cn.hyps ⊢ pivot ⟹ goal
        } else {
            lit_branch(l, &resolvent)
        }
    };

    elim_disj(cp, &pl, &goal, &p_branch)
}

/// `⊢ l ⟹ build_disj(resolvent)` for a surviving literal `l`: assume
/// it and re-inject it into the resolvent.
fn lit_branch(l: &Term, resolvent: &[Term]) -> Result<Thm> {
    let idx = resolvent
        .iter()
        .position(|r| r == l)
        .ok_or_else(|| Error::ConnectiveRule("resolve: literal absent from resolvent".into()))?;
    inject(Thm::assume(l.clone())?, resolvent, idx)?.imp_intro(l)
}

/// `⊢ m ⟹ goal` for a literal of the ¬pivot clause, with `⊢ pivot`
/// in scope. The matching `¬pivot` literal contradicts it (ex falso);
/// any other literal re-injects into the resolvent.
fn n_branch(
    m: &Term,
    not_pivot: &Term,
    p_assumed: &Thm,
    goal: &Term,
    resolvent: &[Term],
) -> Result<Thm> {
    if m == not_pivot {
        let f = Thm::assume(not_pivot.clone())?.not_elim(p_assumed.clone())?;
        f.false_elim(goal.clone())?.imp_intro(not_pivot)
    } else {
        lit_branch(m, resolvent)
    }
}

/// Binary propositional resolution that finds the pivot itself.
///
/// Scans the top-level literals of `left` and `right` for the first
/// complementary pair `(l, ¬l)` and resolves on it via [`resolve_on`].
/// The convenience entry point for chained resolution (fold a premise
/// list through it). Errors if the clauses share no complementary
/// literal.
pub fn resolve(left: Thm, right: Thm) -> Result<Thm> {
    let left_lits = disjuncts(left.concl());
    let right_lits = disjuncts(right.concl());
    for l in &left_lits {
        let comp = complement(l)?;
        if right_lits.contains(&comp) {
            // Pivot is the positive form of the complementary pair.
            let pivot = match parse_not(l) {
                Some(inner) => inner, // l = ¬inner ; pivot = inner
                None => l.clone(),    // l positive ; pivot = l
            };
            return resolve_on(left, right, &pivot);
        }
    }
    Err(Error::ConnectiveRule(
        "resolve: clauses share no complementary literal".into(),
    ))
}

/// Push hypotheses into a clause as negated literals (clausification).
///
/// Given `thm : Γ ∪ {h₀, …, hₖ₋₁} ⊢ c` and the list `[h₀, …, hₖ₋₁]`,
/// returns `Γ ⊢ ¬h₀ ∨ ¬h₁ ∨ … ∨ ¬hₖ₋₁ ∨ c`. This is the classical
/// "deduction ⟹ clause" move: each step trades a hypothesis for a
/// negated disjunct, justified by [`Thm::lem`] on that hypothesis. It is
/// what turns an intuitionistically-derived sequent (e.g. modus ponens
/// `{p ⟺ q, p} ⊢ q`) into the disjunctive clause an SMT format states
/// (`⊢ ¬(p ⟺ q) ∨ ¬p ∨ q`). Hypotheses are discharged in the given
/// order, so `h₀` ends up the outermost disjunct.
pub fn clause_intro(thm: Thm, hyps: &[Term]) -> Result<Thm> {
    let mut acc = thm;
    for h in hyps.iter().rev() {
        acc = disch_one(acc, h)?;
    }
    Ok(acc)
}

/// One clausification step: `Δ ∪ {h} ⊢ tail` → `Δ ⊢ ¬h ∨ tail`.
fn disch_one(thm: Thm, h: &Term) -> Result<Thm> {
    let tail = thm.concl().clone();
    let nh = h.clone().not()?;
    // h ⟹ (¬h ∨ tail): inject `tail` on the right, discharge h.
    let branch_h = thm.or_intro_r(nh.clone())?.imp_intro(h)?;
    // ¬h ⟹ (¬h ∨ tail): assume ¬h, inject on the left, discharge.
    let branch_nh = Thm::assume(nh.clone())?.or_intro_l(tail)?.imp_intro(&nh)?;
    Thm::lem(h.clone())?.or_elim(branch_h, branch_nh)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn truth_is_axiom_free() {
        let t = truth();
        assert!(t.hyps().is_empty(), "TRUTH must be axiom-free");
        assert_eq!(t.concl(), &Term::bool_lit(true));
    }

    #[test]
    fn and_comm_is_an_axiom_free_implication() {
        let thm = and_comm();
        assert!(thm.hyps().is_empty(), "and_comm must be axiom-free");
        assert!(thm.has_no_obs(), "and_comm must be oracle-free");
        let p = Term::free("p", Type::bool());
        let q = Term::free("q", Type::bool());
        let expected = p.clone().and(q.clone()).unwrap().imp(q.and(p).unwrap()).unwrap();
        assert_eq!(thm.concl(), &expected);
    }

    #[test]
    fn or_comm_is_an_axiom_free_implication() {
        let thm = or_comm();
        assert!(thm.hyps().is_empty(), "or_comm must be axiom-free");
        assert!(thm.has_no_obs(), "or_comm must be oracle-free");
        let p = Term::free("p", Type::bool());
        let q = Term::free("q", Type::bool());
        let expected = p.clone().or(q.clone()).unwrap().imp(q.or(p).unwrap()).unwrap();
        assert_eq!(thm.concl(), &expected);
    }

    fn b() -> Type {
        Type::bool()
    }

    #[test]
    fn resolve_unit_clauses_to_empty() {
        // {a} ⊢ a  and  {¬a} ⊢ ¬a   resolve to   {a, ¬a} ⊢ F.
        let a = Term::free("a", b());
        let pos = Thm::assume(a.clone()).unwrap();
        let neg = Thm::assume(a.clone().not().unwrap()).unwrap();
        let res = resolve(pos, neg).unwrap();
        assert_eq!(res.concl(), &Term::bool_lit(false), "empty clause is F");
        assert_eq!(res.hyps().len(), 2);
    }

    #[test]
    fn resolve_drops_pivot_keeps_rest() {
        // {¬a ∨ b} ⊢ ¬a ∨ b   and   {a} ⊢ a   resolve on `a` to ⊢ b.
        let a = Term::free("a", b());
        let bb = Term::free("b", b());
        let clause = a.clone().not().unwrap().or(bb.clone()).unwrap();
        let left = Thm::assume(clause).unwrap();
        let right = Thm::assume(a.clone()).unwrap();
        let res = resolve(left, right).unwrap();
        assert_eq!(res.concl(), &bb);
    }

    #[test]
    fn resolve_three_way_chain() {
        // The UF1 shape: (¬e ∨ ¬a ∨ c), e, a  ⟶  c.
        let a = Term::free("a", b());
        let c = Term::free("c", b());
        let e = Term::free("e", b());
        let t0 = Thm::assume(
            e.clone()
                .not()
                .unwrap()
                .or(a.clone().not().unwrap().or(c.clone()).unwrap())
                .unwrap(),
        )
        .unwrap();
        let t1 = Thm::assume(e).unwrap();
        let a1 = Thm::assume(a).unwrap();
        let step = resolve(resolve(t0, t1).unwrap(), a1).unwrap();
        assert_eq!(step.concl(), &c);
    }

    #[test]
    fn clause_intro_excluded_middle() {
        // clause_intro({a} ⊢ a, [a])  =  ⊢ ¬a ∨ a.
        let a = Term::free("a", b());
        let cl = clause_intro(Thm::assume(a.clone()).unwrap(), &[a.clone()]).unwrap();
        assert!(cl.hyps().is_empty(), "the only hyp was clausified away");
        let expected = a.clone().not().unwrap().or(a).unwrap();
        assert_eq!(cl.concl(), &expected);
    }

    #[test]
    fn clause_intro_equiv_pos2_shape() {
        // The equiv_pos2 tautology, built as `{p⟺q, p} ⊢ q` then clausified:
        // ⊢ ¬(p = q) ∨ ¬p ∨ q.   (`=` at bool is `⟺`.)
        let p = Term::free("p", b());
        let q = Term::free("q", b());
        let eq = p.clone().equals(q.clone()).unwrap();
        // {p=q, p} ⊢ q   via eq_mp.
        let seq = Thm::assume(eq.clone())
            .unwrap()
            .eq_mp(Thm::assume(p.clone()).unwrap())
            .unwrap();
        let cl = clause_intro(seq, &[eq.clone(), p.clone()]).unwrap();
        assert!(cl.hyps().is_empty());
        let expected = eq
            .not()
            .unwrap()
            .or(p.not().unwrap().or(q).unwrap())
            .unwrap();
        assert_eq!(cl.concl(), &expected);
    }

    #[test]
    fn and_sym_swaps_a_conjunction() {
        let p = Thm::assume(Term::bool_lit(true)).unwrap();
        let q = Thm::assume(Term::bool_lit(false)).unwrap();
        let conj = p.and_intro(q).unwrap(); // ⊢ T ∧ F (with hyps)
        let swapped = and_sym(conj).unwrap();
        // Now `F ∧ T`.
        let (f, r) = swapped.concl().as_app().unwrap();
        let (_head, l) = f.as_app().unwrap();
        assert_eq!(l, &Term::bool_lit(false));
        assert_eq!(r, &Term::bool_lit(true));
    }
}
