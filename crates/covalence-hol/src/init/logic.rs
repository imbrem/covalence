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
//!
//! On top of that sit the **classical** procedures, all powered by
//! [`Thm::lem`]:
//!
//! - clause reasoning — [`resolve`] / [`resolve_on`] (binary
//!   resolution), [`clause_intro`] / [`clause_intro_neg`]
//!   (sequent → clause), and [`dne`] (double-negation elimination);
//! - propositional simplification — [`simp`] (a normalising `⊢ t = t'`
//!   conversion over the connective identities, the analogue of
//!   [`eq::beta_nf`](crate::init::eq::beta_nf)), with [`tauto`] and
//!   [`decide`] deciding trivial (anti)tautologies on top of it.

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
/// (see the module-level ⚠️ note on naive splitting). `F` is treated as
/// an ordinary literal here — the *empty* clause is `build_disj(&[])`,
/// also `F`, so the two coincide structurally; callers that must tell a
/// unit `(cl false)` from the empty `(cl)` track arity separately.
fn disjuncts(t: &Term) -> Vec<Term> {
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

/// Push *negated* hypotheses into a clause as positive literals.
///
/// The polarity-flipped companion to [`clause_intro`]: given
/// `thm : Γ ∪ {¬a₀, …, ¬aₖ₋₁} ⊢ c` and the list of *atoms*
/// `[a₀, …, aₖ₋₁]`, returns `Γ ⊢ a₀ ∨ a₁ ∨ … ∨ aₖ₋₁ ∨ c`. Where
/// [`clause_intro`] trades a hypothesis `h` for the literal `¬h`, this
/// trades a hypothesis `¬a` for the literal `a` — handy when the sequent
/// was derived under negated assumptions (e.g. case analysis) and the
/// clause should state them positively.
pub fn clause_intro_neg(thm: Thm, atoms: &[Term]) -> Result<Thm> {
    let mut acc = thm;
    for a in atoms.iter().rev() {
        acc = disch_neg(acc, a)?;
    }
    Ok(acc)
}

/// One negated-clausification step: `Δ ∪ {¬a} ⊢ tail` → `Δ ⊢ a ∨ tail`.
fn disch_neg(thm: Thm, a: &Term) -> Result<Thm> {
    let tail = thm.concl().clone();
    let na = a.clone().not()?;
    // a ⟹ (a ∨ tail): assume a, inject on the left, discharge.
    let branch_a = Thm::assume(a.clone())?.or_intro_l(tail.clone())?.imp_intro(a)?;
    // ¬a ⟹ (a ∨ tail): inject `tail` on the right, discharge ¬a.
    let branch_na = thm.or_intro_r(a.clone())?.imp_intro(&na)?;
    Thm::lem(a.clone())?.or_elim(branch_a, branch_na)
}

// ============================================================================
// Double-negation elimination
// ============================================================================

/// `Δ ⊢ ¬¬p` → `Δ ⊢ p` — double-negation elimination.
///
/// The classical step the kernel's intuitionistic `not_intro`/`not_elim`
/// can't reach on their own. Case-split on [`Thm::lem`] of `p`: the `p`
/// branch is immediate, the `¬p` branch contradicts the premise and uses
/// ex falso.
pub fn dne(thm: Thm) -> Result<Thm> {
    let nnp = thm.concl().clone();
    let np = parse_not(&nnp)
        .ok_or_else(|| Error::ConnectiveRule(format!("dne: `{nnp}` is not a negation")))?;
    let p = parse_not(&np)
        .ok_or_else(|| Error::ConnectiveRule(format!("dne: `{nnp}` is not a double negation")))?;
    let branch_p = Thm::assume(p.clone())?.imp_intro(&p)?; // ⊢ p ⟹ p
    // ¬p ⟹ p : ¬¬p with ¬p is absurd, ex falso to p.
    let contra = thm.not_elim(Thm::assume(np.clone())?)?; // Δ, {¬p} ⊢ F
    let branch_np = contra.false_elim(p.clone())?.imp_intro(&np)?;
    Thm::lem(p.clone())?.or_elim(branch_p, branch_np)
}

// ============================================================================
// Logical simplification — a propositional rewriting conversion
// ============================================================================
//
// `simp` is to the connectives what `eq::beta_nf` is to β: a normalising
// conversion returning `⊢ t = t'`. It descends the term (congruence on
// every `App`), then fires a local simplification at each node and keeps
// going to a fixpoint. Every local step is a closed equivalence proved on
// the spot with `deduct_antisym`, so the result is a genuine kernel
// theorem — no rewrite is trusted.
//
// Covered identities (and their mirrors): `p∧p=p`, `p∨p=p`, `p∧T=p`,
// `T∧p=p`, `p∨F=p`, `F∨p=p`, `p∧F=F`, `F∧p=F`, `p∨T=T`, `T∨p=T`,
// `p∧¬p=F`, `p∨¬p=T`, `¬T=F`, `¬F=T`, `¬¬p=p`, the implication forms
// `F⟹p=T`, `p⟹T=T`, `T⟹p=p`, `p⟹F=¬p`, `p⟹p=T`, and — since `⟺`
// is `λp q. p = q` — the `bool`-equality / biconditional forms `(p=p)=T`,
// `(p=T)=p`, `(T=p)=p`, `(p=F)=¬p`, `(F=p)=¬p`, `(p=¬p)=F`. A
// biconditional that matches one of those is unfolded to the primitive
// equation and simplified on the next pass; a contingent `⟺` is left as
// the unfolded `=` (its definitional form).

/// `⊢ t = t'`, the propositional **simplification** of `t`: every
/// connective identity above is applied, repeatedly and under congruence,
/// until none fires. Leaves non-`bool` and non-connective structure
/// untouched (and never descends under a binder). The result equation has
/// the same hypotheses as the input (none, for a closed `t`).
pub fn simp(t: &Term) -> Result<Thm> {
    simp_conv(t)
}

/// `⊢ p`, if `p` is a **trivial tautology** — i.e. [`simp`] reduces it to
/// `T`. Errors otherwise (the theorem is left unproven). The propositional
/// analogue of [`TermExt::prove_true`](crate::init::ext::TermExt::prove_true),
/// which decides by βι-evaluation rather than connective simplification.
pub fn tauto(p: &Term) -> Result<Thm> {
    let eq = simp(p)?; // ⊢ p = p'
    let rhs = eq.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone();
    if matches!(rhs.as_bool(), Some(true)) {
        eq.eqt_elim() // ⊢ p
    } else {
        Err(Error::ConnectiveRule(format!(
            "tauto: `{p}` simplifies to `{rhs}`, not `T`"
        )))
    }
}

/// Prove `p` *or* `¬p`, whichever is a trivial tautology (see [`tauto`]).
///
/// Returns `⊢ p` when `p` simplifies to `T`, else `⊢ ¬p` when `¬p` does,
/// else an error — a one-sided decision procedure for the fragment [`simp`]
/// normalises. Inspect the returned theorem's conclusion to learn which
/// way it went.
pub fn decide(p: &Term) -> Result<Thm> {
    if let Ok(thm) = tauto(p) {
        return Ok(thm);
    }
    let np = p.clone().not()?;
    tauto(&np).map_err(|_| {
        Error::ConnectiveRule(format!("decide: neither `{p}` nor its negation is a trivial tautology"))
    })
}

/// The normalising conversion behind [`simp`]: congruence-descend, then
/// fire a local rule and recurse to a fixpoint.
fn simp_conv(t: &Term) -> Result<Thm> {
    let cong = if let Some((f, x)) = t.as_app() {
        let f_eq = simp_conv(f)?;
        let x_eq = simp_conv(x)?;
        f_eq.cong_app(x_eq)? // ⊢ t = f' x'
    } else {
        Thm::refl(t.clone())?
    };
    let t1 = cong.concl().as_eq().expect("cong yields an equation").1.clone();
    if let Some(step) = simp_at(&t1)? {
        let t2 = step.concl().as_eq().expect("simp step yields an equation").1.clone();
        let rest = simp_conv(&t2)?;
        return cong.trans(step)?.trans(rest);
    }
    Ok(cong)
}

/// Fire a single local simplification at `node`, returning `⊢ node = rhs`
/// if any identity applies.
fn simp_at(node: &Term) -> Result<Option<Thm>> {
    if let Some(x) = parse_not(node) {
        return not_simp(&x);
    }
    // Primitive `=` at `bool` — `(=)` and `⟺` coincide, so this also
    // catches what `iff` unfolds to.
    if let Some((a, b)) = node.as_eq()
        && a.type_of().map(|t| t.is_bool()).unwrap_or(false)
    {
        return eq_simp(&a.clone(), &b.clone());
    }
    if let Some((spec, a, b)) = parse_binop(node) {
        if spec.ptr_eq(&and_spec()) {
            return and_simp(&a, &b);
        }
        if spec.ptr_eq(&or_spec()) {
            return or_simp(&a, &b);
        }
        if spec.ptr_eq(&imp_spec()) {
            return imp_simp(&a, &b);
        }
        if spec.ptr_eq(&iff_spec()) {
            return iff_simp(&a, &b);
        }
    }
    Ok(None)
}

// -- the `T`/`F` literals --
fn tt() -> Term {
    Term::bool_lit(true)
}
fn ff() -> Term {
    Term::bool_lit(false)
}
fn is_t(t: &Term) -> bool {
    matches!(t.as_bool(), Some(true))
}
fn is_f(t: &Term) -> bool {
    matches!(t.as_bool(), Some(false))
}
/// `true` iff `x` and `y` are complementary literals (`x = ¬y` or `y = ¬x`).
fn complementary(x: &Term, y: &Term) -> bool {
    parse_not(x).as_ref() == Some(y) || parse_not(y).as_ref() == Some(x)
}

/// `¬·` simplifications: `¬T=F`, `¬F=T`, `¬¬p=p`.
fn not_simp(x: &Term) -> Result<Option<Thm>> {
    if is_t(x) {
        // ⊢ ¬T = F
        let nt = tt().not()?;
        let fwd = Thm::assume(ff())?.false_elim(nt.clone())?; // {F} ⊢ ¬T
        let bwd = Thm::assume(nt)?.not_elim(truth())?; // {¬T} ⊢ F
        return Ok(Some(fwd.deduct_antisym(bwd)?));
    }
    if is_f(x) {
        // ⊢ ¬F = T
        let nf = Thm::assume(ff())?.imp_intro(&ff())?.not_intro()?; // ⊢ ¬F
        return Ok(Some(nf.deduct_antisym(truth())?));
    }
    if let Some(y) = parse_not(x) {
        // ⊢ ¬¬y = y
        let ny = y.clone().not()?;
        let f = Thm::assume(ny.clone())?.not_elim(Thm::assume(y.clone())?)?; // {¬y,y} ⊢ F
        let fwd = f.imp_intro(&ny)?.not_intro()?; // {y} ⊢ ¬¬y
        let nny = ny.not()?;
        let bwd = dne(Thm::assume(nny)?)?; // {¬¬y} ⊢ y
        return Ok(Some(fwd.deduct_antisym(bwd)?));
    }
    Ok(None)
}

/// `∧` simplifications.
fn and_simp(a: &Term, b: &Term) -> Result<Option<Thm>> {
    let ab = a.clone().and(b.clone())?;
    if is_t(a) {
        // (T ∧ b) = b
        let fwd = truth().and_intro(Thm::assume(b.clone())?)?; // {b} ⊢ T∧b
        let bwd = Thm::assume(ab.clone())?.and_elim_r()?; // {T∧b} ⊢ b
        return Ok(Some(fwd.deduct_antisym(bwd)?));
    }
    if is_t(b) {
        // (a ∧ T) = a
        let fwd = Thm::assume(a.clone())?.and_intro(truth())?; // {a} ⊢ a∧T
        let bwd = Thm::assume(ab.clone())?.and_elim_l()?; // {a∧T} ⊢ a
        return Ok(Some(fwd.deduct_antisym(bwd)?));
    }
    if is_f(a) || is_f(b) {
        // (a ∧ b) = F
        let fwd = Thm::assume(ff())?
            .false_elim(a.clone())?
            .and_intro(Thm::assume(ff())?.false_elim(b.clone())?)?; // {F} ⊢ a∧b
        let assumed = Thm::assume(ab.clone())?;
        let bwd = if is_f(a) {
            assumed.and_elim_l()?
        } else {
            assumed.and_elim_r()?
        }; // {a∧b} ⊢ F
        return Ok(Some(fwd.deduct_antisym(bwd)?));
    }
    if complementary(a, b) {
        // (a ∧ b) = F
        let assumed = Thm::assume(ab.clone())?;
        let la = assumed.clone().and_elim_l()?;
        let lb = assumed.and_elim_r()?;
        let bwd = if parse_not(a).as_ref() == Some(b) {
            la.not_elim(lb)?
        } else {
            lb.not_elim(la)?
        }; // {a∧b} ⊢ F
        let fwd = Thm::assume(ff())?
            .false_elim(a.clone())?
            .and_intro(Thm::assume(ff())?.false_elim(b.clone())?)?;
        return Ok(Some(fwd.deduct_antisym(bwd)?));
    }
    if a == b {
        // (a ∧ a) = a
        let fwd = Thm::assume(a.clone())?.and_intro(Thm::assume(b.clone())?)?; // {a} ⊢ a∧a
        let bwd = Thm::assume(ab.clone())?.and_elim_l()?; // {a∧a} ⊢ a
        return Ok(Some(fwd.deduct_antisym(bwd)?));
    }
    Ok(None)
}

/// `∨` simplifications.
fn or_simp(a: &Term, b: &Term) -> Result<Option<Thm>> {
    let ab = a.clone().or(b.clone())?;
    if is_t(a) || is_t(b) {
        // (a ∨ b) = T
        let fwd = if is_t(a) {
            truth().or_intro_l(b.clone())?
        } else {
            truth().or_intro_r(a.clone())?
        }; // ⊢ a∨b
        return Ok(Some(fwd.deduct_antisym(truth())?));
    }
    if complementary(a, b) {
        // (a ∨ b) = T
        let fwd = if parse_not(b).as_ref() == Some(a) {
            Thm::lem(a.clone())? // a ∨ ¬a
        } else {
            or_sym(Thm::lem(b.clone())?)? // ¬b ∨ b
        };
        return Ok(Some(fwd.deduct_antisym(truth())?));
    }
    if is_f(a) {
        // (F ∨ b) = b
        let fwd = Thm::assume(b.clone())?.or_intro_r(ff())?; // {b} ⊢ F∨b
        let id_b = Thm::assume(b.clone())?.imp_intro(b)?; // ⊢ b ⟹ b
        let f_imp = Thm::assume(ff())?.false_elim(b.clone())?.imp_intro(&ff())?; // ⊢ F ⟹ b
        let bwd = Thm::assume(ab.clone())?.or_elim(f_imp, id_b)?; // {F∨b} ⊢ b
        return Ok(Some(fwd.deduct_antisym(bwd)?));
    }
    if is_f(b) {
        // (a ∨ F) = a
        let fwd = Thm::assume(a.clone())?.or_intro_l(ff())?; // {a} ⊢ a∨F
        let id_a = Thm::assume(a.clone())?.imp_intro(a)?; // ⊢ a ⟹ a
        let f_imp = Thm::assume(ff())?.false_elim(a.clone())?.imp_intro(&ff())?; // ⊢ F ⟹ a
        let bwd = Thm::assume(ab.clone())?.or_elim(id_a, f_imp)?; // {a∨F} ⊢ a
        return Ok(Some(fwd.deduct_antisym(bwd)?));
    }
    if a == b {
        // (a ∨ a) = a
        let fwd = Thm::assume(a.clone())?.or_intro_l(b.clone())?; // {a} ⊢ a∨a
        let id_a = Thm::assume(a.clone())?.imp_intro(a)?; // ⊢ a ⟹ a
        let bwd = Thm::assume(ab.clone())?.or_elim(id_a.clone(), id_a)?; // {a∨a} ⊢ a
        return Ok(Some(fwd.deduct_antisym(bwd)?));
    }
    Ok(None)
}

/// `⟹` simplifications.
fn imp_simp(a: &Term, b: &Term) -> Result<Option<Thm>> {
    let ab = a.clone().imp(b.clone())?;
    if is_f(a) {
        // (F ⟹ b) = T
        let fwd = Thm::assume(ff())?.false_elim(b.clone())?.imp_intro(&ff())?; // ⊢ F⟹b
        return Ok(Some(fwd.deduct_antisym(truth())?));
    }
    if is_t(b) {
        // (a ⟹ T) = T
        let fwd = truth().imp_intro(a)?; // ⊢ a⟹T
        return Ok(Some(fwd.deduct_antisym(truth())?));
    }
    if is_t(a) {
        // (T ⟹ b) = b
        let fwd = Thm::assume(b.clone())?.imp_intro(&tt())?; // {b} ⊢ T⟹b
        let bwd = Thm::assume(ab.clone())?.imp_elim(truth())?; // {T⟹b} ⊢ b
        return Ok(Some(fwd.deduct_antisym(bwd)?));
    }
    if is_f(b) {
        // (a ⟹ F) = ¬a
        let na = a.clone().not()?;
        let contra = Thm::assume(na.clone())?.not_elim(Thm::assume(a.clone())?)?; // {¬a,a} ⊢ F
        let fwd = contra.imp_intro(a)?; // {¬a} ⊢ a⟹F
        let bwd = Thm::assume(ab.clone())?.not_intro()?; // {a⟹F} ⊢ ¬a
        return Ok(Some(fwd.deduct_antisym(bwd)?));
    }
    if a == b {
        // (a ⟹ a) = T
        let fwd = Thm::assume(a.clone())?.imp_intro(a)?; // ⊢ a⟹a
        return Ok(Some(fwd.deduct_antisym(truth())?));
    }
    Ok(None)
}

/// Primitive `=`-at-`bool` simplifications: `(a=a)=T`, `(a=T)=a`,
/// `(T=a)=a`, `(a=F)=¬a`, `(F=a)=¬a`.
fn eq_simp(a: &Term, b: &Term) -> Result<Option<Thm>> {
    if a == b {
        // (a = a) = T
        return Ok(Some(Thm::refl(a.clone())?.eqt_intro()?));
    }
    if is_t(b) {
        // (a = T) = a
        let fwd = Thm::assume(a.clone())?.eqt_intro()?; // {a} ⊢ a=T
        let bwd = Thm::assume(a.clone().equals(tt())?)?.eqt_elim()?; // {a=T} ⊢ a
        return Ok(Some(fwd.deduct_antisym(bwd)?));
    }
    if is_t(a) {
        // (T = a) = a
        let fwd = Thm::assume(b.clone())?.eqt_intro()?.sym()?; // {b} ⊢ T=b
        let bwd = Thm::assume(tt().equals(b.clone())?)?.sym()?.eqt_elim()?; // {T=b} ⊢ b
        return Ok(Some(fwd.deduct_antisym(bwd)?));
    }
    if is_f(b) {
        // (a = F) = ¬a
        return Ok(Some(eq_false(a, false)?));
    }
    if is_f(a) {
        // (F = a) = ¬a
        return Ok(Some(eq_false(b, true)?));
    }
    if complementary(a, b) {
        // (a = b) = F — complementary bools are never equal.
        let eq = a.clone().equals(b.clone())?;
        // Reduce to the canonical contradiction `x = ¬x` (x the positive
        // atom), so the excluded-middle split is symmetric.
        let (xeqnx, x) = if parse_not(b).as_ref() == Some(a) {
            (Thm::assume(eq.clone())?, a.clone()) // a = ¬a
        } else {
            (Thm::assume(eq.clone())?.sym()?, b.clone()) // (¬b = b) ⟹ b = ¬b
        };
        let nx = x.clone().not()?;
        // x ⟹ F : x and (x = ¬x) give ¬x, contradiction.
        let from_x = {
            let xt = Thm::assume(x.clone())?;
            xeqnx.clone().eq_mp(xt.clone())?.not_elim(xt)?.imp_intro(&x)?
        };
        // ¬x ⟹ F : ¬x and (¬x = x) give x, contradiction.
        let from_nx = {
            let nxt = Thm::assume(nx.clone())?;
            let xres = xeqnx.sym()?.eq_mp(nxt.clone())?; // ⊢ x
            nxt.not_elim(xres)?.imp_intro(&nx)?
        };
        let fwd = Thm::lem(x)?.or_elim(from_x, from_nx)?; // {a=b} ⊢ F
        let bwd = Thm::assume(ff())?.false_elim(eq)?; // {F} ⊢ a=b
        return Ok(Some(bwd.deduct_antisym(fwd)?));
    }
    Ok(None)
}

/// `⊢ (a = F) = ¬a` (or `⊢ (F = a) = ¬a` when `flipped`).
fn eq_false(a: &Term, flipped: bool) -> Result<Thm> {
    let eq = if flipped {
        ff().equals(a.clone())?
    } else {
        a.clone().equals(ff())?
    };
    let na = a.clone().not()?;
    // {a = F} ⊢ ¬a : a forces F, contradiction, discharge.
    let a_eq_f = if flipped {
        Thm::assume(eq.clone())?.sym()? // {F=a} ⊢ a=F
    } else {
        Thm::assume(eq.clone())? // {a=F} ⊢ a=F
    };
    let fwd = a_eq_f
        .eq_mp(Thm::assume(a.clone())?)? // {…, a} ⊢ F
        .imp_intro(a)?
        .not_intro()?; // {a=F or F=a} ⊢ ¬a
    // {¬a} ⊢ a = F : under ¬a, a and F agree.
    let a_from_f = Thm::assume(ff())?.false_elim(a.clone())?; // {F} ⊢ a
    let f_from_a = Thm::assume(na.clone())?.not_elim(Thm::assume(a.clone())?)?; // {¬a,a} ⊢ F
    let bwd_af = a_from_f.deduct_antisym(f_from_a)?; // {¬a} ⊢ a = F
    let bwd = if flipped { bwd_af.sym()? } else { bwd_af }; // {¬a} ⊢ (F=a)/(a=F)
    bwd.deduct_antisym(fwd) // ⊢ eq = ¬a
}

/// `⟺` simplifications. Since `iff ≡ λp q. p = q`, a simplifiable
/// biconditional is unfolded to a primitive `bool` equation and handed to
/// [`eq_simp`] on the next pass; otherwise it is left alone.
fn iff_simp(a: &Term, b: &Term) -> Result<Option<Thm>> {
    let simplifiable =
        a == b || is_t(a) || is_t(b) || is_f(a) || is_f(b) || complementary(a, b);
    if !simplifiable {
        return Ok(None);
    }
    let node = a.clone().iff(b.clone())?;
    // ⊢ (a ⟺ b) = ((λp q. p = q) a b), then β-reduce the rhs to `a = b`.
    let eq_form = node.delta_all(iff_spec().symbol())?.reduce_rhs()?;
    Ok(Some(eq_form))
}

/// Parse a binary-connective application `App(App(op, a), b)` →
/// `(op_spec, a, b)`. Callers filter on the spec by `ptr_eq`.
fn parse_binop(t: &Term) -> Option<(covalence_core::defs::TermSpec, Term, Term)> {
    let (f, b) = t.as_app()?;
    let (head, a) = f.as_app()?;
    let (spec, _) = head.as_spec()?;
    Some((spec.clone(), a.clone(), b.clone()))
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

    /// `⊢ t = rhs` ⟹ return `rhs`.
    fn rhs_of(thm: &Thm) -> Term {
        thm.concl().as_eq().expect("equation").1.clone()
    }

    #[test]
    fn dne_eliminates_double_negation() {
        // {¬¬a} ⊢ a.
        let a = Term::free("a", b());
        let nna = a.clone().not().unwrap().not().unwrap();
        let out = dne(Thm::assume(nna.clone()).unwrap()).unwrap();
        assert_eq!(out.concl(), &a);
        assert!(out.hyps().iter().any(|h| h == &nna));
    }

    #[test]
    fn clause_intro_neg_makes_positive_literals() {
        // {¬a} ⊢ ¬a  ⟶  ⊢ a ∨ ¬a   (the literal stays positive).
        let a = Term::free("a", b());
        let na = a.clone().not().unwrap();
        let cl = clause_intro_neg(Thm::assume(na.clone()).unwrap(), &[a.clone()]).unwrap();
        assert!(cl.hyps().is_empty());
        assert_eq!(cl.concl(), &a.clone().or(na).unwrap());
    }

    #[test]
    fn simp_core_identities() {
        let a = Term::free("a", b());
        let cases: Vec<(Term, Term)> = vec![
            (a.clone().and(a.clone()).unwrap(), a.clone()), // p∧p = p
            (a.clone().or(a.clone()).unwrap(), a.clone()),  // p∨p = p
            (a.clone().and(tt()).unwrap(), a.clone()),      // p∧T = p
            (tt().and(a.clone()).unwrap(), a.clone()),      // T∧p = p
            (a.clone().or(ff()).unwrap(), a.clone()),       // p∨F = p
            (a.clone().and(ff()).unwrap(), ff()),           // p∧F = F
            (a.clone().or(tt()).unwrap(), tt()),            // p∨T = T
            (a.clone().or(a.clone().not().unwrap()).unwrap(), tt()), // p∨¬p = T
            (a.clone().and(a.clone().not().unwrap()).unwrap(), ff()), // p∧¬p = F
            (tt().not().unwrap(), ff()),                    // ¬T = F
            (a.clone().not().unwrap().not().unwrap(), a.clone()), // ¬¬p = p
            (ff().imp(a.clone()).unwrap(), tt()),           // F⟹p = T
            (a.clone().imp(ff()).unwrap(), a.clone().not().unwrap()), // p⟹F = ¬p
        ];
        for (input, want) in cases {
            let eq = simp(&input).unwrap();
            assert_eq!(eq.concl().as_eq().unwrap().0, &input, "lhs preserved");
            assert_eq!(rhs_of(&eq), want, "simp {input}");
            assert!(eq.hyps().is_empty(), "simp of a closed term is axiom-free");
        }
    }

    #[test]
    fn simp_iff_and_bool_equality() {
        let a = Term::free("a", b());
        let cases: Vec<(Term, Term)> = vec![
            // primitive `=` at bool
            (a.clone().equals(a.clone()).unwrap(), tt()), // (a=a) = T
            (a.clone().equals(tt()).unwrap(), a.clone()), // (a=T) = a
            (tt().equals(a.clone()).unwrap(), a.clone()), // (T=a) = a
            (a.clone().equals(ff()).unwrap(), a.clone().not().unwrap()), // (a=F) = ¬a
            (ff().equals(a.clone()).unwrap(), a.clone().not().unwrap()), // (F=a) = ¬a
            (a.clone().equals(a.clone().not().unwrap()).unwrap(), ff()), // (a=¬a) = F
            (a.clone().not().unwrap().equals(a.clone()).unwrap(), ff()), // (¬a=a) = F
            // the biconditional, which unfolds to the above
            (a.clone().iff(a.clone()).unwrap(), tt()),    // (a ⟺ a) = T
            (a.clone().iff(tt()).unwrap(), a.clone()),    // (a ⟺ T) = a
            (a.clone().iff(ff()).unwrap(), a.clone().not().unwrap()), // (a ⟺ F) = ¬a
        ];
        for (input, want) in cases {
            let eq = simp(&input).unwrap();
            assert_eq!(eq.concl().as_eq().unwrap().0, &input, "lhs preserved for {input}");
            assert_eq!(rhs_of(&eq), want, "simp {input}");
            assert!(eq.hyps().is_empty());
        }
    }

    #[test]
    fn simp_leaves_contingent_iff_and_nonbool_eq_alone() {
        // A genuine biconditional `a ⟺ c` has no identity to fire — but
        // note `simp` still unfolds it to `a = c` (its definitional form).
        let a = Term::free("a", b());
        let c = Term::free("c", b());
        let iff = a.clone().iff(c.clone()).unwrap();
        // No T/F/idempotence pattern → left as the iff term, unchanged.
        assert_eq!(rhs_of(&simp(&iff).unwrap()), iff);
        // A non-bool equation is not propositional — untouched.
        let n = Term::free("n", Type::nat());
        let neq = n.clone().equals(n.clone()).unwrap();
        assert_eq!(rhs_of(&simp(&neq).unwrap()), neq);
    }

    #[test]
    fn tauto_decide_cover_iff() {
        let a = Term::free("a", b());
        // a ⟺ a is a tautology.
        let refl_iff = a.clone().iff(a.clone()).unwrap();
        assert_eq!(tauto(&refl_iff).unwrap().concl(), &refl_iff);
        // a ⟺ ¬a is contradictory → it unfolds to `a = ¬a`, which the
        // complement rule sends to F, so decide proves its negation.
        let bad = a.clone().iff(a.clone().not().unwrap()).unwrap();
        let out = decide(&bad).unwrap();
        assert_eq!(out.concl(), &bad.not().unwrap());
    }

    #[test]
    fn simp_recurses_under_congruence() {
        // (a ∧ T) ∨ (b ∧ b)  simplifies to  a ∨ b.
        let a = Term::free("a", b());
        let bb = Term::free("b", b());
        let input = a
            .clone()
            .and(tt())
            .unwrap()
            .or(bb.clone().and(bb.clone()).unwrap())
            .unwrap();
        let eq = simp(&input).unwrap();
        assert_eq!(rhs_of(&eq), a.or(bb).unwrap());
    }

    #[test]
    fn tauto_proves_trivial_tautologies() {
        let a = Term::free("a", b());
        // a ∨ ¬a
        let lem = a.clone().or(a.clone().not().unwrap()).unwrap();
        let thm = tauto(&lem).unwrap();
        assert_eq!(thm.concl(), &lem);
        assert!(thm.hyps().is_empty());
        // a ⟹ a
        assert!(tauto(&a.clone().imp(a.clone()).unwrap()).is_ok());
        // a bare atom is not a tautology
        assert!(tauto(&a).is_err());
    }

    #[test]
    fn decide_handles_both_polarities() {
        let a = Term::free("a", b());
        // a ∨ ¬a is a tautology → ⊢ (a ∨ ¬a).
        let lem = a.clone().or(a.clone().not().unwrap()).unwrap();
        assert_eq!(decide(&lem).unwrap().concl(), &lem);
        // a ∧ ¬a is contradictory → ⊢ ¬(a ∧ ¬a).
        let contra = a.clone().and(a.clone().not().unwrap()).unwrap();
        let out = decide(&contra).unwrap();
        assert_eq!(out.concl(), &contra.not().unwrap());
        // A contingent atom is decided neither way.
        assert!(decide(&a).is_err());
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
