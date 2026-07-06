//! **Existence** — the first proof layer of the recursion engine: the
//! graph relates *every* element of the inductive type to *some* value.
//!
//! Two pieces, both generic over an [`InductiveSig`] / [`Inductive`]:
//!
//! - [`graph_intro`] — the per-constructor introduction rule
//!   `⊢ (⋀ⱼ Graph rⱼ bⱼ) ⟹ Graph (Cᵢ x⃗) (fᵢ x⃗ b⃗)`, pure impredicative
//!   manipulation (no freeness, no induction). Generalises `nat`'s
//!   hand-written `graph_base` / `graph_step`.
//! - [`graph_total`] — `⊢ ∀t. ∃a. Graph t a`, by the supplied structural
//!   induction over the introduction rules. Generalises `nat`'s
//!   `graph_total`.
//!
//! The other uniqueness pieces are [`super::uniqueness`] (inversion) and
//! [`super::determinacy`]; only the **ε-assembly** remains specialised to
//! `nat` (see `SKELETONS.md`).

use covalence_core::{Result, Term, Type, subst};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::derived::DerivedRules;

use super::data::Inductive;
use super::graph::{self, CtorInstance};
use super::sig::InductiveSig;
use super::util::{and_all, discharge_conj, project, var_name};
use crate::init::eq::{beta_expand, beta_reduce};
use crate::init::ext::TermExt;
use crate::init::logic::{exists_elim, exists_intro};

// ============================================================================
// Per-constructor graph introduction
// ============================================================================

/// `⊢ (⋀ⱼ Graph fs rⱼ bⱼ) ⟹ Graph fs (Cᵢ x⃗) (fᵢ x⃗ b⃗)` — constructor
/// `i`'s graph-introduction rule, over fresh argument / image variables.
/// For a non-recursive constructor this is just
/// `⊢ Graph fs (Cᵢ x⃗) (fᵢ x⃗)`.
///
/// Fix the relation `G`, assume it closed, take its `i`-th clause and
/// instantiate at `x⃗ b⃗`; discharge that clause's `G rⱼ bⱼ` antecedents
/// from the assumed `Graph rⱼ bⱼ` (each unfolds its own `∀G`), giving
/// `G (Cᵢ x⃗) (fᵢ x⃗ b⃗)`; re-close `∀G` and discharge the assumptions.
pub fn graph_intro(sig: &InductiveSig, steps: &[Term], beta: &Type, i: usize) -> Result<Thm> {
    let g_ty = graph::relation_ty(sig, beta);
    let g = Term::free(sig.relation, g_ty.clone());
    let cl = graph::closed(sig, steps, beta, &g)?;
    let inst = graph::ctor_instance(&sig.ty, beta, &sig.ctors[i], &steps[i])?;

    // {CL} ⊢ clause_i, ∀-eliminated at the argument and image vars.
    let mut clause = project(Thm::assume(cl.clone())?, i, sig.arity())?;
    for a in &inst.args {
        clause = clause.all_elim(a.clone())?;
    }
    for (_, img) in &inst.rec_pairs {
        clause = clause.all_elim(img.clone())?;
    }

    // The `Graph rⱼ bⱼ` premises, and from each its `G rⱼ bⱼ`.
    let premises: Vec<Term> = inst
        .rec_pairs
        .iter()
        .map(|(sub, img)| graph::graph(sig, steps, beta, sub.clone(), img.clone()))
        .collect::<Result<_>>()?;
    let g_at_recs: Vec<Thm> = premises
        .iter()
        .map(|prem| {
            // {Graph rⱼ bⱼ, CL} ⊢ G rⱼ bⱼ
            Thm::assume(prem.clone())?
                .all_elim(g.clone())?
                .imp_elim(Thm::assume(cl.clone())?)
        })
        .collect::<Result<_>>()?;

    // Drive the clause: discharge its (possibly conjunctive) antecedent.
    let g_head = if g_at_recs.is_empty() {
        clause
    } else {
        clause.imp_elim(and_all(&g_at_recs)?)?
    };

    // Re-close `∀G` (discharging CL), then discharge the premises.
    let graphed = g_head.imp_intro(&cl)?.all_intro(sig.relation, g_ty)?;
    discharge_conj(graphed, &premises)
}

// ============================================================================
// Totality
// ============================================================================

/// `λa. Graph fs t a` — the existential predicate at a fixed `t`.
fn exists_pred(sig: &InductiveSig, steps: &[Term], beta: &Type, t: &Term) -> Result<Term> {
    let a = Term::free("__a", beta.clone());
    let body = graph::graph(sig, steps, beta, t.clone(), a)?;
    Ok(Term::abs(beta.clone(), subst::close(&body, "__a")))
}

/// `λt. ∃a. Graph fs t a` — the totality motive (`a : β`).
fn total_motive(sig: &InductiveSig, steps: &[Term], beta: &Type) -> Result<Term> {
    let t = Term::free("__t", sig.ty.clone());
    let a = Term::free("__a", beta.clone());
    let body = graph::graph(sig, steps, beta, t.clone(), a)?.exists("__a", beta.clone())?;
    Ok(Term::abs(sig.ty.clone(), subst::close(&body, "__t")))
}

/// The totality induction case for constructor `i`:
/// `⊢ (⋀ⱼ motive rⱼ) ⟹ motive (Cᵢ x⃗)`.
///
/// Witness `fᵢ x⃗ b⃗` for the goal existential via [`graph_intro`], then
/// peel each recursive argument's IH `∃bⱼ. Graph rⱼ bⱼ` with an
/// `exists_elim` so the conclusion stays witness-free.
fn total_case(
    sig: &InductiveSig,
    steps: &[Term],
    beta: &Type,
    motive: &Term,
    i: usize,
) -> Result<Thm> {
    let inst: CtorInstance = graph::ctor_instance(&sig.ty, beta, &sig.ctors[i], &steps[i])?;
    let intro = graph_intro(sig, steps, beta, i)?;

    // For each recursive argument: its existential predicate `pred_j =
    // λa. Graph rⱼ a`, the **applied** witness hypothesis `pred_j bⱼ`
    // (kept in applied form so `exists_elim`'s `step` antecedent matches),
    // and the β-reduced `⊢ Graph rⱼ bⱼ` that feeds `graph_intro`.
    let mut applied_hyps = Vec::new();
    let mut graph_thms = Vec::new();
    for (sub, img) in &inst.rec_pairs {
        let pred = exists_pred(sig, steps, beta, sub)?;
        let hyp = Term::app(pred, img.clone());
        graph_thms.push(beta_reduce(Thm::assume(hyp.clone())?)?); // {hyp} ⊢ Graph rⱼ bⱼ
        applied_hyps.push(hyp);
    }

    // Core, under {pred_j bⱼ}: Graph (Cᵢ x⃗) (fᵢ x⃗ b⃗), then ∃-introduce.
    let g_head = if graph_thms.is_empty() {
        intro
    } else {
        intro.imp_elim(and_all(&graph_thms)?)?
    };
    let head_pred = exists_pred(sig, steps, beta, &inst.head)?;
    let at_value = beta_expand(&head_pred, inst.value.clone(), g_head)?;
    let ex = exists_intro(head_pred, inst.value.clone(), at_value)?;
    let mut acc = beta_expand(motive, inst.head.clone(), ex)?; // {pred_j bⱼ} ⊢ motive (Cᵢ x⃗)

    // Peel each IH `motive rⱼ` (= `∃bⱼ. Graph rⱼ bⱼ`), removing its
    // applied `pred_j bⱼ` hypothesis.
    let goal = Term::app(motive.clone(), inst.head.clone());
    for ((sub, img), hyp) in inst.rec_pairs.iter().zip(&applied_hyps) {
        let ih_exists = beta_reduce(Thm::assume(Term::app(motive.clone(), sub.clone()))?)?;
        let step = acc.imp_intro(hyp)?.all_intro(var_name(img), beta.clone())?;
        acc = exists_elim(ih_exists, goal.clone(), step)?;
    }

    let ih_terms: Vec<Term> = inst
        .rec_pairs
        .iter()
        .map(|(sub, _)| Term::app(motive.clone(), sub.clone()))
        .collect();
    discharge_conj(acc, &ih_terms)
}

/// `⊢ ∀t. (λt. ∃a. Graph fs t a) t` — the graph is **total**. The
/// induction principle comes from `theory`; the per-constructor cases are
/// built from [`graph_intro`].
pub fn graph_total<I: Inductive>(theory: &I, steps: &[Term], beta: &Type) -> Result<Thm> {
    let sig = theory.sig();
    let motive = total_motive(sig, steps, beta)?;
    let cases: Vec<Thm> = (0..sig.arity())
        .map(|i| total_case(sig, steps, beta, &motive, i))
        .collect::<Result<_>>()?;
    theory.induct(&motive, cases)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::init::inductive::sig::{Arg, Constructor};
    use crate::init::nat::{nat_succ, succ, zero};

    fn nat() -> Type {
        Type::nat()
    }

    /// The `nat` signature, matching [`crate::init::recursion`].
    fn nat_sig() -> InductiveSig {
        InductiveSig {
            ty: nat(),
            relation: "G",
            ctors: vec![
                Constructor::nullary(zero()),
                Constructor::new(
                    nat_succ(),
                    vec![Arg::Rec {
                        name: "m",
                        image: "b",
                    }],
                ),
            ],
        }
    }

    fn zf() -> (Term, Term) {
        (
            Term::free("z", nat()),
            Term::free("f", Type::fun(nat(), Type::fun(nat(), nat()))),
        )
    }

    /// `graph_intro` at the nullary constructor is `⊢ Graph z f 0 z`, with
    /// no hypotheses and no antecedent.
    #[test]
    fn graph_intro_nullary_is_axiom_free() {
        let (z, f) = zf();
        let thm = graph_intro(&nat_sig(), &[z.clone(), f.clone()], &nat(), 0).unwrap();
        assert!(thm.hyps().is_empty());
        let expected = graph::graph(&nat_sig(), &[z.clone(), f], &nat(), zero(), z).unwrap();
        assert_eq!(thm.concl(), &expected);
    }

    /// `graph_intro` at the recursive constructor is
    /// `⊢ Graph z f m b ⟹ Graph z f (S m) (f m b)`.
    #[test]
    fn graph_intro_recursive_is_the_step_rule() {
        let (z, f) = zf();
        let steps = [z.clone(), f.clone()];
        let thm = graph_intro(&nat_sig(), &steps, &nat(), 1).unwrap();
        assert!(thm.hyps().is_empty());

        let m = Term::free("m", nat());
        let b = Term::free("b", nat());
        let ante = graph::graph(&nat_sig(), &steps, &nat(), m.clone(), b.clone()).unwrap();
        let fmb = f.apply(m.clone()).unwrap().apply(b.clone()).unwrap();
        let conseq = graph::graph(&nat_sig(), &steps, &nat(), succ(m), fmb).unwrap();
        assert_eq!(thm.concl(), &ante.imp(conseq).unwrap());
    }

    // ------------------------------------------------------------------
    // Multi-recursive-argument coverage: a binary-tree `branch` constructor
    // with TWO recursive arguments. `graph_intro` is pure impredicative
    // manipulation (no `Inductive` adapter, no induction/freeness), so it
    // validates the engine's multi-rec-arg graph + existence layer directly:
    // the introduction rule must carry the *conjunctive* antecedent
    // `Graph l bl ∧ Graph r br ⟹ Graph (branch l r) (f l r bl br)`.
    // ------------------------------------------------------------------

    /// A `tree nat := leaf nat | branch (tree nat) (tree nat)` signature
    /// (carrier stood in by `nat` for the term-layer test), result type
    /// `β := nat`. `branch` has two recursive arguments `l`, `r`.
    fn tree_sig() -> InductiveSig {
        let leaf = Term::free("leaf", Type::fun(nat(), nat())); // nat → T
        let branch = Term::free("branch", Type::fun(nat(), Type::fun(nat(), nat()))); // T → T → T
        InductiveSig {
            ty: nat(),
            relation: "G",
            ctors: vec![
                Constructor::new(
                    leaf,
                    vec![Arg::Param {
                        ty: nat(),
                        name: "x",
                    }],
                ),
                Constructor::new(
                    branch,
                    vec![
                        Arg::Rec {
                            name: "l",
                            image: "bl",
                        },
                        Arg::Rec {
                            name: "r",
                            image: "br",
                        },
                    ],
                ),
            ],
        }
    }

    /// `graph_intro` at a **two-recursive-argument** constructor produces the
    /// conjunctive-antecedent introduction rule
    /// `⊢ (Graph l bl ∧ Graph r br) ⟹ Graph (branch l r) (f l r bl br)`,
    /// hypothesis-free. This exercises the multi-rec-arg graph/existence path
    /// the engine extension generalised.
    #[test]
    fn graph_intro_two_rec_args_is_conjunctive() {
        let sig = tree_sig();
        // Step terms: `fl : nat → β` (leaf), `fb : T → T → β → β → β` (branch).
        let fl = Term::free("fl", Type::fun(nat(), nat()));
        let fb = Term::free(
            "fb",
            Type::fun(
                nat(),
                Type::fun(nat(), Type::fun(nat(), Type::fun(nat(), nat()))),
            ),
        );
        let steps = [fl, fb.clone()];

        let thm = graph_intro(&sig, &steps, &nat(), 1).unwrap();
        assert!(thm.hyps().is_empty(), "graph_intro must be axiom-free");

        // Expected: `(Graph l bl ∧ Graph r br) ⟹ Graph (branch l r) (fb l r bl br)`.
        let branch = sig.ctors[1].ctor.clone();
        let l = Term::free("l", nat());
        let r = Term::free("r", nat());
        let bl = Term::free("bl", nat());
        let br = Term::free("br", nat());
        let g_l = graph::graph(&sig, &steps, &nat(), l.clone(), bl.clone()).unwrap();
        let g_r = graph::graph(&sig, &steps, &nat(), r.clone(), br.clone()).unwrap();
        let ante = g_l.and(g_r).unwrap();
        let branch_lr = branch.apply(l.clone()).unwrap().apply(r.clone()).unwrap();
        let f_val = fb
            .apply(l)
            .unwrap()
            .apply(r)
            .unwrap()
            .apply(bl)
            .unwrap()
            .apply(br)
            .unwrap();
        let conseq = graph::graph(&sig, &steps, &nat(), branch_lr, f_val).unwrap();
        assert_eq!(thm.concl(), &ante.imp(conseq).unwrap());
    }
}
