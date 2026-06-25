//! **Uniqueness**, part 2: **determinacy** — the recursion graph relates
//! each element of the inductive type to *at most one* value:
//!
//! ```text
//!   graph_det :  ⊢ ∀t a b. Graph t a ⟹ Graph t b ⟹ a = b
//! ```
//!
//! By the supplied structural induction. In each constructor case, both
//! `Graph (Cᵢ x⃗) a` and `Graph (Cᵢ x⃗) b` invert
//! ([`super::uniqueness::graph_inv`]) to `a = fᵢ x⃗ c⃗` / `b = fᵢ x⃗ d⃗` with
//! `Graph rⱼ cⱼ` / `Graph rⱼ dⱼ`; the induction hypothesis equates `cⱼ = dⱼ`,
//! so `a = fᵢ x⃗ c⃗ = fᵢ x⃗ d⃗ = b`.
//!
//! This and the ε-assembly are the last pieces of the recursor construction
//! that were specialised to `nat`; `graph_det` here is now generic. The
//! **multi-recursive-argument** case — two or more recursive arguments in one
//! constructor (a binary tree's `branch`) — is now handled: [`det_step`]
//! peels *all* the inversion witnesses on each side, equates each pair by its
//! own induction hypothesis, and chains the resulting congruences. The
//! single-recursive-argument shape (`nat`'s `succ`) is the degenerate `k = 1`
//! instance of the same code.

use covalence_core::{Error, Result, Term, Thm, Type, subst};

use super::data::Inductive;
use super::graph::{self, CtorInstance};
use super::sig::InductiveSig;
use super::uniqueness::graph_inv;
use super::util::discharge_conj;
use crate::init::eq::{beta_expand, beta_reduce};
use crate::init::ext::{TermExt, ThmExt};
use crate::init::logic::exists_elim;

/// `λt. ∀a b. Graph t a ⟹ Graph t b ⟹ a = b` — the determinacy motive.
fn det_motive(sig: &InductiveSig, steps: &[Term], beta: &Type) -> Result<Term> {
    let t = Term::free("__t", sig.ty.clone());
    let a = Term::free("__a", beta.clone());
    let b = Term::free("__b", beta.clone());
    let body = graph::graph(sig, steps, beta, t.clone(), a.clone())?
        .imp(graph::graph(sig, steps, beta, t.clone(), b.clone())?.imp(a.equals(b)?)?)?;
    let inner = body
        .forall("__b", beta.clone())?
        .forall("__a", beta.clone())?;
    Ok(Term::abs(sig.ty.clone(), subst::close(&inner, "__t")))
}

/// The inversion of `Graph (Cᵢ x⃗) v`, as a theorem under hypothesis
/// `Graph (Cᵢ x⃗) v`: `a = fᵢ x⃗` (nullary) or `∃c⃗. (⋀ Graph rⱼ cⱼ) ∧ v =
/// fᵢ x⃗ c⃗` (recursive). `v` is the value variable (`graph_inv` is over `a`;
/// for `b` it is instantiated).
fn invert<I: Inductive>(
    theory: &I,
    steps: &[Term],
    beta: &Type,
    i: usize,
    head: &Term,
    v: &Term,
) -> Result<Thm> {
    let inv = graph_inv(theory, steps, beta, i)?.inst("a", v.clone())?;
    let gh = graph::graph(theory.sig(), steps, beta, head.clone(), v.clone())?;
    inv.imp_elim(Thm::assume(gh)?)
}

/// The determinacy induction case for constructor `i`:
/// `⊢ (⋀ⱼ motive rⱼ) ⟹ motive (Cᵢ x⃗)`.
fn det_case<I: Inductive>(
    theory: &I,
    steps: &[Term],
    beta: &Type,
    motive: &Term,
    i: usize,
) -> Result<Thm> {
    let sig = theory.sig();
    let inst: CtorInstance = graph::ctor_instance(&sig.ty, beta, &sig.ctors[i], &steps[i])?;
    let a = Term::free("__a", beta.clone());
    let b = Term::free("__b", beta.clone());
    let gsa = graph::graph(sig, steps, beta, inst.head.clone(), a.clone())?;
    let gsb = graph::graph(sig, steps, beta, inst.head.clone(), b.clone())?;
    let goal = a.clone().equals(b.clone())?;

    let inv_a = invert(theory, steps, beta, i, &inst.head, &a)?; // {gsa} ⊢ …a…
    let inv_b = invert(theory, steps, beta, i, &inst.head, &b)?; // {gsb} ⊢ …b…

    // `{gsa, gsb, IHs} ⊢ a = b`.
    let core = if inst.rec_pairs.is_empty() {
        // Nullary: `a = fᵢ x⃗`, `b = fᵢ x⃗`, hence `a = b`.
        inv_a.trans(inv_b.sym()?)?
    } else {
        // One *or more* recursive arguments: peel every witness on each
        // side, equate them pairwise by the IHs, chain the congruences.
        det_step(motive, &inst, inv_a, inv_b, &goal)?
    };

    // `motive (Cᵢ x⃗)` (applied), then discharge the IH antecedents.
    let inner = core
        .imp_intro(&gsb)?
        .imp_intro(&gsa)?
        .all_intro("__b", beta.clone())?
        .all_intro("__a", beta.clone())?;
    let applied = beta_expand(motive, inst.head.clone(), inner)?;
    let ih_terms: Vec<Term> = inst
        .rec_pairs
        .iter()
        .map(|(r, _)| Term::app(motive.clone(), r.clone()))
        .collect();
    discharge_conj(applied, &ih_terms)
}

/// The recursive-constructor determinacy core, for **any** number `k ≥ 1`
/// of recursive arguments. From the two inversion existentials
/// `inv_a : Graph (Cᵢ x⃗) a ⊢ ∃c⃗. (⋀ⱼ Graph rⱼ cⱼ) ∧ a = fᵢ x⃗ c⃗` (and the
/// `d⃗` mirror for `b`): peel *all* the `c⃗` witnesses, then *all* the `d⃗`
/// witnesses, equate `cⱼ = dⱼ` by the IH `motive rⱼ`, and chain
/// `a = fᵢ x⃗ c⃗ = fᵢ x⃗ d⃗ = b` by rewriting every `cⱼ ↦ dⱼ`. The
/// single-argument case (`nat`'s `succ`) is `k = 1`.
fn det_step(
    motive: &Term,
    inst: &CtorInstance,
    inv_a: Thm,
    inv_b: Thm,
    goal: &Term,
) -> Result<Thm> {
    let beta_ty = goal.as_eq().ok_or(Error::NotAnEquation)?.0.type_of()?;
    let recs: Vec<Term> = inst.rec_pairs.iter().map(|(r, _)| r.clone()).collect();
    let k = recs.len();

    // Fresh witness variables for each side, named disjointly from anything
    // the inversion existentials bind (their own `__c…` / image binders).
    let ca_vars: Vec<Term> = (0..k)
        .map(|j| Term::free(format!("__dca{j}"), beta_ty.clone()))
        .collect();
    let cb_vars: Vec<Term> = (0..k)
        .map(|j| Term::free(format!("__dcb{j}"), beta_ty.clone()))
        .collect();

    // Inner core: under the fully-peeled body hypotheses on both sides,
    // build `{…} ⊢ a = b`.
    let core = |a_body: Thm, b_body: Thm| -> Result<Thm> {
        // Split each side's `(⋀ⱼ Graph rⱼ ·ⱼ) ∧ (· = fᵢ x⃗ ·⃗)`.
        let (a_graphs, a_eq) = split_inv_body(a_body, k)?;
        let (b_graphs, b_eq) = split_inv_body(b_body, k)?;

        // `cⱼ = dⱼ` by the IH `motive rⱼ`, for every recursive argument.
        let mut comp_eqs = Vec::with_capacity(k);
        for (j, rec) in recs.iter().enumerate() {
            let ih = beta_reduce(Thm::assume(Term::app(motive.clone(), rec.clone()))?)?;
            let eq = ih
                .all_elim(ca_vars[j].clone())?
                .all_elim(cb_vars[j].clone())?
                .imp_elim(a_graphs[j].clone())?
                .imp_elim(b_graphs[j].clone())?;
            comp_eqs.push(eq);
        }

        // `fᵢ x⃗ c⃗ = fᵢ x⃗ d⃗` by rewriting every `cⱼ ↦ dⱼ`, then
        // `a = fᵢ x⃗ c⃗ = fᵢ x⃗ d⃗ = b`.
        let f_c = a_eq.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone();
        let mut f_cong = Thm::refl(f_c)?;
        for eq in &comp_eqs {
            let rhs = f_cong
                .concl()
                .as_eq()
                .ok_or(Error::NotAnEquation)?
                .1
                .clone();
            f_cong = f_cong.trans(rhs.rw_all(eq)?)?;
        }
        a_eq.trans(f_cong)?.trans(b_eq.sym()?)
    };

    // Peel `a`'s witnesses `c⃗` (outer), then `b`'s `d⃗` (inner), then `core`.
    peel_exists(inv_a, &ca_vars, goal, &beta_ty, |a_body| {
        peel_exists(inv_b.clone(), &cb_vars, goal, &beta_ty, |b_body| {
            core(a_body, b_body)
        })
    })
}

/// Split a fully-peeled inversion body `(⋀ⱼ Graph rⱼ cⱼ) ∧ (v = fᵢ x⃗ c⃗)`
/// into the `k` graph proofs and the value equation. For `k = 1` the
/// conjunction is the binary `Graph r₀ c₀ ∧ v = …`; for `k ≥ 2` the left
/// conjunct is itself the right-associated `⋀ⱼ Graph rⱼ cⱼ`.
fn split_inv_body(body: Thm, k: usize) -> Result<(Vec<Thm>, Thm)> {
    let (graphs_thm, val_eq) = body.conjuncts()?;
    let graphs = (0..k)
        .map(|j| super::util::project(graphs_thm.clone(), j, k))
        .collect::<Result<_>>()?;
    Ok((graphs, val_eq))
}

/// Peel a chain of `∃`-witnesses from `ex = ⊢ ∃w⃗. body[w⃗]`, supplying the
/// fresh `vars` as the bound names, and discharge `goal` through nested
/// [`exists_elim`]s. `cont` proves `goal` from the *fully β-reduced* body —
/// over the hypothesis that the innermost applied-predicate holds — and is
/// run at the bottom of the peel. Generalises single-witness peeling to a
/// chain.
fn peel_exists(
    ex: Thm,
    vars: &[Term],
    goal: &Term,
    beta_ty: &Type,
    cont: impl FnOnce(Thm) -> Result<Thm>,
) -> Result<Thm> {
    let (var, rest) = vars.split_first().expect("peel_exists: empty witness list");
    // `ex`'s predicate, applied to this layer's fresh witness.
    let pred = ex.concl().as_app().ok_or(Error::NotAnEquation)?.1.clone();
    let applied = Term::app(pred, var.clone());
    let reduced = beta_reduce(Thm::assume(applied.clone())?)?;

    let inner = if rest.is_empty() {
        // Bottom: the β-reduct is the body; run the continuation.
        cont(reduced)?
    } else {
        // `reduced`'s conclusion is the inner existential `∃w'. …`; recurse.
        peel_exists(reduced, rest, goal, beta_ty, cont)?
    };

    let step = inner
        .imp_intro(&applied)?
        .all_intro(super::util::var_name(var), beta_ty.clone())?;
    exists_elim(ex, goal.clone(), step)
}

/// `⊢ ∀t. (λt. ∀a b. Graph t a ⟹ Graph t b ⟹ a = b) t` — the graph is
/// **functional**. The induction principle comes from `theory`; the cases
/// invert via [`super::uniqueness::graph_inv`].
pub fn graph_det<I: Inductive>(theory: &I, steps: &[Term], beta: &Type) -> Result<Thm> {
    let sig = theory.sig();
    let motive = det_motive(sig, steps, beta)?;
    let cases: Vec<Thm> = (0..sig.arity())
        .map(|i| det_case(theory, steps, beta, &motive, i))
        .collect::<Result<_>>()?;
    theory.induct(&motive, cases)
}
