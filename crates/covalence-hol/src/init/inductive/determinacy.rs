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
//! that were specialised to `nat`; `graph_det` here is now generic. (The
//! multi-recursive-argument case — two or more recursive arguments in one
//! constructor — is not yet handled; see `SKELETONS.md`. No present type
//! needs it: `nat` has one recursive constructor with a single recursive
//! argument.)

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
    let core = match inst.rec_pairs.as_slice() {
        // Nullary: `a = fᵢ x⃗`, `b = fᵢ x⃗`, hence `a = b`.
        [] => inv_a.trans(inv_b.sym()?)?,
        // One recursive argument: peel each witness, equate them by the IH.
        [(rec, _)] => det_step_single(motive, &a, rec, inv_a, inv_b, &goal)?,
        _ => {
            return Err(Error::ConnectiveRule(
                "inductive::determinacy: constructors with ≥2 recursive arguments not yet supported"
                    .into(),
            ));
        }
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

/// The single-recursive-argument determinacy core: from the two inversion
/// existentials, peel each witness, equate them by the IH `motive rec`, and
/// conclude `a = b`. Mirrors `nat`'s hand proof.
fn det_step_single(
    motive: &Term,
    a: &Term,
    rec: &Term,
    inv_a: Thm,
    inv_b: Thm,
    goal: &Term,
) -> Result<Thm> {
    let beta_ty = a.type_of()?;
    let ca = Term::free("__ca", beta_ty.clone());
    let cb = Term::free("__cb", beta_ty.clone());

    // Peel `a`'s witness `ca`: `Graph rec ca` and `a = fᵢ x⃗ ca`.
    let pred_a = inv_a
        .concl()
        .as_app()
        .ok_or(Error::NotAnEquation)?
        .1
        .clone();
    let pred_a_ca = Term::app(pred_a, ca.clone());
    let (gca, a_eq) = beta_reduce(Thm::assume(pred_a_ca.clone())?)?.conjuncts()?;

    // Peel `b`'s witness `cb`.
    let pred_b = inv_b
        .concl()
        .as_app()
        .ok_or(Error::NotAnEquation)?
        .1
        .clone();
    let pred_b_cb = Term::app(pred_b, cb.clone());
    let (gcb, b_eq) = beta_reduce(Thm::assume(pred_b_cb.clone())?)?.conjuncts()?;

    // `ca = cb` by the IH at `rec`; then `a = fᵢ x⃗ ca = fᵢ x⃗ cb = b`.
    let ih = beta_reduce(Thm::assume(Term::app(motive.clone(), rec.clone()))?)?;
    let ca_eq_cb = ih
        .all_elim(ca.clone())?
        .all_elim(cb.clone())?
        .imp_elim(gca)?
        .imp_elim(gcb)?;
    let f_ca = a_eq.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone();
    let f_cong = f_ca.rw_all(&ca_eq_cb)?; // ⊢ fᵢ x⃗ ca = fᵢ x⃗ cb
    let a_eq_b = a_eq.trans(f_cong)?.trans(b_eq.sym()?)?; // {…, ca-hyp, cb-hyp} ⊢ a = b

    // Discharge the two witnesses (nested `exists_elim`).
    let step_b = a_eq_b
        .imp_intro(&pred_b_cb)?
        .all_intro("__cb", beta_ty.clone())?;
    let step_a = exists_elim(inv_b, goal.clone(), step_b)?
        .imp_intro(&pred_a_ca)?
        .all_intro("__ca", beta_ty)?;
    exists_elim(inv_a, goal.clone(), step_a)
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
