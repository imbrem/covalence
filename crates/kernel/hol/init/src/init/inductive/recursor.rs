//! **Assembly**: the recursor via Hilbert choice, its defining equations,
//! and the **recursion theorem** `⊢ ∃rec. P_rec rec`.
//!
//! With totality ([`super::existence::graph_total`]) and determinacy
//! ([`super::determinacy::graph_det`]) in hand, the graph is a total
//! function, so
//!
//! ```text
//!   rec ≜ λ(steps). λt. ε a. Graph steps t a
//! ```
//!
//! is well-defined and satisfies one equation per constructor:
//!
//! ```text
//!   rec (Cᵢ x⃗) = fᵢ x⃗ (rec r⃗)
//! ```
//!
//! (the recursive arguments `r⃗` replaced by their `rec`-images). The chosen
//! value is in the graph ([`graph_at_rec`], from totality + Hilbert choice);
//! the graph also relates `Cᵢ x⃗` to `fᵢ x⃗ (rec r⃗)` (graph introduction); and
//! determinacy forces the two equal.
//!
//! ## The `P_rec` coupling
//!
//! `P_rec` — the predicate a recursor must satisfy — is *not* reconstructed
//! here: it lives in the `defs` recursor spec (e.g. `natRec`'s selector
//! predicate), and `spec_ax` later transfers the equations to the catalogue
//! constant. So [`recursion_theorem`] takes it as a parameter; the caller
//! passes the `defs` predicate, and the engine's per-constructor equation
//! conjunction must β-match `pred recursor`. The caller also supplies the
//! **step variables** (one free variable per constructor — `nat`'s `z`, `f`)
//! that the recursor abstracts and the equations generalise over.
//!
//! Constructors with **any** number of recursive arguments are handled (as
//! in [`super::determinacy`]): the `k ≥ 1` arm of `rec_equation` feeds graph
//! introduction the conjunction of the per-argument `Graph rⱼ (rec rⱼ)`
//! memberships and bridges every inner `rec rⱼ` to its applied form. The
//! nullary and single-argument shapes are the `k = 0` / `k = 1` instances.

use covalence_core::{Error, Result, Term, Type, subst};
use covalence_hol_eval::EvalThm as Thm;

use super::data::Inductive;
use super::determinacy::graph_det;
use super::existence::{graph_intro, graph_total};
use super::graph::{self, CtorInstance};
use super::sig::InductiveSig;
use super::util::var_name;
use crate::init::eq::{beta_expand, beta_nf, beta_reduce};
use crate::init::ext::TermExt;
use crate::init::logic::{exists_elim, exists_intro};

/// `λa. Graph steps t a` — the predicate the recursor chooses from at `t`.
fn eps_pred(sig: &InductiveSig, steps: &[Term], beta: &Type, t: &Term) -> Result<Term> {
    let a = Term::free("__a", beta.clone());
    let body = graph::graph(sig, steps, beta, t.clone(), a)?;
    Ok(Term::abs(beta.clone(), subst::close(&body, "__a")))
}

/// `ε a. Graph steps t a` — the chosen value at `t`.
fn rec_at(sig: &InductiveSig, steps: &[Term], beta: &Type, t: &Term) -> Result<Term> {
    Ok(Term::app(
        Term::select_op(beta.clone()),
        eps_pred(sig, steps, beta, t)?,
    ))
}

/// The closed recursor `λ(steps). λt. ε a. Graph steps t a`.
fn recursor_term(sig: &InductiveSig, steps: &[Term], beta: &Type) -> Result<Term> {
    let t = Term::free("__t", sig.ty.clone());
    let body = rec_at(sig, steps, beta, &t)?;
    let mut term = Term::abs(sig.ty.clone(), subst::close(&body, "__t"));
    for sv in steps.iter().rev() {
        term = Term::abs(sv.type_of()?, subst::close(&term, var_name(sv)));
    }
    Ok(term)
}

/// `recursor (steps) t` — the recursor applied to its step terms and `t`.
fn rec_app(recursor: &Term, steps: &[Term], t: &Term) -> Result<Term> {
    let mut r = recursor.clone();
    for sv in steps {
        r = r.apply(sv.clone())?;
    }
    r.apply(t.clone())
}

/// `⊢ Graph steps t (ε a. Graph steps t a)`, for free `t` — the chosen
/// value really is in the graph. From totality + Hilbert choice. Generic.
pub fn graph_at_rec<I: Inductive>(theory: &I, steps: &[Term], beta: &Type) -> Result<Thm> {
    let sig = theory.sig();
    let t = Term::free("__t", sig.ty.clone());
    let pred = eps_pred(sig, steps, beta, &t)?;
    let exists_t = beta_reduce(graph_total(theory, steps, beta)?.all_elim(t.clone())?)?;
    let choose = Thm::select_ax(pred.clone(), Term::free("__a", beta.clone()))?
        .all_intro("__a", beta.clone())?;
    let eps = Term::app(Term::select_op(beta.clone()), pred.clone());
    beta_reduce(exists_elim(exists_t, Term::app(pred, eps), choose)?)
}

/// The defining equation for constructor `i`, as a hypothesis-free theorem:
/// `⊢ ∀x⃗. rec (Cᵢ x⃗) = fᵢ x⃗ (rec r⃗)`.
///
/// `g_at_rec` is the shared `⊢ Graph __t (rec __t)` (free `__t`) — independent
/// of the constructor, so it is built once by [`recursion_theorem`] and only
/// `inst`-specialised here. `det` memoises the equally-shared determinacy
/// theorem ([`graph_det`]) across the non-nullary constructors that need it.
fn rec_equation<I: Inductive>(
    theory: &I,
    recursor: &Term,
    steps: &[Term],
    beta: &Type,
    i: usize,
    g_at_rec: &Thm,
    det: &mut Option<Thm>,
) -> Result<Thm> {
    let sig = theory.sig();
    let inst: CtorInstance = graph::ctor_instance(&sig.ty, beta, &sig.ctors[i], &steps[i])?;
    let rec_head = rec_at(sig, steps, beta, &inst.head)?;
    let g_at_head = g_at_rec.clone().inst("__t", inst.head.clone())?;

    let body = if inst.rec_pairs.is_empty() {
        // Nullary: invert `Graph (Cᵢ) (rec Cᵢ)` to `rec Cᵢ = fᵢ`.
        let inv = super::uniqueness::graph_inv(theory, steps, beta, i)?
            .inst("a", rec_head.clone())?
            .imp_elim(g_at_head)?; // ⊢ rec Cᵢ = fᵢ
        // Bridge `rec_app (Cᵢ) = rec Cᵢ`, then transitivity.
        beta_nf(rec_app(recursor, steps, &inst.head)?).trans(inv)?
    } else {
        // `k ≥ 1` recursive arguments: `rec (Cᵢ x⃗) = fᵢ x⃗ (rec r⃗)`. Each
        // recursive sub-term `rⱼ` contributes its chosen value `rec rⱼ` and
        // the membership `Graph rⱼ (rec rⱼ)`; graph introduction (fed their
        // conjunction) places `fᵢ x⃗ (rec r⃗)` in the graph, and determinacy
        // forces the recursor's chosen value equal to it.
        let rec_rs: Vec<Term> = inst
            .rec_pairs
            .iter()
            .map(|(r, _)| rec_at(sig, steps, beta, r))
            .collect::<Result<_>>()?;
        let g_at_rs: Vec<Thm> = inst
            .rec_pairs
            .iter()
            .map(|(r, _)| g_at_rec.clone().inst("__t", r.clone()))
            .collect::<Result<_>>()?;

        // `graph_intro(i)` with each image var `bⱼ := rec rⱼ`, antecedent
        // (the right-associated `⋀ⱼ Graph rⱼ (rec rⱼ)`) discharged.
        let mut g_intro = graph_intro(sig, steps, beta, i)?;
        for ((_, img), rec_r) in inst.rec_pairs.iter().zip(&rec_rs) {
            g_intro = g_intro.inst(var_name(img), rec_r.clone())?;
        }
        g_intro = g_intro.imp_elim(super::util::and_all(&g_at_rs)?)?;

        // The step value `fᵢ x⃗ (rec r⃗)`: `inst.value` with every image var
        // replaced by its `rec rⱼ`. (Not extractable from `g_intro`'s
        // conclusion, the whole `∀G. …` graph predicate.)
        let mut value = inst.value.clone();
        for ((_, img), rec_r) in inst.rec_pairs.iter().zip(&rec_rs) {
            value = subst::open(&subst::close(&value, var_name(img)), rec_r);
        }

        // Determinacy: `rec (Cᵢ x⃗) = fᵢ x⃗ (rec r⃗)`. The determinacy theorem is
        // constructor-independent — build it once and reuse across constructors.
        let det_thm = match det {
            Some(d) => d.clone(),
            None => {
                let d = graph_det(theory, steps, beta)?;
                *det = Some(d.clone());
                d
            }
        };
        let det_eq = beta_reduce(det_thm.all_elim(inst.head.clone())?)?
            .all_elim(rec_head.clone())?
            .all_elim(value.clone())?
            .imp_elim(g_at_head)?
            .imp_elim(g_intro)?;

        // Bridge each inner `rec rⱼ` (a β-reduct ε-term) to the applied
        // `rec_app rⱼ`, by rewriting `rec rⱼ ↦ rec_app rⱼ` in the RHS.
        let mut bridged = beta_nf(rec_app(recursor, steps, &inst.head)?).trans(det_eq)?;
        for (r, _) in &inst.rec_pairs {
            // ⊢ rec rⱼ = rec_app rⱼ  (rec_app β-reduces to rec rⱼ).
            let bridge = beta_nf(rec_app(recursor, steps, r)?).sym()?;
            let rhs = bridged
                .concl()
                .as_eq()
                .ok_or(Error::NotAnEquation)?
                .1
                .clone();
            bridged = bridged.trans(rhs.rw_all(&bridge)?)?;
        }
        bridged
    };

    // ∀-close the constructor's arguments.
    let mut t = body;
    for arg in inst.args.iter().rev() {
        t = t.all_intro(var_name(arg), arg.type_of()?)?;
    }
    Ok(t)
}

/// The recursor term and its per-constructor defining equations, **without**
/// the `∃`/`P_rec` packaging — the bundle-shaped engine exit used by the
/// inductive-types-API backends (`carved`), which want equations for a
/// *concrete* recursor term rather than a `defs`-catalogue transfer.
///
/// Returns `(recursor, eqs)` where `recursor` is the closed
/// `λ(steps). λt. ε a. Graph steps t a` (abstracting the given `step_vars`
/// in order) and `eqs[i] : ⊢ ∀x⃗. recursor s⃗ (Cᵢ x⃗) = fᵢ x⃗ (rec r⃗)` — the
/// **paramorphic** equation for constructor `i`, with the `step_vars` still
/// free (callers `inst` them at concrete steps).
pub fn recursion_equations<I: Inductive>(
    theory: &I,
    step_vars: &[Term],
    beta: &Type,
) -> Result<(Term, Vec<Thm>)> {
    let sig = theory.sig();
    let recursor = recursor_term(sig, step_vars, beta)?;
    let g_at_rec = graph_at_rec(theory, step_vars, beta)?;
    let mut det: Option<Thm> = None;
    let eqs: Vec<Thm> = (0..sig.arity())
        .map(|i| rec_equation(theory, &recursor, step_vars, beta, i, &g_at_rec, &mut det))
        .collect::<Result<_>>()?;
    Ok((recursor, eqs))
}

/// `⊢ ∃rec. P_rec rec` — **the recursion theorem**. `step_vars` are the free
/// variables the recursor abstracts (one per constructor); `pred` is the
/// recursor predicate from the `defs` catalogue (see the [module docs](self)).
pub fn recursion_theorem<I: Inductive>(
    theory: &I,
    step_vars: &[Term],
    beta: &Type,
    pred: &Term,
) -> Result<Thm> {
    let sig = theory.sig();
    let recursor = recursor_term(sig, step_vars, beta)?;

    // `⊢ Graph __t (rec __t)` (free `__t`) and the determinacy theorem are
    // constructor-independent. Build the graph membership once here (each
    // `rec_equation` only `inst`-specialises it, instead of re-running the
    // expensive `graph_total` existence proof per constructor *and* per
    // recursive argument); determinacy is memoised lazily across the
    // constructors that need it.
    let g_at_rec = graph_at_rec(theory, step_vars, beta)?;
    let mut det: Option<Thm> = None;

    // The conjunction of per-constructor equations, generalised over the
    // step variables.
    let eqs: Vec<Thm> = (0..sig.arity())
        .map(|i| rec_equation(theory, &recursor, step_vars, beta, i, &g_at_rec, &mut det))
        .collect::<Result<_>>()?;
    let mut body = eqs
        .last()
        .cloned()
        .ok_or_else(|| Error::ConnectiveRule("inductive::recursor: no constructors".into()))?;
    for eq in eqs[..eqs.len() - 1].iter().rev() {
        body = eq.clone().and_intro(body)?;
    }
    for sv in step_vars.iter().rev() {
        body = body.all_intro(var_name(sv), sv.type_of()?)?;
    }

    // `pred recursor` fires its single outer `λr` redex to `body`'s
    // conclusion (the inner `recursor …` applications stay un-reduced, as in
    // the equations); ∃-introduce.
    let at = beta_expand(pred, recursor.clone(), body)?;
    exists_intro(pred.clone(), recursor, at)
}
