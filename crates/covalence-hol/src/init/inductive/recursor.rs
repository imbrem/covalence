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
//! Only the nullary and single-recursive-argument constructor shapes are
//! handled (as in [`super::determinacy`]); see `SKELETONS.md`.

use covalence_core::{Error, Result, Term, Thm, Type, subst};

use super::data::Inductive;
use super::determinacy::graph_det;
use super::existence::{graph_intro, graph_total};
use super::graph::{self, CtorInstance};
use super::sig::InductiveSig;
use super::util::var_name;
use crate::init::eq::{beta_expand, beta_nf, beta_reduce};
use crate::init::ext::{TermExt, ThmExt};
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
fn rec_equation<I: Inductive>(
    theory: &I,
    recursor: &Term,
    steps: &[Term],
    beta: &Type,
    i: usize,
) -> Result<Thm> {
    let sig = theory.sig();
    let inst: CtorInstance = graph::ctor_instance(&sig.ty, beta, &sig.ctors[i], &steps[i])?;
    let rec_head = rec_at(sig, steps, beta, &inst.head)?;
    let g_at_head = graph_at_rec(theory, steps, beta)?.inst("__t", inst.head.clone())?;

    let body = match inst.rec_pairs.as_slice() {
        // Nullary: invert `Graph (Cᵢ) (rec Cᵢ)` to `rec Cᵢ = fᵢ`.
        [] => {
            let inv = super::uniqueness::graph_inv(theory, steps, beta, i)?
                .inst("a", rec_head.clone())?
                .imp_elim(g_at_head)?; // ⊢ rec Cᵢ = fᵢ
            // Bridge `rec_app (Cᵢ) = rec Cᵢ`, then transitivity.
            beta_nf(rec_app(recursor, steps, &inst.head)?).trans(inv)?
        }
        // One recursive argument: `rec (Cᵢ x⃗) = fᵢ x⃗ (rec r)`.
        [(rec, _)] => {
            let rec_r = rec_at(sig, steps, beta, rec)?;
            let g_at_r = graph_at_rec(theory, steps, beta)?.inst("__t", rec.clone())?;
            // `Graph (Cᵢ x⃗) (fᵢ x⃗ (rec r))` via graph introduction.
            let img = inst.rec_pairs[0].1.clone();
            let g_intro = graph_intro(sig, steps, beta, i)?
                .inst(var_name(&img), rec_r.clone())?
                .imp_elim(g_at_r)?;
            // The step value `fᵢ x⃗ (rec r)`: `inst.value` with its image var
            // replaced by `rec r`. (Not extractable from `g_intro`'s
            // conclusion, which is the whole `∀G. …` graph predicate.)
            let value = subst::open(&subst::close(&inst.value, var_name(&img)), &rec_r);
            // Determinacy: `rec (Cᵢ x⃗) = fᵢ x⃗ (rec r)`.
            let det_eq = beta_reduce(graph_det(theory, steps, beta)?.all_elim(inst.head.clone())?)?
                .all_elim(rec_head.clone())?
                .all_elim(value.clone())?
                .imp_elim(g_at_head)?
                .imp_elim(g_intro)?;
            // Bridge the inner `rec r` (β-reduct) to the applied `rec_app r`.
            let f_part = value.as_app().ok_or(Error::NotAnEquation)?.0.clone(); // fᵢ x⃗
            let f_cong = beta_nf(rec_app(recursor, steps, rec)?)
                .sym()?
                .cong_arg(f_part)?;
            beta_nf(rec_app(recursor, steps, &inst.head)?)
                .trans(det_eq)?
                .trans(f_cong)?
        }
        _ => {
            return Err(Error::ConnectiveRule(
                "inductive::recursor: constructors with ≥2 recursive arguments not yet supported"
                    .into(),
            ));
        }
    };

    // ∀-close the constructor's arguments.
    let mut t = body;
    for arg in inst.args.iter().rev() {
        t = t.all_intro(var_name(arg), arg.type_of()?)?;
    }
    Ok(t)
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

    // The conjunction of per-constructor equations, generalised over the
    // step variables.
    let eqs: Vec<Thm> = (0..sig.arity())
        .map(|i| rec_equation(theory, &recursor, step_vars, beta, i))
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
