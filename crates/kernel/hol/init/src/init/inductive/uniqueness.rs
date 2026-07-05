//! **Uniqueness**, part 1: the per-constructor **inversion** lemmas — the
//! recursion graph relates `Cᵢ x⃗` to *at most one* shape of value.
//!
//! For constructor `Cᵢ` with arguments `x⃗` (recursive ones `r⃗`),
//!
//! ```text
//!   graph_inv :  ⊢ Graph (Cᵢ x⃗) a ⟹ ∃b⃗. (⋀ⱼ Graph rⱼ bⱼ) ∧ a = fᵢ x⃗ b⃗
//! ```
//!
//! degenerating, for a non-recursive constructor, to `⊢ Graph (Cᵢ x⃗) a ⟹
//! a = fᵢ x⃗`. This generalises `nat`'s hand-written `graph_base_inv`
//! (nullary) and `graph_step_inv` (recursive).
//!
//! The proof instantiates the graph's `∀G` at a **determinizing relation**
//!
//! ```text
//!   Good ≜ λk c. Graph k c ∧ wit k c
//!   wit  ≜ λk c. ∀x⃗. (k = Cᵢ x⃗) ⟹ ∃b⃗. (⋀ⱼ Graph rⱼ bⱼ) ∧ c = fᵢ x⃗ b⃗
//! ```
//!
//! `Good` is closed under the recursion rules (`good_closed`) — its `wit`
//! conjunct is discharged at every *other* constructor by **distinctness**
//! and at `Cᵢ` itself by **injectivity** (both from the [`Inductive`]
//! trait). Instantiating the graph at `Good` and reading off `wit` at the
//! actual arguments gives the inversion.
//!
//! ## Naming discipline
//!
//! `wit`'s bound variables (`x⃗`, `b⃗`) are named with the `_wx_` / `_wb_`
//! prefixes (`WX` / `WB`) so they are **disjoint** from a constructor's
//! own argument / image binders (`m`, `b`, …). Without that, building
//! `Good`'s closure clause at `Cᵢ` — where the clause's arguments and
//! `wit`'s bound arguments would share names — captures the wrong
//! variables. (`nat`'s hand proof achieves the same by using `j`/`d` for
//! `wit` against `m`/`b` for the clause.)
//!
//! Determinacy (`∀t a b. Graph t a ⟹ Graph t b ⟹ a = b`) builds on these
//! in [`super::determinacy`]; only the ε-assembly remains in
//! [`crate::init::recursion`] (see `SKELETONS.md`).

use covalence_core::{Result, Term, Thm, Type, subst};

use super::data::Inductive;
use super::graph;
use super::sig::InductiveSig;
use super::util::{and_all, discharge_conj, project, var_name};
use crate::init::eq::{beta_expand, beta_nf_concl, beta_nf_expand};
use crate::init::ext::{TermExt, ThmExt};
use crate::init::logic::exists_intro;

/// Binder prefix for `wit`'s universally-quantified arguments `x⃗`.
const WX: &str = "_wx_";
/// Binder prefix for `wit`'s existentially-quantified images `b⃗`.
const WB: &str = "_wb_";

/// One constructor materialised over freshly-prefixed binders — the
/// `wit`-side analogue of [`graph::CtorInstance`], named disjointly from
/// the clause's own variables.
struct Inst {
    /// The argument variables `x⃗`.
    args: Vec<Term>,
    /// `Cᵢ x⃗`.
    head: Term,
    /// The recursive `(sub-term, image)` pairs `(rⱼ, bⱼ)`.
    rec_pairs: Vec<(Term, Term)>,
}

/// Materialise constructor `i` with binder names `{arg_prefix}{name}` /
/// `{img_prefix}{image}`.
fn instance(
    sig: &InductiveSig,
    beta: &Type,
    i: usize,
    arg_prefix: &str,
    img_prefix: &str,
) -> Result<Inst> {
    let mut args = Vec::new();
    let mut rec_pairs = Vec::new();
    let mut head = sig.ctors[i].ctor.clone();
    for arg in &sig.ctors[i].args {
        let v = Term::free(format!("{arg_prefix}{}", arg.name()), arg.ty(&sig.ty));
        head = head.apply(v.clone())?;
        args.push(v.clone());
        if let Some(image) = arg.image() {
            rec_pairs.push((v, Term::free(format!("{img_prefix}{image}"), beta.clone())));
        }
    }
    Ok(Inst {
        args,
        head,
        rec_pairs,
    })
}

/// `fᵢ x⃗ b⃗` for the given argument and image terms.
fn step_value(steps: &[Term], i: usize, args: &[Term], images: &[Term]) -> Result<Term> {
    args.iter()
        .chain(images)
        .try_fold(steps[i].clone(), |acc, x| acc.apply(x.clone()))
}

// ============================================================================
// `wit` / `Good` term builders
// ============================================================================

/// `wit`'s existential `∃b⃗. (⋀ⱼ Graph xₗ bₗ) ∧ (c = fᵢ x⃗ b⃗)`, over the
/// arguments `x⃗` of `inst` and a fixed value `c`. Bound images use the
/// [`WB`] prefix.
fn wit_existential(
    sig: &InductiveSig,
    steps: &[Term],
    beta: &Type,
    i: usize,
    inst: &Inst,
    c: &Term,
) -> Result<Term> {
    let imgs: Vec<Term> = inst.rec_pairs.iter().map(|(_, b)| b.clone()).collect();
    let value = step_value(steps, i, &inst.args, &imgs)?;
    let val_eq = c.clone().equals(value)?;
    let inner = if inst.rec_pairs.is_empty() {
        val_eq
    } else {
        let graphs: Vec<Term> = inst
            .rec_pairs
            .iter()
            .map(|(sub, img)| graph::graph(sig, steps, beta, sub.clone(), img.clone()))
            .collect::<Result<_>>()?;
        graph::conj(&graphs)?.and(val_eq)?
    };
    let mut ex = inner;
    for (_, img) in inst.rec_pairs.iter().rev() {
        ex = ex.exists(var_name(img), beta.clone())?;
    }
    Ok(ex)
}

/// `wit_i k c ≜ ∀x⃗. (k = Cᵢ x⃗) ⟹ <wit existential>`.
fn wit_term(
    sig: &InductiveSig,
    steps: &[Term],
    beta: &Type,
    i: usize,
    k: &Term,
    c: &Term,
) -> Result<Term> {
    let inst = instance(sig, beta, i, WX, WB)?;
    let eq = k.clone().equals(inst.head.clone())?;
    let ex = wit_existential(sig, steps, beta, i, &inst, c)?;
    let mut all = eq.imp(ex)?;
    for arg in inst.args.iter().rev() {
        all = all.forall(var_name(arg), arg.type_of()?)?;
    }
    Ok(all)
}

/// `Good_i ≜ λk c. Graph k c ∧ wit_i k c`.
fn good_term(sig: &InductiveSig, steps: &[Term], beta: &Type, i: usize) -> Result<Term> {
    let k = Term::free("__k", sig.ty.clone());
    let c = Term::free("__c", beta.clone());
    let body = graph::graph(sig, steps, beta, k.clone(), c.clone())?
        .and(wit_term(sig, steps, beta, i, &k, &c)?)?;
    let lam_c = Term::abs(beta.clone(), subst::close(&body, "__c"));
    Ok(Term::abs(sig.ty.clone(), subst::close(&lam_c, "__k")))
}

// ============================================================================
// `Good_i` is closed
// ============================================================================

/// The `wit_i` conjunct of `Good_i`'s clause at a **different** constructor
/// `j ≠ i`: `⊢ wit_i (Cⱼ y⃗) (fⱼ y⃗ d⃗)`, vacuous because `Cⱼ y⃗ = Cᵢ x⃗` is
/// impossible (distinctness).
fn wit_vacuous<I: Inductive>(
    theory: &I,
    steps: &[Term],
    beta: &Type,
    i: usize,
    j: usize,
    value_j: &Term,
) -> Result<Thm> {
    let sig = theory.sig();
    let xi = instance(sig, beta, i, WX, WB)?; // Cᵢ x⃗
    let yj = instance(sig, beta, j, "", "")?; // Cⱼ y⃗ (default names)
    let ex_body = wit_existential(sig, steps, beta, i, &xi, value_j)?;

    let eq = yj.head.clone().equals(xi.head.clone())?; // Cⱼ y⃗ = Cᵢ x⃗
    let contra = theory
        .distinct(j, i, &yj.args, &xi.args)?
        .imp_elim(Thm::assume(eq.clone())?)?;
    let mut t = contra.false_elim(ex_body)?.imp_intro(&eq)?;
    for arg in xi.args.iter().rev() {
        t = t.all_intro(var_name(arg), arg.type_of()?)?;
    }
    Ok(t)
}

/// The `wit_i` conjunct of `Good_i`'s clause at `Cᵢ` itself: `⊢ wit_i
/// (Cᵢ y⃗) (fᵢ y⃗ d⃗)`, under the antecedents `Good_i rₗ dₗ`. Injectivity
/// turns `Cᵢ y⃗ = Cᵢ x⃗` into `y⃗ = x⃗`; the witness is `b⃗ := d⃗`.
fn wit_match<I: Inductive>(theory: &I, steps: &[Term], beta: &Type, i: usize) -> Result<Thm> {
    let sig = theory.sig();
    let good = good_term(sig, steps, beta, i)?;
    let y = instance(sig, beta, i, "", "")?; // Cᵢ y⃗, images d⃗ (default names)
    let x = instance(sig, beta, i, WX, WB)?; // Cᵢ x⃗ (wit's ∀-bound)
    let d_imgs: Vec<Term> = y.rec_pairs.iter().map(|(_, d)| d.clone()).collect();
    let value_y = step_value(steps, i, &y.args, &d_imgs)?; // fᵢ y⃗ d⃗ (the fixed `c`)

    // Injectivity: `⋀ₖ yₖ = xₖ`, then each component. A nullary
    // constructor has no arguments — `Cᵢ = Cᵢ` is componentless and there
    // is nothing to rewrite.
    let eq = y.head.clone().equals(x.head.clone())?;
    let comps: Vec<Thm> = if y.args.is_empty() {
        Vec::new()
    } else {
        let inj = theory
            .injective(i, &y.args, &x.args)?
            .imp_elim(Thm::assume(eq.clone())?)?;
        (0..y.args.len())
            .map(|k| project(inj.clone(), k, y.args.len()))
            .collect::<Result<_>>()?
    };

    // Existential body, witnessing `b⃗ := d⃗`: each `Graph xₗ dₗ` (rewrite
    // `Graph yₗ dₗ`, from `Good_i yₗ dₗ`, by `y⃗ = x⃗`), plus `fᵢ y⃗ d⃗ =
    // fᵢ x⃗ d⃗` by congruence.
    let mut graph_xs: Vec<Thm> = Vec::new();
    let mut good_hyps: Vec<Term> = Vec::new();
    for (sub_y, img) in &y.rec_pairs {
        let good_app = apply2(&good, sub_y, img)?;
        let graph_y = beta_nf_concl(Thm::assume(good_app.clone())?)?.and_elim_l()?;
        good_hyps.push(good_app);
        graph_xs.push(rewrite_all(graph_y, &comps)?); // ⊢ Graph xₗ dₗ
    }
    let f_eq = rewrite_term_all(&value_y, &comps)?; // ⊢ fᵢ y⃗ d⃗ = fᵢ x⃗ d⃗
    let body_thm = {
        let mut all = graph_xs;
        all.push(f_eq);
        and_all(&all)?
    };

    // `∃b⃗. <body>`, witnessing `b⃗ := d⃗`: drive `∃`-introduction over
    // `wit`'s existential structure (its `_wb_` binders keep the fixed `c`
    // intact, unlike abstracting the proof's conclusion would).
    let ex_full = wit_existential(sig, steps, beta, i, &x, &value_y)?;
    let ex = intro_exists_rec(&ex_full, &d_imgs, body_thm)?;

    // `(Cᵢ y⃗ = Cᵢ x⃗) ⟹ ∃b⃗. …`, ∀-close `x⃗`, leaving `{Good_i yₗ dₗ}`.
    let mut t = ex.imp_intro(&eq)?;
    for arg in x.args.iter().rev() {
        t = t.all_intro(var_name(arg), arg.type_of()?)?;
    }
    let _ = good_hyps;
    Ok(t)
}

/// `Good_i`'s closure clause at constructor `j`:
/// `⊢ ∀y⃗ d⃗. (⋀ₗ Good_i rₗ dₗ) ⟹ Good_i (Cⱼ y⃗) (fⱼ y⃗ d⃗)`.
fn good_clause<I: Inductive>(
    theory: &I,
    steps: &[Term],
    beta: &Type,
    i: usize,
    j: usize,
    good: &Term,
) -> Result<Thm> {
    let sig = theory.sig();
    let inst_j = graph::ctor_instance(&sig.ty, beta, &sig.ctors[j], &steps[j])?;

    // Graph conjunct: `Graph (Cⱼ y⃗)(fⱼ y⃗ d⃗)` from `graph_intro_j` fed the
    // `Graph rₗ dₗ` extracted from each antecedent `Good_i rₗ dₗ`.
    let good_apps: Vec<Term> = inst_j
        .rec_pairs
        .iter()
        .map(|(sub, img)| apply2(good, sub, img))
        .collect::<Result<_>>()?;
    let graph_recs: Vec<Thm> = good_apps
        .iter()
        .map(|app| beta_nf_concl(Thm::assume(app.clone())?)?.and_elim_l())
        .collect::<Result<_>>()?;
    let intro = super::existence::graph_intro(sig, steps, beta, j)?;
    let graph_conj = if graph_recs.is_empty() {
        intro
    } else {
        intro.imp_elim(and_all(&graph_recs)?)?
    };

    // wit conjunct.
    let wit_conj = if j == i {
        wit_match(theory, steps, beta, i)?
    } else {
        wit_vacuous(theory, steps, beta, i, j, &inst_j.value)?
    };

    // `Good_i (Cⱼ y⃗)(fⱼ y⃗ d⃗)` = `Graph … ∧ wit_i …` (β-expanded), then
    // discharge the antecedents and ∀-close `y⃗ d⃗`.
    let reduced = graph_conj.and_intro(wit_conj)?;
    let good_app = apply2(good, &inst_j.head, &inst_j.value)?;
    let consequent = beta_nf_expand(good_app, reduced)?;
    let discharged = discharge_conj(consequent, &good_apps)?;

    let mut t = discharged;
    for (_, img) in inst_j.rec_pairs.iter().rev() {
        t = t.all_intro(var_name(img), beta.clone())?;
    }
    for arg in inst_j.args.iter().rev() {
        t = t.all_intro(var_name(arg), arg.type_of()?)?;
    }
    Ok(t)
}

/// `⊢ closed(steps, Good_i)`.
fn good_closed<I: Inductive>(theory: &I, steps: &[Term], beta: &Type, i: usize) -> Result<Thm> {
    let sig = theory.sig();
    let good = good_term(sig, steps, beta, i)?;
    let clauses: Vec<Thm> = (0..sig.arity())
        .map(|j| good_clause(theory, steps, beta, i, j, &good))
        .collect::<Result<_>>()?;
    and_all(&clauses)
}

// ============================================================================
// The inversion lemma
// ============================================================================

/// `⊢ Graph (Cᵢ x⃗) a ⟹ ∃b⃗. (⋀ⱼ Graph rⱼ bⱼ) ∧ a = fᵢ x⃗ b⃗` (the
/// existential / conjunction absent for a non-recursive constructor) — the
/// per-constructor inversion lemma. See the [module docs](self).
pub fn graph_inv<I: Inductive>(theory: &I, steps: &[Term], beta: &Type, i: usize) -> Result<Thm> {
    let sig = theory.sig();
    let inst = graph::ctor_instance(&sig.ty, beta, &sig.ctors[i], &steps[i])?;
    let a = Term::free("a", beta.clone());
    let good = good_term(sig, steps, beta, i)?;

    let gh = graph::graph(sig, steps, beta, inst.head.clone(), a.clone())?;
    // {GH} ⊢ Good_i (Cᵢ x⃗) a, β-reduce, take the `wit` conjunct.
    let good_at = Thm::assume(gh.clone())?
        .all_elim(good)?
        .imp_elim(good_closed(theory, steps, beta, i)?)?;
    let wit_at = beta_nf_concl(good_at)?.and_elim_r()?; // {GH} ⊢ wit_i (Cᵢ x⃗) a

    // Specialise `wit` at the actual args `x⃗` (none for a nullary
    // constructor), then discharge the antecedent `Cᵢ x⃗ = Cᵢ x⃗`.
    let mut spec = wit_at;
    for arg in &inst.args {
        spec = spec.all_elim(arg.clone())?;
    }
    let ex = spec.imp_elim(Thm::refl(inst.head.clone())?)?;
    ex.imp_intro(&gh)
}

// ============================================================================
// Small helpers
// ============================================================================

/// `g x y`.
fn apply2(g: &Term, x: &Term, y: &Term) -> Result<Term> {
    g.clone().apply(x.clone())?.apply(y.clone())
}

/// Drive a chain of `∃`-introductions over `ex_term = ∃b₀ … bₙ. P`,
/// supplying `witnesses` and ending at the proof `body` of
/// `P[b⃗ := witnesses]`. The `∃`-predicate at each layer is taken from
/// `ex_term`'s own structure (so a fixed value inside `P` is preserved,
/// not abstracted), recursing outermost image first.
fn intro_exists_rec(ex_term: &Term, witnesses: &[Term], body: Thm) -> Result<Thm> {
    let Some(w) = witnesses.first() else {
        return Ok(body); // no `∃` remains — `body` proves it directly
    };
    // `ex_term = exists[β] pred`; `pred` is this layer's `∃`-predicate.
    let pred = ex_term
        .as_app()
        .expect("wit existential is an application")
        .1
        .clone();
    let inner = if witnesses.len() == 1 {
        body
    } else {
        // The inner `∃…` term is `pred w` β-reduced; recurse into it.
        let bc: Thm = Thm::beta_conv(Term::app(pred.clone(), w.clone()))?;
        let inner_ex = bc.concl().as_eq().unwrap().1.clone();
        intro_exists_rec(&inner_ex, &witnesses[1..], body)?
    };
    let at = beta_expand(&pred, w.clone(), inner)?;
    exists_intro(pred, w.clone(), at)
}

/// Rewrite a theorem's conclusion by every equation in `eqs` (in order).
fn rewrite_all(thm: Thm, eqs: &[Thm]) -> Result<Thm> {
    eqs.iter().try_fold(thm, |acc, eq| acc.rewrite(eq))
}

/// `⊢ t = t'` where `t'` is `t` rewritten by every equation in `eqs`.
fn rewrite_term_all(t: &Term, eqs: &[Thm]) -> Result<Thm> {
    let mut acc = Thm::refl(t.clone())?;
    for eq in eqs {
        let rhs = acc
            .concl()
            .as_eq()
            .expect("refl/rewrite yields eq")
            .1
            .clone();
        acc = acc.trans(rhs.rw_all(eq)?)?;
    }
    Ok(acc)
}
