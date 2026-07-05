//! `prod` theorems: the `defs/prod.rs` catalogue re-exported, plus the
//! **computational theory of products** — the `abs`/`rep` seam, the
//! projection clauses, surjective pairing, and pair injectivity. Same
//! abstraction-barrier shape as [`init::set`] / [`init::list`].
//!
//! [`init::set`]: mod@crate::init::set
//! [`init::list`]: mod@crate::init::list
//!
//! ## What `prod α β` is
//!
//! `prod α β := rel α β where (∃a b. R = λx y. x = a ∧ y = b)` — the
//! **subtype** of the relation type `α → β → bool` carved by "`R` is a
//! singleton relation". The constructor and projections funnel through
//! the kernel coercions `abs : (α → β → bool) → prod α β` and
//! `rep : prod α β → (α → β → bool)`:
//!
//! ```text
//!   pair a b ≔ abs (λx y. x = a ∧ y = b)
//!   fst p    ≔ ε(λa. ∃b. rep p = λx y. x = a ∧ y = b)
//!   snd p    ≔ ε(λb. ∃a. rep p = λx y. x = a ∧ y = b)
//! ```
//!
//! **Downstream proofs must not see that** — they reason through the
//! clauses exposed here ([`fst_pair`], [`snd_pair`], [`surjective_pairing`],
//! [`pair_inj`]), never `abs` / `rep`.
//!
//! ## The singleton gate
//!
//! `prod` is a genuine subtype, so the carrier-side round-trip
//! [`Thm::spec_rep_abs_fwd`] is *conditional* on the selector predicate
//! `prod_predicate R = ∃a b. R = λx y. x = a ∧ y = b`. For `pair a b`
//! that relation is `λx y. x = a ∧ y = b`, which is a singleton by its
//! own definition (`singleton_pred`) — so the seam [`rep_pair`] is
//! reachable with no further machinery.
//!
//! ## No postulates
//!
//! Everything bottoms out in the kernel's witness-free subtype laws plus
//! the choice axiom ([`Thm::select_ax`]); every theorem here is genuine
//! (hypothesis- and oracle-free). The key engine is `determines`: the
//! singleton-relation equation `λx y. x=a ∧ y=b = λx y. x=c ∧ y=d` pins
//! `a = c` and `b = d` (apply both relations to `a`, `b` and read off the
//! conjuncts), which both projections and injectivity ride on.

use covalence_core::{Error, Result, Term, Thm, Type};

use crate::init::ext::{TermExt, ThmExt};
use crate::init::logic::{exists_elim, exists_intro};

// ============================================================================
// The `.cov` proof-script layer for `prod`.
//
// `prod_env()` exports the seam lemmas as Rust-proved GIVENs (rep_pair,
// fst_pair, snd_pair, surjective_pairing) — their proofs use spec_abs/spec_rep
// and select_ax which are NOT expressible in the proof language.
//
// On top of those givens, `prod.cov` proves `pair_inj` using only the
// language-available rules: assume, cong-arg, sym, trans, and-intro, imp-intro.
// ============================================================================

/// The `prod` seam environment: projection lemmas as Rust-proved givens,
/// plus the typed constructors registered as `ConstDef::Op`s so the
/// inference engine can build `prod 'a 'b`-typed terms.
pub fn prod_env() -> crate::script::Env {
    let alpha = Type::tfree("a");
    let beta = Type::tfree("b");
    let mut e = crate::script::Env::empty();

    // -- operators (needed so the type-inferencer can type `pair a b` etc.) --
    //
    // Registered as `ConstDef::Poly`: each use site instantiates the free
    // type variables (`'a`/`'b`) with fresh metavariables, so `pair`/`fst`/
    // `snd` can appear at several type instances within one term.
    use crate::script::ConstDef;
    e.define_const("pair", ConstDef::Poly(pair(alpha.clone(), beta.clone())));
    e.define_const("fst", ConstDef::Poly(fst(alpha.clone(), beta.clone())));
    e.define_const("snd", ConstDef::Poly(snd(alpha.clone(), beta.clone())));

    // -- seam givens (Rust-proved, not expressible in the language) --

    // ⊢ ∀(a:'a). ∀(b:'b). rep (pair a b) = λx y. x=a ∧ y=b
    let a = Term::free("a", alpha.clone());
    let b = Term::free("b", beta.clone());
    let rp = rep_pair(&alpha, &beta, &a, &b)
        .and_then(|t| t.all_intro("b", beta.clone()))
        .and_then(|t| t.all_intro("a", alpha.clone()))
        .expect("prod_env: rep.pair");
    e.define_lemma("rep.pair", rp);

    // ⊢ ∀(a:'a). ∀(b:'b). fst (pair a b) = a
    let fp = fst_pair(&alpha, &beta, &a, &b)
        .and_then(|t| t.all_intro("b", beta.clone()))
        .and_then(|t| t.all_intro("a", alpha.clone()))
        .expect("prod_env: fst.pair");
    e.define_lemma("fst.pair", fp);

    // ⊢ ∀(a:'a). ∀(b:'b). snd (pair a b) = b
    let sp = snd_pair(&alpha, &beta, &a, &b)
        .and_then(|t| t.all_intro("b", beta.clone()))
        .and_then(|t| t.all_intro("a", alpha.clone()))
        .expect("prod_env: snd.pair");
    e.define_lemma("snd.pair", sp);

    // ⊢ ∀p : prod 'a 'b. pair (fst p) (snd p) = p
    let p = Term::free("p", covalence_core::defs::prod(alpha.clone(), beta.clone()));
    let surj = surjective_pairing(&alpha, &beta, &p)
        .and_then(|t| t.all_intro("p", covalence_core::defs::prod(alpha.clone(), beta.clone())))
        .expect("prod_env: surjective.pairing");
    e.define_lemma("surjective.pairing", surj);

    e
}

crate::cov_theory! {
    /// `prod` theorems: `pair_inj`, ported from Rust to `prod.cov`.
    pub mod cov from "prod.cov" {
        import "core"    = crate::script::Env::core();
        import "logic"   = crate::init::logic::cov::env();
        import "prodprim" = crate::init::prod::prod_env();
        "pair.inj" => pub fn pair_inj_cov;
    }
}

#[cfg(test)]
mod cov_tests {
    use super::*;

    /// `pair_inj` from `prod.cov` must have the same conclusion as the
    /// hand-written Rust `pair_inj`.
    #[test]
    fn pair_inj_cov_matches_rust() {
        let alpha = Type::tfree("a");
        let beta = Type::tfree("b");
        let a = Term::free("a", alpha.clone());
        let b = Term::free("b", beta.clone());
        let c = Term::free("c", alpha.clone());
        let d = Term::free("d", beta.clone());
        let rust_thm = pair_inj(&alpha, &beta, &a, &b, &c, &d).expect("pair.inj");
        let cov_thm = cov::pair_inj_cov();
        assert_eq!(
            cov_thm.concl(),
            rust_thm.concl(),
            "pair.inj from prod.cov must match the Rust proof"
        );
    }
}

// Re-export the `defs/prod.rs` term catalogue (the `*_spec` handles stay
// in `covalence_core::defs`, reached via the blanket re-export there).
pub use covalence_core::defs::{fst, pair, prod, snd};

use covalence_core::defs::{fst_spec, pair_spec, prod_spec, snd_spec};

// ============================================================================
// Term helpers (private — the public surface is the clauses).
// ============================================================================

/// `pair[α,β] a b : prod α β` — the constructor as a builder.
fn pair_at(alpha: &Type, beta: &Type, a: &Term, b: &Term) -> Term {
    Term::app(
        Term::app(pair(alpha.clone(), beta.clone()), a.clone()),
        b.clone(),
    )
}

/// `rep : prod α β → (α → β → bool)` — the raw carrier coercion.
fn rep(alpha: &Type, beta: &Type) -> Term {
    Term::spec_rep(prod_spec(), vec![alpha.clone(), beta.clone()])
}

// ============================================================================
// THE SEAM — the only code aware that `prod` is a subtype of the relation
// type carved by the singleton predicate.
// ============================================================================

/// `⊢ prod_predicate (λx y. x = a ∧ y = b)` (the antecedent `prem` of the
/// subtype's forward law) — every `pair a b` relation *is* a singleton,
/// witnessed by `a`, `b` themselves. `rel` must be the relation
/// `λx y. x = a ∧ y = b`; `prem` is `spec_rep_abs_fwd`'s antecedent,
/// which β-reduces to `∃a' b'. rel = λx y. x = a' ∧ y = b'`.
fn singleton_pred(prem: &Term, a: &Term, b: &Term, rel: &Term) -> Result<Thm> {
    // prem β= ∃a'. ∃b'. rel = pairRel a' b' (single β — the forward law's
    // predicate is the bare `prod_predicate`, not eta-expanded).
    let prem_beta = Thm::beta_conv(prem.clone())?;
    let ex = rhs_of(&prem_beta)?;
    prem_beta
        .sym()?
        .eq_mp(prove_singleton_exists(&ex, a, b, rel)?)
}

/// `⊢ ∃a'. ∃b'. rel = (λx y. x = a' ∧ y = b')`, given `rel = pairRel a b`
/// — witness the existentials by `a`, `b` and discharge by reflexivity.
/// `ex_term` is the exact nested-existential term to prove (taken from the
/// β-reduced predicate so it matches structurally). Shared by the seam
/// ([`singleton_pred`]) and the inhabitation witness
/// ([`predicate_inhabited`]).
fn prove_singleton_exists(ex_term: &Term, a: &Term, b: &Term, rel: &Term) -> Result<Thm> {
    let outer_pred = ex_term.as_app().ok_or(Error::NotAnEquation)?.1.clone();

    // outer_pred a β= ∃b'. rel = pairRel a b'
    let inner_beta = Thm::beta_conv(Term::app(outer_pred.clone(), a.clone()))?;
    let ex_inner = rhs_of(&inner_beta)?;
    let inner_pred = ex_inner.as_app().ok_or(Error::NotAnEquation)?.1.clone();

    // inner_pred b β= (rel = rel) — discharge by reflexivity.
    let at_b = beta_expand(&inner_pred, b.clone(), Thm::refl(rel.clone())?)?; // ⊢ inner_pred b
    let inner_ex = exists_intro(inner_pred, b.clone(), at_b)?; // ⊢ ∃b'. rel = pairRel a b'
    let at_a = inner_beta.sym()?.eq_mp(inner_ex)?; // ⊢ outer_pred a
    exists_intro(outer_pred, a.clone(), at_a) // ⊢ ∃a' b'. …
}

/// `⊢ rep (pair a b) = (λx y. x = a ∧ y = b)` — the carrier-side
/// round-trip for `prod`, with the singleton premise discharged by
/// `singleton_pred`. The seam every clause builds on; its RHS is the
/// canonical `pairRel a b` relation.
pub fn rep_pair(alpha: &Type, beta: &Type, a: &Term, b: &Term) -> Result<Thm> {
    // pair a b = abs (pairRel a b). Unfold the **head** `pair` only
    // (`delta` + `cong_fn`); `delta_all` would also unfold any `pair` *inside*
    // `a`/`b` (a component may itself be a `pair`), desyncing later rewrites.
    let pab_unfold = pair(alpha.clone(), beta.clone())
        .delta()? // ⊢ pair = body
        .cong_fn(a.clone())?
        .cong_fn(b.clone())? // ⊢ pair a b = body a b
        .rhs_conv(|t| t.reduce())?;
    let abs_rel = rhs_of(&pab_unfold)?;
    let rel = abs_rel.as_app().ok_or(Error::NotAnEquation)?.1.clone(); // pairRel a b

    // rep (abs (pairRel a b)) = pairRel a b, premise discharged.
    let fwd = Thm::spec_rep_abs_fwd(prod_spec(), vec![alpha.clone(), beta.clone()], rel.clone())?;
    let prem = fwd
        .concl()
        .as_app()
        .and_then(|(imp_p, _)| imp_p.as_app())
        .map(|(_, p)| p.clone())
        .ok_or(Error::NotAnEquation)?;
    let ra = fwd.imp_elim(singleton_pred(&prem, a, b, &rel)?)?; // ⊢ rep (abs rel) = rel

    // rep (pair a b) = rep (abs rel) = rel.
    pab_unfold.cong_arg(rep(alpha, beta))?.trans(ra)
}

// ============================================================================
// `determines` — the singleton relation pins its components.
// ============================================================================

/// From `ex : ⊢ ∃w. (λx y. x = a ∧ y = b) = (λx y. x = … ∧ y = …)` — a
/// singleton-relation equation with one component existentially bound and
/// the other fixed at `c` — read off the *fixed* component's value:
/// `⊢ a = c` when `first`, else `⊢ b = c`.
///
/// Apply both relations to `a` then `b`: the LHS computes to `a = a ∧ b =
/// b` (true), so the RHS conjunction `a = c ∧ b = w` (resp. `a = w ∧ b =
/// c`) holds; the requested conjunct is the answer. The bound component
/// `w` is discharged by [`exists_elim`].
fn determines(ex: Thm, a: &Term, b: &Term, c: &Term, first: bool) -> Result<Thm> {
    let pred = ex.concl().as_app().ok_or(Error::NotAnEquation)?.1.clone();
    let dom = match pred.type_of()?.kind().clone() {
        covalence_core::TypeKind::Fun(d, _) => d,
        _ => return Err(Error::NotAnEquation),
    };
    let goal = if first {
        a.clone().equals(c.clone())?
    } else {
        b.clone().equals(c.clone())?
    };

    // Open the existential at a fresh witness `w`, peel the equation.
    let w = Term::free("__det_w", dom.clone());
    let pred_w = Term::app(pred.clone(), w.clone());
    let eqn = Thm::beta_conv(pred_w.clone())?.eq_mp(Thm::assume(pred_w.clone())?)?; // {pred_w} ⊢ relL = relR

    // (relL) a b = (relR) a b, then **β-only** normalise each side. (Not
    // βι: ι would fold a literal `3 = 3` to `T`, so the LHS would stop
    // matching the `a=a ∧ b=b` we discharge it with at concrete values.)
    let conj_eq = eqn
        .cong_fn(a.clone())?
        .cong_fn(b.clone())?
        .lhs_conv(beta2)? // (a=a ∧ b=b) = …
        .rhs_conv(beta2)?; // … = (a=c ∧ b=w) | (a=w ∧ b=c)
    let lhs_true = Thm::refl(a.clone())?.and_intro(Thm::refl(b.clone())?)?; // ⊢ a=a ∧ b=b
    let rhs_conj = conj_eq.eq_mp(lhs_true)?; // {pred_w} ⊢ RHS conjunction
    // `first` ⇒ the fixed component `c` is the *first* relation arg, so
    // the equation `a = c` is the left conjunct; otherwise `b = c` right.
    let comp = if first {
        rhs_conj.and_elim_l()?
    } else {
        rhs_conj.and_elim_r()?
    };

    let step = comp.imp_intro(&pred_w)?.all_intro("__det_w", dom)?;
    exists_elim(ex, goal, step)
}

// ============================================================================
// Projection clauses.
// ============================================================================

/// `⊢ fst (pair a b) = a` — first projection. Genuine: hypothesis- and
/// oracle-free.
pub fn fst_pair(alpha: &Type, beta: &Type, a: &Term, b: &Term) -> Result<Thm> {
    projection(alpha, beta, a, b, true)
}

/// `⊢ snd (pair a b) = b` — second projection. Genuine: hypothesis- and
/// oracle-free.
pub fn snd_pair(alpha: &Type, beta: &Type, a: &Term, b: &Term) -> Result<Thm> {
    projection(alpha, beta, a, b, false)
}

/// `⊢ fst (pair a b) = a` (`first`) or `⊢ snd (pair a b) = b`. Unfold the
/// projection to its `ε P` over the carrier relation, rewrite `rep (pair
/// a b)` to `pairRel a b` ([`rep_pair`]), show the chosen component
/// satisfies `P` so the choice does too ([`Thm::select_ax`]), and pin its
/// value with [`determines`].
fn projection(alpha: &Type, beta: &Type, a: &Term, b: &Term, first: bool) -> Result<Thm> {
    let proj = if first {
        fst(alpha.clone(), beta.clone())
    } else {
        snd(alpha.clone(), beta.clone())
    };
    // chosen component for this projection (`a` for fst, `b` for snd).
    let comp = if first { a } else { b };

    // proj (pair a b) = ε P, with `rep (pair a b)` rewritten to pairRel a b.
    let rp = rep_pair(alpha, beta, a, b)?; // ⊢ rep (pair a b) = pairRel a b
    // Unfold the **head** projection only (`delta` + `cong_fn`), not
    // `delta_all` — the latter also unfolds any `fst`/`snd` *inside* `a`/`b`
    // (when a component is itself a projection), desyncing the body from
    // `rp`'s rewrite pattern.
    let unfold = proj
        .delta()? // ⊢ proj = body
        .cong_fn(pair_at(alpha, beta, a, b))? // ⊢ proj (pair a b) = body (pair a b)
        .rhs_conv(|t| t.reduce())?
        .rhs_conv(|t| t.rw_all(&rp))?; // ⊢ proj (pair a b) = ε P
    let eps = rhs_of(&unfold)?;
    let p = eps.as_app().ok_or(Error::NotAnEquation)?.1.clone(); // P : comp_ty → bool

    // ⊢ P comp — the chosen component satisfies the predicate (witness the
    // other component by `b`/`a` respectively, then refl).
    let at_comp = pred_holds(&p, a, b, comp, first)?;
    // ⊢ P (ε P) — the choice satisfies it too.
    let at_eps = Thm::select_ax(p.clone(), comp.clone())?.imp_elim(at_comp)?;
    let ex_eps = Thm::beta_conv(Term::app(p, eps.clone()))?.eq_mp(at_eps)?; // ⊢ ∃w. pairRel a b = pairRel …

    // determines: ⊢ comp = ε P, i.e. `a = εP` (fst) / `b = εP` (snd).
    let comp_eq_eps = determines(ex_eps, a, b, &eps, first)?;
    unfold.trans(comp_eq_eps.sym()?) // ⊢ proj (pair a b) = comp
}

/// `⊢ P comp`, where `P` is the projection predicate `λs. ∃w. pairRel a b
/// = pairRel …` and `comp` the chosen component — witness the *other*
/// component, discharge by reflexivity. `first` says which projection we
/// are on (so the bound var is the *other* component): `fst` ranges its `s`
/// over the first component and `∃`-binds the second, so its witness is
/// `b`; `snd` is the mirror, witness `a`. (Choosing by the `first` flag —
/// not by component type — is essential when `α = β`, where the two
/// components are type-indistinguishable.)
fn pred_holds(p: &Term, a: &Term, b: &Term, comp: &Term, first: bool) -> Result<Thm> {
    // P comp β= ∃w. pairRel a b = pairRel … (with `comp` slotted in).
    let beta = Thm::beta_conv(Term::app(p.clone(), comp.clone()))?;
    let ex = rhs_of(&beta)?;
    let inner_pred = ex.as_app().ok_or(Error::NotAnEquation)?.1.clone();
    // The witness for the bound (other) component: `b` for fst (∃b'), `a`
    // for snd (∃a'). The body then reduces to `pairRel a b = pairRel a b`.
    let wit = if first { b.clone() } else { a.clone() };
    // The relation `pairRel a b` is the LHS of the (reflexive) inner body.
    let rel = {
        let body = Thm::beta_conv(Term::app(inner_pred.clone(), wit.clone()))?;
        rhs_of(&body)?
            .as_eq()
            .ok_or(Error::NotAnEquation)?
            .0
            .clone()
    };
    let at_wit = beta_expand(&inner_pred, wit.clone(), Thm::refl(rel)?)?; // ⊢ inner_pred wit
    let inner_ex = exists_intro(inner_pred, wit, at_wit)?; // ⊢ ∃w. …
    beta.sym()?.eq_mp(inner_ex) // ⊢ P comp
}

// ============================================================================
// Surjective pairing + injectivity.
// ============================================================================

/// `⊢ pair (fst p) (snd p) = p` — every product is the pair of its
/// projections (η for products). Genuine: hypothesis- and oracle-free.
pub fn surjective_pairing(alpha: &Type, beta: &Type, p: &Term) -> Result<Thm> {
    // Get `∃a b. rep p = pairRel a b` from the subtype's back-direction
    // law (the predicate is inhabited — `pairRel` of anything is a
    // singleton — so the `¬∃` escape disjunct is refuted), then eliminate
    // the two witnesses and assemble.
    let ex_ab = rep_is_singleton(alpha, beta, p)?; // ⊢ ∃a. ∃b. rep p = pairRel a b

    // Under witnesses a0, b0 with `rep p = pairRel a0 b0`:
    //   fst p = a0, snd p = b0  (projections, via determines on rep p),
    //   pair a0 b0 = abs (rep p) = p,
    //   so pair (fst p) (snd p) = pair a0 b0 = p.
    let goal = pair_at(
        alpha,
        beta,
        &Term::app(fst(alpha.clone(), beta.clone()), p.clone()),
        &Term::app(snd(alpha.clone(), beta.clone()), p.clone()),
    )
    .equals(p.clone())?;

    let outer_pred = ex_ab
        .concl()
        .as_app()
        .ok_or(Error::NotAnEquation)?
        .1
        .clone();
    let a0 = Term::free("__sp_a", alpha.clone());
    let inner_ex = beta_reduce(Thm::assume(Term::app(outer_pred.clone(), a0.clone()))?)?; // {…} ⊢ ∃b. rep p = pairRel a0 b
    let inner_pred = inner_ex
        .concl()
        .as_app()
        .ok_or(Error::NotAnEquation)?
        .1
        .clone();
    let b0 = Term::free("__sp_b", beta.clone());
    let eqn = beta_reduce(Thm::assume(Term::app(inner_pred.clone(), b0.clone()))?)?; // {E} ⊢ rep p = pairRel a0 b0

    let body = surjective_under(alpha, beta, p, &a0, &b0, eqn)?; // {E} ⊢ goal
    // Peel b0 then a0.
    let step_b = body
        .imp_intro(&Term::app(inner_pred.clone(), b0.clone()))?
        .all_intro("__sp_b", beta.clone())?;
    let by_b = exists_elim(inner_ex, goal.clone(), step_b)?; // {outer_pred a0} ⊢ goal
    let step_a = by_b
        .imp_intro(&Term::app(outer_pred, a0.clone()))?
        .all_intro("__sp_a", alpha.clone())?;
    exists_elim(ex_ab, goal, step_a)
}

/// The body of [`surjective_pairing`] under the assumption
/// `eqn : ⊢ rep p = pairRel a0 b0` — derive `⊢ pair (fst p) (snd p) = p`.
fn surjective_under(
    alpha: &Type,
    beta: &Type,
    p: &Term,
    a0: &Term,
    b0: &Term,
    eqn: Thm,
) -> Result<Thm> {
    // fst p = a0 and snd p = b0 — same `select_ax` + `determines` route as
    // `projection`, but the relation is `pairRel a0 b0` (from `eqn`) and
    // `rep p` is rewritten by `eqn` rather than `rep_pair`.
    let fst_p = proj_value(alpha, beta, p, a0, b0, &eqn, true)?; // {E} ⊢ fst p = a0
    let snd_p = proj_value(alpha, beta, p, a0, b0, &eqn, false)?; // {E} ⊢ snd p = b0

    // pair (fst p) (snd p) = pair a0 b0  (congruence on both args).
    let pair_op = pair(alpha.clone(), beta.clone());
    let pair_cong = Thm::refl(pair_op)?.cong_app(fst_p)?.cong_app(snd_p)?; // {E} ⊢ pair (fst p)(snd p) = pair a0 b0

    // pair a0 b0 = abs (pairRel a0 b0) = abs (rep p) = p.
    let pab_unfold = pair_at(alpha, beta, a0, b0)
        .delta_all(pair_spec().symbol())?
        .rhs_conv(|t| t.reduce())?; // ⊢ pair a0 b0 = abs (pairRel a0 b0)
    let abs = Term::spec_abs(prod_spec(), vec![alpha.clone(), beta.clone()]);
    // abs (pairRel a0 b0) = abs (rep p)  via eqn.sym under abs.
    let abs_cong = eqn.clone().sym()?.cong_arg(abs)?; // {E} ⊢ abs (pairRel a0 b0) = abs (rep p)
    let abs_rep = Thm::spec_abs_rep(prod_spec(), vec![alpha.clone(), beta.clone()], p.clone())?; // ⊢ abs (rep p) = p

    pair_cong.trans(pab_unfold)?.trans(abs_cong)?.trans(abs_rep)
}

/// `⊢ proj p = comp` given `eqn : ⊢ rep p = pairRel a0 b0`, for a free
/// `p` — the projection-value lemma surjective pairing needs (the
/// [`projection`] route with `rep p` rewritten by `eqn`). `comp` is `a0`
/// (fst) or `b0` (snd).
fn proj_value(
    alpha: &Type,
    beta: &Type,
    p: &Term,
    a0: &Term,
    b0: &Term,
    eqn: &Thm,
    first: bool,
) -> Result<Thm> {
    let (proj_spec, proj) = if first {
        (fst_spec(), fst(alpha.clone(), beta.clone()))
    } else {
        (snd_spec(), snd(alpha.clone(), beta.clone()))
    };
    let comp = if first { a0 } else { b0 };

    let unfold = Term::app(proj, p.clone())
        .delta_all(proj_spec.symbol())?
        .rhs_conv(|t| t.reduce())?
        .rhs_conv(|t| t.rw_all(eqn))?; // {E} ⊢ proj p = ε P  (P over pairRel a0 b0)
    let eps = rhs_of(&unfold)?;
    let pp = eps.as_app().ok_or(Error::NotAnEquation)?.1.clone();

    let at_comp = pred_holds(&pp, a0, b0, comp, first)?;
    let at_eps = Thm::select_ax(pp.clone(), comp.clone())?.imp_elim(at_comp)?;
    let ex_eps = Thm::beta_conv(Term::app(pp, eps.clone()))?.eq_mp(at_eps)?;
    let comp_eq_eps = determines(ex_eps, a0, b0, &eps, first)?;
    unfold.trans(comp_eq_eps.sym()?)
}

/// `⊢ ∃a b. rep p = (λx y. x = a ∧ y = b)`, for a free `p : prod α β` —
/// `rep p` is a singleton relation. From the kernel's witness-free
/// back-direction law [`Thm::spec_rep_abs_back`] (`rep (abs (rep p)) =
/// rep p ⟹ prod_predicate (rep p) ∨ ¬∃R. prod_predicate R`); the premise
/// holds by `abs_rep` congruence, and the `¬∃` escape is refuted by
/// inhabitation ([`predicate_inhabited`]).
fn rep_is_singleton(alpha: &Type, beta: &Type, p: &Term) -> Result<Thm> {
    let rep_p = Term::app(rep(alpha, beta), p.clone());
    let back = Thm::spec_rep_abs_back(
        prod_spec(),
        vec![alpha.clone(), beta.clone()],
        rep_p.clone(),
    )?;
    // premise: rep (abs (rep p)) = rep p — from abs (rep p) = p under rep.
    let abs_rep = Thm::spec_abs_rep(prod_spec(), vec![alpha.clone(), beta.clone()], p.clone())?; // ⊢ abs (rep p) = p
    let prem = abs_rep.cong_arg(rep(alpha, beta))?; // ⊢ rep (abs (rep p)) = rep p
    let disj = back.imp_elim(prem)?; // ⊢ P (rep p) ∨ ¬∃R. P R

    // Eliminate the disjunction: the left disjunct *is* the goal; the
    // right (`¬∃R. P R`) is refuted by inhabitation, then ex falso.
    let (left, right) = as_or(disj.concl())?;
    let from_left = Thm::assume(left.clone())?.imp_intro(&left)?; // ⊢ left ⟹ left
    let ex_r = right.as_app().ok_or(Error::NotAnEquation)?.1.clone(); // ∃R. P R
    let inhab = predicate_inhabited(alpha, beta, &ex_r)?; // ⊢ ∃R. P R
    let from_right = Thm::assume(right.clone())?
        .not_elim(inhab)? // ⊢ F
        .false_elim(left.clone())? // ⊢ left
        .imp_intro(&right)?; // ⊢ right ⟹ left
    let p_rep = disj.or_elim(from_left, from_right)?; // ⊢ P (rep p)

    // P (rep p) β= ∃a b. rep p = pairRel a b.
    beta_reduce(p_rep)
}

/// `⊢ ∃R. prod_predicate R` — the singleton predicate is inhabited
/// (witness `pairRel a b` for fresh `a`, `b`). `ex_r` is the exact `∃R. P
/// R` term to prove (taken from the back-law disjunct, so it matches).
fn predicate_inhabited(alpha: &Type, beta: &Type, ex_r: &Term) -> Result<Thm> {
    // The back-law's existential predicate is **eta-expanded** —
    // `λx. prod_predicate x` — so `pred rel` needs full β-normalisation,
    // not a single `beta_conv`.
    let pred = ex_r.as_app().ok_or(Error::NotAnEquation)?.1.clone(); // λx. prod_predicate x
    // Witness: the carrier relation behind `pair a b` for fresh a, b.
    let a = Term::free("__inh_a", alpha.clone());
    let b = Term::free("__inh_b", beta.clone());
    let rp = rep_pair(alpha, beta, &a, &b)?; // ⊢ rep (pair a b) = pairRel a b
    let rel = rhs_of(&rp)?; // pairRel a b
    // pred rel ⟶β ∃a' b'. rel = pairRel a' b' (strong β through the η layer).
    let nf = crate::init::eq::beta_nf(Term::app(pred.clone(), rel.clone())); // ⊢ pred rel = ∃a' b'. …
    let ex = rhs_of(&nf)?;
    let at_rel = nf
        .sym()?
        .eq_mp(prove_singleton_exists(&ex, &a, &b, &rel)?)?; // ⊢ pred rel
    exists_intro(pred, rel, at_rel)
}

/// `⊢ (pair a b = pair c d) ⟹ (a = c ∧ b = d)` — pair injectivity, by
/// applying the projection clauses to both sides. Genuine.
pub fn pair_inj(alpha: &Type, beta: &Type, a: &Term, b: &Term, c: &Term, d: &Term) -> Result<Thm> {
    let h_term = pair_at(alpha, beta, a, b).equals(pair_at(alpha, beta, c, d))?;
    let h = Thm::assume(h_term.clone())?; // {H} ⊢ pair a b = pair c d

    // a = fst (pair a b) = fst (pair c d) = c.
    let fst_ab = fst_pair(alpha, beta, a, b)?; // ⊢ fst (pair a b) = a
    let fst_cd = fst_pair(alpha, beta, c, d)?; // ⊢ fst (pair c d) = c
    let fst_cong = h.clone().cong_arg(fst(alpha.clone(), beta.clone()))?; // {H} ⊢ fst (pair a b) = fst (pair c d)
    let a_eq_c = fst_ab.sym()?.trans(fst_cong)?.trans(fst_cd)?; // {H} ⊢ a = c

    let snd_ab = snd_pair(alpha, beta, a, b)?;
    let snd_cd = snd_pair(alpha, beta, c, d)?;
    let snd_cong = h.cong_arg(snd(alpha.clone(), beta.clone()))?;
    let b_eq_d = snd_ab.sym()?.trans(snd_cong)?.trans(snd_cd)?; // {H} ⊢ b = d

    a_eq_c.and_intro(b_eq_d)?.imp_intro(&h_term) // ⊢ (pair a b = pair c d) ⟹ (a = c ∧ b = d)
}

// ============================================================================
// Small helpers.
// ============================================================================

/// The right-hand side of an equational theorem's conclusion.
fn rhs_of(thm: &Thm) -> Result<Term> {
    Ok(thm.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone())
}

/// `⊢ ((λx.λy. body) p) q = body[p][q]` — reduce the **outer two** β-redexes
/// of a binary-relation application, leaving `p`, `q`, and `body`'s
/// sub-structure untouched. Unlike a full normaliser ([`beta_nf`]), this does
/// not descend into `p`/`q`, so a compound component carrying un-reduced
/// redexes (e.g. `mk_int`'s `λx. int_rel … x`) still matches `refl`.
///
/// [`beta_nf`]: crate::init::eq::beta_nf
fn beta2(t: &Term) -> Result<Thm> {
    let (fp, q) = t.as_app().ok_or(Error::NotAnEquation)?; // (λx.λy. body) p , q
    let s1 = Thm::beta_conv(fp.clone())?; // (λx.λy. body) p = λy. body[p]
    let s2 = s1.cong_fn(q.clone())?; // (…) p q = (λy. body[p]) q
    let mid = rhs_of(&s2)?;
    s2.trans(Thm::beta_conv(mid)?) // = body[p][q]
}

/// `⊢ f arg` from `⊢ body`, where `body` is `f arg` β-reduced.
fn beta_expand(f: &Term, arg: Term, body_proof: Thm) -> Result<Thm> {
    Thm::beta_conv(Term::app(f.clone(), arg))?
        .sym()?
        .eq_mp(body_proof)
}

/// β-reduce a theorem whose conclusion is a redex: `Γ ⊢ f arg` →
/// `Γ ⊢ body[arg]`.
fn beta_reduce(thm: Thm) -> Result<Thm> {
    Thm::beta_conv(thm.concl().clone())?.eq_mp(thm)
}

/// Split a `p ∨ q` term into `(p, q)`.
fn as_or(t: &Term) -> Result<(Term, Term)> {
    // `p ∨ q` = `((∨) p) q`.
    let (or_p, q) = t.as_app().ok_or(Error::NotAnEquation)?;
    let (_or, p) = or_p.as_app().ok_or(Error::NotAnEquation)?;
    Ok((p.clone(), q.clone()))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn alpha() -> Type {
        Type::tfree("a")
    }
    fn beta() -> Type {
        Type::tfree("b")
    }

    fn ab() -> (Term, Term) {
        (Term::free("a", alpha()), Term::free("b", beta()))
    }

    #[test]
    fn rep_pair_round_trips() {
        let (a, b) = ab();
        let thm = rep_pair(&alpha(), &beta(), &a, &b).unwrap();
        assert!(thm.hyps().is_empty() && thm.has_no_obs());
        // LHS is `rep (pair a b)`.
        let (lhs, _rhs) = thm.concl().as_eq().unwrap();
        assert_eq!(
            lhs,
            &Term::app(rep(&alpha(), &beta()), pair_at(&alpha(), &beta(), &a, &b))
        );
    }

    #[test]
    fn fst_pair_is_first() {
        let (a, b) = ab();
        let thm = fst_pair(&alpha(), &beta(), &a, &b).unwrap();
        assert!(thm.hyps().is_empty(), "fst.pair is proved, not postulated");
        assert!(thm.has_no_obs(), "fst.pair is oracle-free");
        let (lhs, rhs) = thm.concl().as_eq().unwrap();
        assert_eq!(
            lhs,
            &Term::app(fst(alpha(), beta()), pair_at(&alpha(), &beta(), &a, &b))
        );
        assert_eq!(rhs, &a);
    }

    #[test]
    fn snd_pair_is_second() {
        let (a, b) = ab();
        let thm = snd_pair(&alpha(), &beta(), &a, &b).unwrap();
        assert!(thm.hyps().is_empty() && thm.has_no_obs());
        let (lhs, rhs) = thm.concl().as_eq().unwrap();
        assert_eq!(
            lhs,
            &Term::app(snd(alpha(), beta()), pair_at(&alpha(), &beta(), &a, &b))
        );
        assert_eq!(rhs, &b);
    }

    #[test]
    fn projections_at_concrete_values() {
        // fst (pair 3 T) = 3, snd (pair 3 T) = T at (nat, bool).
        let three = Term::nat_lit(covalence_types::Nat::from_inner(3u32.into()));
        let tt = Term::bool_lit(true);
        let f = fst_pair(&Type::nat(), &Type::bool(), &three, &tt).unwrap();
        assert_eq!(rhs_of(&f).unwrap(), three);
        let s = snd_pair(&Type::nat(), &Type::bool(), &three, &tt).unwrap();
        assert_eq!(rhs_of(&s).unwrap(), tt);
        assert!(f.hyps().is_empty() && s.hyps().is_empty());
    }

    #[test]
    fn pair_inj_both_components() {
        let (a, b) = ab();
        let c = Term::free("c", alpha());
        let d = Term::free("d", beta());
        let thm = pair_inj(&alpha(), &beta(), &a, &b, &c, &d).unwrap();
        assert!(thm.hyps().is_empty() && thm.has_no_obs());
        // ⊢ (pair a b = pair c d) ⟹ (a = c ∧ b = d)
        let expected = pair_at(&alpha(), &beta(), &a, &b)
            .equals(pair_at(&alpha(), &beta(), &c, &d))
            .unwrap()
            .imp(
                a.clone()
                    .equals(c)
                    .unwrap()
                    .and(b.clone().equals(d).unwrap())
                    .unwrap(),
            )
            .unwrap();
        assert_eq!(thm.concl(), &expected);
    }

    #[test]
    fn surjective_pairing_reassembles() {
        let p = Term::free("p", prod(alpha(), beta()));
        let thm = surjective_pairing(&alpha(), &beta(), &p).unwrap();
        assert!(
            thm.hyps().is_empty(),
            "surjective.pairing is proved, not postulated"
        );
        assert!(thm.has_no_obs(), "surjective.pairing is oracle-free");
        let expected = pair_at(
            &alpha(),
            &beta(),
            &Term::app(fst(alpha(), beta()), p.clone()),
            &Term::app(snd(alpha(), beta()), p.clone()),
        )
        .equals(p.clone())
        .unwrap();
        assert_eq!(thm.concl(), &expected);
    }
}
