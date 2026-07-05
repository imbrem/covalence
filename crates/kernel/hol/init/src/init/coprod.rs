//! `coprod` theorems: the disjoint-union round-trips, injection
//! injectivity, and — the property the tagged encoding exists to give —
//! injection **disjointness** (`inl a ≠ inr b`).
//!
//! `coprod α β` is a *subtype* of the tagged relation `α → β → bool →
//! bool` (see `defs/coprod.rs`): `inl a = abs (λx y z. z ∧ x=a)`,
//! `inr b = abs (λx y z. ¬z ∧ y=b)`. The `z` discriminator makes the two
//! injection relations provably distinct for *every* carrier, so the
//! round-trips (`rep (abs (inj …)) = inj …`, which need the subtype
//! predicate discharged) and disjointness go through unconditionally.
//!
//! This is the foundation under [`init::option`](mod@crate::init::option).
//!
//! On top of the round-trips this module now proves the full coproduct
//! **universal property**: the `coprod_case` computation equations
//! [`case_inl`] / [`case_inr`] (`[f,g] ∘ inl = f` pointwise), injection
//! **injectivity** [`inl_inj`] / [`inr_inj`] (`inl a = inl a' ⟹ a = a'`),
//! **surjectivity** [`cases`] (every value is `inl` or `inr`), and the
//! **η / fusion** law [`case_eta`] (`m = [m ∘ inl, m ∘ inr]`). Together
//! with [`init::cat`](crate::init::cat) these are the axioms the
//! point-free [`monoidal`](crate::algebra::monoidal) API reasons through.
//!
//! The colocated `coprod.cov` script re-proves the η / fusion law
//! ([`cov::case_eta_cov`]) and a coproduct **case-analysis** principle
//! ([`cov::case_eq_cov`], `∀c P. (∀x. P (inl x)) ⟹ (∀y. P (inr y)) ⟹ P c`)
//! *genuinely* over the seam givens — driving the `cases` disjunction
//! through `(exists-elim …)` rather than re-exporting a Rust bridge.

use covalence_core::{Error, Result, Term, Type};
use covalence_hol_eval::EvalThm as Thm;

use crate::init::eq::delta_head;
use crate::init::ext::{TermExt, ThmExt};
use crate::init::logic::{exists_elim, exists_intro, simp, truth};

pub use covalence_hol_eval::defs::{coprod, coprod_case, inl, inr};

// ============================================================================
// The `.cov` proof-script layer for `coprod`.
//
// `coprod_env()` is the **seam** environment imported by `coprod.cov`. It
// exposes:
//   * the injection/case operators (`inl`/`inr`/`coprod_case`) and `compose`
//     as polymorphic (`ConstDef::Poly`) schemes, so the type-inferencer can
//     build `coprod`-typed and composite terms at any instance; and
//   * the lemmas that cross the abs/rep / Hilbert-choice barrier — and are
//     therefore *not* expressible in the proof language — as universally
//     quantified Rust-proved GIVENS:
//       inl_ne_inr  : ∀av bv. ¬(inl av = inr bv)        (disjointness)
//       inl_inj     : ∀av av2. inl av = inl av2 ⟹ av = av2
//       inr_inj     : ∀bv bv2. inr bv = inr bv2 ⟹ bv = bv2
//       case_inl    : ∀f g av. coprod_case f g (inl av) = f av
//       case_inr    : ∀f g bv. coprod_case f g (inr bv) = g bv
//       cases       : ∀c. (∃x. c = inl x) ∨ (∃y. c = inr y)
//       comp_beta   : ∀g f x. compose g f x = g (f x)    (from `cat`)
//       fun_ext     : ∀f g. (∀x. f x = g x) ⟹ f = g     (from `cat`)
//
// `coprod.cov` then proves the η/fusion law `case_eta` and the case-analysis
// `case_eq` GENUINELY over those givens, using the existential machinery
// (`exists-elim` over `cases`, the `case_*` computations, `comp_beta`, and
// `fun_ext`) — no Rust bridge for those two.
// ============================================================================

/// The `coprod` seam environment: see the module comment above. The operators
/// are `Poly` (multi-type-var) schemes and the barrier-crossing lemmas are
/// universally-quantified Rust givens.
pub fn coprod_env() -> crate::script::Env {
    use crate::init::cat::{comp, comp_beta, fun_ext};
    use crate::script::ConstDef;
    use covalence_hol_eval::defs::compose;

    let alpha = Type::tfree("a");
    let beta = Type::tfree("b");
    let gamma = Type::tfree("c");
    let mut e = crate::script::Env::empty();

    // -- operators (Poly so each use site re-instantiates the type vars) --
    e.define_const("inl", ConstDef::Poly(inl(alpha.clone(), beta.clone())));
    e.define_const("inr", ConstDef::Poly(inr(alpha.clone(), beta.clone())));
    e.define_const(
        "coprod_case",
        ConstDef::Poly(coprod_case(alpha.clone(), beta.clone(), gamma.clone())),
    );
    e.define_const(
        "compose",
        ConstDef::Poly(compose(alpha.clone(), beta.clone(), gamma.clone())),
    );

    // -- seam givens (Rust-proved, used as axioms by coprod.cov) --

    // ⊢ ∀(av:'a). ∀(bv:'b). ¬(inl av = inr bv)
    let av = Term::free("av", alpha.clone());
    let bv = Term::free("bv", beta.clone());
    let ne = inl_ne_inr(&alpha, &beta, &av, &bv)
        .and_then(|t| t.all_intro("bv", beta.clone()))
        .and_then(|t| t.all_intro("av", alpha.clone()))
        .expect("coprod_env: inl_ne_inr");
    e.define_lemma("inl_ne_inr", ne);

    // ⊢ ∀(av:'a). ∀(av2:'a). inl av = inl av2 ⟹ av = av2
    let av2 = Term::free("av2", alpha.clone());
    let ili = inl_inj(&alpha, &beta, &av, &av2)
        .and_then(|t| t.all_intro("av2", alpha.clone()))
        .and_then(|t| t.all_intro("av", alpha.clone()))
        .expect("coprod_env: inl_inj");
    e.define_lemma("inl_inj", ili);

    // ⊢ ∀(bv:'b). ∀(bv2:'b). inr bv = inr bv2 ⟹ bv = bv2
    let bv2 = Term::free("bv2", beta.clone());
    let iri = inr_inj(&alpha, &beta, &bv, &bv2)
        .and_then(|t| t.all_intro("bv2", beta.clone()))
        .and_then(|t| t.all_intro("bv", beta.clone()))
        .expect("coprod_env: inr_inj");
    e.define_lemma("inr_inj", iri);

    // ⊢ ∀(f:'a→'c). ∀(g:'b→'c). ∀(av:'a).
    //     coprod_case f g (inl av) = f av
    let f = Term::free("f", Type::fun(alpha.clone(), gamma.clone()));
    let g = Term::free("g", Type::fun(beta.clone(), gamma.clone()));
    let av_f = Term::free("av", alpha.clone());
    let ci = case_inl(&alpha, &beta, &gamma, &f, &g, &av_f)
        .and_then(|t| t.all_intro("av", alpha.clone()))
        .and_then(|t| t.all_intro("g", Type::fun(beta.clone(), gamma.clone())))
        .and_then(|t| t.all_intro("f", Type::fun(alpha.clone(), gamma.clone())))
        .expect("coprod_env: case_inl");
    e.define_lemma("case_inl", ci);

    // ⊢ ∀(f:'a→'c). ∀(g:'b→'c). ∀(bv:'b).
    //     coprod_case f g (inr bv) = g bv
    let bv_f = Term::free("bv", beta.clone());
    let cr = case_inr(&alpha, &beta, &gamma, &f, &g, &bv_f)
        .and_then(|t| t.all_intro("bv", beta.clone()))
        .and_then(|t| t.all_intro("g", Type::fun(beta.clone(), gamma.clone())))
        .and_then(|t| t.all_intro("f", Type::fun(alpha.clone(), gamma.clone())))
        .expect("coprod_env: case_inr");
    e.define_lemma("case_inr", cr);

    // ⊢ ∀(c : coprod 'a 'b). (∃x:'a. c = inl x) ∨ (∃y:'b. c = inr y)
    let c = Term::free("c", coprod(alpha.clone(), beta.clone()));
    let ca = cases(&alpha, &beta, &c)
        .and_then(|t| t.all_intro("c", coprod(alpha.clone(), beta.clone())))
        .expect("coprod_env: cases");
    e.define_lemma("cases", ca);

    // Function extensionality (from `cat`), **pre-instantiated** at maps out of
    // `coprod 'a 'b` (the same exact-type-match reason as the comp-β givens
    // below): ∀(f g : coprod 'a 'b → 'c). (∀c. f c = g c) ⟹ f = g.
    let cab = coprod(alpha.clone(), beta.clone());
    let map_ty = Type::fun(cab.clone(), gamma.clone());
    {
        let f = Term::free("f", map_ty.clone());
        let g = Term::free("g", map_ty.clone());
        let c = Term::free("c", cab.clone());
        let hyp = Term::app(f.clone(), c.clone())
            .equals(Term::app(g.clone(), c.clone()))
            .and_then(|eq| eq.forall("c", cab.clone()))
            .expect("coprod_env: fun_ext hyp");
        let app_eq = Thm::assume(hyp.clone())
            .and_then(|h| h.all_elim(c.clone()))
            .expect("coprod_env: fun_ext app_eq");
        let fe = fun_ext(app_eq, "c", &cab)
            .and_then(|t| t.imp_intro(&hyp))
            .and_then(|t| t.all_intro("g", map_ty.clone()))
            .and_then(|t| t.all_intro("f", map_ty.clone()))
            .expect("coprod_env: fun_ext");
        e.define_lemma("fun_ext", fe);
    }

    // The composition-β law `case_eta` needs, pre-instantiated at the coprod
    // injections — the *generic* `cat::comp_beta` (`∀(g:'b→'c) f x`) cannot be
    // `all-elim`'d at `m : coprod 'a 'b → 'c` because the kernel's `all_elim`
    // demands an exact type match and the proof language has no per-witness
    // type instantiation (the same `id`-style TFree clash `cat` documents). So
    // we ship the two instances `case_eta` actually uses:
    //   comp_beta_inl : ∀(m:coprod 'a 'b→'c)(x:'a). compose m inl x = m (inl x)
    //   comp_beta_inr : ∀(m:coprod 'a 'b→'c)(y:'b). compose m inr y = m (inr y)
    let mty = Type::fun(coprod(alpha.clone(), beta.clone()), gamma.clone());
    let m = Term::free("m", mty.clone());
    let xv = Term::free("x", alpha.clone());
    let yv = Term::free("y", beta.clone());
    let cbl = comp(&m, &inl(alpha.clone(), beta.clone()))
        .and_then(|gf| comp_beta(&gf, &xv))
        .and_then(|t| t.all_intro("x", alpha.clone()))
        .and_then(|t| t.all_intro("m", mty.clone()))
        .expect("coprod_env: comp_beta_inl");
    e.define_lemma("comp_beta_inl", cbl);
    let cbr = comp(&m, &inr(alpha.clone(), beta.clone()))
        .and_then(|gf| comp_beta(&gf, &yv))
        .and_then(|t| t.all_intro("y", beta.clone()))
        .and_then(|t| t.all_intro("m", mty.clone()))
        .expect("coprod_env: comp_beta_inr");
    e.define_lemma("comp_beta_inr", cbr);

    e
}

crate::cov_theory! {
    /// `coprod` theorems ported to `coprod.cov`, over `core` + the `coprodrpm`
    /// seam env. `case_eta` (η/fusion) and `case_eq` (case-analysis) are proved
    /// genuinely there over the seam givens, using the existential machinery.
    pub mod cov from "coprod.cov" {
        import "core"     = crate::script::Env::core();
        import "coprodrpm" = crate::init::coprod::coprod_env();
        "case_eta" => pub fn case_eta_cov;
        "case_eq"  => pub fn case_eq_cov;
    }
}

#[cfg(test)]
mod cov_tests {
    use super::*;

    /// `case_eta` from `coprod.cov` must have the same conclusion as the
    /// hand-written Rust `case_eta` — but proved genuinely in the script
    /// layer (not a Rust bridge), so this is a real cross-check of two proofs.
    #[test]
    fn case_eta_cov_matches_rust() {
        let alpha = Type::tfree("a");
        let beta = Type::tfree("b");
        let gamma = Type::tfree("c");
        let m = Term::free(
            "m",
            Type::fun(coprod(alpha.clone(), beta.clone()), gamma.clone()),
        );
        let rust_thm = case_eta(&alpha, &beta, &gamma, &m).expect("case_eta");
        // `case_eta_cov` is stated over the same free `m` (the `.cov` `#fix`),
        // so its conclusion equals the Rust proof's directly.
        let cov_thm = cov::case_eta_cov();
        assert_eq!(
            cov_thm.concl(),
            rust_thm.concl(),
            "case_eta from coprod.cov must match the Rust proof"
        );
        assert!(cov_thm.hyps().is_empty(), "case_eta_cov is hypothesis-free");
    }

    /// `case_eq` from `coprod.cov` — the genuinely-proved case-analysis
    /// principle: from a proof on each injection arm, conclude the goal at any
    /// `c : coprod α β`. Stated and checked here as a hypothesis-free theorem.
    #[test]
    fn case_eq_cov_is_genuine() {
        let thm = cov::case_eq_cov();
        assert!(thm.hyps().is_empty(), "case_eq is proved, not postulated");
    }
}

use covalence_hol_eval::defs::coprod_spec;

// ============================================================================
// Raw coercions + injection unfolding.
// ============================================================================

fn rep_c(a: &Type, b: &Type) -> Term {
    Term::spec_rep(coprod_spec(), vec![a.clone(), b.clone()])
}

/// `(⊢ inl av = abs (left_rel av), left_rel av)` — unfold `inl` to expose
/// its carrier relation `left_rel av = λx y z. z ∧ (x = av)`.
fn inl_unfold(a: &Type, b: &Type, av: &Term) -> Result<(Thm, Term)> {
    let inl_a = Term::app(inl(a.clone(), b.clone()), av.clone());
    let eq = delta_head(&inl_a)?.rhs_conv(|t| t.reduce())?;
    let rel = rhs_of(&eq)?.as_app().ok_or(Error::NotAnEquation)?.1.clone();
    Ok((eq, rel))
}

/// `(⊢ inr bv = abs (right_rel bv), right_rel bv)`.
fn inr_unfold(a: &Type, b: &Type, bv: &Term) -> Result<(Thm, Term)> {
    let inr_b = Term::app(inr(a.clone(), b.clone()), bv.clone());
    let eq = delta_head(&inr_b)?.rhs_conv(|t| t.reduce())?;
    let rel = rhs_of(&eq)?.as_app().ok_or(Error::NotAnEquation)?.1.clone();
    Ok((eq, rel))
}

// ============================================================================
// Subtype round-trips for the injection relations.
//
// `coprod` is a subtype, so `rep (abs rel) = rel` needs the carving
// predicate `coprod_predicate rel` discharged. For `rel = left_rel av`
// the predicate's *left* disjunct `∃a. rel = left_rel a` holds (witness
// `av`); for `rel = right_rel bv`, the *right* disjunct.
// ============================================================================

/// `⊢ rep (abs rel) = rel` for a coprod injection relation `rel`, with
/// `left` selecting which predicate disjunct to witness with `witness`.
fn round_trip(a: &Type, b: &Type, rel: &Term, witness: &Term, left: bool) -> Result<Thm> {
    let fwd = Thm::spec_rep_abs_fwd(coprod_spec(), vec![a.clone(), b.clone()], rel.clone())?;
    // fwd : ⊢ (λR. D1 ∨ D2) rel ⟹ rep (abs rel) = rel.
    let prem = fwd
        .concl()
        .as_app()
        .and_then(|(f, _)| f.as_app())
        .ok_or(Error::NotAnEquation)?
        .1
        .clone();
    let beta = Thm::beta_conv(prem)?; // ⊢ prem = (D1 ∨ D2)
    let disj = rhs_of(&beta)?;
    let (d1, d2) = parse_or(&disj).ok_or_else(|| {
        Error::ConnectiveRule(format!(
            "coprod round_trip: predicate is not a disjunction: {disj}"
        ))
    })?;
    let chosen = if left { &d1 } else { &d2 };
    let pred = chosen.as_app().ok_or(Error::NotAnEquation)?.1.clone(); // the ∃'s λ
    // `⊢ pred witness` — β-reduces to `rel = rel`, discharged by refl.
    let app = Term::app(pred.clone(), witness.clone());
    let pred_at = Thm::beta_conv(app)?.sym()?.eq_mp(Thm::refl(rel.clone())?)?;
    let disjunct = exists_intro(pred, witness.clone(), pred_at)?;
    let disj_thm = if left {
        disjunct.or_intro_l(d2)?
    } else {
        disjunct.or_intro_r(d1)?
    };
    let prem_thm = beta.sym()?.eq_mp(disj_thm)?; // ⊢ prem
    fwd.imp_elim(prem_thm)
}

// ============================================================================
// Disjointness — `inl a ≠ inr b`.
// ============================================================================

/// `⊢ ¬(inl av = inr bv)` — the disjoint-union injections never agree.
/// This is exactly the property the tagged carrier relation buys: at the
/// discriminator value `z = T` the left relation forces `x = av` while
/// the right forces `F`, so `left_rel av` and `right_rel bv` differ.
pub fn inl_ne_inr(a: &Type, b: &Type, av: &Term, bv: &Term) -> Result<Thm> {
    let inl_av = Term::app(inl(a.clone(), b.clone()), av.clone());
    let inr_bv = Term::app(inr(a.clone(), b.clone()), bv.clone());
    let eq = inl_av.clone().equals(inr_bv.clone())?;

    // Under H : inl av = inr bv, derive F.
    let h = Thm::assume(eq.clone())?;
    let (inl_u, lrel) = inl_unfold(a, b, av)?; // ⊢ inl av = abs LR ;  LR = left_rel av
    let (inr_u, rrel) = inr_unfold(a, b, bv)?; // ⊢ inr bv = abs RR ;  RR = right_rel bv
    let abs_eq = inl_u.sym()?.trans(h)?.trans(inr_u)?; // {H} ⊢ abs LR = abs RR
    let rep_cong = abs_eq.cong_arg(rep_c(a, b))?; // {H} ⊢ rep (abs LR) = rep (abs RR)
    let rel_eq = round_trip(a, b, &lrel, av, true)?
        .sym()?
        .trans(rep_cong)?
        .trans(round_trip(a, b, &rrel, bv, false)?)?; // {H} ⊢ LR = RR
    // Apply both sides to (av, bv, T) and βι-reduce.
    let tt = Term::bool_lit(true);
    let applied = rel_eq
        .cong_fn(av.clone())?
        .cong_fn(bv.clone())?
        .cong_fn(tt)?
        .reduce_lhs()?
        .reduce_rhs()?; // {H} ⊢ (T ∧ av=av) = (¬T ∧ bv=bv)
    // The carrier equalities `av=av` / `bv=bv` are not `bool`-equations,
    // so `simp` leaves them; rewrite them to `T` by reflexivity first.
    let av_t = Thm::refl(av.clone())?.eqt_intro()?; // ⊢ (av=av) = T
    let bv_t = Thm::refl(bv.clone())?.eqt_intro()?; // ⊢ (bv=bv) = T
    let applied = applied.rewrite(&av_t)?.rewrite(&bv_t)?; // {H} ⊢ (T ∧ T) = (¬T ∧ T)
    let (lhs, rhs) = {
        let (l, r) = applied.concl().as_eq().ok_or(Error::NotAnEquation)?;
        (l.clone(), r.clone())
    };
    let l_t = simp(&lhs)?; // ⊢ (T ∧ T) = T
    let r_f = simp(&rhs)?; // ⊢ (¬T ∧ T) = F
    let t_eq_f = l_t.sym()?.trans(applied)?.trans(r_f)?; // {H} ⊢ T = F
    let f = t_eq_f.eq_mp(truth())?; // {H} ⊢ F
    f.imp_intro(&eq)?.not_intro() // ⊢ ¬(inl av = inr bv)
}

// ============================================================================
// Injection round-trips on `rep`, relation injectivity / disjointness.
//
// The pieces the coprod **universal property** (`coprod_case` β below)
// needs: `rep (inj v) = injRel v`, the injection relations are injective
// (`leftRel a = leftRel a' ⟹ a = a'`), and the two relation families are
// disjoint (`¬(leftRel a = rightRel b)`).
// ============================================================================

/// `⊢ rep (inl av) = leftRel av` — the left injection's representative.
fn rep_inl(a: &Type, b: &Type, av: &Term) -> Result<Thm> {
    let (inl_u, lrel) = inl_unfold(a, b, av)?; // ⊢ inl av = abs LR
    inl_u
        .cong_arg(rep_c(a, b))? // ⊢ rep (inl av) = rep (abs LR)
        .trans(round_trip(a, b, &lrel, av, true)?) // ⊢ rep (abs LR) = LR
}

/// `⊢ rep (inr bv) = rightRel bv` — the right injection's representative.
fn rep_inr(a: &Type, b: &Type, bv: &Term) -> Result<Thm> {
    let (inr_u, rrel) = inr_unfold(a, b, bv)?;
    inr_u
        .cong_arg(rep_c(a, b))?
        .trans(round_trip(a, b, &rrel, bv, false)?)
}

/// `⊢ ¬(leftRel av = rightRel bv)` — the two injection relations never
/// agree (the discriminator `z` forces `T` on the left, `F` on the
/// right). This is the relation-level core of [`inl_ne_inr`].
fn left_ne_right(a: &Type, b: &Type, av: &Term, bv: &Term) -> Result<Thm> {
    let lrel = inl_unfold(a, b, av)?.1;
    let rrel = inr_unfold(a, b, bv)?.1;
    let eq = lrel.clone().equals(rrel.clone())?;
    let h = Thm::assume(eq.clone())?;
    // Apply both sides to (av, bv, T) and βι-reduce.
    let tt = Term::bool_lit(true);
    let applied = h
        .cong_fn(av.clone())?
        .cong_fn(bv.clone())?
        .cong_fn(tt)?
        .reduce_lhs()?
        .reduce_rhs()?; // {H} ⊢ (T ∧ av=av) = (¬T ∧ bv=bv)
    let av_t = Thm::refl(av.clone())?.eqt_intro()?;
    let bv_t = Thm::refl(bv.clone())?.eqt_intro()?;
    let applied = applied.rewrite(&av_t)?.rewrite(&bv_t)?; // {H} ⊢ (T ∧ T) = (¬T ∧ T)
    let (lhs, rhs) = {
        let (l, r) = applied.concl().as_eq().ok_or(Error::NotAnEquation)?;
        (l.clone(), r.clone())
    };
    let t_eq_f = simp(&lhs)?.sym()?.trans(applied)?.trans(simp(&rhs)?)?; // {H} ⊢ T = F
    let f = t_eq_f.eq_mp(truth())?; // {H} ⊢ F
    f.imp_intro(&eq)?.not_intro()
}

/// `⊢ injRel v = injRel v2 ⟹ v = v2` — injectivity of a tagged injection
/// relation (here `injRel v2` is `rel2`). `x` / `y` are the two carrier
/// slots and `z` the discriminator to probe at: for `leftRel` use
/// `(x = v, y arbitrary, z = T)`, for `rightRel` use `(x arbitrary,
/// y = v, z = F)`. At those slots both sides reduce to `z' ∧ (v = v[2])`;
/// folding `v = v` to `T` and discharging the (true) discriminator leaves
/// `v = v2`.
fn rel_inj(rel: &Term, rel2: &Term, v: &Term, x: &Term, y: &Term, z: bool) -> Result<Thm> {
    let eq = rel.clone().equals(rel2.clone())?;
    let h = Thm::assume(eq.clone())?;
    let applied = h
        .cong_fn(x.clone())?
        .cong_fn(y.clone())?
        .cong_fn(Term::bool_lit(z))?
        .reduce_lhs()?
        .reduce_rhs()?; // {H} ⊢ (z' ∧ (v = v)) = (z' ∧ (v = v2))
    // Fold `v = v` to `T` (simp leaves carrier equalities), then let `simp`
    // collapse the discriminator and `T ∧ _`.
    let vv_t = Thm::refl(v.clone())?.eqt_intro()?; // ⊢ (v=v) = T
    let applied = applied.rewrite(&vv_t)?; // {H} ⊢ (z' ∧ T) = (z' ∧ (v = v2))
    let (lhs, rhs) = {
        let (l, r) = applied.concl().as_eq().ok_or(Error::NotAnEquation)?;
        (l.clone(), r.clone())
    };
    let v_eq = simp(&lhs)? // ⊢ (z' ∧ T) = T
        .sym()?
        .trans(applied)? // {H} ⊢ T = (z' ∧ (v = v2))
        .trans(simp(&rhs)?)? // {H} ⊢ T = (v = v2)
        .sym()?
        .eqt_elim()?; // {H} ⊢ v = v2
    v_eq.imp_intro(&eq)
}

// ============================================================================
// Injection injectivity — `inl a = inl a' ⟹ a = a'` (and the `inr` dual).
//
// `inl` and `inr` are injective: `rep` is, the round-trips identify
// `rep (inl a)` with `leftRel a`, and the injection relations are injective
// at their discriminator slot ([`rel_inj`]). These are the constructor laws
// the case-analysis layer needs *positively* (the disjointness `inl_ne_inr`
// is the negative companion).
// ============================================================================

/// `⊢ inl av = inl av2 ⟹ av = av2` — the left injection is injective.
/// Genuine: hypothesis- and oracle-free.
pub fn inl_inj(a: &Type, b: &Type, av: &Term, av2: &Term) -> Result<Thm> {
    let inl_av = Term::app(inl(a.clone(), b.clone()), av.clone());
    let inl_av2 = Term::app(inl(a.clone(), b.clone()), av2.clone());
    let eq = inl_av.clone().equals(inl_av2.clone())?;
    let h = Thm::assume(eq.clone())?;
    // rep both sides; collapse to the underlying relations.
    let rels_eq = rep_inl(a, b, av)?
        .sym()?
        .trans(h.cong_arg(rep_c(a, b))?)?
        .trans(rep_inl(a, b, av2)?)?; // {H} ⊢ leftRel av = leftRel av2
    let probe_y = Term::free("__iiy", b.clone());
    let inj = rel_inj(
        &lrel_of(a, b, av)?,
        &lrel_of(a, b, av2)?,
        av,
        av,
        &probe_y,
        true,
    )?;
    inj.imp_elim(rels_eq)?.imp_intro(&eq) // ⊢ (inl av = inl av2) ⟹ av = av2
}

/// `⊢ inr bv = inr bv2 ⟹ bv = bv2` — the right injection is injective.
/// Genuine: hypothesis- and oracle-free.
pub fn inr_inj(a: &Type, b: &Type, bv: &Term, bv2: &Term) -> Result<Thm> {
    let inr_bv = Term::app(inr(a.clone(), b.clone()), bv.clone());
    let inr_bv2 = Term::app(inr(a.clone(), b.clone()), bv2.clone());
    let eq = inr_bv.clone().equals(inr_bv2.clone())?;
    let h = Thm::assume(eq.clone())?;
    let rels_eq = rep_inr(a, b, bv)?
        .sym()?
        .trans(h.cong_arg(rep_c(a, b))?)?
        .trans(rep_inr(a, b, bv2)?)?; // {H} ⊢ rightRel bv = rightRel bv2
    let probe_x = Term::free("__iix", a.clone());
    let inj = rel_inj(
        &rrel_of(a, b, bv)?,
        &rrel_of(a, b, bv2)?,
        bv,
        &probe_x,
        bv,
        false,
    )?;
    inj.imp_elim(rels_eq)?.imp_intro(&eq)
}

// ============================================================================
// The coproduct universal property — `coprod_case` β-equations.
//
//   ⊢ coprod_case f g (inl a) = f a        (case_inl)
//   ⊢ coprod_case f g (inr b) = g b        (case_inr)
//
// `coprod_case f g c = ε(λr. (∀a. rep c = leftRel a  ⟹ r = f a)
//                         ∧ (∀b. rep c = rightRel b ⟹ r = g b))`.
// At `c = inl a₀`, `rep c = leftRel a₀`: the *left* clause at `a := a₀`
// (antecedent `refl`) pins `ε = f a₀`, while the right clause is vacuous
// by disjointness. The witness `f a₀` satisfies the predicate (left clause
// by `leftRel` injectivity, right clause vacuously), so the choice axiom
// applies. `inr` is symmetric.
// ============================================================================

/// `⊢ coprod_case f g (inl av) = f av`. Genuine: hypothesis- and
/// oracle-free.
pub fn case_inl(a: &Type, b: &Type, gamma: &Type, f: &Term, g: &Term, av: &Term) -> Result<Thm> {
    let c = Term::app(inl(a.clone(), b.clone()), av.clone());
    let (pred, eps_eq) = case_unfold(a, b, gamma, f, g, &c)?;
    let witness = Term::app(f.clone(), av.clone());

    // ⊢ pred witness — the predicate holds at `f av`.
    let p_at = pred_at_inl(a, b, f, g, av, &pred, &witness)?;
    // ⊢ ε pred = f av, from the left clause at `a := av`.
    let at_choice = Thm::select_ax(pred.clone(), witness.clone())?.imp_elim(p_at)?;
    let eps = at_choice
        .concl()
        .as_app()
        .ok_or(Error::NotAnEquation)?
        .1
        .clone();
    let conj = Thm::beta_conv(Term::app(pred.clone(), eps))?.eq_mp(at_choice)?;
    let left_clause = conj.and_elim_l()?; // ∀a. rep(inl av)=leftRel a ⟹ ε = f a
    let pinned = left_clause
        .all_elim(av.clone())? // ⊢ rep(inl av)=leftRel av ⟹ ε = f av
        .imp_elim(rep_inl(a, b, av)?)?; // ⊢ ε pred = f av
    eps_eq.trans(pinned)
}

/// `⊢ coprod_case f g (inr bv) = g bv`. Genuine: hypothesis- and
/// oracle-free.
pub fn case_inr(a: &Type, b: &Type, gamma: &Type, f: &Term, g: &Term, bv: &Term) -> Result<Thm> {
    let c = Term::app(inr(a.clone(), b.clone()), bv.clone());
    let (pred, eps_eq) = case_unfold(a, b, gamma, f, g, &c)?;
    let witness = Term::app(g.clone(), bv.clone());

    let p_at = pred_at_inr(a, b, f, g, bv, &pred, &witness)?;
    let at_choice = Thm::select_ax(pred.clone(), witness.clone())?.imp_elim(p_at)?;
    let eps = at_choice
        .concl()
        .as_app()
        .ok_or(Error::NotAnEquation)?
        .1
        .clone();
    let conj = Thm::beta_conv(Term::app(pred.clone(), eps))?.eq_mp(at_choice)?;
    let right_clause = conj.and_elim_r()?; // ∀b. rep(inr bv)=rightRel b ⟹ ε = g b
    let pinned = right_clause
        .all_elim(bv.clone())?
        .imp_elim(rep_inr(a, b, bv)?)?; // ⊢ ε pred = g bv
    eps_eq.trans(pinned)
}

/// δ-unfold `coprod_case f g c` to its choice term `ε pred`, returning
/// `(pred, ⊢ coprod_case f g c = ε pred)`.
fn case_unfold(
    a: &Type,
    b: &Type,
    gamma: &Type,
    f: &Term,
    g: &Term,
    c: &Term,
) -> Result<(Term, Thm)> {
    let cc = coprod_case(a.clone(), b.clone(), gamma.clone())
        .apply(f.clone())?
        .apply(g.clone())?
        .apply(c.clone())?;
    // Unfold only the *head* `coprod_case` — `delta_all` would also unfold
    // any `coprod_case` nested inside `f` / `g` / `c` (e.g. when they are
    // themselves copairings, as the monoidal structure morphisms are).
    let unfold = delta_head(&cc)?.rhs_conv(|t| t.reduce())?; // ⊢ cc = ε pred
    let eps = rhs_of(&unfold)?;
    let pred = eps.as_app().ok_or(Error::NotAnEquation)?.1.clone();
    Ok((pred, unfold))
}

/// `⊢ pred (f av)` for `c = inl av`: the left clause holds by `leftRel`
/// injectivity (`leftRel av = leftRel a ⟹ av = a ⟹ f av = f a`), the
/// right clause vacuously by disjointness.
fn pred_at_inl(
    a: &Type,
    b: &Type,
    f: &Term,
    g: &Term,
    av: &Term,
    pred: &Term,
    witness: &Term,
) -> Result<Thm> {
    let rep_eq = rep_inl(a, b, av)?; // ⊢ rep(inl av) = leftRel av

    // Left clause: ∀a. rep(inl av) = leftRel a ⟹ f av = f a.
    let a_var = Term::free("__cia", a.clone());
    let lrel_a = inl_unfold(a, b, &a_var)?.1;
    let ante_l = lhs_of(&rep_eq)?.equals(lrel_a.clone())?; // rep(inl av) = leftRel __cia
    let hl = Thm::assume(ante_l.clone())?;
    let rels_eq = rep_eq.clone().sym()?.trans(hl)?; // {H} ⊢ leftRel av = leftRel __cia
    let probe_y = Term::free("__ciy", b.clone());
    let inj = rel_inj(&lrel_of(a, b, av)?, &lrel_a, av, av, &probe_y, true)?;
    let v_eq = inj.imp_elim(rels_eq)?; // {H} ⊢ av = __cia
    let f_cong = Thm::refl(f.clone())?.cong_app(v_eq)?; // {H} ⊢ f av = f __cia
    let left_clause = f_cong.imp_intro(&ante_l)?.all_intro("__cia", a.clone())?;

    // Right clause: ∀b. rep(inl av) = rightRel b ⟹ f av = g b (vacuous).
    let b_var = Term::free("__cib", b.clone());
    let rrel_b = inr_unfold(a, b, &b_var)?.1;
    let ante_r = lhs_of(&rep_eq)?.equals(rrel_b.clone())?;
    let hr = Thm::assume(ante_r.clone())?;
    let bad = rep_eq.sym()?.trans(hr)?; // {H} ⊢ leftRel av = rightRel __cib
    let f_false = left_ne_right(a, b, av, &b_var)?.not_elim(bad)?; // {H} ⊢ F
    let goal = witness.clone().equals(Term::app(g.clone(), b_var))?;
    let right_clause = f_false
        .false_elim(goal)?
        .imp_intro(&ante_r)?
        .all_intro("__cib", b.clone())?;

    let conj = left_clause.and_intro(right_clause)?;
    Thm::beta_conv(Term::app(pred.clone(), witness.clone()))?
        .sym()?
        .eq_mp(conj)
}

/// `⊢ pred (g bv)` for `c = inr bv`: symmetric to [`pred_at_inl`].
fn pred_at_inr(
    a: &Type,
    b: &Type,
    f: &Term,
    g: &Term,
    bv: &Term,
    pred: &Term,
    witness: &Term,
) -> Result<Thm> {
    let rep_eq = rep_inr(a, b, bv)?; // ⊢ rep(inr bv) = rightRel bv

    // Left clause: ∀a. rep(inr bv) = leftRel a ⟹ g bv = f a (vacuous).
    let a_var = Term::free("__cia", a.clone());
    let lrel_a = inl_unfold(a, b, &a_var)?.1;
    let ante_l = lhs_of(&rep_eq)?.equals(lrel_a.clone())?;
    let hl = Thm::assume(ante_l.clone())?;
    let bad = rep_eq.clone().sym()?.trans(hl)?; // {H} ⊢ rightRel bv = leftRel __cia
    let f_false = left_ne_right(a, b, &a_var, bv)?.not_elim(bad.sym()?)?; // {H} ⊢ F
    let goal = witness.clone().equals(Term::app(f.clone(), a_var))?;
    let left_clause = f_false
        .false_elim(goal)?
        .imp_intro(&ante_l)?
        .all_intro("__cia", a.clone())?;

    // Right clause: ∀b. rep(inr bv) = rightRel b ⟹ g bv = g b.
    let b_var = Term::free("__cib", b.clone());
    let rrel_b = inr_unfold(a, b, &b_var)?.1;
    let ante_r = lhs_of(&rep_eq)?.equals(rrel_b.clone())?;
    let hr = Thm::assume(ante_r.clone())?;
    let rels_eq = rep_eq.sym()?.trans(hr)?; // {H} ⊢ rightRel bv = rightRel __cib
    let probe_x = Term::free("__cix", a.clone());
    let inj = rel_inj(&rrel_of(a, b, bv)?, &rrel_b, bv, &probe_x, bv, false)?;
    // ⊢ (rightRel bv = rightRel __cib) ⟹ bv = __cib
    let v_eq = inj.imp_elim(rels_eq)?; // {H} ⊢ bv = __cib
    let g_cong = Thm::refl(g.clone())?.cong_app(v_eq)?; // {H} ⊢ g bv = g __cib
    let right_clause = g_cong.imp_intro(&ante_r)?.all_intro("__cib", b.clone())?;

    let conj = left_clause.and_intro(right_clause)?;
    Thm::beta_conv(Term::app(pred.clone(), witness.clone()))?
        .sym()?
        .eq_mp(conj)
}

/// The reduced left/right injection relations at a carrier value.
fn lrel_of(a: &Type, b: &Type, av: &Term) -> Result<Term> {
    Ok(inl_unfold(a, b, av)?.1)
}
fn rrel_of(a: &Type, b: &Type, bv: &Term) -> Result<Term> {
    Ok(inr_unfold(a, b, bv)?.1)
}

// ============================================================================
// Surjectivity of the injections + the η / fusion law.
//
// `coprod` is *covered* by its two injections: every `c : coprod α β` is
// `inl x` or `inr y`. That follows from the subtype interface — `c =
// abs (rep c)` and `rep c` satisfies the carving predicate `(∃a. rep c =
// leftRel a) ∨ (∃b. rep c = rightRel b)` — mapped through `abs`. Together
// with the β-equations it gives the **uniqueness / η** law: a map out of
// `coprod` is determined by its two restrictions, so
// `m = [m ∘ inl, m ∘ inr]`. This is the workhorse for *proving* point-free
// equations between maps out of a coproduct.
// ============================================================================

/// `⊢ (∃x. c = inl x) ∨ (∃y. c = inr y)` — every `coprod α β` value is an
/// injection. Genuine: hypothesis- and oracle-free.
pub fn cases(a: &Type, b: &Type, c: &Term) -> Result<Thm> {
    let repc = Term::app(rep_c(a, b), c.clone());
    // c = abs(rep c) and rep(abs(rep c)) = rep c.
    let abs_rep = Thm::spec_abs_rep(coprod_spec(), vec![a.clone(), b.clone()], c.clone())?;
    let rep_abs_rep = abs_rep.clone().cong_arg(rep_c(a, b))?;
    // ⊢ P(rep c) ∨ ¬∃R. P R  (the witness-free subtype back-direction).
    let back = Thm::spec_rep_abs_back(coprod_spec(), vec![a.clone(), b.clone()], repc.clone())?;
    let disj0 = back.imp_elim(rep_abs_rep)?;
    let (p_repc, not_ex) =
        parse_or(disj0.concl()).ok_or_else(|| Error::ConnectiveRule("cases: not a ∨".into()))?;
    let pred_p = p_repc.as_app().ok_or(Error::NotAnEquation)?.0.clone(); // P

    // The predicate is inhabited (by `leftRel` of a fresh carrier), so the
    // empty-predicate escape disjunct `¬∃R. P R` is refutable. The `∃`
    // there is over `λR. P R` (η-expanded), so extract that exact body.
    let ex_term = not_ex.as_app().ok_or(Error::NotAnEquation)?.1.clone(); // ∃R. (λR. P R) R
    let pred_ex = ex_term.as_app().ok_or(Error::NotAnEquation)?.1.clone(); // λR. P R
    let ex_p = pred_nonempty(a, b, &pred_p, &pred_ex)?;
    let left = Thm::assume(p_repc.clone())?.imp_intro(&p_repc)?;
    let right = Thm::assume(not_ex.clone())?
        .not_elim(ex_p)?
        .false_elim(p_repc.clone())?
        .imp_intro(&not_ex)?;
    let p_rep = disj0.or_elim(left, right)?; // ⊢ P(rep c)

    // β: ⊢ (∃a. rep c = leftRel a) ∨ (∃b. rep c = rightRel b).
    let inner = Thm::beta_conv(Term::app(pred_p, repc))?.eq_mp(p_rep)?;
    let (ex_lrel, ex_rrel) =
        parse_or(inner.concl()).ok_or_else(|| Error::ConnectiveRule("cases: inner ∨".into()))?;

    let (goal_l, goal_r) = cases_goal(a, b, c)?;
    // Map each representative disjunct to the corresponding injection.
    let left2 = map_to_inj(a, b, &abs_rep, &ex_lrel, &goal_l, &goal_r, true)?;
    let right2 = map_to_inj(a, b, &abs_rep, &ex_rrel, &goal_l, &goal_r, false)?;
    inner.or_elim(left2, right2)
}

/// `(∃x. c = inl x, ∃y. c = inr y)`.
fn cases_goal(a: &Type, b: &Type, c: &Term) -> Result<(Term, Term)> {
    let x = Term::free("__sx", a.clone());
    let ex_inl = c
        .clone()
        .equals(Term::app(inl(a.clone(), b.clone()), x))?
        .exists("__sx", a.clone())?;
    let y = Term::free("__sy", b.clone());
    let ex_inr = c
        .clone()
        .equals(Term::app(inr(a.clone(), b.clone()), y))?
        .exists("__sy", b.clone())?;
    Ok((ex_inl, ex_inr))
}

/// `⊢ ∃R. (λR. P R) R` — the coprod carving predicate is inhabited
/// (witness `leftRel av`). `pred_p` is the bare predicate `P` (for the
/// inner β-reduct); `pred_ex` is the η-expanded `λR. P R` the `∃` in the
/// `spec_rep_abs_back` escape disjunct quantifies, so the result matches
/// it exactly. Sub-predicates are *extracted* from `P`'s β-reduct.
fn pred_nonempty(a: &Type, b: &Type, pred_p: &Term, pred_ex: &Term) -> Result<Thm> {
    let av = Term::free("__pne", a.clone());
    let lr_av = lrel_of(a, b, &av)?;
    let beta = Thm::beta_conv(Term::app(pred_p.clone(), lr_av.clone()))?; // ⊢ P(leftRel av) = D
    let d = rhs_of(&beta)?;
    let (ex_l, ex_r) =
        parse_or(&d).ok_or_else(|| Error::ConnectiveRule("pred_nonempty: not ∨".into()))?;
    let pred_l = ex_l.as_app().ok_or(Error::NotAnEquation)?.1.clone(); // λa. leftRel av = leftRel a
    // ⊢ pred_l av  (β-reduces to leftRel av = leftRel av, refl).
    let at = Thm::beta_conv(Term::app(pred_l.clone(), av.clone()))?;
    let pred_l_av = at.sym()?.eq_mp(Thm::refl(lr_av.clone())?)?;
    let d_thm = exists_intro(pred_l, av, pred_l_av)?.or_intro_l(ex_r)?; // ⊢ D
    let p_at = beta.sym()?.eq_mp(d_thm)?; // ⊢ P(leftRel av)
    // Re-wrap through the η-expanded predicate `λR. P R`.
    let ex_beta = Thm::beta_conv(Term::app(pred_ex.clone(), lr_av.clone()))?; // ⊢ (λR.P R)(leftRel av) = P(leftRel av)
    let pred_ex_at = ex_beta.sym()?.eq_mp(p_at)?; // ⊢ (λR. P R)(leftRel av)
    exists_intro(pred_ex.clone(), lr_av, pred_ex_at)
}

/// `⊢ (∃v. rep c = injRel v) ⟹ ((∃x. c = inl x) ∨ (∃y. c = inr y))`,
/// the `is_left` arm mapping a representative disjunct to its injection.
fn map_to_inj(
    a: &Type,
    b: &Type,
    abs_rep: &Thm,
    ex_rel: &Term,
    goal_l: &Term,
    goal_r: &Term,
    is_left: bool,
) -> Result<Thm> {
    let pred = ex_rel.as_app().ok_or(Error::NotAnEquation)?.1.clone(); // λv. rep c = injRel v
    let carrier = if is_left { a } else { b };
    let v = Term::free("__mtv", carrier.clone());
    let ante_app = Term::app(pred.clone(), v.clone());
    // ⊢ rep c = injRel v, from the assumed `pred v`.
    let ante_beta = Thm::beta_conv(ante_app.clone())?; // ⊢ pred v = (rep c = injRel v)
    let h = ante_beta.clone().eq_mp(Thm::assume(ante_app.clone())?)?;
    // c = inj v: cong `abs`, then abs_rep on the left, inj round-trip on the right.
    let abs = Term::spec_abs(coprod_spec(), vec![a.clone(), b.clone()]);
    let inj_unfold = if is_left {
        inl_unfold(a, b, &v)?.0 // ⊢ inl v = abs(leftRel v)
    } else {
        inr_unfold(a, b, &v)?.0
    };
    let c_eq_inj = abs_rep
        .clone()
        .sym()? // ⊢ c = abs(rep c)
        .trans(h.cong_arg(abs)?)? // ⊢ c = abs(injRel v)
        .trans(inj_unfold.sym()?)?; // ⊢ c = inj v
    // ∃-introduce, then inject into the goal disjunction.
    let goal = if is_left { goal_l } else { goal_r };
    let goal_pred = goal.as_app().ok_or(Error::NotAnEquation)?.1.clone();
    let intro_beta = Thm::beta_conv(Term::app(goal_pred.clone(), v.clone()))?; // ⊢ goal_pred v = (c = inj v)
    let at = intro_beta.sym()?.eq_mp(c_eq_inj)?; // ⊢ goal_pred v
    let ex = exists_intro(goal_pred, v.clone(), at)?; // ⊢ ∃. c = inj _
    let full = if is_left {
        ex.or_intro_l(goal_r.clone())?
    } else {
        ex.or_intro_r(goal_l.clone())?
    };
    // ⊢ ∀v. pred v ⟹ goal, then close the existential.
    let step = full
        .imp_intro(&ante_app)?
        .all_intro("__mtv", carrier.clone())?;
    let branch = exists_elim(
        Thm::assume(ex_rel.clone())?,
        full_goal(goal_l, goal_r)?,
        step,
    )?;
    branch.imp_intro(ex_rel)
}

/// `(∃x. c = inl x) ∨ (∃y. c = inr y)`.
fn full_goal(goal_l: &Term, goal_r: &Term) -> Result<Term> {
    goal_l.clone().or(goal_r.clone())
}

/// `⊢ m = coprod_case (m ∘ inl) (m ∘ inr)` — the coproduct **η / fusion**
/// law: a map out of `coprod α β` equals the copairing of its
/// restrictions. `m : coprod α β → γ`. Genuine: hypothesis- and
/// oracle-free.
pub fn case_eta(a: &Type, b: &Type, gamma: &Type, m: &Term) -> Result<Thm> {
    use crate::init::cat::comp;
    let inl_t = inl(a.clone(), b.clone());
    let inr_t = inr(a.clone(), b.clone());
    let m_inl = comp(m, &inl_t)?; // m ∘ inl : α → γ
    let m_inr = comp(m, &inr_t)?; // m ∘ inr : β → γ
    let k = coprod_case(a.clone(), b.clone(), gamma.clone())
        .apply(m_inl.clone())?
        .apply(m_inr.clone())?; // [m∘inl, m∘inr]

    // Extensionality at a fresh point `c`, by cases on `c`.
    let c = Term::free("__etc", coprod(a.clone(), b.clone()));
    let point = case_eta_point(a, b, gamma, m, &m_inl, &m_inr, &k, &c)?; // ⊢ m c = k c

    // ⊢ m = k via abs + η on both sides.
    crate::init::cat::fun_ext(point, "__etc", &coprod(a.clone(), b.clone()))
}

/// `⊢ m c = k c` for `k = [m∘inl, m∘inr]`, by case analysis on `c`.
#[allow(clippy::too_many_arguments)]
fn case_eta_point(
    a: &Type,
    b: &Type,
    gamma: &Type,
    m: &Term,
    m_inl: &Term,
    m_inr: &Term,
    k: &Term,
    c: &Term,
) -> Result<Thm> {
    let goal = Term::app(m.clone(), c.clone()).equals(Term::app(k.clone(), c.clone()))?;
    let (ex_inl, ex_inr) = cases_goal(a, b, c)?;
    let cases_thm = cases(a, b, c)?;
    let left = eta_branch(a, b, gamma, m, m_inl, m_inr, k, &ex_inl, &goal, true)?;
    let right = eta_branch(a, b, gamma, m, m_inl, m_inr, k, &ex_inr, &goal, false)?;
    cases_thm.or_elim(left, right)
}

/// `⊢ (∃v. c = inj v) ⟹ (m c = k c)` on one injection arm, where
/// `k = [m_inl, m_inr]`.
#[allow(clippy::too_many_arguments)]
fn eta_branch(
    a: &Type,
    b: &Type,
    gamma: &Type,
    m: &Term,
    m_inl: &Term,
    m_inr: &Term,
    k: &Term,
    ex_inj: &Term,
    goal: &Term,
    is_left: bool,
) -> Result<Thm> {
    let (carrier, m_inj) = if is_left { (a, m_inl) } else { (b, m_inr) };
    let pred = ex_inj.as_app().ok_or(Error::NotAnEquation)?.1.clone(); // λv. c = inj v
    let v = Term::free("__ebv", carrier.clone());
    let ante_app = Term::app(pred.clone(), v.clone());
    let h = Thm::beta_conv(ante_app.clone())?.eq_mp(Thm::assume(ante_app.clone())?)?; // ⊢ c = inj v

    // m c = m (inj v).
    let m_lhs = Thm::refl(m.clone())?.cong_app(h.clone())?; // ⊢ m c = m (inj v)
    // k c = k (inj v) = m_inj v = (m ∘ inj) v = m (inj v).
    let k_at_inj = if is_left {
        case_inl(a, b, gamma, m_inl, m_inr, &v)?
    } else {
        case_inr(a, b, gamma, m_inl, m_inr, &v)?
    }; // ⊢ k (inj v) = (m ∘ inj) v
    let mij_reduce = crate::init::cat::comp_beta(m_inj, &v)?; // ⊢ (m ∘ inj) v = m (inj v)
    let k_rhs = Thm::refl(k.clone())?
        .cong_app(h)? // ⊢ k c = k (inj v)
        .trans(k_at_inj)? // ⊢ k c = (m ∘ inj) v
        .trans(mij_reduce)?; // ⊢ k c = m (inj v)
    let point = m_lhs.trans(k_rhs.sym()?)?; // ⊢ m c = k c
    // ⊢ ∀v. pred v ⟹ (m c = k c), then exists-eliminate the witness.
    let step = point
        .imp_intro(&ante_app)?
        .all_intro("__ebv", carrier.clone())?;
    let branch = exists_elim(Thm::assume(ex_inj.clone())?, goal.clone(), step)?;
    branch.imp_intro(ex_inj)
}

// ============================================================================
// Helpers.
// ============================================================================

fn lhs_of(thm: &Thm) -> Result<Term> {
    Ok(thm.concl().as_eq().ok_or(Error::NotAnEquation)?.0.clone())
}

fn rhs_of(thm: &Thm) -> Result<Term> {
    Ok(thm.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone())
}

/// Parse `App(App(∨, p), q)` → `(p, q)`.
fn parse_or(t: &Term) -> Option<(Term, Term)> {
    let (f, q) = t.as_app()?;
    let (head, p) = f.as_app()?;
    let (spec, _) = head.as_spec()?;
    spec.ptr_eq(&covalence_hol_eval::defs::or_spec())
        .then(|| (p.clone(), q.clone()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn inl_ne_inr_is_genuine() {
        // ¬(inl av = inr bv) at α = β = unit — the delicate case where the two
        // injections could be identified. Provable, hypothesis-free.
        let u = Type::unit();
        let av = Term::free("av", u.clone());
        let bv = Term::free("bv", u.clone());
        let thm = inl_ne_inr(&u, &u, &av, &bv).unwrap();
        assert!(thm.hyps().is_empty(), "disjointness is proved, no hyps");
        let inl_av = Term::app(inl(u.clone(), u.clone()), av);
        let inr_bv = Term::app(inr(u.clone(), u.clone()), bv);
        assert_eq!(thm.concl(), &inl_av.equals(inr_bv).unwrap().not().unwrap());
    }

    #[test]
    fn inl_ne_inr_polymorphic() {
        let a = Type::tfree("a");
        let b = Type::tfree("b");
        let av = Term::free("av", a.clone());
        let bv = Term::free("bv", b.clone());
        assert!(inl_ne_inr(&a, &b, &av, &bv).unwrap().hyps().is_empty());
    }

    fn abc() -> (Type, Type, Type) {
        (Type::tfree("a"), Type::tfree("b"), Type::tfree("c"))
    }

    #[test]
    fn case_inl_computes() {
        // ⊢ coprod_case f g (inl av) = f av — the left β-equation.
        let (a, b, c) = abc();
        let f = Term::free("f", Type::fun(a.clone(), c.clone()));
        let g = Term::free("g", Type::fun(b.clone(), c.clone()));
        let av = Term::free("av", a.clone());
        let thm = case_inl(&a, &b, &c, &f, &g, &av).unwrap();
        assert!(thm.hyps().is_empty(), "case_inl is proved, not postulated");
        let lhs = coprod_case(a, b, c)
            .apply(f.clone())
            .unwrap()
            .apply(g)
            .unwrap()
            .apply(Term::app(
                inl(av.type_of().unwrap(), Type::tfree("b")),
                av.clone(),
            ))
            .unwrap();
        assert_eq!(thm.concl(), &lhs.equals(Term::app(f, av)).unwrap());
    }

    #[test]
    fn case_inr_computes() {
        // ⊢ coprod_case f g (inr bv) = g bv — the right β-equation.
        let (a, b, c) = abc();
        let f = Term::free("f", Type::fun(a.clone(), c.clone()));
        let g = Term::free("g", Type::fun(b.clone(), c.clone()));
        let bv = Term::free("bv", b.clone());
        let thm = case_inr(&a, &b, &c, &f, &g, &bv).unwrap();
        assert!(thm.hyps().is_empty());
        assert_eq!(rhs_of(&thm).unwrap(), Term::app(g, bv));
    }

    #[test]
    fn cases_covers_both_injections() {
        let (a, b, _c) = abc();
        let c = Term::free("c", coprod(a.clone(), b.clone()));
        let thm = cases(&a, &b, &c).unwrap();
        assert!(thm.hyps().is_empty());
        let (ex_l, ex_r) = cases_goal(&a, &b, &c).unwrap();
        assert_eq!(thm.concl(), &ex_l.or(ex_r).unwrap());
    }

    #[test]
    fn case_eta_fuses_restrictions() {
        // ⊢ m = coprod_case (m∘inl) (m∘inr).
        let (a, b, g) = abc();
        let m = Term::free("m", Type::fun(coprod(a.clone(), b.clone()), g.clone()));
        let thm = case_eta(&a, &b, &g, &m).unwrap();
        assert!(thm.hyps().is_empty(), "η/fusion is proved, not postulated");
        // LHS is `m`.
        assert_eq!(thm.concl().as_eq().unwrap().0, &m);
    }

    #[test]
    fn inl_inj_is_genuine() {
        // ⊢ inl av = inl av2 ⟹ av = av2 — the left injection is injective.
        let (a, b, _c) = abc();
        let av = Term::free("av", a.clone());
        let av2 = Term::free("av2", a.clone());
        let thm = inl_inj(&a, &b, &av, &av2).unwrap();
        assert!(thm.hyps().is_empty(), "inl_inj is proved, not postulated");
        let inl_av = Term::app(inl(a.clone(), b.clone()), av.clone());
        let inl_av2 = Term::app(inl(a.clone(), b.clone()), av2.clone());
        let expected = inl_av
            .equals(inl_av2)
            .unwrap()
            .imp(av.equals(av2).unwrap())
            .unwrap();
        assert_eq!(thm.concl(), &expected);
    }

    #[test]
    fn inr_inj_is_genuine() {
        // ⊢ inr bv = inr bv2 ⟹ bv = bv2 — the right injection is injective.
        let (a, b, _c) = abc();
        let bv = Term::free("bv", b.clone());
        let bv2 = Term::free("bv2", b.clone());
        let thm = inr_inj(&a, &b, &bv, &bv2).unwrap();
        assert!(thm.hyps().is_empty());
        let inr_bv = Term::app(inr(a.clone(), b.clone()), bv.clone());
        let inr_bv2 = Term::app(inr(a.clone(), b.clone()), bv2.clone());
        let expected = inr_bv
            .equals(inr_bv2)
            .unwrap()
            .imp(bv.equals(bv2).unwrap())
            .unwrap();
        assert_eq!(thm.concl(), &expected);
    }

    #[test]
    fn inl_inj_at_unit() {
        // Injectivity even at the singleton carrier — `inl a = inl a' ⟹ a = a'`
        // holds for `α = unit`.
        let u = Type::unit();
        let av = Term::free("av", u.clone());
        let av2 = Term::free("av2", u.clone());
        let thm = inl_inj(&u, &u, &av, &av2).unwrap();
        assert!(thm.hyps().is_empty());
    }

    #[test]
    fn case_inl_at_unit() {
        // The delicate singleton-carrier case.
        let u = Type::unit();
        let f = Term::free("f", Type::fun(u.clone(), u.clone()));
        let g = Term::free("g", Type::fun(u.clone(), u.clone()));
        let av = Term::free("av", u.clone());
        let thm = case_inl(&u, &u, &u, &f, &g, &av).unwrap();
        assert!(thm.hyps().is_empty());
        assert_eq!(rhs_of(&thm).unwrap(), Term::app(f, av));
    }
}
