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
//! This is the foundation under [`init::option`](crate::init::option).
//! The `coprodCase` computation equations build on the round-trips here
//! (still to come).

use covalence_core::{Error, Result, Term, Thm, Type};

use crate::init::eq::delta_head;
use crate::init::ext::{TermExt, ThmExt};
use crate::init::logic::{exists_intro, simp, truth};

pub use covalence_core::defs::{coprod, coprod_case, inl, inr};

use covalence_core::defs::coprod_spec;

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
        Error::ConnectiveRule(format!("coprod round_trip: predicate is not a disjunction: {disj}"))
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
// Helpers.
// ============================================================================

fn rhs_of(thm: &Thm) -> Result<Term> {
    Ok(thm.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone())
}

/// Parse `App(App(∨, p), q)` → `(p, q)`.
fn parse_or(t: &Term) -> Option<(Term, Term)> {
    let (f, q) = t.as_app()?;
    let (head, p) = f.as_app()?;
    let (spec, _) = head.as_spec()?;
    spec.ptr_eq(&covalence_core::defs::or_spec())
        .then(|| (p.clone(), q.clone()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn inl_ne_inr_is_genuine() {
        // ¬(inl av = inr bv) at α = β = unit — the case the OLD untagged
        // encoding wrongly identified. Now provable, hypothesis-free.
        let u = Type::unit();
        let av = Term::free("av", u.clone());
        let bv = Term::free("bv", u.clone());
        let thm = inl_ne_inr(&u, &u, &av, &bv).unwrap();
        assert!(thm.hyps().is_empty(), "disjointness is proved, no hyps");
        assert!(thm.has_no_obs(), "and oracle-free");
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
}
