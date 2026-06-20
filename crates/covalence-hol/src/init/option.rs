//! `option` theorems: the catalogue re-exported, the `option` newtype
//! round-trip, and the key constructor fact `some x ≠ none`.
//!
//! `option α = coprod α unit` (a newtype), with `some a = abs (inl a)`,
//! `none = abs (inr unit.nil)`. So `some x ≠ none` reduces — through the
//! option round-trip — to the coprod injection disjointness
//! [`coprod::inl_ne_inr`], which the tagged encoding makes universal.
//! (Under the *old* untagged coprod, `some unit.nil = none` was provable
//! in `option unit`; this module is the downstream payoff of the fix.)
//!
//! This is the foundation under `list α := stream (option α) where
//! finite`, hence under `set.finite` / `set.card`.

use covalence_core::{Error, Result, Term, Thm, Type};

use crate::init::coprod::inl_ne_inr;
use crate::init::eq::delta_head;
use crate::init::ext::{TermExt, ThmExt};
use crate::init::logic::{exists_elim, exists_intro, truth};

pub use covalence_core::defs::{is_some, none, option, option_case, some, unwrap};

use covalence_core::defs::{option_spec, unit_nil};

// ============================================================================
// Raw coercions of the `option` newtype + constructor unfolding.
// ============================================================================

fn rep_o(alpha: &Type) -> Term {
    Term::spec_rep(option_spec(), vec![alpha.clone()])
}

/// `(⊢ some a = abs (inl a), inl a)` — unfold `some` to its `coprod`
/// representative.
fn some_unfold(alpha: &Type, a: &Term) -> Result<(Thm, Term)> {
    let some_a = Term::app(some(alpha.clone()), a.clone());
    let eq = delta_head(&some_a)?.rhs_conv(|t| t.reduce())?;
    let inner = rhs_of(&eq)?.as_app().ok_or(Error::NotAnEquation)?.1.clone();
    Ok((eq, inner))
}

/// `(⊢ none = abs (inr unit.nil), inr unit.nil)`.
fn none_unfold(alpha: &Type) -> Result<(Thm, Term)> {
    let eq = delta_head(&none(alpha.clone()))?.rhs_conv(|t| t.reduce())?;
    let inner = rhs_of(&eq)?.as_app().ok_or(Error::NotAnEquation)?.1.clone();
    Ok((eq, inner))
}

/// `⊢ rep (abs c) = c` for the `option` newtype — from the kernel's
/// [`Thm::spec_rep_abs_fwd`] with the always-true premise discharged by
/// β + [`truth`].
fn rep_abs(alpha: &Type, c: &Term) -> Result<Thm> {
    let fwd = Thm::spec_rep_abs_fwd(option_spec(), vec![alpha.clone()], c.clone())?;
    let (imp_p, _eq) = fwd.concl().as_app().ok_or(Error::NotAnEquation)?;
    let (_imp, prem) = imp_p.as_app().ok_or(Error::NotAnEquation)?;
    let prem_thm = Thm::beta_conv(prem.clone())?.sym()?.eq_mp(truth())?;
    fwd.imp_elim(prem_thm)
}

// ============================================================================
// `some x ≠ none`.
// ============================================================================

/// `⊢ ¬(some a = none)` — the two `option` constructors are distinct, for
/// **every** `α` (including `α = unit`).
pub fn some_ne_none(alpha: &Type, a: &Term) -> Result<Thm> {
    let some_a = Term::app(some(alpha.clone()), a.clone());
    let eq = some_a.clone().equals(none(alpha.clone()))?;

    // Under H : some a = none, transport to a coprod-level equality and
    // contradict injection disjointness.
    let h = Thm::assume(eq.clone())?;
    let (some_u, inl_a) = some_unfold(alpha, a)?; // ⊢ some a = abs (inl a)
    let (none_u, inr_u) = none_unfold(alpha)?; // ⊢ none = abs (inr unit.nil)
    let abs_eq = some_u.sym()?.trans(h)?.trans(none_u)?; // {H} ⊢ abs (inl a) = abs (inr unit.nil)
    let rep_cong = abs_eq.cong_arg(rep_o(alpha))?; // {H} ⊢ rep (abs (inl a)) = rep (abs (inr unit.nil))
    let coprod_eq = rep_abs(alpha, &inl_a)?
        .sym()?
        .trans(rep_cong)?
        .trans(rep_abs(alpha, &inr_u)?)?; // {H} ⊢ inl a = inr unit.nil
    // ¬(inl a = inr unit.nil) contradicts it.
    let disjoint = inl_ne_inr(alpha, &Type::unit(), a, &unit_nil())?;
    let f = disjoint.not_elim(coprod_eq)?; // {H} ⊢ F
    f.imp_intro(&eq)?.not_intro() // ⊢ ¬(some a = none)
}

// ============================================================================
// Exhaustiveness — every option is `some` or `none`.
// ============================================================================

/// `⊢ (∃a. o = some a) ∨ (o = none)` — every `option α` value is `some`
/// of something or `none`. Genuine: hypothesis- and oracle-free. Maps
/// [`coprod::cases`](crate::init::coprod::cases) on the carrier `rep o`
/// through the option newtype (`inl x ↦ some x`, `inr _ ↦ none` since the
/// right component is the `unit` singleton).
pub fn option_cases(alpha: &Type, o: &Term) -> Result<Thm> {
    use crate::init::coprod::cases;

    let unit = Type::unit();
    let abs = Term::spec_abs(option_spec(), vec![alpha.clone()]);
    let repo = Term::app(rep_o(alpha), o.clone());

    // o = abs (rep o).
    let abs_rep = Thm::spec_abs_rep(option_spec(), vec![alpha.clone()], o.clone())?; // abs (rep o) = o

    // coprod cases on `rep o`: (∃x. rep o = inl x) ∨ (∃y. rep o = inr y).
    let cs = cases(alpha, &unit, &repo)?;
    let (ex_inl, ex_inr) = {
        let (l, r) = cs
            .concl()
            .as_app()
            .and_then(|(orp, r)| orp.as_app().map(|(_, l)| (l.clone(), r.clone())))
            .ok_or(Error::NotAnEquation)?;
        (l, r)
    };

    // The goal `(∃a. o = some a) ∨ (o = none)`.
    let some_a = Term::app(some(alpha.clone()), Term::free("__a", alpha.clone()));
    let goal_some = o.clone().equals(some_a)?.exists("__a", alpha.clone())?;
    let goal_none = o.clone().equals(none(alpha.clone()))?;
    let goal = goal_some.clone().or(goal_none.clone())?;

    // The η-predicates the existentials carry (`λx. rep o = inl x`, etc.),
    // so the `exists_elim` step antecedents match in *applied* form.
    let pred_inl = ex_inl.as_app().ok_or(Error::NotAnEquation)?.1.clone();
    let pred_inr = ex_inr.as_app().ok_or(Error::NotAnEquation)?.1.clone();

    // Left (inl): x fresh, assume `pred_inl x` (rep o = inl x); show o = some x.
    let left_step = {
        let x = Term::free("__cx", alpha.clone());
        let applied = Term::app(pred_inl.clone(), x.clone()); // (λx. rep o = inl x) x
        let h = crate::init::eq::beta_reduce(Thm::assume(applied.clone())?)?; // {applied} ⊢ rep o = inl x
        let (some_u, _) = some_unfold(alpha, &x)?; // some x = abs (inl x)
        let o_eq = abs_rep
            .clone()
            .sym()? // o = abs (rep o)
            .trans(h.cong_arg(abs.clone())?)? // = abs (inl x)
            .trans(some_u.sym()?)?; // = some x
        // pred = λa. o = some a.
        let some_body = o
            .clone()
            .equals(Term::app(some(alpha.clone()), Term::free("__a", alpha.clone())))?;
        let some_pred = Term::abs(alpha.clone(), covalence_core::subst::close(&some_body, "__a"));
        let at_x = crate::init::eq::beta_expand(&some_pred, x.clone(), o_eq)?; // {applied} ⊢ pred x
        let some_intro = exists_intro(some_pred, x.clone(), at_x)?; // {applied} ⊢ ∃a. o = some a
        let body = some_intro.or_intro_l(goal_none.clone())?; // {applied} ⊢ (∃a. o=some a) ∨ (o=none)
        body.imp_intro(&applied)?.all_intro("__cx", alpha.clone())? // ⊢ ∀x. pred_inl x ⟹ goal
    };

    // Right (inr): y : unit fresh, assume `pred_inr y` (rep o = inr y); show o = none.
    let right_step = {
        let y = Term::free("__cy", unit.clone());
        let applied = Term::app(pred_inr.clone(), y.clone());
        let h = crate::init::eq::beta_reduce(Thm::assume(applied.clone())?)?; // {applied} ⊢ rep o = inr y
        let (none_u, _) = none_unfold(alpha)?; // none = abs (inr unit.nil)
        let y_eq_nil = Thm::unit_eq(y.clone(), unit_nil())?; // y = unit.nil
        let inr_eq = y_eq_nil.cong_arg(crate::init::coprod::inr(alpha.clone(), unit.clone()))?; // inr y = inr unit.nil
        let o_eq = abs_rep
            .clone()
            .sym()? // o = abs (rep o)
            .trans(h.cong_arg(abs.clone())?)? // = abs (inr y)
            .trans(inr_eq.cong_arg(abs.clone())?)? // = abs (inr unit.nil)
            .trans(none_u.sym()?)?; // = none
        let body = o_eq.or_intro_r(goal_some.clone())?; // {applied} ⊢ (∃a. o=some a) ∨ (o=none)
        body.imp_intro(&applied)?.all_intro("__cy", unit.clone())? // ⊢ ∀y. pred_inr y ⟹ goal
    };

    // Outer or_elim over `cs`: each branch assumes its existential and
    // discharges it to `goal` via exists_elim.
    let lb = exists_elim(Thm::assume(ex_inl.clone())?, goal.clone(), left_step)?.imp_intro(&ex_inl)?;
    let rb = exists_elim(Thm::assume(ex_inr.clone())?, goal.clone(), right_step)?.imp_intro(&ex_inr)?;
    cs.or_elim(lb, rb)
}

// ============================================================================
// `some` injectivity.
// ============================================================================

/// `⊢ some a = some b ⟹ a = b` — the `some` constructor is injective.
/// Genuine: hypothesis- and oracle-free. Transports through the `option`
/// newtype to the `coprod` representative `inl`, then reads the argument
/// back with `coprod_case id g` ([`case_inl`](crate::init::coprod::case_inl)).
pub fn some_inj(alpha: &Type, a: &Term, b: &Term) -> Result<Thm> {
    use crate::init::coprod::case_inl;
    use covalence_core::defs::id;

    let unit = Type::unit();
    let some_a = Term::app(some(alpha.clone()), a.clone());
    let some_b = Term::app(some(alpha.clone()), b.clone());
    let eq = some_a.clone().equals(some_b.clone())?;

    // Under H : some a = some b, reach `inl a = inl b`.
    let h = Thm::assume(eq.clone())?;
    let (some_a_u, inl_a) = some_unfold(alpha, a)?; // some a = abs (inl a)
    let (some_b_u, inl_b) = some_unfold(alpha, b)?; // some b = abs (inl b)
    let abs_eq = some_a_u.sym()?.trans(h)?.trans(some_b_u)?; // {H} ⊢ abs (inl a) = abs (inl b)
    let rep_cong = abs_eq.cong_arg(rep_o(alpha))?; // {H} ⊢ rep (abs (inl a)) = rep (abs (inl b))
    let inl_eq = rep_abs(alpha, &inl_a)?
        .sym()?
        .trans(rep_cong)?
        .trans(rep_abs(alpha, &inl_b)?)?; // {H} ⊢ inl a = inl b

    // Read the argument out: coprod_case id g (inl ·) = id · = ·.
    let id_a = id(alpha.clone()); // id : α → α
    // The right branch `g : unit → α` is irrelevant; pick `λ_. a`.
    let g = Term::abs(unit.clone(), subst_close_const(a, alpha));
    let case_a = case_inl(alpha, &unit, alpha, &id_a, &g, a)?; // coprod_case id g (inl a) = id a
    let case_b = case_inl(alpha, &unit, alpha, &id_a, &g, b)?; // coprod_case id g (inl b) = id b
    // id a = a, id b = b.
    let id_spec = covalence_core::defs::id_spec();
    let ida = Term::app(id_a.clone(), a.clone())
        .delta_all(id_spec.symbol())?
        .rhs_conv(|t| t.reduce())?; // id a = a
    let idb = Term::app(id_a.clone(), b.clone())
        .delta_all(id_spec.symbol())?
        .rhs_conv(|t| t.reduce())?; // id b = b

    // From inl a = inl b: coprod_case id g (inl a) = coprod_case id g (inl b).
    let case_head = coprod_case_at(alpha, &unit, alpha, &id_a, &g);
    let cong = inl_eq.cong_arg(case_head)?; // {H} ⊢ case (inl a) = case (inl b)
    // a = case (inl a) = case (inl b) = b.
    let a_eq = ida.sym()?.trans(case_a.sym()?)?; // ⊢ a = case (inl a)
    let b_eq = case_b.trans(idb)?; // ⊢ case (inl b) = b
    let ab = a_eq.trans(cong)?.trans(b_eq)?; // {H} ⊢ a = b
    ab.imp_intro(&eq)
}

/// `coprod_case[α,unit,α] f g` — the case head, as a term.
fn coprod_case_at(a: &Type, b: &Type, gamma: &Type, f: &Term, g: &Term) -> Term {
    Term::app(
        Term::app(covalence_core::defs::coprod_case(a.clone(), b.clone(), gamma.clone()), f.clone()),
        g.clone(),
    )
}

/// `close(a)` — the body of the irrelevant `λ_:unit.` right branch. The
/// branch ignores its argument, so `a` stands unchanged (it never
/// references the bound `#0`).
fn subst_close_const(a: &Term, _alpha: &Type) -> Term {
    a.clone()
}

// ============================================================================
// Helpers.
// ============================================================================

fn rhs_of(thm: &Thm) -> Result<Term> {
    Ok(thm.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn some_ne_none_polymorphic() {
        let a = Type::tfree("a");
        let x = Term::free("x", a.clone());
        let thm = some_ne_none(&a, &x).unwrap();
        assert!(thm.hyps().is_empty() && thm.has_no_obs());
        let expected = Term::app(some(a.clone()), x)
            .equals(none(a))
            .unwrap()
            .not()
            .unwrap();
        assert_eq!(thm.concl(), &expected);
    }

    #[test]
    fn option_cases_is_exhaustive() {
        let a = Type::tfree("a");
        let o = Term::free("o", option(a.clone()));
        let thm = option_cases(&a, &o).unwrap();
        assert!(thm.hyps().is_empty() && thm.has_no_obs());
        // ⊢ (∃a. o = some a) ∨ (o = none)
        let some_a = Term::app(some(a.clone()), Term::free("__a", a.clone()));
        let goal_some = o.clone().equals(some_a).unwrap().exists("__a", a.clone()).unwrap();
        let goal_none = o.equals(none(a)).unwrap();
        let expected = goal_some.or(goal_none).unwrap();
        assert_eq!(thm.concl(), &expected);
    }

    #[test]
    fn some_inj_recovers_argument() {
        let a = Type::tfree("a");
        let x = Term::free("x", a.clone());
        let y = Term::free("y", a.clone());
        let thm = some_inj(&a, &x, &y).unwrap();
        assert!(thm.hyps().is_empty() && thm.has_no_obs());
        // ⊢ (some x = some y) ⟹ (x = y)
        let prem = Term::app(some(a.clone()), x.clone())
            .equals(Term::app(some(a.clone()), y.clone()))
            .unwrap();
        let expected = prem.imp(x.equals(y).unwrap()).unwrap();
        assert_eq!(thm.concl(), &expected);
    }

    #[test]
    fn some_ne_none_at_unit() {
        // The case the OLD encoding got wrong: `some unit.nil = none` in
        // `option unit`. Now its negation is a genuine theorem.
        let u = Type::unit();
        let thm = some_ne_none(&u, &unit_nil()).unwrap();
        assert!(thm.hyps().is_empty(), "some ≠ none holds even at unit");
    }
}
