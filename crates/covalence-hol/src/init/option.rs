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

use crate::init::coprod::{case_inl, case_inr, cases, inl, inl_ne_inr, inr};
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
// `rep` of the constructors — the bridge to the `coprod` layer.
//
// `some a = abs (inl a)`, so `rep (some a) = rep (abs (inl a)) = inl a` (the
// option newtype's round-trip is unconditional). Symmetrically for `none`.
// These are the option analogues of `coprod`'s `rep_inl`/`rep_inr`, and the
// pieces the `option_case` computations and `option_cases` need.
// ============================================================================

/// `⊢ rep (some a) = inl a` — the `some` representative is the left injection.
fn rep_some(alpha: &Type, a: &Term) -> Result<Thm> {
    let (some_u, inl_a) = some_unfold(alpha, a)?; // ⊢ some a = abs (inl a)
    some_u
        .cong_arg(rep_o(alpha))? // ⊢ rep (some a) = rep (abs (inl a))
        .trans(rep_abs(alpha, &inl_a)?) // ⊢ rep (abs (inl a)) = inl a
}

/// `⊢ rep none = inr unit.nil` — the `none` representative is the right
/// injection at the `unit` carrier.
fn rep_none(alpha: &Type) -> Result<Thm> {
    let (none_u, inr_u) = none_unfold(alpha)?; // ⊢ none = abs (inr unit.nil)
    none_u
        .cong_arg(rep_o(alpha))? // ⊢ rep none = rep (abs (inr unit.nil))
        .trans(rep_abs(alpha, &inr_u)?) // ⊢ rep (abs (inr unit.nil)) = inr unit.nil
}

// ============================================================================
// The `option` eliminator — the `option_case` β-equations.
//
//   ⊢ option_case d f (some x) = f x        (case_some)
//   ⊢ option_case d f none     = d          (case_none)
//
// `option_case d f o ≔ coprod_case f (λ_:unit. d) (rep o)`. δ-unfold the head,
// rewrite `rep (some x)` to `inl x` / `rep none` to `inr unit.nil`, then the
// `coprod_case` β-equation (`case_inl` / `case_inr`) fires; the `none` arm's
// `(λ_. d) unit.nil` β-reduces to `d`.
// ============================================================================

/// `⊢ option_case d f (some x) = f x`. Genuine: hypothesis- and oracle-free.
pub fn case_some(alpha: &Type, beta: &Type, d: &Term, f: &Term, x: &Term) -> Result<Thm> {
    let some_x = Term::app(some(alpha.clone()), x.clone());
    let (g, eps_eq) = case_unfold(alpha, beta, d, f, &some_x)?; // ⊢ option_case … = coprod_case f g (rep (some x))
    // Rewrite `rep (some x)` to `inl x` inside the coprod_case argument.
    let to_inl = eps_eq.rewrite(&rep_some(alpha, x)?)?; // ⊢ option_case … = coprod_case f g (inl x)
    // The coprod left β-equation: coprod_case f g (inl x) = f x.
    let cc = case_inl(alpha, &Type::unit(), beta, f, &g, x)?;
    to_inl.trans(cc)
}

/// `⊢ option_case d f none = d`. Genuine: hypothesis- and oracle-free. The
/// `none` branch's ignored-argument abstraction `(λ_:unit. d) unit.nil`
/// β-reduces to `d`.
pub fn case_none(alpha: &Type, beta: &Type, d: &Term, f: &Term) -> Result<Thm> {
    let (g, eps_eq) = case_unfold(alpha, beta, d, f, &none(alpha.clone()))?;
    let to_inr = eps_eq.rewrite(&rep_none(alpha)?)?; // ⊢ option_case … = coprod_case f g (inr unit.nil)
    // coprod_case f g (inr unit.nil) = g unit.nil = (λ_. d) unit.nil = d.
    let cc = case_inr(alpha, &Type::unit(), beta, f, &g, &unit_nil())?; // = g unit.nil
    to_inr.trans(cc)?.rhs_conv(|t| t.reduce()) // β: (λ_. d) unit.nil = d
}

/// δ-unfold the head `option_case` of `option_case d f o`, returning
/// `(g, ⊢ option_case d f o = coprod_case f g (rep o))` where the carried
/// `g = λ_:unit. d` is the (reduced) `none` branch.
fn case_unfold(
    alpha: &Type,
    beta: &Type,
    d: &Term,
    f: &Term,
    o: &Term,
) -> Result<(Term, Thm)> {
    let oc = option_case(alpha.clone(), beta.clone())
        .apply(d.clone())?
        .apply(f.clone())?
        .apply(o.clone())?;
    // Unfold only the head so the nested `f`/`d`/`o` stay opaque, then β-reduce
    // the exposed redexes to `coprod_case f (λ_. d) (rep o)`.
    let unfold = delta_head(&oc)?.rhs_conv(|t| t.reduce())?;
    // The rhs is `coprod_case f g (rep o)`; pull out `g` (its second argument).
    let rhs = rhs_of(&unfold)?;
    let (cc_f, _rep_o) = rhs.as_app().ok_or(Error::NotAnEquation)?;
    let g = cc_f.as_app().ok_or(Error::NotAnEquation)?.1.clone();
    Ok((g, unfold))
}

// ============================================================================
// `some` injectivity.
// ============================================================================

/// `⊢ some x = some y ⟹ x = y`. The `some` constructor is injective: apply
/// `unwrap` (`= option_case fail id`) to both sides; `case_some` collapses
/// each to the wrapped value.
pub fn some_inj(alpha: &Type, x: &Term, y: &Term) -> Result<Thm> {
    let some_x = Term::app(some(alpha.clone()), x.clone());
    let some_y = Term::app(some(alpha.clone()), y.clone());
    let eq = some_x.clone().equals(some_y.clone())?;
    let h = Thm::assume(eq.clone())?; // {H} ⊢ some x = some y

    // unwrap (some v) = v, via δ-unfold of `unwrap` to `option_case fail id`
    // and `case_some` with `id = λw. w`.
    let unwrap_x = unwrap_some(alpha, x)?; // ⊢ unwrap (some x) = x
    let unwrap_y = unwrap_some(alpha, y)?; // ⊢ unwrap (some y) = y
    let cong = h.cong_arg(unwrap(alpha.clone()))?; // {H} ⊢ unwrap (some x) = unwrap (some y)
    unwrap_x
        .sym()?
        .trans(cong)?
        .trans(unwrap_y)? // {H} ⊢ x = y
        .imp_intro(&eq) // ⊢ some x = some y ⟹ x = y
}

/// `⊢ unwrap (some x) = x` — δ-unfold `unwrap` to `option_case fail id`, then
/// `case_some` reduces it to `id x = x`.
fn unwrap_some(alpha: &Type, x: &Term) -> Result<Thm> {
    let some_x = Term::app(some(alpha.clone()), x.clone());
    let app = Term::app(unwrap(alpha.clone()), some_x);
    // unwrap (some x) = option_case fail (λw. w) (some x).
    let unfold = delta_head(&app)?.rhs_conv(|t| t.reduce())?;
    let rhs = rhs_of(&unfold)?; // option_case fail id (some x)
    let (d, f) = case_args(&rhs)?; // fail , (λw. w)
    let cs = case_some(alpha, alpha, &d, &f, x)?; // = (λw. w) x
    unfold.trans(cs)?.rhs_conv(|t| t.reduce()) // β: (λw. w) x = x
}

/// Pull the `d` (default) and `f` (some-branch) arguments out of an applied
/// `option_case d f o`.
fn case_args(applied: &Term) -> Result<(Term, Term)> {
    let (oc_f, _o) = applied.as_app().ok_or(Error::NotAnEquation)?;
    let (oc_d, f) = oc_f.as_app().ok_or(Error::NotAnEquation)?;
    let d = oc_d.as_app().ok_or(Error::NotAnEquation)?.1.clone();
    Ok((d, f.clone()))
}

// ============================================================================
// Exhaustiveness — every `option α` value is `some _` or `none`.
//
// `coprod`'s `cases` covers `rep o` by its two injections: `rep o = inl x` or
// `rep o = inr u`. Mapping through `o = abs (rep o)` and the constructor
// unfoldings turns each into `o = some x` / `o = none` (the right injection at
// `unit` is `inr unit.nil`, since `unit` is a singleton: `unit_eq` collapses
// any `u : unit` to `unit.nil`).
// ============================================================================

/// `⊢ (∃x. o = some x) ∨ (o = none)` — exhaustiveness of the `option`
/// constructors. Genuine: hypothesis- and oracle-free.
pub fn option_cases(alpha: &Type, o: &Term) -> Result<Thm> {
    let unit = Type::unit();
    let rep_op = rep_o(alpha);
    let rep_o_t = Term::app(rep_op.clone(), o.clone());
    // o = abs (rep o)  (newtype round-trip, both directions trivially true).
    let abs_rep = Thm::spec_abs_rep(option_spec(), vec![alpha.clone()], o.clone())?;

    // coprod `cases` on `rep o : coprod α unit`.
    let cov = cases(alpha, &unit, &rep_o_t)?; // ⊢ (∃x. rep o = inl x) ∨ (∃u. rep o = inr u)

    let goal_some = some_goal(alpha, o)?; // ∃x. o = some x
    let goal_none = o.clone().equals(none(alpha.clone()))?; // o = none
    let goal = goal_some.clone().or(goal_none.clone())?;

    // Left arm: ∃x. rep o = inl x  ⟹  goal (via o = some x).
    let left = cases_some_branch(alpha, o, &abs_rep, &goal_some, &goal_none)?;
    // Right arm: ∃u. rep o = inr u  ⟹  goal (via o = none).
    let right = cases_none_branch(alpha, o, &abs_rep, &goal_some, &goal_none)?;
    let _ = &goal; // documents the disjunction the two arms land in
    cov.or_elim(left, right)
}

/// `∃x. o = some x`.
fn some_goal(alpha: &Type, o: &Term) -> Result<Term> {
    let x = Term::free("__osx", alpha.clone());
    o.clone()
        .equals(Term::app(some(alpha.clone()), x))?
        .exists("__osx", alpha.clone())
}

/// `⊢ (∃x. rep o = inl x) ⟹ goal` — map a left-injection witness to `some`.
fn cases_some_branch(
    alpha: &Type,
    o: &Term,
    abs_rep: &Thm,
    goal_some: &Term,
    goal_none: &Term,
) -> Result<Thm> {
    let unit = Type::unit();
    let ex_inl = {
        let x = Term::free("__cx", alpha.clone());
        Term::app(rep_o(alpha), o.clone())
            .equals(Term::app(inl(alpha.clone(), unit.clone()), x))?
            .exists("__cx", alpha.clone())?
    };
    let pred = ex_inl.as_app().ok_or(Error::NotAnEquation)?.1.clone(); // λx. rep o = inl x
    let x = Term::free("__cx", alpha.clone());
    let ante = Term::app(pred.clone(), x.clone());
    let h = Thm::beta_conv(ante.clone())?.eq_mp(Thm::assume(ante.clone())?)?; // {ante} ⊢ rep o = inl x
    // o = abs (rep o) = abs (inl x) = some x.
    let abs = Term::spec_abs(option_spec(), vec![alpha.clone()]);
    let (some_u, _inl_x) = some_unfold(alpha, &x)?; // ⊢ some x = abs (inl x)
    let o_eq_some = abs_rep
        .clone()
        .sym()? // ⊢ o = abs (rep o)
        .trans(h.cong_arg(abs)?)? // ⊢ o = abs (inl x)
        .trans(some_u.sym()?)?; // ⊢ o = some x
    // ∃-introduce into goal_some, inject into the disjunction.
    let gpred = goal_some.as_app().ok_or(Error::NotAnEquation)?.1.clone();
    let at = Thm::beta_conv(Term::app(gpred.clone(), x.clone()))?
        .sym()?
        .eq_mp(o_eq_some)?; // ⊢ gpred x
    let intro = exists_intro(gpred, x.clone(), at)?.or_intro_l(goal_none.clone())?; // ⊢ goal
    let step = intro
        .imp_intro(&ante)?
        .all_intro("__cx", alpha.clone())?;
    let full = goal_some.clone().or(goal_none.clone())?;
    exists_elim(Thm::assume(ex_inl.clone())?, full, step)?.imp_intro(&ex_inl)
}

/// `⊢ (∃u. rep o = inr u) ⟹ goal` — map a right-injection witness to `none`.
/// `unit_eq` collapses the witness `u : unit` to `unit.nil`, so the right
/// injection is exactly `inr unit.nil` and `o = none`.
fn cases_none_branch(
    alpha: &Type,
    o: &Term,
    abs_rep: &Thm,
    goal_some: &Term,
    goal_none: &Term,
) -> Result<Thm> {
    let unit = Type::unit();
    let ex_inr = {
        let u = Term::free("__cu", unit.clone());
        Term::app(rep_o(alpha), o.clone())
            .equals(Term::app(inr(alpha.clone(), unit.clone()), u))?
            .exists("__cu", unit.clone())?
    };
    let pred = ex_inr.as_app().ok_or(Error::NotAnEquation)?.1.clone(); // λu. rep o = inr u
    let u = Term::free("__cu", unit.clone());
    let ante = Term::app(pred.clone(), u.clone());
    let h = Thm::beta_conv(ante.clone())?.eq_mp(Thm::assume(ante.clone())?)?; // {ante} ⊢ rep o = inr u
    // `unit` is a singleton: u = unit.nil, so `inr u = inr unit.nil`.
    let u_eq_nil = Thm::unit_eq(u.clone(), unit_nil())?; // ⊢ u = unit.nil
    let inr_eq = Thm::refl(inr(alpha.clone(), unit.clone()))?.cong_app(u_eq_nil)?; // ⊢ inr u = inr unit.nil
    // o = abs (rep o) = abs (inr u) = abs (inr unit.nil) = none.
    let abs = Term::spec_abs(option_spec(), vec![alpha.clone()]);
    let (none_u, _inr_nil) = none_unfold(alpha)?; // ⊢ none = abs (inr unit.nil)
    let o_eq_none = abs_rep
        .clone()
        .sym()? // ⊢ o = abs (rep o)
        .trans(h.cong_arg(abs.clone())?)? // ⊢ o = abs (inr u)
        .trans(inr_eq.cong_arg(abs)?)? // ⊢ o = abs (inr unit.nil)
        .trans(none_u.sym()?)?; // ⊢ o = none
    let inject = o_eq_none.or_intro_r(goal_some.clone())?; // ⊢ goal
    let step = inject
        .imp_intro(&ante)?
        .all_intro("__cu", unit.clone())?;
    let full = goal_some.clone().or(goal_none.clone())?;
    exists_elim(Thm::assume(ex_inr.clone())?, full, step)?.imp_intro(&ex_inr)
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
    fn some_ne_none_at_unit() {
        // The case the OLD encoding got wrong: `some unit.nil = none` in
        // `option unit`. Now its negation is a genuine theorem.
        let u = Type::unit();
        let thm = some_ne_none(&u, &unit_nil()).unwrap();
        assert!(thm.hyps().is_empty(), "some ≠ none holds even at unit");
    }

    fn ab() -> (Type, Type) {
        (Type::tfree("a"), Type::tfree("b"))
    }

    #[test]
    fn case_some_computes() {
        // ⊢ option_case d f (some x) = f x.
        let (a, b) = ab();
        let d = Term::free("d", b.clone());
        let f = Term::free("f", Type::fun(a.clone(), b.clone()));
        let x = Term::free("x", a.clone());
        let thm = case_some(&a, &b, &d, &f, &x).unwrap();
        assert!(thm.hyps().is_empty() && thm.has_no_obs(), "proved, not postulated");
        let lhs = option_case(a.clone(), b.clone())
            .apply(d)
            .unwrap()
            .apply(f.clone())
            .unwrap()
            .apply(Term::app(some(a), x.clone()))
            .unwrap();
        assert_eq!(thm.concl(), &lhs.equals(Term::app(f, x)).unwrap());
    }

    #[test]
    fn case_none_computes() {
        // ⊢ option_case d f none = d.
        let (a, b) = ab();
        let d = Term::free("d", b.clone());
        let f = Term::free("f", Type::fun(a.clone(), b.clone()));
        let thm = case_none(&a, &b, &d, &f).unwrap();
        assert!(thm.hyps().is_empty() && thm.has_no_obs());
        assert_eq!(rhs_of(&thm).unwrap(), d);
    }

    #[test]
    fn case_some_at_unit() {
        // The singleton-carrier case the old untagged encoding mishandled.
        let u = Type::unit();
        let d = Term::free("d", u.clone());
        let f = Term::free("f", Type::fun(u.clone(), u.clone()));
        let thm = case_some(&u, &u, &d, &f, &unit_nil()).unwrap();
        assert!(thm.hyps().is_empty());
        assert_eq!(rhs_of(&thm).unwrap(), Term::app(f, unit_nil()));
    }

    #[test]
    fn some_inj_is_genuine() {
        // ⊢ some x = some y ⟹ x = y.
        let a = Type::tfree("a");
        let x = Term::free("x", a.clone());
        let y = Term::free("y", a.clone());
        let thm = some_inj(&a, &x, &y).unwrap();
        assert!(thm.hyps().is_empty() && thm.has_no_obs());
        let some_x = Term::app(some(a.clone()), x.clone());
        let some_y = Term::app(some(a.clone()), y.clone());
        let expected = some_x.equals(some_y).unwrap().imp(x.equals(y).unwrap()).unwrap();
        assert_eq!(thm.concl(), &expected);
    }

    #[test]
    fn option_cases_covers_some_and_none() {
        // ⊢ (∃x. o = some x) ∨ (o = none).
        let a = Type::tfree("a");
        let o = Term::free("o", option(a.clone()));
        let thm = option_cases(&a, &o).unwrap();
        assert!(thm.hyps().is_empty() && thm.has_no_obs());
        let some_g = some_goal(&a, &o).unwrap();
        let none_g = o.equals(none(a)).unwrap();
        assert_eq!(thm.concl(), &some_g.or(none_g).unwrap());
    }

    #[test]
    fn option_cases_at_unit() {
        // Exhaustiveness even at `option unit`, where some/none would have
        // collided under the old untagged encoding.
        let u = Type::unit();
        let o = Term::free("o", option(u.clone()));
        let thm = option_cases(&u, &o).unwrap();
        assert!(thm.hyps().is_empty());
    }
}
