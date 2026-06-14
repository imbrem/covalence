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
use crate::init::logic::truth;

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
}
