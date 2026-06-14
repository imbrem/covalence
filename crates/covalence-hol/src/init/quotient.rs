//! Quotient lifting — `base / rel` reasoning, derived (no postulates).
//!
//! A quotient `TypeSpec` ([`TypeSpec::quot`](covalence_core::defs::TypeSpec))
//! is **literally a subtype of the powerset** `base → bool`: an element is
//! an equivalence class, represented as the set of its members. So the
//! kernel's witness-free subtype laws ([`Thm::spec_abs_rep`] /
//! [`Thm::spec_rep_abs_fwd`]) apply directly, and quotient reasoning needs
//! no new primitive — exactly the way [`init::set`](crate::init::set)
//! builds the `set` API over a `newtype`.
//!
//! The bridge between a representative `a : base` and its class is
//!
//! ```text
//!     classOf a ≔ λx. rel a x          -- the set of things rel-after a
//!     mkClass a ≔ abs (classOf a)      -- the quotient element [a]
//! ```
//!
//! ## What this module provides
//!
//! - [`mk_class`] — the class constructor `abs (λx. rel a x)`.
//! - [`class_intro`] — the **forward** lifting law: from `Γ ⊢ rel a b`
//!   conclude `Γ ⊢ mkClass a = mkClass b`. This is the workhorse for
//!   *proving quotient equations*: an `int` identity like `mkInt p =
//!   mkInt q` reduces to the `nat` fact `rel p q`. It needs only symmetry
//!   and transitivity of `rel` (supplied as `∀`-theorems) and function
//!   extensionality (derived inline) — **not** the `close` predicate.
//!
//! The converse (`mkClass a = mkClass b ⟹ rel a b`, which additionally
//! needs `Thm::spec_rep_abs_fwd` and a proof that `classOf a` satisfies the
//! quotient's carving predicate) is the next step; see `SKELETONS.md`.

use covalence_core::defs::TypeSpec;
use covalence_core::{Error, Result, Term, Thm, Type};

use crate::init::ext::ThmExt;

/// `λx:base. rel a x` — the equivalence class of `a` as a subset of
/// `base` (the carrier value `mkClass` abstracts).
fn class_of(base: &Type, rel: &Term, a: &Term) -> Term {
    let x = Term::free("_q", base.clone());
    let body = Term::app(Term::app(rel.clone(), a.clone()), x);
    Term::abs(base.clone(), covalence_core::subst::close(&body, "_q"))
}

/// `mkClass a ≔ abs (λx. rel a x) : (spec args)` — the quotient element
/// `[a]`. `spec` must be a quotient/subtype of the powerset `base → bool`.
pub fn mk_class(spec: &TypeSpec, args: &[Type], base: &Type, rel: &Term, a: &Term) -> Term {
    let abs = Term::spec_abs(spec.clone(), args.to_vec());
    Term::app(abs, class_of(base, rel, a))
}

/// **Forward lifting.** From `ab : Γ ⊢ rel a b` conclude
/// `Γ ⊢ mkClass a = mkClass b`.
///
/// `symm` / `trans` are the symmetry / transitivity of `rel`, as the
/// `∀`-theorems `⊢ ∀x y. rel x y ⟹ rel y x` and
/// `⊢ ∀x y z. rel x y ⟹ rel y z ⟹ rel x z`. The relation, `a`, and `b`
/// are read back from `ab`'s conclusion `rel a b`.
///
/// Derivation: `rel a b` makes membership-after-`a` and membership-after-
/// `b` pointwise-equivalent (`rel a x ⟺ rel b x`, by symm/trans), so the
/// two class-sets are equal by extensionality (`abs` of a pointwise
/// equation, no η needed since the sets are λ's), and congruence under
/// `abs` lifts that to the classes.
pub fn class_intro(
    spec: &TypeSpec,
    args: &[Type],
    base: &Type,
    symm: &Thm,
    trans: &Thm,
    ab: Thm,
) -> Result<Thm> {
    let (rel, a, b) = dest_rel(ab.concl())?;

    // Pointwise: ⊢ (rel a x) = (rel b x) for a fresh `x`.
    let x = Term::free("_q", base.clone());
    let rel_ax = app2(&rel, &a, &x);
    let rel_bx = app2(&rel, &b, &x);

    // rel b a, from symm applied to `ab`.
    let ba = inst3(symm, &[&a, &b])?.imp_elim(ab.clone())?; // Γ ⊢ rel b a
    // {rel a x} ⊢ rel b x : trans rel b a, rel a x.
    let fwd = inst3(trans, &[&b, &a, &x])?
        .imp_elim(ba)?
        .imp_elim(Thm::assume(rel_ax.clone())?)?;
    // {rel b x} ⊢ rel a x : trans rel a b, rel b x.
    let bwd = inst3(trans, &[&a, &b, &x])?
        .imp_elim(ab)?
        .imp_elim(Thm::assume(rel_bx.clone())?)?;
    // ⊢ (rel a x) = (rel b x).
    let pointwise = bwd.deduct_antisym(fwd)?;

    // abs of a pointwise equation = the two class-sets are equal.
    let classes_eq = pointwise.abs("_q", base.clone())?; // Γ ⊢ (λx. rel a x) = (λx. rel b x)
    // Congruence under `abs`.
    let abs = Term::spec_abs(spec.clone(), args.to_vec());
    classes_eq.cong_arg(abs) // Γ ⊢ mkClass a = mkClass b
}

/// Parse `rel a b` — `App(App(rel, a), b)` — into `(rel, a, b)`.
fn dest_rel(t: &Term) -> Result<(Term, Term, Term)> {
    let (rel_a, b) = t
        .as_app()
        .ok_or_else(|| Error::ConnectiveRule(format!("quotient: `{t}` is not `rel a b`")))?;
    let (rel, a) = rel_a
        .as_app()
        .ok_or_else(|| Error::ConnectiveRule(format!("quotient: `{t}` is not `rel a b`")))?;
    Ok((rel.clone(), a.clone(), b.clone()))
}

/// `App(App(rel, a), b)`.
fn app2(rel: &Term, a: &Term, b: &Term) -> Term {
    Term::app(Term::app(rel.clone(), a.clone()), b.clone())
}

/// Specialise a `∀x y[ z]. …` theorem at the given witnesses, in order.
fn inst3(thm: &Thm, witnesses: &[&Term]) -> Result<Thm> {
    let mut acc = thm.clone();
    for w in witnesses {
        acc = acc.all_elim((*w).clone())?;
    }
    Ok(acc)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::init::ext::TermExt;
    use covalence_core::defs::TypeSpec;

    /// Symmetry / transitivity of `=` at `nat`, as the ∀-theorems
    /// `class_intro` expects.
    fn eq_symm() -> Thm {
        let (x, y) = (Term::free("x", Type::nat()), Term::free("y", Type::nat()));
        Thm::assume(eq(&x, &y))
            .unwrap()
            .sym()
            .unwrap()
            .imp_intro(&eq(&x, &y))
            .unwrap()
            .all_intro("y", Type::nat())
            .unwrap()
            .all_intro("x", Type::nat())
            .unwrap()
    }
    fn eq_trans() -> Thm {
        let (x, y, z) = (
            Term::free("x", Type::nat()),
            Term::free("y", Type::nat()),
            Term::free("z", Type::nat()),
        );
        Thm::assume(eq(&x, &y))
            .unwrap()
            .trans(Thm::assume(eq(&y, &z)).unwrap())
            .unwrap()
            .imp_intro(&eq(&y, &z))
            .unwrap()
            .imp_intro(&eq(&x, &y))
            .unwrap()
            .all_intro("z", Type::nat())
            .unwrap()
            .all_intro("y", Type::nat())
            .unwrap()
            .all_intro("x", Type::nat())
            .unwrap()
    }
    fn eq(a: &Term, b: &Term) -> Term {
        a.clone().equals(b.clone()).unwrap()
    }

    #[test]
    fn class_intro_lifts_a_relation_fact_to_a_class_equation() {
        // Quotient of nat by equality (classes are singletons).
        let rel = Term::eq_op(Type::nat());
        let spec = TypeSpec::quot(
            smol_str::SmolStr::new_static("q.test"),
            Type::nat(),
            rel.clone(),
        );
        let base = Type::nat();

        // From {a = b} ⊢ a = b, lift to ⊢ mkClass a = mkClass b.
        let a = Term::free("a", base.clone());
        let b = Term::free("b", base.clone());
        let ab = Thm::assume(eq(&a, &b)).unwrap();
        let lifted = class_intro(&spec, &[], &base, &eq_symm(), &eq_trans(), ab).unwrap();

        let expected_l = mk_class(&spec, &[], &base, &rel, &a);
        let expected_r = mk_class(&spec, &[], &base, &rel, &b);
        let (l, r) = lifted.concl().as_eq().unwrap();
        assert_eq!(l, &expected_l);
        assert_eq!(r, &expected_r);
        // Hypotheses: just the `a = b` we lifted from.
        assert!(lifted.hyps().iter().any(|h| h == &eq(&a, &b)));
    }
}
