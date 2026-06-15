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
//! ## The converse direction — [`round_trip`]
//!
//! For dis-equations / order / quotient-induction we need the *converse*
//! ingredient: the chosen representative of a class is back in the class —
//! [`round_trip`] proves `⊢ rel a (rep_class (mk_class a))`. It rests on
//! the kernel's carrier-side round-trip [`Thm::spec_rep_abs_fwd`] (which
//! needs that `classOf a` satisfies the `close` carving predicate — proved
//! by [`close_pred_holds`], non-emptiness from `refl`, upward-closure from
//! `symm`/`trans` after `or_elim` on the symmetric closure) plus Hilbert
//! choice [`Thm::select_ax`].
//!
//! ⚠️ **Two gotchas, handled.** (1) `close_predicate` writes membership as
//! `S x`, so under `S := classOf a` the proof works with the η-expanded
//! `λx. (classOf a) x` (extract the `exists`/closed parts from
//! `beta_conv`'s RHS). (2) When `rel` is itself a λ (`int_rel`), plain
//! `reduce` over-reduces `rel a x` into its body; the membership/closure
//! unfolds use single-step `beta_conv` / [`beta2`] so `rel`-applications
//! survive (matching the equivalence lemmas).

use covalence_core::defs::TypeSpec;
use covalence_core::{Error, Result, Term, Thm, Type, subst};

use crate::init::ext::{TermExt, ThmExt};
use crate::init::logic;

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

/// Specialise a `∀x …. …` theorem at the given witnesses, in order.
fn inst3(thm: &Thm, witnesses: &[&Term]) -> Result<Thm> {
    let mut acc = thm.clone();
    for w in witnesses {
        acc = acc.all_elim((*w).clone())?;
    }
    Ok(acc)
}

// ============================================================================
// The converse direction: the round-trip `rel a (rep_class (mk_class a))`
// ============================================================================
//
// For the order axioms and for *quotient induction* (relating an element to
// `mk_class` of its representative) we need that the chosen representative
// of a class is back in the class. Built from `Thm::spec_rep_abs_fwd` (the
// carrier-side round-trip, needing the `close` predicate holds of `classOf
// a`) + `Thm::select_ax` (Hilbert choice).

/// `λu v. rel u v ∨ rel v u` — the symmetric closure that
/// [`TypeSpec::quot`](covalence_core::defs::TypeSpec) carves with.
fn sym_closure(base: &Type, rel: &Term) -> Result<Term> {
    let (u, v) = (Term::free("x", base.clone()), Term::free("y", base.clone()));
    let body = app2(rel, &u, &v).or(app2(rel, &v, &u))?;
    let inner = Term::abs(base.clone(), subst::close(&body, "y"));
    Ok(Term::abs(base.clone(), subst::close(&inner, "x")))
}

/// `⊢ (f x y) = body[x, y]` for a curried `f = λu v. …` — two β-steps.
/// (Unlike `reduce`, this stops after unfolding `f`, leaving any `rel`
/// applications *inside* `body` un-reduced — essential when `rel` is itself
/// a λ, e.g. `int_rel`.)
fn beta2(f: &Term, x: &Term, y: &Term) -> Result<Thm> {
    let step1 = Thm::beta_conv(Term::app(f.clone(), x.clone()))?; // f x = λv. body[x]
    let after = step1.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone();
    step1
        .cong_fn(y.clone())? // (f x) y = (λv. body[x]) y
        .trans(Thm::beta_conv(Term::app(after, y.clone()))?) // = body[x, y]
}

/// A bound-variable name not occurring free in `avoid` (capture-safe).
fn fresh(avoid: &Term) -> String {
    let mut i = 0usize;
    loop {
        let name = format!("_q{i}");
        if !subst::has_free_var(avoid, &name) {
            return name;
        }
        i += 1;
    }
}

/// `λq:base. (rep x) q`, with `q` chosen capture-safe for `x`.
fn rep_pred(spec: &TypeSpec, args: &[Type], base: &Type, x: &Term) -> Term {
    let rep = Term::spec_rep(spec.clone(), args.to_vec());
    let rep_x = Term::app(rep, x.clone());
    let q = fresh(&rep_x);
    Term::abs(
        base.clone(),
        subst::close(&Term::app(rep_x, Term::free(&q, base.clone())), &q),
    )
}

/// `ε(λq:base. (rep x) q)` — a chosen representative of the class `x`
/// (`int`'s `rep_pair`, generically).
pub fn rep_class(spec: &TypeSpec, args: &[Type], base: &Type, x: &Term) -> Term {
    Term::app(Term::select_op(base.clone()), rep_pred(spec, args, base, x))
}

/// `⊢ P (classOf a)` — `classOf a = λx. rel a x` satisfies the quotient's
/// `close` carving predicate `P = spec.tm()` (non-empty + symmetric-closure
/// upward-closed). Needs `rel`'s reflexivity / symmetry / transitivity.
fn close_pred_holds(
    spec: &TypeSpec,
    args: &[Type],
    base: &Type,
    rel: &Term,
    refl: &Thm,
    symm: &Thm,
    trans: &Thm,
    a: &Term,
) -> Result<Thm> {
    let _ = args;
    let coa = class_of(base, rel, a); // λx. rel a x
    let pred = spec
        .tm()
        .ok_or_else(|| Error::ConnectiveRule("quotient: spec has no carving predicate".into()))?
        .clone();
    let body_eq = Thm::beta_conv(Term::app(pred, coa.clone()))?; // ⊢ P(coa) = (closed' ∧ nonempty')
    let body = body_eq.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone();
    let nonempty = body.as_app().ok_or(Error::NotAnEquation)?.1.clone();

    // nonempty': ∃x. coa x — witness `a`, since `coa a` → `rel a a`.
    let pred_ne = nonempty.as_app().ok_or(Error::NotAnEquation)?.1.clone();
    let rel_aa = inst3(refl, &[a])?;
    let pne_a = Thm::beta_conv(Term::app(pred_ne.clone(), a.clone()))?; // pred_ne a = coa a
    let coa_a = Thm::beta_conv(beta_rhs(&pne_a)?)?; // coa a = rel a a
    let ne_proof = pne_a.trans(coa_a)?.sym()?.eq_mp(rel_aa)?; // ⊢ pred_ne a
    let ne = logic::exists_intro(pred_ne, a.clone(), ne_proof)?;

    // closed': ∀x y. sym_rel x y ⟹ coa x ⟹ coa y.
    let sym_rel = sym_closure(base, rel)?;
    let (x, y) = (Term::free("x", base.clone()), Term::free("y", base.clone()));
    let symxy = app2(&sym_rel, &x, &y);
    let coax = Term::app(coa.clone(), x.clone());
    let coay = Term::app(coa.clone(), y.clone());

    let h_coax = Thm::assume(coax.clone())?;
    let rel_ax = Thm::beta_conv(coax.clone())?.eq_mp(h_coax)?; // {coa x} ⊢ rel a x
    let disj = {
        let h = Thm::assume(symxy.clone())?;
        beta2(&sym_rel, &x, &y)?.eq_mp(h)? // {sym_rel x y} ⊢ rel x y ∨ rel y x
    };
    let rxy = app2(rel, &x, &y);
    let ryx = app2(rel, &y, &x);
    // rel x y ⟹ rel a y.
    let branch1 = inst3(trans, &[a, &x, &y])?
        .imp_elim(rel_ax.clone())?
        .imp_elim(Thm::assume(rxy.clone())?)?
        .imp_intro(&rxy)?;
    // rel y x ⟹ rel a y, via symm.
    let from_ryx = inst3(symm, &[&y, &x])?.imp_elim(Thm::assume(ryx.clone())?)?;
    let branch2 = inst3(trans, &[a, &x, &y])?
        .imp_elim(rel_ax)?
        .imp_elim(from_ryx)?
        .imp_intro(&ryx)?;
    let rel_ay = disj.or_elim(branch1, branch2)?; // {sym_rel x y, coa x} ⊢ rel a y
    let closed = Thm::beta_conv(coay)?
        .sym()?
        .eq_mp(rel_ay)? // {…} ⊢ coa y
        .imp_intro(&coax)?
        .imp_intro(&symxy)?
        .all_intro("y", base.clone())?
        .all_intro("x", base.clone())?;

    body_eq.sym()?.eq_mp(closed.and_intro(ne)?) // ⊢ P(coa)
}

/// **Round-trip.** `⊢ rel a (rep_class (mk_class a))` — the chosen
/// representative of `a`'s class is `rel`-related to `a`. `refl` / `symm` /
/// `trans` witness that `rel` is an equivalence.
pub fn round_trip(
    spec: &TypeSpec,
    args: &[Type],
    base: &Type,
    rel: &Term,
    refl: &Thm,
    symm: &Thm,
    trans: &Thm,
    a: &Term,
) -> Result<Thm> {
    let coa = class_of(base, rel, a);
    let abs = Term::spec_abs(spec.clone(), args.to_vec());
    let mkc = Term::app(abs, coa.clone()); // mk_class a

    // rep(mkc) = coa.
    let ph = close_pred_holds(spec, args, base, rel, refl, symm, trans, a)?;
    let rep_abs = Thm::spec_rep_abs_fwd(spec.clone(), args.to_vec(), coa.clone())?.imp_elim(ph)?;

    // φ = λq. (rep mkc) q ;  eps = ε φ = rep_class(mkc).
    let phi = rep_pred(spec, args, base, &mkc);
    let eps = Term::app(Term::select_op(base.clone()), phi.clone());

    // ⊢ φ a, since φ a → (rep mkc) a = coa a → rel a a.
    let rel_aa = inst3(refl, &[a])?;
    let coa_a = Thm::beta_conv(Term::app(coa.clone(), a.clone()))?.sym()?.eq_mp(rel_aa)?; // ⊢ coa a
    let repmkc_a = rep_abs.clone().cong_fn(a.clone())?.sym()?.eq_mp(coa_a)?; // ⊢ (rep mkc) a
    let phi_a = Thm::beta_conv(Term::app(phi.clone(), a.clone()))?
        .sym()?
        .eq_mp(repmkc_a)?; // ⊢ φ a

    // Choice: φ a ⟹ φ eps ; then φ eps → (rep mkc) eps = coa eps → rel a eps.
    let phi_eps = Thm::select_ax(phi.clone(), a.clone())?.imp_elim(phi_a)?; // ⊢ φ eps
    let repmkc_eps = Thm::beta_conv(Term::app(phi.clone(), eps.clone()))?.eq_mp(phi_eps)?; // ⊢ (rep mkc) eps
    let coa_eps = rep_abs.cong_fn(eps.clone())?.eq_mp(repmkc_eps)?; // ⊢ coa eps
    Thm::beta_conv(Term::app(coa, eps))?.eq_mp(coa_eps) // ⊢ rel a (rep_class (mk_class a))
}

/// The right-hand side of an equational theorem.
fn beta_rhs(thm: &Thm) -> Result<Term> {
    Ok(thm.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone())
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
