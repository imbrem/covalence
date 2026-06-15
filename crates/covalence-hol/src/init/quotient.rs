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
//!   extensionality (derived inline) — **not** the carving predicate.
//! - [`class_elim`] — the **converse** lifting law: from
//!   `Γ ⊢ mkClass a = mkClass b` conclude `Γ ⊢ rel a b`. For
//!   dis-equations / order. Needs only reflexivity of `rel`.
//!
//! ## The round-trip — [`round_trip`]
//!
//! For order and for *quotient induction* (relating an element to
//! `mk_class` of its representative) we also need that the chosen
//! representative of a class is back in the class — [`round_trip`] proves
//! `⊢ rel a (rep_class (mk_class a))`. It rests on the kernel's
//! carrier-side round-trip [`Thm::spec_rep_abs_fwd`] (which needs that
//! `classOf a` satisfies the `quot` carving predicate `λS. ∃z. S =
//! classOf z` — proved trivially by [`quot_pred_holds`], witness `z := a`,
//! `classOf a = classOf a` by `refl`) plus Hilbert choice
//! [`Thm::select_ax`] (with `refl` supplying the non-emptiness witness
//! that the ε-picked representative is real).
//!
//! The image predicate makes both `quot_pred_holds` and `class_elim`
//! cheap: there is no upward-closure obligation (the source of the old
//! `symm`/`trans`/`or_elim` proof), only the single membership equation
//! `classOf a = classOf z`.

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
// The round-trip `rel a (rep_class (mk_class a))` and the converse lift
// ============================================================================
//
// For the order axioms and for *quotient induction* (relating an element to
// `mk_class` of its representative) we need that the chosen representative
// of a class is back in the class. Built from `Thm::spec_rep_abs_fwd` (the
// carrier-side round-trip, needing the `quot` predicate holds of `classOf
// a`) + `Thm::select_ax` (Hilbert choice).

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
/// image carving predicate `P = λS. ∃z. S = classOf z` (`= spec.tm()`).
/// Trivial: witness `z := a`, and `classOf a = classOf a` by reflexivity
/// of `=`. Needs **nothing** about `rel` itself.
fn quot_pred_holds(spec: &TypeSpec, base: &Type, rel: &Term, a: &Term) -> Result<Thm> {
    let coa = class_of(base, rel, a); // λx. rel a x
    let pred = spec
        .tm()
        .ok_or_else(|| Error::ConnectiveRule("quotient: spec has no carving predicate".into()))?
        .clone();
    let body_eq = Thm::beta_conv(Term::app(pred, coa.clone()))?; // ⊢ P(coa) = (∃z. coa = classOf z)
    let body = body_eq
        .concl()
        .as_eq()
        .ok_or(Error::NotAnEquation)?
        .1
        .clone();
    let exists_pred = body.as_app().ok_or(Error::NotAnEquation)?.1.clone(); // λz. coa = classOf z

    // ⊢ exists_pred a, i.e. `coa = classOf a`, which is `coa = coa` (refl).
    let pa = Thm::beta_conv(Term::app(exists_pred.clone(), a.clone()))?; // ⊢ (exists_pred a) = (coa = classOf a)
    let proof = pa.sym()?.eq_mp(Thm::refl(coa.clone())?)?; // ⊢ exists_pred a
    let ne = logic::exists_intro(exists_pred, a.clone(), proof)?; // ⊢ ∃z. coa = classOf z
    body_eq.sym()?.eq_mp(ne) // ⊢ P(coa)
}

/// **Round-trip.** `⊢ rel a (rep_class (mk_class a))` — the chosen
/// representative of `a`'s class is `rel`-related to `a`. `refl` (`⊢ ∀x.
/// rel x x`) witnesses that `a` is in its own class, so the ε-picked
/// representative is real.
pub fn round_trip(
    spec: &TypeSpec,
    args: &[Type],
    base: &Type,
    rel: &Term,
    refl: &Thm,
    a: &Term,
) -> Result<Thm> {
    let coa = class_of(base, rel, a);
    let abs = Term::spec_abs(spec.clone(), args.to_vec());
    let mkc = Term::app(abs, coa.clone()); // mk_class a

    // rep(mkc) = coa.
    let ph = quot_pred_holds(spec, base, rel, a)?;
    let rep_abs = Thm::spec_rep_abs_fwd(spec.clone(), args.to_vec(), coa.clone())?.imp_elim(ph)?;

    // φ = λq. (rep mkc) q ;  eps = ε φ = rep_class(mkc).
    let phi = rep_pred(spec, args, base, &mkc);
    let eps = Term::app(Term::select_op(base.clone()), phi.clone());

    // ⊢ φ a, since φ a → (rep mkc) a = coa a → rel a a.
    let rel_aa = inst3(refl, &[a])?;
    let coa_a = Thm::beta_conv(Term::app(coa.clone(), a.clone()))?
        .sym()?
        .eq_mp(rel_aa)?; // ⊢ coa a
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

/// **Converse lifting.** From `eq : Γ ⊢ mkClass a = mkClass b` conclude
/// `Γ ⊢ rel a b`. The dual of [`class_intro`], for dis-equations and
/// order: a class equation now *implies* the underlying `~`-fact, because
/// the [junk-free `quot`](covalence_core::defs::TypeSpec::quot) predicate
/// makes every inhabitant exactly one class.
///
/// `a`, `b` are passed explicitly (they cannot be read off `mkClass a`,
/// whose representative-set hides them). `refl` (`⊢ ∀x. rel x x`) is the
/// only `rel` property needed.
///
/// Derivation: apply `rep` to both sides — `rep(mkClass a) = rep(mkClass
/// b)` — and use [`quot_pred_holds`] + [`Thm::spec_rep_abs_fwd`] to rewrite
/// each into its class set, giving `classOf a = classOf b`. Apply both
/// sides to `b`: `rel a b = rel b b`; `rel b b` holds by `refl`, so
/// `rel a b`.
pub fn class_elim(
    spec: &TypeSpec,
    args: &[Type],
    base: &Type,
    rel: &Term,
    refl: &Thm,
    a: &Term,
    b: &Term,
    eq: Thm,
) -> Result<Thm> {
    let coa = class_of(base, rel, a);
    let cob = class_of(base, rel, b);
    let rep = Term::spec_rep(spec.clone(), args.to_vec());

    // ⊢ rep(mkClass a) = rep(mkClass b).
    let rep_eq = eq.cong_arg(rep)?;
    // ⊢ rep(abs coa) = coa  and  ⊢ rep(abs cob) = cob.
    let ra = Thm::spec_rep_abs_fwd(spec.clone(), args.to_vec(), coa.clone())?
        .imp_elim(quot_pred_holds(spec, base, rel, a)?)?;
    let rb = Thm::spec_rep_abs_fwd(spec.clone(), args.to_vec(), cob.clone())?
        .imp_elim(quot_pred_holds(spec, base, rel, b)?)?;
    // ⊢ classOf a = classOf b.
    let classes_eq = ra.sym()?.trans(rep_eq)?.trans(rb)?;

    // Apply to `b`: ⊢ coa b = cob b, and β-reduce each side.
    let at_b = classes_eq.cong_fn(b.clone())?; // ⊢ coa b = cob b
    let lhs = Thm::beta_conv(Term::app(coa, b.clone()))?; // ⊢ coa b = rel a b
    let rhs = Thm::beta_conv(Term::app(cob, b.clone()))?; // ⊢ cob b = rel b b
    let rel_eq = lhs.sym()?.trans(at_b)?.trans(rhs)?; // ⊢ rel a b = rel b b

    let rel_bb = inst3(refl, &[b])?; // ⊢ rel b b
    rel_eq.sym()?.eq_mp(rel_bb) // ⊢ rel a b
}

/// **Reconstruction (quotient induction base).** `⊢ a = mk_class(rep_class
/// a)` for *any* quotient element `a : spec args` — every inhabitant of the
/// junk-free quotient is the class of (a representative drawn from) itself.
/// This is the keystone for the nested-op `int` axioms: it lets a bound
/// `int` variable be replaced by `mk_class` of a `nat×nat` pair, after which
/// the operation computation rules collapse to `nat` algebra.
///
/// `base_witness : base` supplies non-emptiness of the carving image
/// predicate `P = λS. ∃z. S = classOf z` (any base element works; its class
/// witnesses `∃S. P S`, killing the `¬∃` escape disjunct of
/// [`Thm::spec_rep_abs_back`]). `refl`/`symm`/`trans` are the equivalence
/// properties of `rel` (as the usual `∀`-theorems).
///
/// Derivation: `rep a` satisfies `P` (the back rule + non-emptiness), so
/// `rep a = classOf z` for some `z`. The chosen representative `eps =
/// rep_class a = ε(λp. rep a p)` then lies in that class (`rel z eps`, by
/// `select_ax` and `rel z z`), so `class_intro` gives `mk_class z = mk_class
/// eps`; and `mk_class z = abs(classOf z) = abs(rep a) = a`.
#[allow(clippy::too_many_arguments)]
pub fn recon(
    spec: &TypeSpec,
    args: &[Type],
    base: &Type,
    rel: &Term,
    refl: &Thm,
    symm: &Thm,
    trans: &Thm,
    base_witness: &Term,
    a: &Term,
) -> Result<Thm> {
    let abs = Term::spec_abs(spec.clone(), args.to_vec());
    let rep = Term::spec_rep(spec.clone(), args.to_vec());
    let rep_a = Term::app(rep.clone(), a.clone());

    // ⊢ abs(rep a) = a.
    let abs_rep = Thm::spec_abs_rep(spec.clone(), args.to_vec(), a.clone())?;

    // ⊢ P(rep a) ∨ ¬∃S. P S — back direction at `rep a`, whose premise
    // `rep(abs(rep a)) = rep a` is `abs_rep` pushed under `rep`.
    let back = Thm::spec_rep_abs_back(spec.clone(), args.to_vec(), rep_a.clone())?;
    let prem = abs_rep.clone().cong_arg(rep.clone())?; // rep(abs(rep a)) = rep a
    let disj = back.imp_elim(prem)?;

    // Peel the two disjuncts `P(rep a)` and `¬∃S. P S` off the conclusion.
    let (p_rep_a_tm, notex) = {
        let (or_l, notex) = disj
            .concl()
            .as_app()
            .ok_or_else(|| Error::ConnectiveRule("recon: disjunction shape".into()))?;
        let (_or, l) = or_l
            .as_app()
            .ok_or_else(|| Error::ConnectiveRule("recon: disjunction shape".into()))?;
        (l.clone(), notex.clone())
    };

    // ⊢ ∃S. P S, witnessed by `classOf(base_witness)`. Build it against the
    // exact `λS. P S` inside `notex` so the right branch's `not_elim` lines up.
    let exists_p = {
        let inner = notex
            .as_app()
            .ok_or_else(|| Error::ConnectiveRule("recon: ¬∃ shape".into()))?
            .1; // exists_op (λS. P S)
        let eta_pred = inner
            .as_app()
            .ok_or_else(|| Error::ConnectiveRule("recon: ∃ shape".into()))?
            .1
            .clone(); // λS. P S
        let cow = class_of(base, rel, base_witness);
        let ph = quot_pred_holds(spec, base, rel, base_witness)?; // ⊢ P(cow)
        let proof = Thm::beta_conv(Term::app(eta_pred.clone(), cow.clone()))?
            .sym()?
            .eq_mp(ph)?; // ⊢ (λS. P S) cow
        logic::exists_intro(eta_pred, cow, proof)?
    };

    // ⊢ P(rep a): identity on the left, ex-falso (¬∃ vs ∃) on the right.
    let p_rep_a = {
        let left = Thm::assume(p_rep_a_tm.clone())?.imp_intro(&p_rep_a_tm)?;
        let right = Thm::assume(notex.clone())?
            .not_elim(exists_p)?
            .false_elim(p_rep_a_tm.clone())?
            .imp_intro(&notex)?;
        disj.or_elim(left, right)?
    };

    // ⊢ ∃z. rep a = classOf z — `P(rep a)` β-reduced.
    let exists_z = Thm::beta_conv(p_rep_a_tm)?.eq_mp(p_rep_a)?;
    let pred_z = exists_z
        .concl()
        .as_app()
        .ok_or_else(|| Error::ConnectiveRule("recon: ∃z shape".into()))?
        .1
        .clone(); // λz. rep a = classOf z

    // step: ⊢ ∀z. (rep a = classOf z) ⟹ (a = mk_class(rep_class a)).
    let eps = rep_class(spec, args, base, a); // ε(λp. rep a p)
    let phi = rep_pred(spec, args, base, a); // λp. (rep a) p
    let goal_rhs = mk_class(spec, args, base, rel, &eps);
    let z = Term::free("__recon_z", base.clone());
    // `exists_elim` reads the antecedent as the *un-reduced* `pred_z z`; assume
    // that and β-reduce to the underlying `rep a = classOf z` for the work.
    let app_tm = Term::app(pred_z.clone(), z.clone());
    let h = Thm::beta_conv(app_tm.clone())?.eq_mp(Thm::assume(app_tm.clone())?)?; // {pred_z z} ⊢ rep a = classOf z
    let coz = class_of(base, rel, &z); // classOf z

    // ⊢ (rep a) z ← (classOf z) z ← rel z z.
    let rel_zz = inst3(refl, &[&z])?;
    let coz_z = Thm::beta_conv(Term::app(coz.clone(), z.clone()))?
        .sym()?
        .eq_mp(rel_zz)?; // ⊢ (classOf z) z
    let repa_z = h.clone().cong_fn(z.clone())?.sym()?.eq_mp(coz_z)?; // ⊢ (rep a) z
    // ⊢ φ z, then Hilbert choice ⟹ φ eps.
    let phi_z = Thm::beta_conv(Term::app(phi.clone(), z.clone()))?
        .sym()?
        .eq_mp(repa_z)?;
    let phi_eps = Thm::select_ax(phi.clone(), z.clone())?.imp_elim(phi_z)?;
    let repa_eps = Thm::beta_conv(Term::app(phi.clone(), eps.clone()))?.eq_mp(phi_eps)?; // ⊢ (rep a) eps
    // ⊢ rel z eps, via `h`.
    let coz_eps = h.clone().cong_fn(eps.clone())?.eq_mp(repa_eps)?; // ⊢ (classOf z) eps
    let rel_z_eps = Thm::beta_conv(Term::app(coz, eps))?.eq_mp(coz_eps)?; // ⊢ rel z eps
    // class_intro ⟹ ⊢ mk_class z = mk_class eps.
    let classes = class_intro(spec, args, base, symm, trans, rel_z_eps)?;
    // ⊢ a = mk_class eps.
    let mkz_eq_a = h.sym()?.cong_arg(abs)?.trans(abs_rep)?; // abs(classOf z) = a
    let body = mkz_eq_a.sym()?.trans(classes)?; // {h} ⊢ a = mk_class eps
    let step = body
        .imp_intro(&app_tm)?
        .all_intro("__recon_z", base.clone())?;

    logic::exists_elim(exists_z, a.clone().equals(goal_rhs)?, step)
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
    /// `⊢ ∀x. x = x` — reflexivity of `=` at `nat`, the only `rel`
    /// property `class_elim` / `round_trip` need.
    fn eq_refl() -> Thm {
        let x = Term::free("x", Type::nat());
        Thm::refl(x).unwrap().all_intro("x", Type::nat()).unwrap()
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

    /// `nat`-by-`=` quotient: classes are singletons, so `mkClass a =
    /// mkClass b` must imply `a = b`.
    fn nat_eq_quot() -> (TypeSpec, Term, Type) {
        let rel = Term::eq_op(Type::nat());
        let spec = TypeSpec::quot(
            smol_str::SmolStr::new_static("q.test"),
            Type::nat(),
            rel.clone(),
        );
        (spec, rel, Type::nat())
    }

    #[test]
    fn class_elim_recovers_the_relation_from_a_class_equation() {
        let (spec, rel, base) = nat_eq_quot();
        let a = Term::free("a", base.clone());
        let b = Term::free("b", base.clone());

        // From {mkClass a = mkClass b} ⊢ …, recover ⊢ a = b.
        let class_eq = mk_class(&spec, &[], &base, &rel, &a)
            .equals(mk_class(&spec, &[], &base, &rel, &b))
            .unwrap();
        let assumed = Thm::assume(class_eq.clone()).unwrap();
        let recovered = class_elim(&spec, &[], &base, &rel, &eq_refl(), &a, &b, assumed).unwrap();

        assert_eq!(recovered.concl(), &eq(&a, &b));
        // The only hypothesis is the class equation we started from.
        assert!(recovered.hyps().iter().any(|h| h == &class_eq));
    }

    #[test]
    fn class_intro_then_class_elim_round_trips() {
        let (spec, rel, base) = nat_eq_quot();
        let a = Term::free("a", base.clone());
        let b = Term::free("b", base.clone());

        // a = b  --intro-->  mkClass a = mkClass b  --elim-->  a = b.
        let ab = Thm::assume(eq(&a, &b)).unwrap();
        let lifted = class_intro(&spec, &[], &base, &eq_symm(), &eq_trans(), ab).unwrap();
        let back = class_elim(&spec, &[], &base, &rel, &eq_refl(), &a, &b, lifted).unwrap();
        assert_eq!(back.concl(), &eq(&a, &b));
        assert!(back.hyps().iter().any(|h| h == &eq(&a, &b)));
    }

    #[test]
    fn recon_reconstructs_an_element_as_its_class() {
        let (spec, rel, base) = nat_eq_quot();
        let a = Term::free("a", Type::spec(spec.clone(), vec![])); // a quotient element
        let bw = super::super::nat::zero(); // any base element witnesses non-emptiness
        let rt = recon(
            &spec,
            &[],
            &base,
            &rel,
            &eq_refl(),
            &eq_symm(),
            &eq_trans(),
            &bw,
            &a,
        )
        .expect("recon on nat-eq quotient");
        // ⊢ a = mk_class(rep_class a), hypothesis-free.
        assert!(rt.hyps().is_empty(), "recon is genuine");
        let (l, r) = rt.concl().as_eq().expect("recon yields an equation");
        assert_eq!(l, &a);
        assert_eq!(
            r,
            &mk_class(&spec, &[], &base, &rel, &rep_class(&spec, &[], &base, &a))
        );
    }
}
