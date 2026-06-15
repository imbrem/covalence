//! `int` theorems: the `defs/int.rs` catalogue re-exported, plus the
//! **postulated** ordered-commutative-ring (with discreteness) theory of
//! HOL `int` — mirroring how [`init::nat`] pairs the `nat` definitions
//! with their Peano facts.
//!
//! [`init::nat`]: crate::init::nat
//!
//! ## Status — all postulated
//!
//! Every theorem here is a `Thm::assume` **postulate** (flagged in
//! `SKELETONS.md`), carrying its statement as a self-hypothesis so the
//! audit trail is visible in any downstream theorem. They are the
//! ingredients an integer-linear-arithmetic certificate checker (the
//! Alethe `la_generic` / `la_mult_*` family) needs:
//!
//! - **Commutative ring** — [`add_comm`] / [`mul_comm`] (**proved**),
//!   [`add_assoc`], [`add_zero`], [`add_neg`], [`mul_assoc`], [`mul_one`],
//!   [`mul_zero`], [`distrib`], [`sub_def`].
//! - **Linear order** — [`lt_irrefl`], [`lt_trans`], [`lt_trichotomy`],
//!   [`le_def`].
//! - **Ordered-ring compatibility** — [`lt_add_mono`], [`lt_mul_pos`].
//! - **Discreteness** (the integer-specific axiom) — [`lt_succ`]:
//!   `a < b ⟺ a + 1 ≤ b`.
//!
//! `int := (nat × nat) / ~` is the Grothendieck construction, so each of
//! these is a *theorem* of HOL, derivable from the `nat` Peano facts in
//! [`init::nat`] through the quotient. Discharging them is downstream
//! work; until then they are the `int` postulate set. The public surface
//! (these `fn`s) does not change when the proofs land — only the bodies.
//!
//! ## What the proofs are waiting on
//!
//! Two ingredients. The **`nat` side** is in place: [`init::nat`] proves
//! the additive theory (`add_comm`/`add_assoc`/`add_zero`/`add_cancel`/…)
//! by induction. The **quotient side** is in place too:
//! [`init::quotient`](crate::init::quotient) lifts a `~`-fact to an
//! `int`-class equation (`class_intro`), and [`int_rel`] is now a **proven
//! equivalence** ([`int_rel_refl`] / [`int_rel_symm`] / [`int_rel_trans`],
//! the last by Grothendieck cancellation on `nat::add_interchange` +
//! `nat::add_cancel`). So `class_intro(spec, …, int_rel_symm(),
//! int_rel_trans(), ⊢ int_rel p q)` already lifts to `mkClass p = mkClass q`
//! over the real `int_ty_spec`.
//!
//! The **converse** law (`mkClass a = mkClass b ⟹ rel a b`, for
//! dis-equations / order) is also in place now:
//! [`init::quotient::class_elim`](crate::init::quotient::class_elim) — the
//! [`quot`](covalence_core::defs::TypeSpec::quot) type is junk-free (its
//! carving predicate is `λS. ∃z. S = classOf z`, so every inhabitant is
//! *exactly one* class), which is what makes the converse and quotient
//! induction sound.
//!
//! Remaining to discharge the postulates below: (1) the **β
//! reconciliation** — `class_intro`'s `classOf a = λx. rel a x` vs
//! `defs/int.rs`'s β-reduced `mk_int`; and (2) **unfolding each `int` op**
//! to its representative-pair body (δ + the quotient coercions) so the
//! axiom reduces to a `nat` fact lifted through `class_intro` /
//! `class_elim`.

use covalence_core::defs::{fst, pair, prod, snd};
use covalence_core::{Error, Result, Term, Thm, Type, subst};

use crate::init::ext::{TermExt, ThmExt};
use crate::init::nat;
use crate::init::quotient;

// Re-export the `defs/int.rs` term catalogue (the operations; the
// `*_spec` handles stay in `covalence_core::defs`).
pub use covalence_core::defs::{
    int_abs, int_add, int_div, int_le, int_lt, int_mod, int_mul, int_neg, int_pred, int_sgn,
    int_sub, int_succ, int_zero,
};

// ============================================================================
// Small term helpers (private — the public surface is theorems)
// ============================================================================

fn int() -> Type {
    Type::int()
}

fn lit(n: i128) -> Term {
    Term::int_lit(n)
}

fn var(name: &str) -> Term {
    Term::free(name, int())
}

fn add(a: Term, b: Term) -> Term {
    Term::app(Term::app(int_add(), a), b)
}

fn mul(a: Term, b: Term) -> Term {
    Term::app(Term::app(int_mul(), a), b)
}

// Used by the test-suite statement builders (the proofs go through
// `neg_via_components`, never this surface form).
#[cfg_attr(not(test), allow(dead_code))]
fn neg(a: Term) -> Term {
    Term::app(int_neg(), a)
}

// ============================================================================
// The Grothendieck relation `int_rel` and its equivalence proofs
// ============================================================================
//
// `int := (nat × nat) / ~` with `(a, b) ~ (c, d) ⟺ a + d = c + b`. We prove
// `~` (here `int_rel`) is an equivalence — the `symm` / `trans` the
// quotient lift (`init::quotient::class_intro`) needs. `refl` / `symm` are
// `nat`-equation manipulations; `trans` is the Grothendieck cancellation
// argument, on `nat::add_interchange` + `nat::add_cancel`.

/// `nat × nat` — the representative-pair carrier of `int`.
fn nn() -> Type {
    prod(Type::nat(), Type::nat())
}
/// `fst p` at `(nat, nat)`.
fn fst_nn(p: &Term) -> Term {
    Term::app(fst(Type::nat(), Type::nat()), p.clone())
}
/// `snd p` at `(nat, nat)`.
fn snd_nn(p: &Term) -> Term {
    Term::app(snd(Type::nat(), Type::nat()), p.clone())
}

/// `λp q. fst p + snd q = fst q + snd p` — the Grothendieck relation
/// carving `int`. Structurally the same term `defs/int.rs` quotients by.
pub fn int_rel() -> Term {
    let (p, q) = (Term::free("p", nn()), Term::free("q", nn()));
    let body = nat::add(fst_nn(&p), snd_nn(&q))
        .equals(nat::add(fst_nn(&q), snd_nn(&p)))
        .expect("int_rel: body");
    let inner = Term::abs(nn(), subst::close(&body, "q"));
    Term::abs(nn(), subst::close(&inner, "p"))
}

/// `int_rel p q` as an (un-reduced) application — the shape
/// `quotient::class_intro` reads its relation in.
fn rel_app(p: &Term, q: &Term) -> Term {
    Term::app(Term::app(int_rel(), p.clone()), q.clone())
}
/// `⊢ int_rel p q` → `⊢ <β-reduced equation>`.
fn reduce_rel(thm: Thm) -> Result<Thm> {
    thm.concl().reduce()?.eq_mp(thm)
}
/// `⊢ <β-reduced equation>` → `⊢ int_rel p q`, for the given application.
fn expand_rel(eq: Thm, app: &Term) -> Result<Thm> {
    app.reduce()?.sym()?.eq_mp(eq)
}

cached_thm! {
    /// `⊢ ∀p. int_rel p p` — reflexivity (`fst p + snd p = fst p + snd p`).
    pub fn int_rel_refl() -> Result<Thm> {
        let p = Term::free("p", nn());
        let reduced = Thm::refl(nat::add(fst_nn(&p), snd_nn(&p)))?;
        expand_rel(reduced, &rel_app(&p, &p))?.all_intro("p", nn())
    }
}

cached_thm! {
    /// `⊢ ∀p q. int_rel p q ⟹ int_rel q p` — symmetry (`sym` of the
    /// defining `nat` equation).
    pub fn int_rel_symm() -> Result<Thm> {
        let (p, q) = (Term::free("p", nn()), Term::free("q", nn()));
        let hyp = rel_app(&p, &q);
        let flipped = reduce_rel(Thm::assume(hyp.clone())?)?.sym()?; // ⊢ fst q+snd p = fst p+snd q
        expand_rel(flipped, &rel_app(&q, &p))?
            .imp_intro(&hyp)?
            .all_intro("q", nn())?
            .all_intro("p", nn())
    }
}

cached_thm! {
    /// `⊢ ∀p q r. int_rel p q ⟹ int_rel q r ⟹ int_rel p r` —
    /// transitivity, by adding the two defining equations and cancelling
    /// the common `nat` summand (`add_interchange` + `add_cancel`).
    pub fn int_rel_trans() -> Result<Thm> {
        let (p, q, r) = (
        Term::free("p", nn()),
        Term::free("q", nn()),
        Term::free("r", nn()),
    );
    let (h1, h2) = (rel_app(&p, &q), rel_app(&q, &r));
    let e1 = reduce_rel(Thm::assume(h1.clone())?)?; // ⊢ fp+sq = fq+sp
    let e2 = reduce_rel(Thm::assume(h2.clone())?)?; // ⊢ fq+sr = fr+sq

    let (fp, sp) = (fst_nn(&p), snd_nn(&p));
    let (fq, sq) = (fst_nn(&q), snd_nn(&q));
    let (fr, sr) = (fst_nn(&r), snd_nn(&r));

    // (fp+sq)+(fq+sr) = (fq+sp)+(fr+sq).
    let combined = nat::cong_add(e1, e2)?;
    // (fp+sq)+(fq+sr) = (fp+sr)+(sq+fq).
    let lhs = elim4(nat::add_interchange(), &fp, &sq, &fq, &sr)?;
    // (fq+sp)+(fr+sq) = (fr+sp)+(sq+fq):  commute, then interchange.
    let rhs = nat::add_comm()
        .all_elim(nat::add(fq.clone(), sp.clone()))?
        .all_elim(nat::add(fr.clone(), sq.clone()))? // = (fr+sq)+(fq+sp)
        .trans(elim4(nat::add_interchange(), &fr, &sq, &fq, &sp)?)?;
    // (fp+sr)+(sq+fq) = (fr+sp)+(sq+fq).
    let cancel_eq = lhs.sym()?.trans(combined)?.trans(rhs)?;
    // Cancel the common (sq+fq) ⟹ fp+sr = fr+sp.
    let reduced = nat::add_cancel()
        .all_elim(nat::add(fp.clone(), sr.clone()))?
        .all_elim(nat::add(fr.clone(), sp.clone()))?
        .all_elim(nat::add(sq.clone(), fq.clone()))?
        .imp_elim(cancel_eq)?; // ⊢ fp+sr = fr+sp

    expand_rel(reduced, &rel_app(&p, &r))?
            .imp_intro(&h2)?
            .imp_intro(&h1)?
            .all_intro("r", nn())?
            .all_intro("q", nn())?
            .all_intro("p", nn())
    }
}

/// Specialise a `∀a b c d. …` theorem at four `nat` witnesses.
fn elim4(thm: Thm, a: &Term, b: &Term, c: &Term, d: &Term) -> Result<Thm> {
    thm.all_elim(a.clone())?
        .all_elim(b.clone())?
        .all_elim(c.clone())?
        .all_elim(d.clone())
}

fn lt(a: Term, b: Term) -> Term {
    Term::app(Term::app(int_lt(), a), b)
}

fn le(a: Term, b: Term) -> Term {
    Term::app(Term::app(int_le(), a), b)
}

/// Postulate an `int` axiom: `{t} ⊢ t`. The self-hypothesis is the audit
/// trail — every proof built on it carries it, flagging the unproved leaf
/// until the quotient derivation discharges it.
fn axiom(t: Term) -> Thm {
    Thm::assume(t).expect("init::int::axiom: term must be bool-typed")
}

/// Universally close `body` over the named `int` variables, **outermost
/// first** (so `forall_int(&["a", "b"], body)` is `∀a b. body`).
fn forall_int(vars: &[&str], body: Term) -> Term {
    let mut t = body;
    for name in vars.iter().rev() {
        t = t.forall(name, int()).expect("forall_int: bind variable");
    }
    t
}

// ============================================================================
// Op-unfolding machinery — the defining equations on representatives
// ============================================================================

/// `repPair a ≔ ε(λp. rep a p)` — a representative pair of the int `a`.
/// Reconstructs `defs/int.rs`'s private `rep_pair` so the unfolded op
/// bodies match it structurally (and rewrites can target the components).
/// Delegates to [`quotient::rep_class`] so the bound variable is chosen
/// **capture-avoiding** — `a` may itself mention a free `nat × nat`
/// variable (it does in `mk_int p`), which a fixed bound name would capture.
fn rep_pair(a: &Term) -> Term {
    quotient::rep_class(&spec(), &[], &nn(), a)
}

/// `⊢ int.add a b = abs(classOf (pair Pa Pb))` — `int.add`'s δ-unfolded,
/// β-reduced defining equation, with `Pa = fst(rep a) + fst(rep b)` and
/// `Pb = snd(rep a) + snd(rep b)`.
fn add_defining_eq(a: &Term, b: &Term) -> Result<Thm> {
    add(a.clone(), b.clone())
        .delta_all(covalence_core::defs::int_add_spec().symbol())?
        .rhs_conv(|t| t.reduce())
}

/// `⊢ int.mul a b = abs(classOf (pair P1 P2))` — `int.mul`'s defining
/// equation, with `P1 = fa·fb + sa·sb`, `P2 = fa·sb + sa·fb`
/// (`fa = fst(rep a)`, `sa = snd(rep a)`, …).
fn mul_defining_eq(a: &Term, b: &Term) -> Result<Thm> {
    mul(a.clone(), b.clone())
        .delta_all(covalence_core::defs::int_mul_spec().symbol())?
        .rhs_conv(|t| t.reduce())
}

/// `⊢ t = t'`, applying each `eqs[i]` (`rw_all`, all occurrences) to the
/// running RHS in turn.
fn rewrite_seq(t: &Term, eqs: &[Thm]) -> Result<Thm> {
    let mut acc = Thm::refl(t.clone())?;
    for eq in eqs {
        let cur = acc.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone();
        acc = acc.trans(cur.rw_all(eq)?)?;
    }
    Ok(acc)
}

// ============================================================================
// Quotient lifting bridge — `int` ops as `mk_int` of `nat`-pairs
// ============================================================================
//
// `int := (nat×nat)/~`. The strategy for the ring/order axioms: replace each
// bound `int` variable `a` by `mk_int(rep_pair a)` ([`recon`], = quotient
// induction), unfold each op to `mk_int` of a componentwise `nat`-pair build
// ([`add_class`] / [`mul_class`] / …), and discharge the residual class
// equation either by `nat`-algebra congruence (when the pairs match on the
// nose) or by [`quotient::class_intro`] from a `~`-fact (when they don't).

/// The `int` type-spec handle.
fn spec() -> covalence_core::defs::TypeSpec {
    covalence_core::defs::int_ty_spec()
}

/// `pair a b : nat × nat`.
fn pair_nn(a: Term, b: Term) -> Term {
    Term::app(Term::app(pair(Type::nat(), Type::nat()), a), b)
}

/// `mkInt p ≔ abs(λx. int_rel p x)` — the quotient class of the pair `p`,
/// in [`quotient::mk_class`] form (the canonical shape `class_intro` /
/// `class_elim` / `recon` speak).
fn mk_int(p: &Term) -> Term {
    quotient::mk_class(&spec(), &[], &nn(), &int_rel(), p)
}

/// `(0, 0) : nat × nat` — a base witness for `recon`'s non-emptiness side.
fn pair00() -> Term {
    pair_nn(nat::zero(), nat::zero())
}

/// `⊢ int_rel p x = (fst p + snd x = fst x + snd p)` — two β-steps, **no**
/// `ι` (so `fst p` is left intact even when `p` is a literal pair). Matches
/// the body shape `defs/int.rs`'s `class_of` writes.
fn int_rel_beta(p: &Term, x: &Term) -> Result<Thm> {
    let ir_p = Term::app(int_rel(), p.clone()); // (λp' q. body) p
    let s1 = Thm::beta_conv(ir_p.clone())?; // ⊢ int_rel p = λq. body[p]
    let s2 = s1.cong_fn(x.clone())?; // ⊢ (int_rel p) x = (λq. body[p]) x
    let mid = s2.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone();
    let s3 = Thm::beta_conv(mid)?; // ⊢ (λq. body[p]) x = body[p][x]
    s2.trans(s3)
}

/// `⊢ abs(class_of_defs p) = mk_int p` — the **β reconciliation**: the
/// β-reduced class body `defs/int.rs` produces (the RHS shape of
/// [`add_defining_eq`] etc.) equals the un-reduced `quotient::mk_class`
/// form. Built by β-normalising `λx. int_rel p x` under the binder.
fn defs_to_mk_int(p: &Term) -> Result<Thm> {
    let x = Term::free("__cls", nn());
    let body_eq = int_rel_beta(p, &x)?; // ⊢ int_rel p x = defs_body
    let lam_eq = body_eq.abs("__cls", nn())?; // ⊢ (λx. int_rel p x) = (λx. defs_body)
    let abs = Term::spec_abs(spec(), Vec::<Type>::new());
    // ⊢ mk_int p = abs(class_of_defs p), then flip.
    lam_eq.cong_arg(abs)?.sym()
}

/// **Reconstruction.** `⊢ a = mk_int(rep_pair a)` for any `a : int`.
fn recon(a: &Term) -> Result<Thm> {
    quotient::recon(
        &spec(),
        &[],
        &nn(),
        &int_rel(),
        &int_rel_refl(),
        &int_rel_symm(),
        &int_rel_trans(),
        &pair00(),
        a,
    )
}

/// `⊢ int_rel p (rep_pair (mk_int p))` — the chosen representative of `[p]`
/// is `~`-related to `p` ([`quotient::round_trip`]).
fn round_trip(p: &Term) -> Result<Thm> {
    quotient::round_trip(&spec(), &[], &nn(), &int_rel(), &int_rel_refl(), p)
}

/// `⊢ (a + b) + (c + d) = (a + c) + (b + d)` on `nat` — the "middle swap"
/// rearrangement (commute the right summand, then [`nat::add_interchange`]).
fn mid_swap(a: &Term, b: &Term, c: &Term, d: &Term) -> Result<Thm> {
    let comm_cd = nat::add_comm().all_elim(c.clone())?.all_elim(d.clone())?; // c+d = d+c
    let left = comm_cd.cong_arg(Term::app(nat::nat_add(), nat::add(a.clone(), b.clone())))?; // (a+b)+(c+d) = (a+b)+(d+c)
    let inter = elim4(nat::add_interchange(), a, b, d, c)?; // (a+b)+(d+c) = (a+c)+(b+d)
    left.trans(inter)
}

/// Parse an `int_rel a b` application into `(a, b)`.
fn dest_rel_app(t: &Term) -> Result<(Term, Term)> {
    let (rel_a, b) = t.as_app().ok_or(Error::NotAnEquation)?;
    let (_rel, a) = rel_a.as_app().ok_or(Error::NotAnEquation)?;
    Ok((a.clone(), b.clone()))
}

/// `pair (fst x + fst y) (snd x + snd y)` — the Grothendieck sum of two
/// representative pairs (`int.add`'s componentwise build).
fn add_pair(x: &Term, y: &Term) -> Term {
    pair_nn(
        nat::add(fst_nn(x), fst_nn(y)),
        nat::add(snd_nn(x), snd_nn(y)),
    )
}

/// `⊢ int_rel (pair a1 a2) (pair b1 b2)` from the β-reduced relation
/// `g : ⊢ a1 + b2 = b1 + a2`. `fst`/`snd` of a literal pair are stuck under
/// `reduce` (ε-defined, not primitive), so we bridge `int_rel`'s body via
/// the proven prod projection theorems instead.
fn rel_of_pairs(a1: &Term, a2: &Term, b1: &Term, b2: &Term, g: Thm) -> Result<Thm> {
    let n = Type::nat();
    let a = pair_nn(a1.clone(), a2.clone());
    let b = pair_nn(b1.clone(), b2.clone());
    let beta = int_rel_beta(&a, &b)?; // ⊢ int_rel a b = (fst a + snd b = fst b + snd a)
    let br = beta.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone();
    let projs = [
        crate::init::prod::fst_pair(&n, &n, a1, a2)?, // fst a = a1
        crate::init::prod::snd_pair(&n, &n, b1, b2)?, // snd b = b2
        crate::init::prod::fst_pair(&n, &n, b1, b2)?, // fst b = b1
        crate::init::prod::snd_pair(&n, &n, a1, a2)?, // snd a = a2
    ];
    let proj_eq = rewrite_seq(&br, &projs)?; // ⊢ br = (a1 + b2 = b1 + a2)
    beta.trans(proj_eq)?.sym()?.eq_mp(g) // ⊢ int_rel a b
}

/// **Additive well-definedness.** From `⊢ int_rel x x'` and `⊢ int_rel y y'`
/// conclude `⊢ int_rel (add_pair x y) (add_pair x' y')` — `int.add` respects
/// `~`. Pure `nat` algebra: add the two defining equations and re-pair the
/// four `fst`/`snd` summands ([`mid_swap`]).
fn add_pair_cong(h1: Thm, h2: Thm) -> Result<Thm> {
    let (x, xp) = dest_rel_app(h1.concl())?;
    let (y, yp) = dest_rel_app(h2.concl())?;
    let e1 = reduce_rel(h1)?; // fx + sx' = fx' + sx
    let e2 = reduce_rel(h2)?; // fy + sy' = fy' + sy

    let (fx, sx) = (fst_nn(&x), snd_nn(&x));
    let (fxp, sxp) = (fst_nn(&xp), snd_nn(&xp));
    let (fy, sy) = (fst_nn(&y), snd_nn(&y));
    let (fyp, syp) = (fst_nn(&yp), snd_nn(&yp));

    // (fx+fy)+(sx'+sy') = (fx+sx')+(fy+sy') = (fx'+sx)+(fy'+sy) = (fx'+fy')+(sx+sy).
    let g = mid_swap(&fx, &fy, &sxp, &syp)?
        .trans(nat::cong_add(e1, e2)?)?
        .trans(mid_swap(&fxp, &fyp, &sx, &sy)?.sym()?)?;
    rel_of_pairs(
        &nat::add(fx.clone(), fy.clone()),
        &nat::add(sx, sy),
        &nat::add(fxp, fyp),
        &nat::add(sxp, syp),
        g,
    )
}

/// **Additive computation rule.** `⊢ int.add (mk_int p) (mk_int q) =
/// mk_int (add_pair p q)`. Unfold `int.add` on the two classes, then use the
/// round-trips `p ~ rep_pair[p]`, `q ~ rep_pair[q]` and additive
/// well-definedness to re-quotient the chosen representatives back to `p`, `q`.
fn add_class(p: &Term, q: &Term) -> Result<Thm> {
    let (mp, mq) = (mk_int(p), mk_int(q));
    let dl = add_defining_eq(&mp, &mq)?; // int.add mp mq = abs(class_of_defs(add_pair RPp RPq))
    let (rpp, rpq) = (rep_pair(&mp), rep_pair(&mq));
    let big = add_pair(&rpp, &rpq);
    let dl = dl.trans(defs_to_mk_int(&big)?)?; // = mk_int(add_pair RPp RPq)

    // RPp ~ p, RPq ~ q (symm of the round-trips).
    let rpp_p = inst2(int_rel_symm(), p, &rpp)?.imp_elim(round_trip(p)?)?;
    let rpq_q = inst2(int_rel_symm(), q, &rpq)?.imp_elim(round_trip(q)?)?;
    let cong = add_pair_cong(rpp_p, rpq_q)?; // int_rel (add_pair RPp RPq) (add_pair p q)
    let lift = quotient::class_intro(&spec(), &[], &nn(), &int_rel_symm(), &int_rel_trans(), cong)?;
    dl.trans(lift) // = mk_int(add_pair p q)
}

/// Specialise a `∀x y. …` theorem at two witnesses.
fn inst2(thm: Thm, a: &Term, b: &Term) -> Result<Thm> {
    thm.all_elim(a.clone())?.all_elim(b.clone())
}

// ---- negation ----

/// `pair (snd x) (fst x)` — Grothendieck negation `(a − b) ↦ (b − a)`.
fn neg_pair(x: &Term) -> Term {
    pair_nn(snd_nn(x), fst_nn(x))
}

/// `⊢ int.neg a = abs(class_of_defs (neg_pair (rep_pair a)))`.
fn neg_defining_eq(a: &Term) -> Result<Thm> {
    Term::app(int_neg(), a.clone())
        .delta_all(covalence_core::defs::int_neg_spec().symbol())?
        .rhs_conv(|t| t.reduce())
}

/// **Negation well-definedness.** `⊢ int_rel x x' ⟹` lifted to
/// `⊢ int_rel (neg_pair x) (neg_pair x')` — swap the components; the
/// defining `nat` equation flips by `add_comm`.
fn neg_pair_cong(h: Thm) -> Result<Thm> {
    let (x, xp) = dest_rel_app(h.concl())?;
    let e = reduce_rel(h)?; // fx + sx' = fx' + sx
    let (fx, sx) = (fst_nn(&x), snd_nn(&x));
    let (fxp, sxp) = (fst_nn(&xp), snd_nn(&xp));
    // sx + fx' = fx' + sx = fx + sx' = sx' + fx.
    let g = nat::add_comm()
        .all_elim(sx.clone())?
        .all_elim(fxp.clone())?
        .trans(e.sym()?)?
        .trans(
            nat::add_comm()
                .all_elim(fx.clone())?
                .all_elim(sxp.clone())?,
        )?;
    rel_of_pairs(&sx, &fx, &sxp, &fxp, g)
}

/// **Negation computation rule.** `⊢ int.neg (mk_int p) = mk_int (neg_pair p)`.
fn neg_class(p: &Term) -> Result<Thm> {
    let mp = mk_int(p);
    let dl = neg_defining_eq(&mp)?;
    let rpp = rep_pair(&mp);
    let dl = dl.trans(defs_to_mk_int(&neg_pair(&rpp))?)?; // = mk_int(neg_pair RPp)
    let rpp_p = inst2(int_rel_symm(), p, &rpp)?.imp_elim(round_trip(p)?)?; // int_rel RPp p
    let cong = neg_pair_cong(rpp_p)?; // int_rel (neg_pair RPp) (neg_pair p)
    let lift = quotient::class_intro(&spec(), &[], &nn(), &int_rel_symm(), &int_rel_trans(), cong)?;
    dl.trans(lift)
}

// ---- subtraction ----

/// `pair (fst x + snd y) (snd x + fst y)` — Grothendieck subtraction
/// `(a − b) − (c − d) = (a + d) − (b + c)`.
fn sub_pair(x: &Term, y: &Term) -> Term {
    pair_nn(
        nat::add(fst_nn(x), snd_nn(y)),
        nat::add(snd_nn(x), fst_nn(y)),
    )
}

/// `⊢ int.sub a b = abs(class_of_defs (sub_pair (rep_pair a) (rep_pair b)))`.
fn sub_defining_eq(a: &Term, b: &Term) -> Result<Thm> {
    Term::app(Term::app(int_sub(), a.clone()), b.clone())
        .delta_all(covalence_core::defs::int_sub_spec().symbol())?
        .rhs_conv(|t| t.reduce())
}

/// **Subtraction well-definedness.** From `⊢ int_rel x x'`, `⊢ int_rel y y'`
/// conclude `⊢ int_rel (sub_pair x y) (sub_pair x' y')`.
fn sub_pair_cong(h1: Thm, h2: Thm) -> Result<Thm> {
    let (x, xp) = dest_rel_app(h1.concl())?;
    let (y, yp) = dest_rel_app(h2.concl())?;
    let e1 = reduce_rel(h1)?; // fx + sx' = fx' + sx
    let e2 = reduce_rel(h2)?; // fy + sy' = fy' + sy

    let (fx, sx) = (fst_nn(&x), snd_nn(&x));
    let (fxp, sxp) = (fst_nn(&xp), snd_nn(&xp));
    let (fy, sy) = (fst_nn(&y), snd_nn(&y));
    let (fyp, syp) = (fst_nn(&yp), snd_nn(&yp));

    // sy + fy' = fy' + sy = fy + sy' = sy' + fy.
    let e2p = nat::add_comm()
        .all_elim(sy.clone())?
        .all_elim(fyp.clone())?
        .trans(e2.sym()?)?
        .trans(
            nat::add_comm()
                .all_elim(fy.clone())?
                .all_elim(syp.clone())?,
        )?;
    // (fx+sy)+(sx'+fy') = (fx+sx')+(sy+fy') = (fx'+sx)+(sy'+fy) = (fx'+sy')+(sx+fy).
    let g = mid_swap(&fx, &sy, &sxp, &fyp)?
        .trans(nat::cong_add(e1, e2p)?)?
        .trans(mid_swap(&fxp, &syp, &sx, &fy)?.sym()?)?;
    rel_of_pairs(
        &nat::add(fx, sy),
        &nat::add(sx, fy),
        &nat::add(fxp, syp),
        &nat::add(sxp, fyp),
        g,
    )
}

/// **Subtraction computation rule.** `⊢ int.sub (mk_int p) (mk_int q) =
/// mk_int (sub_pair p q)`.
fn sub_class(p: &Term, q: &Term) -> Result<Thm> {
    let (mp, mq) = (mk_int(p), mk_int(q));
    let dl = sub_defining_eq(&mp, &mq)?;
    let (rpp, rpq) = (rep_pair(&mp), rep_pair(&mq));
    let dl = dl.trans(defs_to_mk_int(&sub_pair(&rpp, &rpq))?)?; // = mk_int(sub_pair RPp RPq)
    let rpp_p = inst2(int_rel_symm(), p, &rpp)?.imp_elim(round_trip(p)?)?;
    let rpq_q = inst2(int_rel_symm(), q, &rpq)?.imp_elim(round_trip(q)?)?;
    let cong = sub_pair_cong(rpp_p, rpq_q)?;
    let lift = quotient::class_intro(&spec(), &[], &nn(), &int_rel_symm(), &int_rel_trans(), cong)?;
    dl.trans(lift)
}

// ============================================================================
// The `MK(f, s)` component layer — `int` values as explicit `nat`-pairs
// ============================================================================
//
// Working with `mk_int(rep_pair a)` directly is awkward: `rep_pair a` is an
// `ε`-pair whose `fst`/`snd` are stuck. So we normalise every reconstructed
// value to `MK(f, s) ≔ mk_int(pair f s)` for explicit `nat` components `f`,
// `s` (via surjective pairing), and the op rules then combine components on
// the nose. The ring identities reduce to `nat` algebra on `f`/`s`.
//
/// `MK(f, s) ≔ mk_int(pair f s)`.
fn mkfs(f: &Term, s: &Term) -> Term {
    mk_int(&pair_nn(f.clone(), s.clone()))
}

/// `fst (rep_pair a)` — the first `nat` component of `a`'s chosen
/// representative.
fn fcomp(a: &Term) -> Term {
    fst_nn(&rep_pair(a))
}
/// `snd (rep_pair a)` — the second component.
fn scomp(a: &Term) -> Term {
    snd_nn(&rep_pair(a))
}

/// **Reconstruction in component form.** `⊢ a = MK(fst(rep_pair a),
/// snd(rep_pair a))` — `recon` followed by surjective pairing of the chosen
/// representative.
fn recon_mk(a: &Term) -> Result<Thm> {
    // a = mk_int(rep_pair a); rewrite rep_pair a ↦ pair (fst rp)(snd rp).
    let rp = rep_pair(a);
    let surj = crate::init::prod::surjective_pairing(&Type::nat(), &Type::nat(), &rp)?; // pair(fst rp)(snd rp) = rp
    recon(a)?.rhs_conv(|t| t.rw_all(&surj.sym()?))
}

/// **Additive computation in component form.** `⊢ int.add (MK fa sa)(MK fb
/// sb) = MK (fa+fb) (sa+sb)` — [`add_class`] with the `add_pair` of two
/// literal pairs simplified componentwise (prod projections).
fn add_mk(fa: &Term, sa: &Term, fb: &Term, sb: &Term) -> Result<Thm> {
    let (pa, pb) = (
        pair_nn(fa.clone(), sa.clone()),
        pair_nn(fb.clone(), sb.clone()),
    );
    let ac = add_class(&pa, &pb)?; // = mk_int(add_pair pa pb)
    let n = Type::nat();
    let projs = [
        crate::init::prod::fst_pair(&n, &n, fa, sa)?,
        crate::init::prod::fst_pair(&n, &n, fb, sb)?,
        crate::init::prod::snd_pair(&n, &n, fa, sa)?,
        crate::init::prod::snd_pair(&n, &n, fb, sb)?,
    ];
    ac.rhs_conv(|t| rewrite_seq(t, &projs)) // = MK (fa+fb)(sa+sb)
}

/// `⊢ MK f s = MK f' s'` from `⊢ f = f'` and `⊢ s = s'` — congruence of the
/// component constructor (rewrite the two components inside `mk_int`).
fn mkfs_cong(f_eq: Thm, s_eq: Thm) -> Result<Thm> {
    let (f, s) = (
        f_eq.concl().as_eq().ok_or(Error::NotAnEquation)?.0.clone(),
        s_eq.concl().as_eq().ok_or(Error::NotAnEquation)?.0.clone(),
    );
    rewrite_seq(&mkfs(&f, &s), &[f_eq, s_eq])
}

/// `⊢ int.add a b = MK (fa+fb)(sa+sb)`, where `MK fa sa = a`, `MK fb sb = b`
/// are the component reconstructions — congruence of `+` over `ra`/`rb`
/// chained with [`add_mk`]. Returns the equation and the four components.
fn add_via_components(ra: &Thm, rb: &Thm) -> Result<Thm> {
    let (a, ma) = dest_eq(ra)?; // a = MK fa sa
    let (b, mb) = dest_eq(rb)?;
    let (fa, sa) = mk_components(&ma)?;
    let (fb, sb) = mk_components(&mb)?;
    // int.add a b = int.add (MK fa sa)(MK fb sb)
    let cong = Thm::refl(int_add())?
        .cong_app(ra.clone())?
        .cong_app(rb.clone())?;
    let _ = (a, b);
    cong.trans(add_mk(&fa, &sa, &fb, &sb)?)
}

/// Split an equation theorem `⊢ l = r` into `(l, r)`.
fn dest_eq(thm: &Thm) -> Result<(Term, Term)> {
    let (l, r) = thm.concl().as_eq().ok_or(Error::NotAnEquation)?;
    Ok((l.clone(), r.clone()))
}

/// **Negation in component form.** `⊢ int.neg (MK f s) = MK s f`.
fn neg_mk(f: &Term, s: &Term) -> Result<Thm> {
    let nc = neg_class(&pair_nn(f.clone(), s.clone()))?; // = mk_int(neg_pair (pair f s))
    let n = Type::nat();
    let projs = [
        crate::init::prod::snd_pair(&n, &n, f, s)?, // snd (pair f s) = s
        crate::init::prod::fst_pair(&n, &n, f, s)?, // fst (pair f s) = f
    ];
    nc.rhs_conv(|t| rewrite_seq(t, &projs)) // = MK s f
}

/// **Subtraction in component form.** `⊢ int.sub (MK fa sa)(MK fb sb) =
/// MK (fa+sb)(sa+fb)`.
fn sub_mk(fa: &Term, sa: &Term, fb: &Term, sb: &Term) -> Result<Thm> {
    let (pa, pb) = (
        pair_nn(fa.clone(), sa.clone()),
        pair_nn(fb.clone(), sb.clone()),
    );
    let sc = sub_class(&pa, &pb)?; // = mk_int(sub_pair pa pb)
    let n = Type::nat();
    let projs = [
        crate::init::prod::fst_pair(&n, &n, fa, sa)?, // fst pa = fa
        crate::init::prod::snd_pair(&n, &n, fb, sb)?, // snd pb = sb
        crate::init::prod::snd_pair(&n, &n, fa, sa)?, // snd pa = sa
        crate::init::prod::fst_pair(&n, &n, fb, sb)?, // fst pb = fb
    ];
    sc.rhs_conv(|t| rewrite_seq(t, &projs)) // = MK (fa+sb)(sa+fb)
}

/// `⊢ int.neg a = MK sa fa`, where `ra : a = MK fa sa`.
fn neg_via_components(ra: &Thm) -> Result<Thm> {
    let (_a, ma) = dest_eq(ra)?;
    let (fa, sa) = mk_components(&ma)?;
    Thm::refl(int_neg())?
        .cong_app(ra.clone())? // int.neg a = int.neg (MK fa sa)
        .trans(neg_mk(&fa, &sa)?)
}

/// `⊢ int.sub a b = MK (fa+sb)(sa+fb)`, where `ra : a = MK fa sa`,
/// `rb : b = MK fb sb`.
fn sub_via_components(ra: &Thm, rb: &Thm) -> Result<Thm> {
    let (_a, ma) = dest_eq(ra)?;
    let (_b, mb) = dest_eq(rb)?;
    let (fa, sa) = mk_components(&ma)?;
    let (fb, sb) = mk_components(&mb)?;
    Thm::refl(int_sub())?
        .cong_app(ra.clone())?
        .cong_app(rb.clone())? // int.sub a b = int.sub (MK fa sa)(MK fb sb)
        .trans(sub_mk(&fa, &sa, &fb, &sb)?)
}

/// From `MK f s = mk_int(pair f s)`, read off `(f, s)`.
fn mk_components(mk: &Term) -> Result<(Term, Term)> {
    // mk = abs(λx. int_rel (pair f s) x). Dig out `pair f s`, then f, s.
    let lam = mk.as_app().ok_or(Error::NotAnEquation)?.1.clone(); // λx. int_rel (pair f s) x
    let body = lam.as_abs().ok_or(Error::NotAnEquation)?.1.clone(); // int_rel (pair f s) #0
    let rel_p = body.as_app().ok_or(Error::NotAnEquation)?.0.clone(); // int_rel (pair f s)
    let p = rel_p.as_app().ok_or(Error::NotAnEquation)?.1.clone(); // pair f s
    let (pair_f, s) = p.as_app().ok_or(Error::NotAnEquation)?;
    let f = pair_f.as_app().ok_or(Error::NotAnEquation)?.1.clone();
    Ok((f, s.clone()))
}

// ============================================================================
// Literal coherence — relating `int_lit n` to its `MK` representative
// ============================================================================
//
// Integer literals are builtin `TermKind::Int`, opaque to the quotient. But
// `int.add`/`int.succ` on literals reduce (`reduce_prim`) AND unfold to the
// Grothendieck body, and those two must agree — which pins the literal's
// class. We exploit that to derive `int_lit 0 = MK(0, 0)` (and `int_lit 1 =
// MK(1, 0)`), the `0`/`1` coherence the unit/inverse axioms need.

/// `⊢ a1 + b2 = b1 + a2` from `eq : ⊢ MK a1 a2 = MK b1 b2` — the converse of
/// [`rel_of_pairs`], via [`quotient::class_elim`] then the prod projections.
fn class_eq_to_nat(eq: Thm, a1: &Term, a2: &Term, b1: &Term, b2: &Term) -> Result<Thm> {
    let n = Type::nat();
    let (a, b) = (
        pair_nn(a1.clone(), a2.clone()),
        pair_nn(b1.clone(), b2.clone()),
    );
    let rel = quotient::class_elim(&spec(), &[], &nn(), &int_rel(), &int_rel_refl(), &a, &b, eq)?; // int_rel a b
    let red = reduce_rel(rel)?; // fst a + snd b = fst b + snd a (fst/snd of pairs stuck)
    let projs = [
        crate::init::prod::fst_pair(&n, &n, a1, a2)?,
        crate::init::prod::snd_pair(&n, &n, b1, b2)?,
        crate::init::prod::fst_pair(&n, &n, b1, b2)?,
        crate::init::prod::snd_pair(&n, &n, a1, a2)?,
    ];
    let mut acc = red;
    for proj in projs {
        acc = acc.rewrite(&proj)?;
    }
    Ok(acc) // ⊢ a1 + b2 = b1 + a2
}

/// `⊢ int_lit 0 = MK(0, 0)` — literal-`0` coherence. `int.add 0 0` reduces to
/// `0` (`reduce_prim`) and unfolds to `MK(f0+f0)(s0+s0)` (`f0`/`s0` the
/// components of `0`'s chosen representative); with `recon`'s `0 = MK(f0, s0)`
/// the two force `f0 = s0`, hence `MK(f0, s0) = MK(0, 0)`.
fn lit0_mk() -> Result<Thm> {
    let z = lit(0);
    let (f0, s0) = (fcomp(&z), scomp(&z));
    let rp = rep_pair(&z);

    // 0 = mk_int(add_pair rp rp) = MK(f0+f0)(s0+s0): two readings of `0 + 0`.
    let e_red = add(z.clone(), z.clone()).reduce()?; // int.add 0 0 = 0
    let e_def = add_defining_eq(&z, &z)?.trans(defs_to_mk_int(&add_pair(&rp, &rp))?)?;
    let z_eq_big = e_red.sym()?.trans(e_def)?; // 0 = mk_int(add_pair rp rp)

    let rm = recon_mk(&z)?; // 0 = MK(f0, s0)
    let big_eq = rm.clone().sym()?.trans(z_eq_big)?; // MK(f0, s0) = MK(f0+f0)(s0+s0)

    // f0 + (s0+s0) = (f0+f0) + s0  ⟹  f0 = s0.
    let nat_eq = class_eq_to_nat(
        big_eq,
        &f0,
        &s0,
        &nat::add(f0.clone(), f0.clone()),
        &nat::add(s0.clone(), s0.clone()),
    )?;
    let f0_eq_s0 = {
        let assoc = elim3(nat::add_assoc(), &f0, &s0, &s0)?; // (f0+s0)+s0 = f0+(s0+s0)
        let step = assoc.trans(nat_eq)?; // (f0+s0)+s0 = (f0+f0)+s0
        let c1 = elim3(
            nat::add_cancel(),
            &nat::add(f0.clone(), s0.clone()),
            &nat::add(f0.clone(), f0.clone()),
            &s0,
        )?
        .imp_elim(step)?; // f0+s0 = f0+f0
        let step2 = nat::add_comm()
            .all_elim(s0.clone())?
            .all_elim(f0.clone())?
            .trans(c1)?; // s0+f0 = f0+f0
        elim3(nat::add_cancel(), &s0, &f0, &f0)?
            .imp_elim(step2)?
            .sym()? // f0 = s0
    };

    // MK(f0, s0) = MK(0, 0): int_rel via f0 + 0 = 0 + s0.
    let g = nat::add_zero()
        .all_elim(f0.clone())? // f0 + 0 = f0
        .trans(f0_eq_s0)? // = s0
        .trans(nat::add_base().all_elim(s0.clone())?.sym()?)?; // = 0 + s0
    let rel = rel_of_pairs(&f0, &s0, &nat::zero(), &nat::zero(), g)?;
    let mk_eq = quotient::class_intro(&spec(), &[], &nn(), &int_rel_symm(), &int_rel_trans(), rel)?;
    rm.trans(mk_eq) // ⊢ 0 = MK(0, 0)
}

// ============================================================================
// Commutative ring
// ============================================================================

cached_thm! {
    /// `⊢ ∀a b. a + b = b + a` — **proved**. `int.add` is componentwise
    /// `nat` addition on representatives, which is commutative *on the nose*
    /// (`Pa = fst(rep a)+fst(rep b) = fst(rep b)+fst(rep a) = Qa` by
    /// `nat::add_comm`, likewise `Pb = Qb`), so no quotient lifting is
    /// needed: unfold both sides and rewrite the representative components.
    pub fn add_comm() -> Result<Thm> {
        let (a, b) = (var("a"), var("b"));
    let dl = add_defining_eq(&a, &b)?; // int.add a b = abs(classOf(pair Pa Pb))
    let dr = add_defining_eq(&b, &a)?; // int.add b a = abs(classOf(pair Qa Qb))

    // Pa = Qa (commute first components); Pb = Qb (second components).
    let (rpa, rpb) = (rep_pair(&a), rep_pair(&b));
    let eq_a = nat::add_comm()
        .all_elim(fst_nn(&rpa))?
        .all_elim(fst_nn(&rpb))?;
    let eq_b = nat::add_comm()
        .all_elim(snd_nn(&rpa))?
        .all_elim(snd_nn(&rpb))?;

    // Rewrite the RHS of `dl` (Pa→Qa, Pb→Qb) into the RHS of `dr`.
    let t0 = dl.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone();
    let r1 = t0.rw_all(&eq_a)?; // ⊢ abs(classOf(pair Pa Pb)) = abs(classOf(pair Qa Pb))
    let t1 = r1.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone();
    let r2 = t1.rw_all(&eq_b)?; // ⊢ … = abs(classOf(pair Qa Qb))
    let rewritten = r1.trans(r2)?; // ⊢ dl.rhs = dr.rhs

    dl.trans(rewritten)?
        .trans(dr.sym()?)? // int.add a b = int.add b a
        .all_intro("b", int())?
        .all_intro("a", int())
    }
}

cached_thm! {
    /// `⊢ ∀a b c. (a + b) + c = a + (b + c)` — **proved**. Reconstruct each
    /// variable in component form, push `int.add` through to `MK` of
    /// componentwise `nat` sums, and close by `nat::add_assoc` on each of the
    /// two `nat` components.
    pub fn add_assoc() -> Result<Thm> {
        let (a, b, c) = (var("a"), var("b"), var("c"));
        let (ra, rb, rc) = (recon_mk(&a)?, recon_mk(&b)?, recon_mk(&c)?);

        // (a+b)+c = MK ((fa+fb)+fc) ((sa+sb)+sc)
        let ab = add_via_components(&ra, &rb)?;
        let lhs = add_via_components(&ab, &rc)?;
        // a+(b+c) = MK (fa+(fb+fc)) (sa+(sb+sc))
        let bc = add_via_components(&rb, &rc)?;
        let rhs = add_via_components(&ra, &bc)?;

        let (fa, sa) = (fcomp(&a), scomp(&a));
        let (fb, sb) = (fcomp(&b), scomp(&b));
        let (fc, sc) = (fcomp(&c), scomp(&c));
        let assoc_f = elim3(nat::add_assoc(), &fa, &fb, &fc)?; // (fa+fb)+fc = fa+(fb+fc)
        let assoc_s = elim3(nat::add_assoc(), &sa, &sb, &sc)?;
        let bridge = mkfs_cong(assoc_f, assoc_s)?;

        lhs.trans(bridge)?
            .trans(rhs.sym()?)?
            .all_intro("c", int())?
            .all_intro("b", int())?
            .all_intro("a", int())
    }
}

/// Specialise a `∀a b c. …` theorem at three witnesses.
fn elim3(thm: Thm, a: &Term, b: &Term, c: &Term) -> Result<Thm> {
    thm.all_elim(a.clone())?
        .all_elim(b.clone())?
        .all_elim(c.clone())
}

cached_thm! {
    /// `⊢ ∀a. a + 0 = a` — **proved**. `0 = MK(0,0)` ([`lit0_mk`]), so
    /// `a + 0 = MK(fa+0)(sa+0) = MK(fa)(sa) = a` by `nat::add_zero` on each
    /// component.
    pub fn add_zero() -> Result<Thm> {
        let a = var("a");
        let ra = recon_mk(&a)?; // a = MK(fa, sa)
        let (fa, sa) = (fcomp(&a), scomp(&a));
        let lhs = add_via_components(&ra, &lit0_mk()?)?; // a + 0 = MK(fa+0)(sa+0)
        let bridge = mkfs_cong(
            nat::add_zero().all_elim(fa.clone())?, // fa+0 = fa
            nat::add_zero().all_elim(sa.clone())?, // sa+0 = sa
        )?;
        lhs.trans(bridge)?.trans(ra.sym()?)?.all_intro("a", int())
    }
}

cached_thm! {
    /// `⊢ ∀a. a + (-a) = 0` — **proved** (additive inverse). `-a = MK(sa,
    /// fa)`, so `a + (-a) = MK(fa+sa)(sa+fa)`, which is `~ (0,0)` since
    /// `(fa+sa)+0 = 0+(sa+fa)` by `nat::add_comm`.
    pub fn add_neg() -> Result<Thm> {
        let a = var("a");
        let ra = recon_mk(&a)?; // a = MK(fa, sa)
        let (fa, sa) = (fcomp(&a), scomp(&a));
        let neg_a = neg_via_components(&ra)?; // -a = MK(sa, fa)
        let lhs = add_via_components(&ra, &neg_a)?; // a + (-a) = MK(fa+sa)(sa+fa)
        // MK(fa+sa)(sa+fa) = MK(0,0): (fa+sa)+0 = 0+(sa+fa).
        let g = nat::add_zero()
            .all_elim(nat::add(fa.clone(), sa.clone()))? // (fa+sa)+0 = fa+sa
            .trans(nat::add_comm().all_elim(fa.clone())?.all_elim(sa.clone())?)? // = sa+fa
            .trans(nat::add_base().all_elim(nat::add(sa.clone(), fa.clone()))?.sym()?)?; // = 0+(sa+fa)
        let rel = rel_of_pairs(
            &nat::add(fa.clone(), sa.clone()),
            &nat::add(sa.clone(), fa.clone()),
            &nat::zero(),
            &nat::zero(),
            g,
        )?;
        let to_zero = quotient::class_intro(&spec(), &[], &nn(), &int_rel_symm(), &int_rel_trans(), rel)?;
        lhs.trans(to_zero)?
            .trans(lit0_mk()?.sym()?)? // MK(0,0) = 0
            .all_intro("a", int())
    }
}

cached_thm! {
    /// `⊢ ∀a b. a * b = b * a` — **proved**. Like [`add_comm`], `int.mul`
    /// is built from `nat::mul` on representatives, so commutativity is *on
    /// the nose*: the first component `fa·fb + sa·sb` commutes to
    /// `fb·fa + sb·sa` by `nat::mul_comm`, and the second `fa·sb + sa·fb`
    /// to `fb·sa + sb·fa` by `nat::mul_comm` (each product) plus one
    /// `nat::add_comm` (to swap the two summands). Unfold + rewrite.
    pub fn mul_comm() -> Result<Thm> {
        let (a, b) = (var("a"), var("b"));
        let dl = mul_defining_eq(&a, &b)?;
    let dr = mul_defining_eq(&b, &a)?;

    let (rpa, rpb) = (rep_pair(&a), rep_pair(&b));
    let (fa, sa) = (fst_nn(&rpa), snd_nn(&rpa));
    let (fb, sb) = (fst_nn(&rpb), snd_nn(&rpb));
    let mc = |x: &Term, y: &Term| -> Result<Thm> {
        nat::mul_comm().all_elim(x.clone())?.all_elim(y.clone())
    };
    // P1: fa·fb→fb·fa, sa·sb→sb·sa.  P2: fa·sb→sb·fa, sa·fb→fb·sa, then
    // swap the two summands (sb·fa)+(fb·sa) → (fb·sa)+(sb·fa).
    let eqs = [
        mc(&fa, &fb)?,
        mc(&sa, &sb)?,
        mc(&fa, &sb)?,
        mc(&sa, &fb)?,
        nat::add_comm()
            .all_elim(nat::mul(sb.clone(), fa.clone()))?
            .all_elim(nat::mul(fb.clone(), sa.clone()))?,
    ];

    let t0 = dl.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone();
    let rewritten = rewrite_seq(&t0, &eqs)?; // ⊢ dl.rhs = dr.rhs
    dl.trans(rewritten)?
        .trans(dr.sym()?)?
        .all_intro("b", int())?
        .all_intro("a", int())
    }
}

/// `⊢ ∀a b c. (a * b) * c = a * (b * c)`.
pub fn mul_assoc() -> Thm {
    let (a, b, c) = (var("a"), var("b"), var("c"));
    let lhs = mul(mul(a.clone(), b.clone()), c.clone());
    let rhs = mul(a, mul(b, c));
    let eq = lhs.equals(rhs).expect("mul_assoc");
    axiom(forall_int(&["a", "b", "c"], eq))
}

/// `⊢ ∀a. a * 1 = a`.
pub fn mul_one() -> Thm {
    let a = var("a");
    let eq = mul(a.clone(), lit(1))
        .equals(a)
        .expect("mul_one: a * 1 = a");
    axiom(forall_int(&["a"], eq))
}

/// `⊢ ∀a. a * 0 = 0`.
pub fn mul_zero() -> Thm {
    let a = var("a");
    let eq = mul(a, lit(0)).equals(lit(0)).expect("mul_zero: a * 0 = 0");
    axiom(forall_int(&["a"], eq))
}

/// `⊢ ∀a b c. a * (b + c) = a * b + a * c` — left distributivity.
pub fn distrib() -> Thm {
    let (a, b, c) = (var("a"), var("b"), var("c"));
    let lhs = mul(a.clone(), add(b.clone(), c.clone()));
    let rhs = add(mul(a.clone(), b), mul(a, c));
    let eq = lhs.equals(rhs).expect("distrib");
    axiom(forall_int(&["a", "b", "c"], eq))
}

cached_thm! {
    /// `⊢ ∀a b. a - b = a + (-b)` — **proved**. Both sides land on the same
    /// representative pair `(fa+sb, sa+fb)`: `int.sub`'s Grothendieck formula
    /// `(a−b)−(c−d) = (a+d)−(b+c)` *is* `int.add` of `a` with the swapped
    /// `int.neg b`, so the `MK` components coincide on the nose.
    pub fn sub_def() -> Result<Thm> {
        let (a, b) = (var("a"), var("b"));
        let (ra, rb) = (recon_mk(&a)?, recon_mk(&b)?);
        // a - b = MK (fa+sb)(sa+fb)
        let lhs = sub_via_components(&ra, &rb)?;
        // a + (-b) = MK (fa+sb)(sa+fb)  (neg b = MK sb fb, then add)
        let neg_b = neg_via_components(&rb)?;
        let rhs = add_via_components(&ra, &neg_b)?;
        lhs.trans(rhs.sym()?)?
            .all_intro("b", int())?
            .all_intro("a", int())
    }
}

// ============================================================================
// Linear order
// ============================================================================

/// `⊢ ∀a. ¬(a < a)` — irreflexivity.
pub fn lt_irrefl() -> Thm {
    let a = var("a");
    let body = lt(a.clone(), a).not().expect("lt_irrefl: ¬(a < a)");
    axiom(forall_int(&["a"], body))
}

/// `⊢ ∀a b c. a < b ⟹ b < c ⟹ a < c` — transitivity.
pub fn lt_trans() -> Thm {
    let (a, b, c) = (var("a"), var("b"), var("c"));
    let inner = lt(b.clone(), c.clone())
        .imp(lt(a.clone(), c))
        .expect("lt_trans inner");
    let body = lt(a, b).imp(inner).expect("lt_trans");
    axiom(forall_int(&["a", "b", "c"], body))
}

/// `⊢ ∀a b. a < b ∨ a = b ∨ b < a` — trichotomy (totality).
pub fn lt_trichotomy() -> Thm {
    let (a, b) = (var("a"), var("b"));
    let eq = a.clone().equals(b.clone()).expect("trichotomy: a = b");
    let tail = eq.or(lt(b.clone(), a.clone())).expect("trichotomy tail");
    let body = lt(a, b).or(tail).expect("trichotomy");
    axiom(forall_int(&["a", "b"], body))
}

/// `⊢ ∀a b. (a ≤ b) = (a < b ∨ a = b)` — `≤` in terms of `<`.
pub fn le_def() -> Thm {
    let (a, b) = (var("a"), var("b"));
    let rhs = lt(a.clone(), b.clone())
        .or(a.clone().equals(b.clone()).expect("le_def: a = b"))
        .expect("le_def rhs");
    let eq = le(a, b).equals(rhs).expect("le_def");
    axiom(forall_int(&["a", "b"], eq))
}

// ============================================================================
// Ordered-ring compatibility
// ============================================================================

/// `⊢ ∀a b c. a < b ⟹ a + c < b + c` — translation invariance of `<`.
pub fn lt_add_mono() -> Thm {
    let (a, b, c) = (var("a"), var("b"), var("c"));
    let concl = lt(add(a.clone(), c.clone()), add(b.clone(), c));
    let body = lt(a, b).imp(concl).expect("lt_add_mono");
    axiom(forall_int(&["a", "b", "c"], body))
}

/// `⊢ ∀a b c. 0 < c ⟹ a < b ⟹ a * c < b * c` — `<` preserved by a
/// positive multiplier.
pub fn lt_mul_pos() -> Thm {
    let (a, b, c) = (var("a"), var("b"), var("c"));
    let concl = lt(mul(a.clone(), c.clone()), mul(b.clone(), c.clone()));
    let inner = lt(a, b).imp(concl).expect("lt_mul_pos inner");
    let body = lt(lit(0), c).imp(inner).expect("lt_mul_pos");
    axiom(forall_int(&["a", "b", "c"], body))
}

// ============================================================================
// Discreteness — the integer-specific axiom
// ============================================================================

/// `⊢ ∀a b. (a < b) = (a + 1 ≤ b)` — the integers are discrete: strict
/// `<` is `+1`-shifted `≤`. The key fact the integer-specific Alethe
/// `la` rules (rounding rational bounds to integer ones) rest on.
pub fn lt_succ() -> Thm {
    let (a, b) = (var("a"), var("b"));
    let eq = lt(a.clone(), b.clone())
        .equals(le(add(a, lit(1)), b))
        .expect("lt_succ: (a < b) = (a + 1 ≤ b)");
    axiom(forall_int(&["a", "b"], eq))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The full postulate set — used to assert the audit-trail invariant.
    fn all() -> Vec<Thm> {
        vec![
            mul_assoc(),
            mul_one(),
            mul_zero(),
            distrib(),
            lt_irrefl(),
            lt_trans(),
            lt_trichotomy(),
            le_def(),
            lt_add_mono(),
            lt_mul_pos(),
            lt_succ(),
        ]
    }

    #[test]
    fn postulates_are_well_typed_and_self_flagged() {
        for ax in all() {
            assert!(
                ax.concl().type_of().unwrap().is_bool(),
                "an int postulate is a bool statement"
            );
            assert!(
                ax.hyps().iter().any(|h| h == ax.concl()),
                "a postulated axiom carries itself as a hypothesis"
            );
        }
    }

    #[test]
    fn recon_and_add_class_hold_on_int() {
        // recon: ⊢ a = mk_int(rep_pair a), genuine.
        let a = var("a");
        let rt = recon(&a).expect("recon on int");
        assert!(rt.hyps().is_empty(), "recon is genuine");
        assert_eq!(rt.concl().as_eq().unwrap().0, &a);

        // add_class: ⊢ int.add (mk_int u)(mk_int v) = mk_int(add_pair u v).
        // (Witness pair vars avoid the names internal machinery introduces.)
        let (u, v) = (Term::free("uu", nn()), Term::free("vv", nn()));
        let ac = add_class(&u, &v).expect("add_class");
        assert!(ac.hyps().is_empty(), "add_class is genuine");
        let (l, r) = ac.concl().as_eq().unwrap();
        assert_eq!(l, &add(mk_int(&u), mk_int(&v)));
        assert_eq!(r, &mk_int(&add_pair(&u, &v)));
    }

    #[test]
    fn add_comm_is_a_genuine_theorem() {
        let thm = add_comm();
        assert!(
            thm.hyps().is_empty(),
            "int::add_comm is proved, not postulated"
        );
        // ∀a b. a + b = b + a, specialised.
        let (a, b) = (var("a"), var("b"));
        let inst = thm
            .all_elim(a.clone())
            .unwrap()
            .all_elim(b.clone())
            .unwrap();
        let expected = add(a.clone(), b.clone()).equals(add(b, a)).unwrap();
        assert_eq!(inst.concl(), &expected);
    }

    #[test]
    fn add_assoc_is_a_genuine_theorem() {
        let thm = add_assoc();
        assert!(
            thm.hyps().is_empty(),
            "int::add_assoc is proved, not postulated"
        );
        let (a, b, c) = (var("a"), var("b"), var("c"));
        let inst = elim3(thm, &a, &b, &c).unwrap();
        let expected = add(add(a.clone(), b.clone()), c.clone())
            .equals(add(a, add(b, c)))
            .unwrap();
        assert_eq!(inst.concl(), &expected);
    }

    #[test]
    fn sub_def_is_a_genuine_theorem() {
        let thm = sub_def();
        assert!(
            thm.hyps().is_empty(),
            "int::sub_def is proved, not postulated"
        );
        let (a, b) = (var("a"), var("b"));
        let inst = thm
            .all_elim(a.clone())
            .unwrap()
            .all_elim(b.clone())
            .unwrap();
        let sub = Term::app(Term::app(int_sub(), a.clone()), b.clone());
        let expected = sub.equals(add(a, neg(b))).unwrap();
        assert_eq!(inst.concl(), &expected);
    }

    #[test]
    fn additive_unit_and_inverse_are_genuine() {
        // add_zero: ∀a. a + 0 = a ; add_neg: ∀a. a + (-a) = 0.
        let a = var("a");
        let z = add_zero();
        assert!(z.hyps().is_empty(), "int::add_zero is proved");
        assert_eq!(
            z.all_elim(a.clone()).unwrap().concl(),
            &add(a.clone(), lit(0)).equals(a.clone()).unwrap()
        );
        let ninv = add_neg();
        assert!(ninv.hyps().is_empty(), "int::add_neg is proved");
        assert_eq!(
            ninv.all_elim(a.clone()).unwrap().concl(),
            &add(a.clone(), neg(a.clone())).equals(lit(0)).unwrap()
        );
    }

    #[test]
    fn mul_comm_is_a_genuine_theorem() {
        let thm = mul_comm();
        assert!(
            thm.hyps().is_empty(),
            "int::mul_comm is proved, not postulated"
        );
        let (a, b) = (var("a"), var("b"));
        let inst = thm
            .all_elim(a.clone())
            .unwrap()
            .all_elim(b.clone())
            .unwrap();
        let expected = mul(a.clone(), b.clone()).equals(mul(b, a)).unwrap();
        assert_eq!(inst.concl(), &expected);
    }

    #[test]
    fn add_comm_specialises() {
        // ∀a b. a + b = b + a  ⟹  (1 + 2) = (2 + 1).
        let inst = add_comm()
            .all_elim(lit(1))
            .and_then(|t| t.all_elim(lit(2)))
            .expect("specialize add_comm");
        let expected = add(lit(1), lit(2)).equals(add(lit(2), lit(1))).unwrap();
        assert_eq!(inst.concl(), &expected);
    }

    #[test]
    fn le_def_is_an_equation_at_bool() {
        let thm = le_def();
        // ∀-stripped twice, the body is a bool equation.
        let inst = thm
            .all_elim(lit(0))
            .and_then(|t| t.all_elim(lit(1)))
            .unwrap();
        assert!(inst.concl().as_eq().is_some(), "le_def body is `(≤) = (…)`");
    }

    #[test]
    fn int_rel_is_a_genuine_equivalence() {
        // All three are hypothesis-free (genuine) theorems.
        for t in [int_rel_refl(), int_rel_symm(), int_rel_trans()] {
            assert!(t.hyps().is_empty(), "int_rel equivalence proof is genuine");
            assert!(t.concl().type_of().unwrap().is_bool());
        }

        let p = Term::free("p", nn());
        let q = Term::free("q", nn());
        // refl specialises to `int_rel p p`.
        assert_eq!(
            int_rel_refl().all_elim(p.clone()).unwrap().concl(),
            &rel_app(&p, &p)
        );
        // symm specialises to `int_rel p q ⟹ int_rel q p`.
        let symm = int_rel_symm()
            .all_elim(p.clone())
            .unwrap()
            .all_elim(q.clone())
            .unwrap();
        assert_eq!(symm.concl(), &rel_app(&p, &q).imp(rel_app(&q, &p)).unwrap());
    }

    #[test]
    fn round_trip_relates_the_chosen_representative() {
        use crate::init::quotient;
        let spec = covalence_core::defs::int_ty_spec();
        let p = Term::free("p", nn());
        // ⊢ int_rel p (rep_class (mk_class p)) — a genuine, hyp-free theorem.
        let rt = quotient::round_trip(&spec, &[], &nn(), &int_rel(), &int_rel_refl(), &p)
            .expect("round_trip on int");
        assert!(rt.hyps().is_empty(), "round_trip is genuine");
        // Conclusion is `int_rel p <something>`.
        let (rel, a, _) = {
            let (ra, b) = rt.concl().as_app().unwrap();
            let (r, a) = ra.as_app().unwrap();
            (r.clone(), a.clone(), b.clone())
        };
        assert_eq!(&rel, &int_rel());
        assert_eq!(&a, &p);
    }

    #[test]
    fn class_intro_lifts_int_rel_to_a_class_equation() {
        // The payoff: with int_rel proven an equivalence, the forward
        // quotient law lifts a `~`-fact to an int-class equation.
        use crate::init::quotient;
        let spec = covalence_core::defs::int_ty_spec();
        let (p, q) = (Term::free("p", nn()), Term::free("q", nn()));
        // From {int_rel p q} ⊢ int_rel p q, lift to mkClass p = mkClass q.
        let ab = Thm::assume(rel_app(&p, &q)).unwrap();
        let lifted =
            quotient::class_intro(&spec, &[], &nn(), &int_rel_symm(), &int_rel_trans(), ab)
                .expect("class_intro on int_rel");
        assert!(
            lifted.concl().as_eq().is_some(),
            "lifted to a class equation"
        );
        assert!(lifted.hyps().iter().any(|h| h == &rel_app(&p, &q)));
    }
}
