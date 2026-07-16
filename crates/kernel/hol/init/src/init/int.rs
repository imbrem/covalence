//! `int` theorems: the `defs/int.rs` catalogue re-exported, plus the
//! **postulated** ordered-commutative-ring (with discreteness) theory of
//! HOL `int` — mirroring how [`init::nat`] pairs the `nat` definitions
//! with their Peano facts.
//!
//! [`init::nat`]: crate::init::nat
//!
//! ## Status — the entire ordered ring is proved (no postulates)
//!
//! `int := (nat × nat) / ~` is the Grothendieck construction, so every
//! axiom here is a *theorem* of HOL derivable from the `nat` Peano facts
//! through the quotient — and **all of them are now discharged**. There are
//! no `Thm::assume` postulates left in this module.
//!
//! - **Commutative ring** — [`add_comm`], [`add_assoc`], [`add_zero`],
//!   [`add_neg`], [`sub_def`], [`mul_comm`], [`mul_assoc`], [`mul_one`],
//!   [`mul_zero`], [`distrib`].
//! - **Linear order** — [`lt_irrefl`], [`lt_trans`], [`lt_trichotomy`],
//!   [`le_def`].
//! - **Ordered-ring compatibility** — [`lt_add_mono`], [`lt_mul_pos`].
//! - **Discreteness** — [`lt_succ`] (`a < b ⟺ a + 1 ≤ b`).
//!
//! The public surface (these `fn`s) does not change as proofs land — only
//! the bodies; downstream consumers (the `int` ring/semiring embedding, the
//! Alethe `la_*` checker) are unaffected.
//!
//! ## The lifting machinery (how the proved axioms work)
//!
//! [`init::quotient`](crate::init::quotient) supplies `class_intro`
//! (forward: `⊢ rel a b → ⊢ mkClass a = mkClass b`), `class_elim`
//! (converse), `round_trip` (`⊢ rel a (rep_class (mk_class a))`), and
//! `recon` (quotient induction: `⊢ a = mk_class (rep_class a)` for *any*
//! element of the junk-free quotient). On top of those, this module:
//!
//! - proves `int_rel` an equivalence ([`int_rel_refl`]/`_symm`/`_trans`);
//! - normalises every reconstructed `int` to the **`MK(f, s)` component
//!   form** `mk_int (pair f s)` (`recon` + surjective pairing), so the op
//!   rules combine explicit `nat` components on the nose;
//! - gives per-op **computation rules** (`add_class` / `neg_class` /
//!   `sub_class` / `mul_class` / `succ_class` and their `*_mk` component
//!   forms) via the defining equation, `round_trip`, and a per-op
//!   well-definedness lemma (`*_pair_cong`). Multiplication
//!   (`mul_pair_cong`) is the one tedious case — proved per-argument
//!   (`distrib` on the defining `nat` equation) and chained by transitivity;
//! - derives **literal coherence** (`lit0_mk`: `int_lit 0 = MK(0, 0)`,
//!   from the two readings of `0 + 0` forcing `fst(rep 0) = snd(rep 0)`;
//!   `lit1_mk`: `int_lit 1 = MK(1, 0)` via `int.succ 0 = succ (MK 0 0)`).
//!
//! Each ring axiom then reduces to `nat` algebra on the `f`/`s` components
//! (e.g. `add_assoc` is `nat::add_assoc` per component; `mul_assoc` /
//! `distrib` distribute to the same `nat` products, re-paired by `mid_swap`).
//!
//! **Order** works the same way: `int.le` / `int.lt` on the `MK` form read
//! off the clean components (`le_mk` / `lt_mk`) — the ε-representatives the
//! comparison picks are `round_trip`-related to `(f, s)`, and `nat::le_cross`
//! / `lt_cross` make the comparison invariant under that. `le_via_components`
//! / `lt_via_components` then express each order axiom as a `nat` order fact
//! (the `nat` strict-order theory `lt_trans` / `lt_trichotomy` /
//! `lt_add_mono_r` / `lt_iff_succ_le` / `le_iff_lt_or_eq` / `lt_mul_mono_r`),
//! and `int_eq_iff` identifies `int` equality with the Grothendieck relation
//! on representatives. The one genuinely heavy lift, `lt_mul_pos`, writes
//! `0 < c` as `fc = sc + m` and decomposes both product comparisons as
//! `D + (fa+sb)·m` / `D + (fb+sa)·m` over the same `D` — the shuffle handled
//! by the reusable `nat` additive normaliser `nat::prove_add_eq`.

use covalence_core::{Error, Result, Term, Type, subst};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::defs::{fst, pair, prod, snd};
use covalence_hol_eval::derived::DerivedRules;

use crate::init::ext::{TermExt, ThmExt};
use crate::init::logic;
use crate::init::nat;
use crate::init::quotient;

// Re-export the `defs/int.rs` term catalogue (the operations; the
// `*_spec` handles stay in `covalence_hol_eval::defs`).
pub use covalence_hol_eval::defs::{
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
    covalence_hol_eval::mk_int(n)
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
        .delta_all(covalence_hol_eval::defs::int_add_spec().symbol())?
        .rhs_conv(|t| t.reduce())
}

/// `⊢ int.mul a b = abs(classOf (pair P1 P2))` — `int.mul`'s defining
/// equation, with `P1 = fa·fb + sa·sb`, `P2 = fa·sb + sa·fb`
/// (`fa = fst(rep a)`, `sa = snd(rep a)`, …).
fn mul_defining_eq(a: &Term, b: &Term) -> Result<Thm> {
    mul(a.clone(), b.clone())
        .delta_all(covalence_hol_eval::defs::int_mul_spec().symbol())?
        .rhs_conv(|t| t.reduce())
}

/// `⊢ t = t'`, applying each `eqs[i]` (`rw_all`, all occurrences) to the
/// running RHS in turn.
fn rewrite_seq(t: &Term, eqs: &[Thm]) -> Result<Thm> {
    rewrite_seq_with(t, eqs, &mut ())
}

/// [`rewrite_seq`] routing every rewrite through a caller-supplied interner — share
/// one `cons` across a whole proof's rewrites.
fn rewrite_seq_with<C: covalence_core::term::TrustedCons + ?Sized>(
    t: &Term,
    eqs: &[Thm],
    cons: &mut C,
) -> Result<Thm> {
    let mut acc = Thm::refl(t.clone())?;
    for eq in eqs {
        let cur = acc.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone();
        acc = acc.trans(cur.rw_all_with(eq, cons)?)?;
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
fn spec() -> covalence_hol_eval::defs::TypeSpec {
    covalence_hol_eval::defs::int_ty_spec()
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
        .delta_all(covalence_hol_eval::defs::int_neg_spec().symbol())?
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
        .delta_all(covalence_hol_eval::defs::int_sub_spec().symbol())?
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

// ---- multiplication ----

/// `pair (fx·fy + sx·sy) (fx·sy + sx·fy)` — Grothendieck product
/// `(a−b)(c−d) = (ac+bd) − (ad+bc)`.
fn mul_pair(x: &Term, y: &Term) -> Term {
    let (fx, sx) = (fst_nn(x), snd_nn(x));
    let (fy, sy) = (fst_nn(y), snd_nn(y));
    pair_nn(
        nat::add(
            nat::mul(fx.clone(), fy.clone()),
            nat::mul(sx.clone(), sy.clone()),
        ),
        nat::add(nat::mul(fx, sy), nat::mul(sx, fy)),
    )
}

/// `⊢ x·m = y·m` from `⊢ x = y`.
fn cong_mul_l(eq: Thm, m: &Term) -> Result<Thm> {
    Thm::refl(nat::nat_mul())?.cong_app(eq)?.cong_fn(m.clone())
}
/// `⊢ m·x = m·y` from `⊢ x = y`.
fn cong_mul_r(m: &Term, eq: Thm) -> Result<Thm> {
    Thm::refl(Term::app(nat::nat_mul(), m.clone()))?.cong_app(eq)
}

/// `⊢ p·m + q·m = r·m + s·m` from `e : ⊢ p + q = r + s` (right multiply).
fn mul_r_eq(p: &Term, q: &Term, r: &Term, s: &Term, e: Thm, m: &Term) -> Result<Thm> {
    let lhs = elim3(nat::distrib_r(), p, q, m)?; // (p+q)·m = p·m+q·m
    let rhs = elim3(nat::distrib_r(), r, s, m)?; // (r+s)·m = r·m+s·m
    lhs.sym()?.trans(cong_mul_l(e, m)?)?.trans(rhs)
}
/// `⊢ m·p + m·q = m·r + m·s` from `e : ⊢ p + q = r + s` (left multiply).
fn mul_l_eq(m: &Term, p: &Term, q: &Term, r: &Term, s: &Term, e: Thm) -> Result<Thm> {
    let lhs = elim3(nat::distrib(), m, p, q)?; // m·(p+q) = m·p+m·q
    let rhs = elim3(nat::distrib(), m, r, s)?; // m·(r+s) = m·r+m·s
    lhs.sym()?.trans(cong_mul_r(m, e)?)?.trans(rhs)
}

/// `⊢ u = u` reflexivity helper for re-pairing under `+`.
fn cong_add_r(left: &Term, eq: Thm) -> Result<Thm> {
    eq.cong_arg(Term::app(nat::nat_add(), left.clone()))
}

/// **Left multiplicative well-definedness.** `⊢ int_rel x x'` lifted to
/// `⊢ int_rel (mul_pair x y) (mul_pair x' y)` (`y` fixed). The Grothendieck
/// product distributes over the defining `nat` equation in the varied factor.
fn mul_pair_cong_l(h1: Thm, y: &Term) -> Result<Thm> {
    let (x, xp) = dest_rel_app(h1.concl())?;
    let e = reduce_rel(h1)?; // a + b' = a' + b   (a=fx, b=sx, a'=fx', b'=sx')
    let (a, b) = (fst_nn(&x), snd_nn(&x));
    let (ap, bp) = (fst_nn(&xp), snd_nn(&xp));
    let (c, d) = (fst_nn(y), snd_nn(y));
    let m = |u: &Term, v: &Term| nat::mul(u.clone(), v.clone());

    // eL_c: a·c+b'·c = a'·c+b·c ; eL_d: a·d+b'·d = a'·d+b·d.
    let elc = mul_r_eq(&a, &bp, &ap, &b, e.clone(), &c)?;
    let eld = mul_r_eq(&a, &bp, &ap, &b, e, &d)?;
    // bd+a'd = a'd+bd = ad+b'd.
    let bd_eq = nat::add_comm()
        .all_elim(m(&b, &d))?
        .all_elim(m(&ap, &d))?
        .trans(eld.sym()?)?; // b·d+a'·d = a·d+b'·d

    let (ac, bd, apd, bpc) = (m(&a, &c), m(&b, &d), m(&ap, &d), m(&bp, &c));
    let (apc, bc, ad, bpd) = (m(&ap, &c), m(&b, &c), m(&a, &d), m(&bp, &d));
    // (ac+bd)+(a'd+b'c) = (ac+b'c)+(bd+a'd) = (a'c+bc)+(ad+b'd)
    //                   = (a'c+b'd)+(bc+ad) = (a'c+b'd)+(ad+bc).
    let g = elim4(nat::add_interchange(), &ac, &bd, &apd, &bpc)?
        .trans(nat::cong_add(elc, bd_eq)?)?
        .trans(elim4(nat::add_interchange(), &apc, &bc, &ad, &bpd)?)?
        .trans(cong_add_r(
            &nat::add(apc.clone(), bpd.clone()),
            nat::add_comm().all_elim(bc.clone())?.all_elim(ad.clone())?,
        )?)?;
    rel_of_pairs(
        &nat::add(ac, bd),
        &nat::add(ad, bc),
        &nat::add(apc, bpd),
        &nat::add(apd, bpc),
        g,
    )
}

/// **Right multiplicative well-definedness.** `⊢ int_rel y y'` lifted to
/// `⊢ int_rel (mul_pair x' y) (mul_pair x' y')` (`x'` fixed).
fn mul_pair_cong_r(xp: &Term, h2: Thm) -> Result<Thm> {
    let (y, yp) = dest_rel_app(h2.concl())?;
    let e2 = reduce_rel(h2)?; // c + d' = c' + d   (c=fy, d=sy, c'=fy', d'=sy')
    let (ap, bp) = (fst_nn(xp), snd_nn(xp));
    let (c, d) = (fst_nn(&y), snd_nn(&y));
    let (cp, dp) = (fst_nn(&yp), snd_nn(&yp));
    let m = |u: &Term, v: &Term| nat::mul(u.clone(), v.clone());

    // eR_a: a'·c+a'·d' = a'·c'+a'·d ; eR_b: b'·c+b'·d' = b'·c'+b'·d.
    let era = mul_l_eq(&ap, &c, &dp, &cp, &d, e2.clone())?;
    let erb = mul_l_eq(&bp, &c, &dp, &cp, &d, e2)?;
    // b'd+b'c' = b'c'+b'd = b'c+b'd'.
    let erb2 = nat::add_comm()
        .all_elim(m(&bp, &d))?
        .all_elim(m(&bp, &cp))?
        .trans(erb.sym()?)?; // b'·d+b'·c' = b'·c+b'·d'

    let (apc, bpd, apdp, bpcp) = (m(&ap, &c), m(&bp, &d), m(&ap, &dp), m(&bp, &cp));
    let (apcp, apd, bpc, bpdp) = (m(&ap, &cp), m(&ap, &d), m(&bp, &c), m(&bp, &dp));
    // (a'c+b'd)+(a'd'+b'c') = (a'c+a'd')+(b'd+b'c') = (a'c'+a'd)+(b'c+b'd')
    //                       = (a'c'+b'd')+(a'd+b'c).
    let g = mid_swap(&apc, &bpd, &apdp, &bpcp)?
        .trans(nat::cong_add(era, erb2)?)?
        .trans(elim4(nat::add_interchange(), &apcp, &apd, &bpc, &bpdp)?)?;
    rel_of_pairs(
        &nat::add(apc, bpd),
        &nat::add(apd, bpc),
        &nat::add(apcp, bpdp),
        &nat::add(apdp, bpcp),
        g,
    )
}

/// **Multiplicative well-definedness.** From `⊢ int_rel x x'`, `⊢ int_rel
/// y y'` conclude `⊢ int_rel (mul_pair x y) (mul_pair x' y')` — vary one
/// factor at a time ([`mul_pair_cong_l`] / [`mul_pair_cong_r`]) and chain by
/// transitivity through `mul_pair x' y`.
fn mul_pair_cong(h1: Thm, h2: Thm) -> Result<Thm> {
    let (x, xp) = dest_rel_app(h1.concl())?;
    let (y, yp) = dest_rel_app(h2.concl())?;
    let left = mul_pair_cong_l(h1, &y)?; // int_rel (mul x y) (mul x' y)
    let right = mul_pair_cong_r(&xp, h2)?; // int_rel (mul x' y) (mul x' y')
    elim3(
        int_rel_trans(),
        &rel_app_target(&x, &y),
        &rel_app_target(&xp, &y),
        &rel_app_target(&xp, &yp),
    )?
    .imp_elim(left)?
    .imp_elim(right)
}

/// `mul_pair x y` — named so `mul_pair_cong`'s `int_rel_trans` instantiation
/// reads cleanly.
fn rel_app_target(x: &Term, y: &Term) -> Term {
    mul_pair(x, y)
}

/// **Multiplicative computation rule.** `⊢ int.mul (mk_int p) (mk_int q) =
/// mk_int (mul_pair p q)`.
fn mul_class(p: &Term, q: &Term) -> Result<Thm> {
    let (mp, mq) = (mk_int(p), mk_int(q));
    let dl = mul_defining_eq(&mp, &mq)?;
    let (rpp, rpq) = (rep_pair(&mp), rep_pair(&mq));
    let dl = dl.trans(defs_to_mk_int(&mul_pair(&rpp, &rpq))?)?; // = mk_int(mul_pair RPp RPq)
    let rpp_p = inst2(int_rel_symm(), p, &rpp)?.imp_elim(round_trip(p)?)?;
    let rpq_q = inst2(int_rel_symm(), q, &rpq)?.imp_elim(round_trip(q)?)?;
    let cong = mul_pair_cong(rpp_p, rpq_q)?;
    let lift = quotient::class_intro(&spec(), &[], &nn(), &int_rel_symm(), &int_rel_trans(), cong)?;
    dl.trans(lift)
}

// ---- successor (the bridge to literal-`1` coherence) ----

/// `pair (succ (fst x)) (snd x)` — `succ (a−b) = (a+1) − b`.
fn succ_pair(x: &Term) -> Term {
    pair_nn(nat::succ(fst_nn(x)), snd_nn(x))
}

/// `⊢ int.succ a = abs(class_of_defs (succ_pair (rep_pair a)))`.
fn succ_defining_eq(a: &Term) -> Result<Thm> {
    Term::app(int_succ(), a.clone())
        .delta_all(covalence_hol_eval::defs::int_succ_spec().symbol())?
        .rhs_conv(|t| t.reduce())
}

/// **Successor well-definedness.** `⊢ int_rel x x'` lifted to
/// `⊢ int_rel (succ_pair x) (succ_pair x')` — push the `succ` through the
/// defining equation by `nat::add_step`.
fn succ_pair_cong(h: Thm) -> Result<Thm> {
    let (x, xp) = dest_rel_app(h.concl())?;
    let e = reduce_rel(h)?; // fx + sx' = fx' + sx
    let (fx, sx) = (fst_nn(&x), snd_nn(&x));
    let (fxp, sxp) = (fst_nn(&xp), snd_nn(&xp));
    // (S fx)+sx' = S(fx+sx') = S(fx'+sx) = (S fx')+sx.
    let g = nat::add_step()
        .all_elim(fx.clone())?
        .all_elim(sxp.clone())?
        .trans(e.cong_arg(nat::nat_succ())?)?
        .trans(
            nat::add_step()
                .all_elim(fxp.clone())?
                .all_elim(sx.clone())?
                .sym()?,
        )?;
    rel_of_pairs(&nat::succ(fx), &sx, &nat::succ(fxp), &sxp, g)
}

/// **Successor computation rule.** `⊢ int.succ (mk_int p) = mk_int (succ_pair p)`.
fn succ_class(p: &Term) -> Result<Thm> {
    let mp = mk_int(p);
    let dl = succ_defining_eq(&mp)?;
    let rpp = rep_pair(&mp);
    let dl = dl.trans(defs_to_mk_int(&succ_pair(&rpp))?)?; // = mk_int(succ_pair RPp)
    let rpp_p = inst2(int_rel_symm(), p, &rpp)?.imp_elim(round_trip(p)?)?;
    let cong = succ_pair_cong(rpp_p)?;
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

/// **Multiplication in component form.** `⊢ int.mul (MK fa sa)(MK fb sb) =
/// MK (fa·fb + sa·sb)(fa·sb + sa·fb)`.
fn mul_mk(fa: &Term, sa: &Term, fb: &Term, sb: &Term) -> Result<Thm> {
    let (pa, pb) = (
        pair_nn(fa.clone(), sa.clone()),
        pair_nn(fb.clone(), sb.clone()),
    );
    let mc = mul_class(&pa, &pb)?; // = mk_int(mul_pair pa pb)
    let n = Type::nat();
    let projs = [
        crate::init::prod::fst_pair(&n, &n, fa, sa)?, // fst pa = fa  (both occurrences)
        crate::init::prod::snd_pair(&n, &n, fa, sa)?, // snd pa = sa
        crate::init::prod::fst_pair(&n, &n, fb, sb)?, // fst pb = fb
        crate::init::prod::snd_pair(&n, &n, fb, sb)?, // snd pb = sb
    ];
    mc.rhs_conv(|t| rewrite_seq(t, &projs)) // = MK (fa·fb+sa·sb)(fa·sb+sa·fb)
}

/// `⊢ int.mul a b = MK (fa·fb+sa·sb)(fa·sb+sa·fb)`, where `ra : a = MK fa
/// sa`, `rb : b = MK fb sb`.
fn mul_via_components(ra: &Thm, rb: &Thm) -> Result<Thm> {
    let (_a, ma) = dest_eq(ra)?;
    let (_b, mb) = dest_eq(rb)?;
    let (fa, sa) = mk_components(&ma)?;
    let (fb, sb) = mk_components(&mb)?;
    Thm::refl(int_mul())?
        .cong_app(ra.clone())?
        .cong_app(rb.clone())? // int.mul a b = int.mul (MK fa sa)(MK fb sb)
        .trans(mul_mk(&fa, &sa, &fb, &sb)?)
}

/// **Successor in component form.** `⊢ int.succ (MK f s) = MK (succ f) s`.
fn succ_mk(f: &Term, s: &Term) -> Result<Thm> {
    let sc = succ_class(&pair_nn(f.clone(), s.clone()))?; // = mk_int(succ_pair (pair f s))
    let n = Type::nat();
    let projs = [
        crate::init::prod::fst_pair(&n, &n, f, s)?, // fst (pair f s) = f  (under succ)
        crate::init::prod::snd_pair(&n, &n, f, s)?, // snd (pair f s) = s
    ];
    sc.rhs_conv(|t| rewrite_seq(t, &projs)) // = MK (succ f) s
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
// Integer literals are opaque kernel leaves (built via the hol-eval
// facade), invisible to the quotient. But
// `int.add`/`int.succ` on literals reduce (the cert path) AND unfold to the
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
/// `0` (the cert path) and unfolds to `MK(f0+f0)(s0+s0)` (`f0`/`s0` the
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

/// `⊢ int_lit 1 = MK(1, 0)` — literal-`1` coherence. Cleanly: `int.succ 0`
/// reduces to `1`, and `int.succ (MK 0 0) = MK (succ 0) 0 = MK 1 0`.
fn lit1_mk() -> Result<Thm> {
    let e_red = Term::app(int_succ(), lit(0)).reduce()?; // int.succ 0 = 1
    let succ_cong = Thm::refl(int_succ())?.cong_app(lit0_mk()?)?; // int.succ 0 = int.succ (MK 0 0)
    let sm = succ_mk(&nat::zero(), &nat::zero())?; // int.succ (MK 0 0) = MK (succ 0) 0
    let succ0_eq_1 = nat::succ(nat::zero()).reduce()?; // succ 0 = 1
    let bridge = mkfs_cong(succ0_eq_1, Thm::refl(nat::zero())?)?; // MK (succ 0) 0 = MK 1 0
    e_red
        .sym()? // int_lit 1 = int.succ 0
        .trans(succ_cong)?
        .trans(sm)?
        .trans(bridge) // = MK 1 0
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
    /// `⊢ ∀a. a + 0 = a` — **proved**. `0 = MK(0,0)` (`lit0_mk`), so
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

cached_thm! {
    /// `⊢ ∀a b c. (a * b) * c = a * (b * c)` — **proved**. On `MK`
    /// components each side expands (`distrib`/`distrib_r` + `nat::mul_assoc`)
    /// to the same four triple-products, re-paired by `mid_swap`.
    pub fn mul_assoc() -> Result<Thm> {
        let (a, b, c) = (var("a"), var("b"), var("c"));
        let (ra, rb, rc) = (recon_mk(&a)?, recon_mk(&b)?, recon_mk(&c)?);
        let (fa, sa) = (fcomp(&a), scomp(&a));
        let (fb, sb) = (fcomp(&b), scomp(&b));
        let (fc, sc) = (fcomp(&c), scomp(&c));
        let m = |u: &Term, v: &Term| nat::mul(u.clone(), v.clone());
        let acomm = |x: &Term, y: &Term| -> Result<Thm> {
            nat::add_comm().all_elim(x.clone())?.all_elim(y.clone())
        };

        // (a*b)*c = MK (P1·fc + P2·sc) (P1·sc + P2·fc),  P1=fa·fb+sa·sb,
        //   P2=fa·sb+sa·fb ; a*(b*c) = MK (fa·Q1 + sa·Q2) (fa·Q2 + sa·Q1),
        //   Q1=fb·fc+sb·sc, Q2=fb·sc+sb·fc.
        let ab = mul_via_components(&ra, &rb)?;
        let lhs = mul_via_components(&ab, &rc)?;
        let bc = mul_via_components(&rb, &rc)?;
        let rhs = mul_via_components(&ra, &bc)?;

        // `(x·y + z·w)·u = x·(y·u) + z·(w·u)` (distrib_r + two mul_assoc).
        let expand_r = |x: &Term, y: &Term, z: &Term, w: &Term, u: &Term| -> Result<Thm> {
            elim3(nat::distrib_r(), &m(x, y), &m(z, w), u)?.trans(nat::cong_add(
                elim3(nat::mul_assoc(), x, y, u)?,
                elim3(nat::mul_assoc(), z, w, u)?,
            )?)
        };

        // fst: (P1·fc + P2·sc) = (fa·Q1 + sa·Q2).  Atoms A,B,C,D.
        let fst_eq = {
            let (aa, bb) = (m(&fa, &m(&fb, &fc)), m(&sa, &m(&sb, &fc)));
            let (cc, dd) = (m(&fa, &m(&sb, &sc)), m(&sa, &m(&fb, &sc)));
            let l = nat::cong_add(
                expand_r(&fa, &fb, &sa, &sb, &fc)?, // P1·fc = A + B
                expand_r(&fa, &sb, &sa, &fb, &sc)?, // P2·sc = C + D
            )?; // L1 = (A+B)+(C+D)
            let r = nat::cong_add(
                elim3(nat::distrib(), &fa, &m(&fb, &fc), &m(&sb, &sc))?, // fa·Q1 = A + C
                elim3(nat::distrib(), &sa, &m(&fb, &sc), &m(&sb, &fc))?, // sa·Q2 = D + B
            )?; // R1 = (A+C)+(D+B)
            l.trans(mid_swap(&aa, &bb, &cc, &dd)?)? // = (A+C)+(B+D)
                .trans(cong_add_r(&nat::add(aa, cc), acomm(&bb, &dd)?)?)? // = (A+C)+(D+B)
                .trans(r.sym()?)?
        };
        // snd: (P1·sc + P2·fc) = (fa·Q2 + sa·Q1).  Atoms E,F,G,H.
        let snd_eq = {
            let (ee, ff) = (m(&fa, &m(&fb, &sc)), m(&sa, &m(&sb, &sc)));
            let (gg, hh) = (m(&fa, &m(&sb, &fc)), m(&sa, &m(&fb, &fc)));
            let l = nat::cong_add(
                expand_r(&fa, &fb, &sa, &sb, &sc)?, // P1·sc = E + F
                expand_r(&fa, &sb, &sa, &fb, &fc)?, // P2·fc = G + H
            )?; // L2 = (E+F)+(G+H)
            let r = nat::cong_add(
                elim3(nat::distrib(), &fa, &m(&fb, &sc), &m(&sb, &fc))?, // fa·Q2 = E + G
                elim3(nat::distrib(), &sa, &m(&fb, &fc), &m(&sb, &sc))?, // sa·Q1 = H + F
            )?; // R2 = (E+G)+(H+F)
            l.trans(mid_swap(&ee, &ff, &gg, &hh)?)? // = (E+G)+(F+H)
                .trans(cong_add_r(&nat::add(ee, gg), acomm(&ff, &hh)?)?)? // = (E+G)+(H+F)
                .trans(r.sym()?)?
        };

        lhs.trans(mkfs_cong(fst_eq, snd_eq)?)?
            .trans(rhs.sym()?)?
            .all_intro("c", int())?
            .all_intro("b", int())?
            .all_intro("a", int())
    }
}

cached_thm! {
    /// `⊢ ∀a. a * 1 = a` — **proved**. `1 = MK(1,0)` (`lit1_mk`), so
    /// `a * 1 = MK(fa·1+sa·0)(fa·0+sa·1) = MK(fa)(sa) = a` by
    /// `nat::mul_one`/`mul_zero` on each component.
    pub fn mul_one() -> Result<Thm> {
        let a = var("a");
        let ra = recon_mk(&a)?;
        let (fa, sa) = (fcomp(&a), scomp(&a));
        let lhs = mul_via_components(&ra, &lit1_mk()?)?; // a*1 = MK(fa·1+sa·0)(fa·0+sa·1)
        // fst: fa·1+sa·0 = fa+0 = fa.
        let fst_eq = nat::cong_add(
            nat::mul_one().all_elim(fa.clone())?,
            nat::mul_zero().all_elim(sa.clone())?,
        )?
        .trans(nat::add_zero().all_elim(fa.clone())?)?;
        // snd: fa·0+sa·1 = 0+sa = sa.
        let snd_eq = nat::cong_add(
            nat::mul_zero().all_elim(fa.clone())?,
            nat::mul_one().all_elim(sa.clone())?,
        )?
        .trans(nat::add_base().all_elim(sa.clone())?)?;
        lhs.trans(mkfs_cong(fst_eq, snd_eq)?)?
            .trans(ra.sym()?)?
            .all_intro("a", int())
    }
}

cached_thm! {
    /// `⊢ ∀a. a * 0 = 0` — **proved**. `0 = MK(0,0)` (`lit0_mk`), so
    /// `a * 0 = MK(fa·0+sa·0)(fa·0+sa·0) = MK(0)(0) = 0`.
    pub fn mul_zero() -> Result<Thm> {
        let a = var("a");
        let ra = recon_mk(&a)?;
        let (fa, sa) = (fcomp(&a), scomp(&a));
        let lhs = mul_via_components(&ra, &lit0_mk()?)?; // a*0 = MK(fa·0+sa·0)(fa·0+sa·0)
        // each component: fa·0+sa·0 = 0+0 = 0.
        let comp = nat::cong_add(
            nat::mul_zero().all_elim(fa.clone())?,
            nat::mul_zero().all_elim(sa.clone())?,
        )?
        .trans(nat::add_base().all_elim(nat::zero())?)?;
        lhs.trans(mkfs_cong(comp.clone(), comp)?)?
            .trans(lit0_mk()?.sym()?)?
            .all_intro("a", int())
    }
}

cached_thm! {
    /// `⊢ ∀a b c. a * (b + c) = a * b + a * c` — **proved** (left
    /// distributivity). On `MK` components: each side's `fst`/`snd` expands
    /// by `nat::distrib` to the same four products, re-paired by `mid_swap`.
    pub fn distrib() -> Result<Thm> {
        let (a, b, c) = (var("a"), var("b"), var("c"));
        let (ra, rb, rc) = (recon_mk(&a)?, recon_mk(&b)?, recon_mk(&c)?);
        let (fa, sa) = (fcomp(&a), scomp(&a));
        let (fb, sb) = (fcomp(&b), scomp(&b));
        let (fc, sc) = (fcomp(&c), scomp(&c));
        let m = |u: &Term, v: &Term| nat::mul(u.clone(), v.clone());

        // a*(b+c) = MK (fa·(fb+fc)+sa·(sb+sc)) (fa·(sb+sc)+sa·(fb+fc))
        let bc = add_via_components(&rb, &rc)?;
        let lhs = mul_via_components(&ra, &bc)?;
        // a*b + a*c = MK ((fa·fb+sa·sb)+(fa·fc+sa·sc)) ((fa·sb+sa·fb)+(fa·sc+sa·fc))
        let ab = mul_via_components(&ra, &rb)?;
        let ac = mul_via_components(&ra, &rc)?;
        let rhs = add_via_components(&ab, &ac)?;

        // fst: fa·(fb+fc)+sa·(sb+sc) = (fa·fb+sa·sb)+(fa·fc+sa·sc).
        let fst_eq = nat::cong_add(
            elim3(nat::distrib(), &fa, &fb, &fc)?, // fa·(fb+fc) = fa·fb+fa·fc
            elim3(nat::distrib(), &sa, &sb, &sc)?, // sa·(sb+sc) = sa·sb+sa·sc
        )?
        .trans(mid_swap(&m(&fa, &fb), &m(&fa, &fc), &m(&sa, &sb), &m(&sa, &sc))?)?;
        // snd: fa·(sb+sc)+sa·(fb+fc) = (fa·sb+sa·fb)+(fa·sc+sa·fc).
        let snd_eq = nat::cong_add(
            elim3(nat::distrib(), &fa, &sb, &sc)?,
            elim3(nat::distrib(), &sa, &fb, &fc)?,
        )?
        .trans(mid_swap(&m(&fa, &sb), &m(&fa, &sc), &m(&sa, &fb), &m(&sa, &fc))?)?;

        lhs.trans(mkfs_cong(fst_eq, snd_eq)?)?
            .trans(rhs.sym()?)?
            .all_intro("c", int())?
            .all_intro("b", int())?
            .all_intro("a", int())
    }
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
// Order machinery — `int.le` / `int.lt` as the `nat` comparison on components
// ============================================================================
//
// `int.le`/`int.lt` pick ε-representatives and compare `a + d ⋚ c + b`. On the
// `MK(f, s)` form the comparison reads off the *clean* components (`le_mk` /
// `lt_mk`) — the ε-reps are `round_trip`-related to `(f, s)`, and the
// comparison is invariant under that (`nat::le_cross` / `lt_cross`). Then each
// order axiom is a `nat` order fact lifted through `*_via_components`.

/// `⊢ int.lt a b = nat.lt (fst(rep a)+snd(rep b)) (fst(rep b)+snd(rep a))`.
fn lt_defining_eq(a: &Term, b: &Term) -> Result<Thm> {
    lt(a.clone(), b.clone())
        .delta_all(covalence_hol_eval::defs::int_lt_spec().symbol())?
        .rhs_conv(|t| t.reduce())
}
/// `⊢ int.le a b = nat.le (…)(…)` — the `≤` mirror of [`lt_defining_eq`].
fn le_defining_eq(a: &Term, b: &Term) -> Result<Thm> {
    le(a.clone(), b.clone())
        .delta_all(covalence_hol_eval::defs::int_le_spec().symbol())?
        .rhs_conv(|t| t.reduce())
}

/// The cross-sum bridge for `MK fa sa` vs `MK fb sb`:
/// `⊢ (F1+S2)+(fb+sa) = (fa+sb)+(F2+S1)`, where `F1/S1` (resp. `F2/S2`) are
/// the components of the ε-representative `int.le`/`int.lt` picks for `MK fa
/// sa` (resp. `MK fb sb`). Shared by [`le_mk`] / [`lt_mk`].
fn cmp_cross_eq(fa: &Term, sa: &Term, fb: &Term, sb: &Term) -> Result<Thm> {
    let n = Type::nat();
    let (rp, rq) = (rep_pair(&mkfs(fa, sa)), rep_pair(&mkfs(fb, sb)));
    let (cf1, cs1) = (fst_nn(&rp), snd_nn(&rp)); // F1, S1
    let (cf2, cs2) = (fst_nn(&rq), snd_nn(&rq)); // F2, S2
    // r1: fa + S1 = F1 + sa ; r2: fb + S2 = F2 + sb  (round_trip + projections).
    let r1 = reduce_rel(round_trip(&pair_nn(fa.clone(), sa.clone()))?)?
        .rewrite(&crate::init::prod::fst_pair(&n, &n, fa, sa)?)?
        .rewrite(&crate::init::prod::snd_pair(&n, &n, fa, sa)?)?;
    let r2 = reduce_rel(round_trip(&pair_nn(fb.clone(), sb.clone()))?)?
        .rewrite(&crate::init::prod::fst_pair(&n, &n, fb, sb)?)?
        .rewrite(&crate::init::prod::snd_pair(&n, &n, fb, sb)?)?;
    // S2 + fb = fb + S2 = F2 + sb = sb + F2.
    let s2_fb = nat::add_comm()
        .all_elim(cs2.clone())?
        .all_elim(fb.clone())?
        .trans(r2)?
        .trans(
            nat::add_comm()
                .all_elim(cf2.clone())?
                .all_elim(sb.clone())?,
        )?;
    // (F1+S2)+(fb+sa) = (F1+sa)+(S2+fb) = (fa+S1)+(sb+F2) = (fa+sb)+(F2+S1).
    elim4(nat::add_interchange(), &cf1, &cs2, fb, sa)?
        .trans(nat::cong_add(r1.sym()?, s2_fb)?)?
        .trans(elim4(nat::add_interchange(), fa, sb, &cf2, &cs1)?.sym()?)
}

/// **Strict comparison computation rule.** `⊢ int.lt (MK fa sa)(MK fb sb) =
/// nat.lt (fa+sb)(fb+sa)`.
fn lt_mk(fa: &Term, sa: &Term, fb: &Term, sb: &Term) -> Result<Thm> {
    let de = lt_defining_eq(&mkfs(fa, sa), &mkfs(fb, sb))?;
    let (rp, rq) = (rep_pair(&mkfs(fa, sa)), rep_pair(&mkfs(fb, sb)));
    let (cf1, cs1) = (fst_nn(&rp), snd_nn(&rp));
    let (cf2, cs2) = (fst_nn(&rq), snd_nn(&rq));
    let well = nat::lt_cross()
        .all_elim(nat::add(cf1, cs2))?
        .all_elim(nat::add(cf2, cs1))?
        .all_elim(nat::add(fa.clone(), sb.clone()))?
        .all_elim(nat::add(fb.clone(), sa.clone()))?
        .imp_elim(cmp_cross_eq(fa, sa, fb, sb)?)?;
    de.trans(well)
}

/// **Non-strict comparison computation rule.** `⊢ int.le (MK fa sa)(MK fb
/// sb) = nat.le (fa+sb)(fb+sa)`.
fn le_mk(fa: &Term, sa: &Term, fb: &Term, sb: &Term) -> Result<Thm> {
    let de = le_defining_eq(&mkfs(fa, sa), &mkfs(fb, sb))?;
    let (rp, rq) = (rep_pair(&mkfs(fa, sa)), rep_pair(&mkfs(fb, sb)));
    let (cf1, cs1) = (fst_nn(&rp), snd_nn(&rp));
    let (cf2, cs2) = (fst_nn(&rq), snd_nn(&rq));
    let well = nat::le_cross()
        .all_elim(nat::add(cf1, cs2))?
        .all_elim(nat::add(cf2, cs1))?
        .all_elim(nat::add(fa.clone(), sb.clone()))?
        .all_elim(nat::add(fb.clone(), sa.clone()))?
        .imp_elim(cmp_cross_eq(fa, sa, fb, sb)?)?;
    de.trans(well)
}

/// `⊢ int.lt a b = nat.lt (fa+sb)(fb+sa)`, where `ra : a = MK fa sa`,
/// `rb : b = MK fb sb`.
fn lt_via_components(ra: &Thm, rb: &Thm) -> Result<Thm> {
    let (fa, sa) = mk_components(&dest_eq(ra)?.1)?;
    let (fb, sb) = mk_components(&dest_eq(rb)?.1)?;
    Thm::refl(int_lt())?
        .cong_app(ra.clone())?
        .cong_app(rb.clone())?
        .trans(lt_mk(&fa, &sa, &fb, &sb)?)
}
/// `⊢ int.le a b = nat.le (fa+sb)(fb+sa)` — the `≤` mirror.
fn le_via_components(ra: &Thm, rb: &Thm) -> Result<Thm> {
    let (fa, sa) = mk_components(&dest_eq(ra)?.1)?;
    let (fb, sb) = mk_components(&dest_eq(rb)?.1)?;
    Thm::refl(int_le())?
        .cong_app(ra.clone())?
        .cong_app(rb.clone())?
        .trans(le_mk(&fa, &sa, &fb, &sb)?)
}

/// `⊢ (a = b) = (fst(rep a)+snd(rep b) = fst(rep b)+snd(rep a))` — `int`
/// equality is the Grothendieck relation on representatives. Forward by
/// congruence; backward by `class_intro` + `recon`.
fn int_eq_iff(a: &Term, b: &Term) -> Result<Thm> {
    let (fa, sa, fb, sb) = (fcomp(a), scomp(a), fcomp(b), scomp(b));
    let nat_eq = nat::add(fa.clone(), sb.clone()).equals(nat::add(fb.clone(), sa.clone()))?; // X = Y
    let int_eq = a.clone().equals(b.clone())?;
    // forward: {a = b} ⊢ X = Y.
    let fwd = {
        let rp_eq = rep_pair(a).rw_all(&Thm::assume(int_eq.clone())?)?; // rep a = rep b
        let n = (Type::nat(), Type::nat());
        nat::cong_add(
            rp_eq.clone().cong_arg(fst(n.0.clone(), n.1.clone()))?, // fst(rep a) = fst(rep b)
            rp_eq.cong_arg(snd(n.0, n.1))?.sym()?,                  // snd(rep b) = snd(rep a)
        )?
    };
    // backward: {X = Y} ⊢ a = b.
    let bwd = {
        let rel = expand_rel(
            Thm::assume(nat_eq.clone())?,
            &rel_app(&rep_pair(a), &rep_pair(b)),
        )?; // int_rel (rep a)(rep b)
        let classes =
            quotient::class_intro(&spec(), &[], &nn(), &int_rel_symm(), &int_rel_trans(), rel)?;
        recon(a)?.trans(classes)?.trans(recon(b)?.sym()?)? // a = b
    };
    bwd.deduct_antisym(fwd) // ⊢ (a = b) = (X = Y)
}

// ============================================================================
// Linear order
// ============================================================================

cached_thm! {
    /// `⊢ ∀a. ¬(a < a)` — **proved**. `int.lt a a = nat.lt N N` (`N = fa+sa`)
    /// and `nat::lt_irrefl`.
    pub fn lt_irrefl() -> Result<Thm> {
        let a = var("a");
        let ra = recon_mk(&a)?;
        let (fa, sa) = (fcomp(&a), scomp(&a));
        let de = lt_via_components(&ra, &ra)?; // int.lt a a = nat.lt(fa+sa)(fa+sa)
        nat::lt_irrefl()
            .all_elim(nat::add(fa, sa))?
            .rewrite(&de.sym()?)? // ¬(int.lt a a)
            .all_intro("a", int())
    }
}

cached_thm! {
    /// `⊢ ∀a b c. a < b ⟹ b < c ⟹ a < c` — **proved**. Add the two
    /// representative inequalities, re-pair, and cancel the common summand.
    pub fn lt_trans() -> Result<Thm> {
        let (a, b, c) = (var("a"), var("b"), var("c"));
        let (ra, rb, rc) = (recon_mk(&a)?, recon_mk(&b)?, recon_mk(&c)?);
        let (fa, sa) = (fcomp(&a), scomp(&a));
        let (fb, sb) = (fcomp(&b), scomp(&b));
        let (fc, sc) = (fcomp(&c), scomp(&c));
        let (hab, hbc) = (lt(a.clone(), b.clone()), lt(b.clone(), c.clone()));

        let e1 = lt_via_components(&ra, &rb)?.eq_mp(Thm::assume(hab.clone())?)?; // (fa+sb)<(fb+sa)
        let e2 = lt_via_components(&rb, &rc)?.eq_mp(Thm::assume(hbc.clone())?)?; // (fb+sc)<(fc+sb)
        let summed = nat::add_lt_add()
            .all_elim(nat::add(fa.clone(), sb.clone()))?
            .all_elim(nat::add(fb.clone(), sa.clone()))?
            .all_elim(nat::add(fb.clone(), sc.clone()))?
            .all_elim(nat::add(fc.clone(), sb.clone()))?
            .imp_elim(e1)?
            .imp_elim(e2)?; // (fa+sb)+(fb+sc) < (fb+sa)+(fc+sb)

        // (fa+sb)+(fb+sc) = (fa+sc)+(fb+sb).
        let eq_l = elim4(nat::add_interchange(), &fa, &sb, &fb, &sc)?.trans(cong_add_r(
            &nat::add(fa.clone(), sc.clone()),
            nat::add_comm().all_elim(sb.clone())?.all_elim(fb.clone())?,
        )?)?;
        // (fb+sa)+(fc+sb) = (fc+sa)+(fb+sb).
        let eq_r = elim4(nat::add_interchange(), &fb, &sa, &fc, &sb)?
            .trans(nat::add_comm().all_elim(nat::add(fb.clone(), sb.clone()))?.all_elim(nat::add(sa.clone(), fc.clone()))?)?
            .trans(nat::cong_add(
                nat::add_comm().all_elim(sa.clone())?.all_elim(fc.clone())?,
                Thm::refl(nat::add(fb.clone(), sb.clone()))?,
            )?)?;
        let shifted = Thm::refl(nat::nat_lt())?
            .cong_app(eq_l)?
            .cong_app(eq_r)?
            .eq_mp(summed)?; // (fa+sc)+K < (fc+sa)+K,  K = fb+sb
        let nat_ac = nat::lt_add_mono_r()
            .all_elim(nat::add(fa.clone(), sc.clone()))?
            .all_elim(nat::add(fc.clone(), sa.clone()))?
            .all_elim(nat::add(fb.clone(), sb.clone()))?
            .eq_mp(shifted)?; // (fa+sc) < (fc+sa)
        lt_via_components(&ra, &rc)?
            .sym()?
            .eq_mp(nat_ac)? // int.lt a c
            .imp_intro(&hbc)?
            .imp_intro(&hab)?
            .all_intro("c", int())?
            .all_intro("b", int())?
            .all_intro("a", int())
    }
}

cached_thm! {
    /// `⊢ ∀a b. (a < b) ∨ ((a = b) ∨ (b < a))` — **proved** from
    /// `nat::lt_trichotomy` on `(fa+sb, fb+sa)`, mapping each disjunct back.
    pub fn lt_trichotomy() -> Result<Thm> {
        let (a, b) = (var("a"), var("b"));
        let (ra, rb) = (recon_mk(&a)?, recon_mk(&b)?);
        let (fa, sa) = (fcomp(&a), scomp(&a));
        let (fb, sb) = (fcomp(&b), scomp(&b));
        let ntri = nat::lt_trichotomy()
            .all_elim(nat::add(fa.clone(), sb.clone()))?
            .all_elim(nat::add(fb.clone(), sa.clone()))?; // (X<Y) ∨ ((X=Y) ∨ (Y<X))
        let dab = lt_via_components(&ra, &rb)?; // int.lt a b = (X<Y)
        let dba = lt_via_components(&rb, &ra)?; // int.lt b a = (Y<X)
        let eqab = int_eq_iff(&a, &b)?; // (a=b) = (X=Y)
        ntri
            .rewrite(&dab.sym()?)?
            .rewrite(&eqab.sym()?)?
            .rewrite(&dba.sym()?)? // (a<b) ∨ ((a=b) ∨ (b<a))
            .all_intro("b", int())?
            .all_intro("a", int())
    }
}

cached_thm! {
    /// `⊢ ∀a b. (a ≤ b) = (a < b ∨ a = b)` — **proved** from
    /// `nat::le_iff_lt_or_eq`, mapping `X<Y ↦ a<b` and `X=Y ↦ a=b`.
    pub fn le_def() -> Result<Thm> {
        let (a, b) = (var("a"), var("b"));
        let (ra, rb) = (recon_mk(&a)?, recon_mk(&b)?);
        let (fa, sa) = (fcomp(&a), scomp(&a));
        let (fb, sb) = (fcomp(&b), scomp(&b));
        let chain = le_via_components(&ra, &rb)?.trans(
            nat::le_iff_lt_or_eq()
                .all_elim(nat::add(fa.clone(), sb.clone()))?
                .all_elim(nat::add(fb.clone(), sa.clone()))?,
        )?; // (a≤b) = (X<Y ∨ X=Y)
        let dlt = lt_via_components(&ra, &rb)?;
        let eqab = int_eq_iff(&a, &b)?;
        chain
            .rewrite(&dlt.sym()?)?
            .rewrite(&eqab.sym()?)? // (a≤b) = (a<b ∨ a=b)
            .all_intro("b", int())?
            .all_intro("a", int())
    }
}

// ============================================================================
// Ordered-ring compatibility
// ============================================================================

cached_thm! {
    /// `⊢ ∀a b c. a < b ⟹ a + c < b + c` — **proved**. `int.lt (a+c)(b+c)`
    /// reads off `(fa+fc)+(sb+sc) ⋚ …`, which is `(fa+sb) ⋚ (fb+sa)` shifted
    /// by `fc+sc` (`nat::lt_add_mono_r`).
    pub fn lt_add_mono() -> Result<Thm> {
        let (a, b, c) = (var("a"), var("b"), var("c"));
        let (ra, rb, rc) = (recon_mk(&a)?, recon_mk(&b)?, recon_mk(&c)?);
        let (fa, sa) = (fcomp(&a), scomp(&a));
        let (fb, sb) = (fcomp(&b), scomp(&b));
        let (fc, sc) = (fcomp(&c), scomp(&c));
        let h = lt(a.clone(), b.clone());

        let rac = add_via_components(&ra, &rc)?; // a+c = MK(fa+fc)(sa+sc)
        let rbc = add_via_components(&rb, &rc)?; // b+c = MK(fb+fc)(sb+sc)
        let dconcl = lt_via_components(&rac, &rbc)?; // int.lt(a+c)(b+c) = nat.lt(P)(Q)
        let xy = lt_via_components(&ra, &rb)?.eq_mp(Thm::assume(h.clone())?)?; // (fa+sb)<(fb+sa)
        let xyk = nat::lt_add_mono_r()
            .all_elim(nat::add(fa.clone(), sb.clone()))?
            .all_elim(nat::add(fb.clone(), sa.clone()))?
            .all_elim(nat::add(fc.clone(), sc.clone()))?
            .sym()?
            .eq_mp(xy)?; // (fa+sb)+(fc+sc) < (fb+sa)+(fc+sc)
        let eq_p = mid_swap(&fa, &fc, &sb, &sc)?; // (fa+fc)+(sb+sc) = (fa+sb)+(fc+sc)
        let eq_q = mid_swap(&fb, &fc, &sa, &sc)?; // (fb+fc)+(sa+sc) = (fb+sa)+(fc+sc)
        let pq = Thm::refl(nat::nat_lt())?
            .cong_app(eq_p.sym()?)?
            .cong_app(eq_q.sym()?)?
            .eq_mp(xyk)?; // nat.lt(P)(Q)
        dconcl
            .sym()?
            .eq_mp(pq)? // int.lt(a+c)(b+c)
            .imp_intro(&h)?
            .all_intro("c", int())?
            .all_intro("b", int())?
            .all_intro("a", int())
    }
}

cached_thm! {
    /// `⊢ ∀a b c. 0 < c ⟹ a < b ⟹ a * c < b * c` — **proved**. Writing
    /// `0 < c` as `fc = sc + m` (`0 < m`), each Grothendieck product
    /// comparison decomposes as `D + (fa+sb)·m` / `D + (fb+sa)·m` over the
    /// **same** `D` (`nat::prove_add_eq` does the shuffle), so the goal is
    /// `(fa+sb)·m < (fb+sa)·m` by `nat::lt_mul_mono_r`.
    pub fn lt_mul_pos() -> Result<Thm> {
        let (a, b, c) = (var("a"), var("b"), var("c"));
        let (ra, rb, rc) = (recon_mk(&a)?, recon_mk(&b)?, recon_mk(&c)?);
        let (fa, sa) = (fcomp(&a), scomp(&a));
        let (fb, sb) = (fcomp(&b), scomp(&b));
        let (fc, sc) = (fcomp(&c), scomp(&c));
        let m_ = |u: &Term, v: &Term| nat::mul(u.clone(), v.clone());
        let (hc, hab) = (lt(lit(0), c.clone()), lt(a.clone(), b.clone()));

        let rac = mul_via_components(&ra, &rc)?; // a·c = MK(fa·fc+sa·sc)(fa·sc+sa·fc)
        let rbc = mul_via_components(&rb, &rc)?;
        let dconcl = lt_via_components(&rac, &rbc)?; // int.lt(a·c)(b·c) = nat.lt(P)(Q)
        let p = nat::add(
            nat::add(m_(&fa, &fc), m_(&sa, &sc)),
            nat::add(m_(&fb, &sc), m_(&sb, &fc)),
        );
        let q = nat::add(
            nat::add(m_(&fb, &fc), m_(&sb, &sc)),
            nat::add(m_(&fa, &sc), m_(&sa, &fc)),
        );

        // positivity: 0 < c ⟹ sc < fc.
        let pos_c = lt_via_components(&lit0_mk()?, &rc)?
            .eq_mp(Thm::assume(hc.clone())?)? // {0<c} ⊢ nat.lt(0+sc)(fc+0)
            .rewrite(&nat::add_base().all_elim(sc.clone())?)?
            .rewrite(&nat::add_zero().all_elim(fc.clone())?)?; // {0<c} ⊢ sc < fc
        // fc = sc + m, m = S(fc − S sc), 0 < m.
        let ssc_le_fc = nat::lt_iff_succ_le()
            .all_elim(sc.clone())?
            .all_elim(fc.clone())?
            .eq_mp(pos_c)?; // {0<c} ⊢ S sc ≤ fc
        let mprime = nat::sub(fc.clone(), nat::succ(sc.clone()));
        let m = nat::succ(mprime.clone());
        let fc_eq = nat::add_succ_r()
            .all_elim(sc.clone())?
            .all_elim(mprime.clone())? // sc + S m' = S(sc+m')
            .trans(nat::add_step().all_elim(sc.clone())?.all_elim(mprime.clone())?.sym()?)? // = S sc + m'
            .trans(
                nat::le_add_sub()
                    .all_elim(nat::succ(sc.clone()))?
                    .all_elim(fc.clone())?
                    .imp_elim(ssc_le_fc)?,
            )?; // {0<c} ⊢ sc + m = fc
        let pos_m = nat::zero_lt_succ().all_elim(mprime.clone())?; // 0 < m

        // X = fa+sb, Y = fb+sa.
        let (xx, yy) = (nat::add(fa.clone(), sb.clone()), nat::add(fb.clone(), sa.clone()));
        let big_d = nat::add(
            nat::add(m_(&fa, &sc), m_(&sa, &sc)),
            nat::add(m_(&fb, &sc), m_(&sb, &sc)),
        );

        // P = D + (u+v)·m, with `(u,v) = (fa,sb)` for P and `(fb,sa)` for Q —
        // the two `_·(sc+m)` products in `lhs[fc→sc+m]` distribute and the six
        // leaves re-pair (via `prove_add_eq`) as `D + (u·m + v·m) = D + (u+v)·m`.
        let fc_sym = fc_eq.clone().sym()?; // {0<c} ⊢ fc = sc + m
        let decompose = |lhs: &Term, u: &Term, v: &Term| -> Result<Thm> {
            let e_sub = lhs.rw_all(&fc_sym)?; // lhs = lhs[fc→sc+m]
            let e_dist = rewrite_seq(
                &dest_eq(&e_sub)?.1,
                &[
                    elim3(nat::distrib(), u, &sc, &m)?,
                    elim3(nat::distrib(), v, &sc, &m)?,
                ],
            )?;
            let target = nat::add(big_d.clone(), nat::add(m_(u, &m), m_(v, &m)));
            let e_norm = nat::prove_add_eq(&dest_eq(&e_dist)?.1, &target)?; // l2 = D + (u·m + v·m)
            let e_fold = cong_add_r(&big_d, elim3(nat::distrib_r(), u, v, &m)?.sym()?)?; // = D + (u+v)·m
            e_sub.trans(e_dist)?.trans(e_norm)?.trans(e_fold)
        };
        let p_eq = decompose(&p, &fa, &sb)?; // {0<c} ⊢ P = D + X·m
        let q_eq = decompose(&q, &fb, &sa)?; // {0<c} ⊢ Q = D + Y·m

        // X·m < Y·m, hence D+X·m < D+Y·m.
        let xy = lt_via_components(&ra, &rb)?.eq_mp(Thm::assume(hab.clone())?)?; // {a<b} ⊢ X < Y
        let xm_lt_ym = nat::lt_mul_mono_r()
            .all_elim(xx.clone())?
            .all_elim(yy.clone())?
            .all_elim(m.clone())?
            .imp_elim(xy)?
            .imp_elim(pos_m)?; // {a<b} ⊢ X·m < Y·m
        let d_lt = nat::lt_add_mono_r()
            .all_elim(m_(&xx, &m))?
            .all_elim(m_(&yy, &m))?
            .all_elim(big_d.clone())?
            .sym()?
            .eq_mp(xm_lt_ym)? // X·m+D < Y·m+D
            .rewrite(&nat::add_comm().all_elim(m_(&xx, &m))?.all_elim(big_d.clone())?)? // D+X·m < Y·m+D
            .rewrite(&nat::add_comm().all_elim(m_(&yy, &m))?.all_elim(big_d.clone())?)?; // D+X·m < D+Y·m
        let pq = d_lt.rewrite(&p_eq.sym()?)?.rewrite(&q_eq.sym()?)?; // {a<b,0<c} ⊢ nat.lt(P)(Q)

        dconcl
            .sym()?
            .eq_mp(pq)? // int.lt(a·c)(b·c)
            .imp_intro(&hab)?
            .imp_intro(&hc)?
            .all_intro("c", int())?
            .all_intro("b", int())?
            .all_intro("a", int())
    }
}

// ============================================================================
// Integral-domain right-cancellation (and the `int.pos` positivity it feeds)
// ============================================================================
//
// `int_mul_rcancel` — `¬(d = 0) ⟹ x·d = y·d ⟹ x = y` — is what `init::rat`'s
// `rat_rel_trans` cancels the common positive denominator with. We **prove**
// it here from the proved order theory: trichotomy splits `x = y` off, and
// `lt_mul_pos` rules out the strict cases (for `d < 0` after flipping the sign
// with the small negation lemmas below). It lives here as a genuine theorem.

/// `⊢ ∀a. 0 + a = a` — left additive unit, from `add_zero` + `add_comm`.
fn add_left_zero() -> Result<Thm> {
    let a = var("a");
    add_comm()
        .all_elim(lit(0))?
        .all_elim(a.clone())? // 0 + a = a + 0
        .trans(add_zero().all_elim(a.clone())?)? // = a
        .all_intro("a", int())
}

cached_thm! {
    /// `⊢ ∀a b. a + b = 0 ⟹ b = -a` — uniqueness of the additive inverse.
    /// `b = 0+b = ((-a)+a)+b = (-a)+(a+b) = (-a)+0 = -a`.
    fn neg_unique() -> Result<Thm> {
        let (a, b) = (var("a"), var("b"));
        let h = add(a.clone(), b.clone()).equals(lit(0))?; // a + b = 0
        let na = neg(a.clone());
        // (-a)+a = 0: add_neg gives a+(-a)=0, commute.
        let na_a = add_comm()
            .all_elim(na.clone())?
            .all_elim(a.clone())?
            .trans(add_neg().all_elim(a.clone())?)?; // (-a)+a = 0
        let step1 = add_assoc()
            .all_elim(na.clone())?
            .all_elim(a.clone())?
            .all_elim(b.clone())?
            .sym()?; // (-a)+(a+b) = ((-a)+a)+b
        let step2 = na_a.cong_arg(int_add())?.cong_fn(b.clone())?; // ((-a)+a)+b = 0+b
        let step3 = add_left_zero()?.all_elim(b.clone())?; // 0+b = b
        let lhs_to_b = step1.trans(step2)?.trans(step3)?; // (-a)+(a+b) = b
        // Under hypothesis a+b=0: (-a)+(a+b) = (-a)+0 = -a.
        let cong_h = Thm::assume(h.clone())?.cong_arg(Term::app(int_add(), na.clone()))?; // (-a)+(a+b) = (-a)+0
        let to_na = cong_h.trans(add_zero().all_elim(na.clone())?)?; // (-a)+(a+b) = -a
        // b = (-a)+(a+b) = -a.
        let res = lhs_to_b.sym()?.trans(to_na)?; // {h} ⊢ b = -a
        res.imp_intro(&h)?
            .all_intro("b", int())?
            .all_intro("a", int())
    }
}

cached_thm! {
    /// `⊢ ∀x d. x·(-d) = -(x·d)` — multiplication distributes over negation
    /// on the right. `x·d + x·(-d) = x·(d+(-d)) = x·0 = 0`, so `x·(-d)` is the
    /// additive inverse of `x·d` ([`neg_unique`]).
    fn mul_neg_r() -> Result<Thm> {
        let (x, d) = (var("x"), var("d"));
        let xd = mul(x.clone(), d.clone());
        let xnd = mul(x.clone(), neg(d.clone()));
        // x·d + x·(-d) = x·(d + (-d)) = x·0 = 0.
        let sum0 = distrib()
            .all_elim(x.clone())?
            .all_elim(d.clone())?
            .all_elim(neg(d.clone()))?
            .sym()? // x·d + x·(-d) = x·(d+(-d))
            .trans(
                add_neg()
                    .all_elim(d.clone())? // d+(-d) = 0
                    .cong_arg(Term::app(int_mul(), x.clone()))?, // x·(d+(-d)) = x·0
            )?
            .trans(mul_zero().all_elim(x.clone())?)?; // = 0
        neg_unique()
            .all_elim(xd.clone())?
            .all_elim(xnd.clone())?
            .imp_elim(sum0)? // x·(-d) = -(x·d)
            .all_intro("d", int())?
            .all_intro("x", int())
    }
}

cached_thm! {
    /// `⊢ ∀d. d < 0 ⟹ 0 < -d` — negation reverses the strict order at 0.
    /// Add `-d` to both sides of `d < 0` ([`lt_add_mono`]) and simplify
    /// `d+(-d) = 0`, `0+(-d) = -d`.
    fn lt_neg_swap() -> Result<Thm> {
        let d = var("d");
        let h = lt(d.clone(), lit(0)); // d < 0
        let shifted = lt_add_mono()
            .all_elim(d.clone())?
            .all_elim(lit(0))?
            .all_elim(neg(d.clone()))?
            .imp_elim(Thm::assume(h.clone())?)?; // d+(-d) < 0+(-d)
        let res = shifted
            .rewrite(&add_neg().all_elim(d.clone())?)? // 0 < 0+(-d)
            .rewrite(&add_left_zero()?.all_elim(neg(d.clone()))?)?; // 0 < -d
        res.imp_intro(&h)?.all_intro("d", int())
    }
}

cached_thm! {
    /// `⊢ ∀x y d. 0 < d ⟹ x·d = y·d ⟹ x = y` — right-cancellation by a
    /// **positive** factor: by trichotomy on `x`/`y`, each strict case gives
    /// `x·d < y·d` (or the reverse) via [`lt_mul_pos`], contradicting
    /// `x·d = y·d` through [`lt_irrefl`].
    fn mul_rcancel_pos() -> Result<Thm> {
        let (x, y, d) = (var("x"), var("y"), var("d"));
        let hpos = lt(lit(0), d.clone()); // 0 < d
        let heq = mul(x.clone(), d.clone()).equals(mul(y.clone(), d.clone()))?; // x·d = y·d
        let goal = x.clone().equals(y.clone())?;

        // x < y ⟹ x·d < y·d ⟹ ⊥ (since x·d = y·d).
        let lt_xy = lt(x.clone(), y.clone());
        let br_lt = {
            let prod_lt = lt_mul_pos()
                .all_elim(x.clone())?
                .all_elim(y.clone())?
                .all_elim(d.clone())?
                .imp_elim(Thm::assume(hpos.clone())?)?
                .imp_elim(Thm::assume(lt_xy.clone())?)?; // x·d < y·d
            let xd_lt_xd = prod_lt.rewrite(&Thm::assume(heq.clone())?)?; // y·d < y·d
            lt_irrefl()
                .all_elim(mul(y.clone(), d.clone()))?
                .not_elim(xd_lt_xd)? // {hpos,heq,x<y} ⊢ ⊥
        };
        // y < x ⟹ y·d < x·d ⟹ ⊥ (rewrite x·d ↦ y·d).
        let lt_yx = lt(y.clone(), x.clone());
        let br_gt = {
            let prod_lt = lt_mul_pos()
                .all_elim(y.clone())?
                .all_elim(x.clone())?
                .all_elim(d.clone())?
                .imp_elim(Thm::assume(hpos.clone())?)?
                .imp_elim(Thm::assume(lt_yx.clone())?)?; // y·d < x·d
            let yd_lt_yd = prod_lt.rewrite(&Thm::assume(heq.clone())?)?; // y·d < y·d
            lt_irrefl()
                .all_elim(mul(y.clone(), d.clone()))?
                .not_elim(yd_lt_yd)? // {hpos,heq,y<x} ⊢ ⊥
        };
        // Trichotomy: (x<y) ∨ (x=y) ∨ (y<x).
        let tri = lt_trichotomy().all_elim(x.clone())?.all_elim(y.clone())?;
        // Right disjunct: (x=y) ∨ (y<x).
        let br_eq = {
            // x=y branch: trivial.
            let eq_branch = Thm::assume(goal.clone())?.imp_intro(&goal)?;
            // y<x branch: ex falso.
            let gt_branch = br_gt.false_elim(goal.clone())?.imp_intro(&lt_yx)?;
            let tail = tri
                .concl()
                .as_app()
                .ok_or_else(|| Error::ConnectiveRule("mul_rcancel_pos: ∨ shape".into()))?
                .1
                .clone(); // (x=y) ∨ (y<x)
            Thm::assume(tail.clone())?
                .or_elim(eq_branch, gt_branch)? // {tail} ⊢ x=y
                .imp_intro(&tail)?
        };
        let lt_branch = br_lt.false_elim(goal.clone())?.imp_intro(&lt_xy)?;
        let res = tri.or_elim(lt_branch, br_eq)?; // {hpos,heq} ⊢ x=y
        res.imp_intro(&heq)?
            .imp_intro(&hpos)?
            .all_intro("d", int())?
            .all_intro("y", int())?
            .all_intro("x", int())
    }
}

cached_thm! {
    /// `⊢ ∀a b. 0 < a ⟹ 0 < b ⟹ 0 < a + b` — a sum of positives is positive.
    /// `0 < a` and `lt_add_mono` (add `b`) give `0+b < a+b`; `0 < b` and
    /// `lt_trans` close it (`0 < b = 0+b < a+b`).
    pub fn add_pos() -> Result<Thm> {
        let (a, b) = (var("a"), var("b"));
        let ha = lt(lit(0), a.clone());
        let hb = lt(lit(0), b.clone());
        // 0 < a ⟹ 0+b < a+b.
        let mono = lt_add_mono()
            .all_elim(lit(0))?
            .all_elim(a.clone())?
            .all_elim(b.clone())?
            .imp_elim(Thm::assume(ha.clone())?)?; // 0+b < a+b
        let zb = mono.rewrite(&add_left_zero()?.all_elim(b.clone())?)?; // b < a+b
        lt_trans()
            .all_elim(lit(0))?
            .all_elim(b.clone())?
            .all_elim(add(a.clone(), b.clone()))?
            .imp_elim(Thm::assume(hb.clone())?)?
            .imp_elim(zb)? // 0 < a+b
            .imp_intro(&hb)?
            .imp_intro(&ha)?
            .all_intro("b", int())?
            .all_intro("a", int())
    }
}

cached_thm! {
    /// `⊢ ∀x y k. (x + k < y + k) = (x < y)` — adding a constant to both sides
    /// preserves and reflects the strict order. `⟸` is `lt_add_mono`; `⟹`
    /// re-adds `-k` and simplifies `(x+k)+(-k) = x`.
    pub fn lt_add_cancel_iff() -> Result<Thm> {
        let (x, y, k) = (var("x"), var("y"), var("k"));
        let lhs = lt(add(x.clone(), k.clone()), add(y.clone(), k.clone())); // x+k < y+k
        let rhs = lt(x.clone(), y.clone());
        // (u+k)+(-k) = u, for u = x and u = y.
        let simp = |u: &Term| -> Result<Thm> {
            add_assoc()
                .all_elim(u.clone())?
                .all_elim(k.clone())?
                .all_elim(neg(k.clone()))? // (u+k)+(-k) = u+(k+(-k))
                .trans(
                    add_neg()
                        .all_elim(k.clone())? // k+(-k) = 0
                        .cong_arg(Term::app(int_add(), u.clone()))?, // u+(k+(-k)) = u+0
                )?
                .trans(add_zero().all_elim(u.clone())?) // = u
        };
        // ⟸ : {x<y} ⊢ x+k < y+k.
        let bwd = lt_add_mono()
            .all_elim(x.clone())?
            .all_elim(y.clone())?
            .all_elim(k.clone())?
            .imp_elim(Thm::assume(rhs.clone())?)?; // {x<y} ⊢ x+k < y+k
        // ⟹ : {x+k<y+k} ⊢ x<y, by re-adding -k.
        let fwd = lt_add_mono()
            .all_elim(add(x.clone(), k.clone()))?
            .all_elim(add(y.clone(), k.clone()))?
            .all_elim(neg(k.clone()))?
            .imp_elim(Thm::assume(lhs.clone())?)? // (x+k)+(-k) < (y+k)+(-k)
            .rewrite(&simp(&x)?)?
            .rewrite(&simp(&y)?)?; // x < y
        bwd.deduct_antisym(fwd)? // {} ... actually both discharge their hyp
            .all_intro("k", int())?
            .all_intro("y", int())?
            .all_intro("x", int())
    }
}

cached_thm! {
    /// `⊢ ∀x y c. 0 < c ⟹ (x·c < y·c) = (x < y)` — strict order is preserved
    /// **and reflected** by multiplication by a positive: the `⟸` direction is
    /// [`lt_mul_pos`]; the `⟹` direction is its contrapositive through
    /// trichotomy (`x=y ⟹ x·c=y·c`, `y<x ⟹ y·c<x·c`, both excluding `x·c<y·c`).
    pub fn lt_mul_pos_iff() -> Result<Thm> {
        let (x, y, c) = (var("x"), var("y"), var("c"));
        let hpos = lt(lit(0), c.clone());
        let lhs = lt(mul(x.clone(), c.clone()), mul(y.clone(), c.clone())); // x·c < y·c
        let rhs = lt(x.clone(), y.clone()); // x < y

        // ⟸ : {0<c, x<y} ⊢ x·c<y·c (lt_mul_pos).
        let bwd = lt_mul_pos()
            .all_elim(x.clone())?
            .all_elim(y.clone())?
            .all_elim(c.clone())?
            .imp_elim(Thm::assume(hpos.clone())?)?
            .imp_elim(Thm::assume(rhs.clone())?)?; // {0<c, x<y} ⊢ x·c<y·c

        // ⟹ : x·c<y·c ⟹ x<y, by trichotomy on x,y.
        let tri = lt_trichotomy().all_elim(x.clone())?.all_elim(y.clone())?; // (x<y)∨(x=y)∨(y<x)
        // x=y ⟹ x·c<y·c is false (x·c=y·c, irrefl).
        let eq_xy = x.clone().equals(y.clone())?;
        let lt_yx = lt(y.clone(), x.clone());
        let br_eq = {
            // x·c = y·c by congruence under (·c); rewrite y·c ↦ x·c.
            let xc_yc = Thm::assume(eq_xy.clone())?
                .cong_arg(int_mul())? // (·) x = (·) y
                .cong_fn(c.clone())?; // x·c = y·c
            let contra = Thm::assume(lhs.clone())?.rewrite(&xc_yc.sym()?)?; // x·c < x·c
            lt_irrefl()
                .all_elim(mul(x.clone(), c.clone()))?
                .not_elim(contra)? // ⊥
                .false_elim(rhs.clone())?
                .imp_intro(&eq_xy)?
        };
        // y<x ⟹ y·c<x·c (lt_mul_pos), contradicting x·c<y·c (asymmetry via trans+irrefl).
        let br_gt = {
            let yc_lt_xc = lt_mul_pos()
                .all_elim(y.clone())?
                .all_elim(x.clone())?
                .all_elim(c.clone())?
                .imp_elim(Thm::assume(hpos.clone())?)?
                .imp_elim(Thm::assume(lt_yx.clone())?)?; // y·c < x·c
            // x·c<y·c and y·c<x·c ⟹ x·c<x·c (trans) ⟹ ⊥.
            let xx = lt_trans()
                .all_elim(mul(x.clone(), c.clone()))?
                .all_elim(mul(y.clone(), c.clone()))?
                .all_elim(mul(x.clone(), c.clone()))?
                .imp_elim(Thm::assume(lhs.clone())?)?
                .imp_elim(yc_lt_xc)?; // x·c < x·c
            lt_irrefl()
                .all_elim(mul(x.clone(), c.clone()))?
                .not_elim(xx)?
                .false_elim(rhs.clone())?
                .imp_intro(&lt_yx)?
        };
        let fwd = {
            // x<y branch: trivial.
            let lt_branch = Thm::assume(rhs.clone())?.imp_intro(&rhs)?;
            let tail = tri
                .concl()
                .as_app()
                .ok_or_else(|| Error::ConnectiveRule("lt_mul_pos_iff: ∨ shape".into()))?
                .1
                .clone(); // (x=y) ∨ (y<x)
            let tail_thm = Thm::assume(tail.clone())?
                .or_elim(br_eq, br_gt)?
                .imp_intro(&tail)?;
            tri.or_elim(lt_branch, tail_thm)? // {0<c, x·c<y·c} ⊢ x<y
        };

        // deduct_antisym: from {…,lhs} ⊢ rhs and {…,rhs} ⊢ lhs get ⊢ lhs=rhs
        // (the shared `0<c` hyp survives; `lhs`/`rhs` are discharged).
        let eq = bwd.deduct_antisym(fwd)?; // {0<c} ⊢ (x·c<y·c) = (x<y)
        eq.imp_intro(&hpos)?
            .all_intro("c", int())?
            .all_intro("y", int())?
            .all_intro("x", int())
    }
}

cached_thm! {
    /// `⊢ ∀x y d. ¬(d = 0) ⟹ x·d = y·d ⟹ x = y` — **proved** integral-domain
    /// right-cancellation. `¬(d=0)` + trichotomy gives `0 < d` or `d < 0`; the
    /// positive case is `mul_rcancel_pos`, the negative case flips `d ↦ -d`
    /// (`lt_neg_swap` + `mul_neg_r`) and cancels `x·(-d) = y·(-d)`.
    pub fn int_mul_rcancel() -> Result<Thm> {
        let (x, y, d) = (var("x"), var("y"), var("d"));
        let neq = d.clone().equals(lit(0))?.not()?; // ¬(d=0)
        let heq = mul(x.clone(), d.clone()).equals(mul(y.clone(), d.clone()))?;

        // From ¬(d=0), trichotomy d/0 collapses to (d<0) ∨ (0<d).
        let tri = lt_trichotomy().all_elim(d.clone())?.all_elim(lit(0))?; // (d<0) ∨ (d=0) ∨ (0<d)
        let dlt0 = lt(d.clone(), lit(0));
        let zltd = lt(lit(0), d.clone());
        let target = dlt0.clone().or(zltd.clone())?; // d<0 ∨ 0<d
        // Middle ∨ collapse: (d=0) branch contradicts ¬(d=0).
        let live = {
            let tail = tri
                .concl()
                .as_app()
                .ok_or_else(|| Error::ConnectiveRule("int_mul_rcancel: ∨ shape".into()))?
                .1
                .clone(); // (d=0) ∨ (0<d)
            let from_dlt0 =
                Thm::assume(dlt0.clone())?.or_intro_l(zltd.clone())?.imp_intro(&dlt0)?; // d<0 ⟹ target
            let from_tail = {
                let eq0 = d.clone().equals(lit(0))?;
                let from_eq0 = Thm::assume(neq.clone())?
                    .not_elim(Thm::assume(eq0.clone())?)? // {¬(d=0),d=0} ⊢ ⊥
                    .false_elim(target.clone())?
                    .imp_intro(&eq0)?;
                let from_zltd =
                    Thm::assume(zltd.clone())?.or_intro_r(dlt0.clone())?.imp_intro(&zltd)?;
                Thm::assume(tail.clone())?
                    .or_elim(from_eq0, from_zltd)?
                    .imp_intro(&tail)?
            };
            tri.or_elim(from_dlt0, from_tail)? // ⊢ (d<0 ∨ 0<d)
        };

        // 0<d branch: direct positive cancellation.
        let br_pos = mul_rcancel_pos()
            .all_elim(x.clone())?
            .all_elim(y.clone())?
            .all_elim(d.clone())?
            .imp_elim(Thm::assume(zltd.clone())?)?
            .imp_elim(Thm::assume(heq.clone())?)? // {0<d,heq} ⊢ x=y
            .imp_intro(&zltd)?;
        // d<0 branch: cancel by -d (which is >0).
        let br_neg = {
            let pos_nd = lt_neg_swap()
                .all_elim(d.clone())?
                .imp_elim(Thm::assume(dlt0.clone())?)?; // 0 < -d
            // x·(-d) = y·(-d): negate heq through mul_neg_r both sides.
            let xnd_eq = mul_neg_r().all_elim(x.clone())?.all_elim(d.clone())?; // x·(-d) = -(x·d)
            let ynd_eq = mul_neg_r().all_elim(y.clone())?.all_elim(d.clone())?; // y·(-d) = -(y·d)
            let neg_eq = Thm::assume(heq.clone())?.cong_arg(int_neg())?; // -(x·d) = -(y·d)
            let prod_eq = xnd_eq
                .trans(neg_eq)?
                .trans(ynd_eq.sym()?)?; // {heq} ⊢ x·(-d) = y·(-d)
            mul_rcancel_pos()
                .all_elim(x.clone())?
                .all_elim(y.clone())?
                .all_elim(neg(d.clone()))?
                .imp_elim(pos_nd)?
                .imp_elim(prod_eq)? // {dlt0,heq} ⊢ x=y
                .imp_intro(&dlt0)?
        };
        let res = live.or_elim(br_neg, br_pos)?; // {neq,heq} ⊢ x=y
        res.imp_intro(&heq)?
            .imp_intro(&neq)?
            .all_intro("d", int())?
            .all_intro("y", int())?
            .all_intro("x", int())
    }
}

cached_thm! {
    /// `⊢ ∀p:int.pos. 0 < rep p` — the carving predicate `0 < x` holds on the
    /// representative of every strictly-positive integer. From the kernel
    /// subtype laws: `abs(rep p) = p` ([`Thm::spec_abs_rep`]) feeds the
    /// witness-free back rule ([`Thm::spec_rep_abs_back`]) at `rep p`, whose
    /// `¬∃x. 0<x` escape disjunct is killed by the witness `1`.
    pub fn int_pos_pos() -> Result<Thm> {
        use covalence_hol_eval::defs::{int_pos_spec, int_pos_ty};
        let spec = int_pos_spec();
        let p = Term::free("p", int_pos_ty());
        let rep = Term::spec_rep(spec.clone(), Vec::<Type>::new());
        let rep_p = Term::app(rep.clone(), p.clone());

        // abs(rep p) = p, pushed under rep ⟹ rep(abs(rep p)) = rep p.
        let abs_rep = Thm::spec_abs_rep(spec.clone(), Vec::<Type>::new(), p.clone())?;
        let prem = abs_rep.cong_arg(rep.clone())?; // rep(abs(rep p)) = rep p
        let back = Thm::spec_rep_abs_back(spec.clone(), Vec::<Type>::new(), rep_p.clone())?
            .imp_elim(prem)?; // (P(rep p)) ∨ ¬(∃x. P x)

        // Peel the two disjuncts.
        let (p_rep_tm, notex) = {
            let (or_l, notex) = back
                .concl()
                .as_app()
                .ok_or_else(|| Error::ConnectiveRule("int_pos_pos: ∨ shape".into()))?;
            let (_or, l) = or_l
                .as_app()
                .ok_or_else(|| Error::ConnectiveRule("int_pos_pos: ∨ shape".into()))?;
            (l.clone(), notex.clone())
        };

        // ⊢ ∃x. (0 < x) — witness 1, against the exact predicate in `notex`.
        let exists_p = {
            let inner = notex
                .as_app()
                .ok_or_else(|| Error::ConnectiveRule("int_pos_pos: ¬∃ shape".into()))?
                .1; // exists_op (λx. 0<x)
            let pred = inner
                .as_app()
                .ok_or_else(|| Error::ConnectiveRule("int_pos_pos: ∃ shape".into()))?
                .1
                .clone(); // λx. 0<x
            let one_pos = lt_succ_zero_one()?; // ⊢ 0 < 1
            // `pred` is `λx. (λy. 0<y) x` (the image predicate is η-redundant),
            // so `pred 1` β-reduces in two steps to `0 < 1` (pure β — the
            // literal reducer would over-evaluate `0<1` to `T`).
            let beta1 = Thm::beta_conv(Term::app(pred.clone(), lit(1)))?; // pred 1 = (λy.0<y) 1
            let inner = beta1.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone();
            let beta2 = Thm::beta_conv(inner)?; // (λy.0<y) 1 = (0<1)
            let proof = beta1.trans(beta2)?.sym()?.eq_mp(one_pos)?; // ⊢ pred 1
            logic::exists_intro(pred, lit(1), proof)?
        };

        // ⊢ P(rep p) = (0 < rep p): left branch identity, right branch ex falso.
        let p_rep = {
            let left = Thm::assume(p_rep_tm.clone())?.imp_intro(&p_rep_tm)?;
            let right = Thm::assume(notex.clone())?
                .not_elim(exists_p)?
                .false_elim(p_rep_tm.clone())?
                .imp_intro(&notex)?;
            back.or_elim(left, right)? // ⊢ (λx. 0<x)(rep p)
        };
        p_rep_tm
            .reduce()? // P(rep p) = (0 < rep p)
            .eq_mp(p_rep)? // ⊢ 0 < rep p
            .all_intro("p", int_pos_ty())
    }
}

cached_thm! {
    /// `⊢ ∀p:int.pos. ¬(rep p = 0)` — positive denominators are nonzero.
    /// From [`int_pos_pos`] (`0 < rep p`): if `rep p = 0` then `0 < 0`,
    /// contradicting [`lt_irrefl`]. Relocated here from `init::rat`.
    pub fn int_pos_nonzero() -> Result<Thm> {
        use covalence_hol_eval::defs::int_pos_ty;
        let p = Term::free("p", int_pos_ty());
        let rep = Term::spec_rep(covalence_hol_eval::defs::int_pos_spec(), Vec::<Type>::new());
        let rep_p = Term::app(rep, p.clone());
        let pos = int_pos_pos().all_elim(p.clone())?; // 0 < rep p
        let eq0 = rep_p.clone().equals(lit(0))?; // rep p = 0
        // rep p = 0 ⟹ 0 < 0 (rewrite the RHS of `0 < rep p`).
        let zlt0 = pos.rewrite(&Thm::assume(eq0.clone())?)?; // {rep p = 0} ⊢ 0 < 0
        lt_irrefl()
            .all_elim(lit(0))?
            .not_elim(zlt0)? // {rep p = 0} ⊢ ⊥
            .imp_intro(&eq0)?
            .not_intro()? // ¬(rep p = 0)
            .all_intro("p", int_pos_ty())
    }
}

// ----------------------------------------------------------------------------
// Multiplicative AC normalisation — `⊢ lhs = rhs` for `·`-trees over the same
// leaf multiset (the int analogue of `nat::prove_add_eq`). Used by the rat
// order lift to rearrange cross-multiplication products.
// ----------------------------------------------------------------------------

/// Destructure `a · b` (an `int.mul` application) into `(a, b)`.
fn as_imul(t: &Term) -> Option<(Term, Term)> {
    let (mul_a, b) = t.as_app()?;
    let (m, a) = mul_a.as_app()?;
    if m == &int_mul() {
        Some((a.clone(), b.clone()))
    } else {
        None
    }
}

/// `⊢ a·b = a'·b'` from `⊢ a = a'`, `⊢ b = b'` (int product congruence).
fn icong_mul(ea: Thm, eb: Thm) -> Result<Thm> {
    Thm::refl(int_mul())?.cong_app(ea)?.cong_app(eb)
}
/// `⊢ left·x = left·y` from `⊢ x = y`.
fn icong_mul_r(left: &Term, eq: Thm) -> Result<Thm> {
    eq.cong_arg(Term::app(int_mul(), left.clone()))
}

/// `⊢ t = right-nested(t)` — re-associate a `·`-tree to the right.
fn imul_right_nest(t: &Term) -> Result<Thm> {
    if let Some((a, b)) = as_imul(t) {
        let ea = imul_right_nest(&a)?;
        let eb = imul_right_nest(&b)?;
        let (rna, rnb) = (
            ea.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone(),
            eb.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone(),
        );
        icong_mul(ea, eb)?.trans(imul_assoc_append(&rna, &rnb)?)
    } else {
        Thm::refl(t.clone())
    }
}

/// `⊢ (rn_a · rn_b) = right-nested(leaves rn_a ++ rn_b)` for right-nested `rn_a`.
fn imul_assoc_append(rn_a: &Term, rn_b: &Term) -> Result<Thm> {
    if let Some((x0, rest)) = as_imul(rn_a) {
        let assoc = mul_assoc()
            .all_elim(x0.clone())?
            .all_elim(rest.clone())?
            .all_elim(rn_b.clone())?; // (x0·rest)·rn_b = x0·(rest·rn_b)
        assoc.trans(icong_mul_r(&x0, imul_assoc_append(&rest, rn_b)?)?)
    } else {
        Thm::refl(mul(rn_a.clone(), rn_b.clone()))
    }
}

/// `⊢ a0·(x·r) = x·(a0·r)` — swap the first two of a right-nested product.
fn imul_swap_front2(a0: &Term, x: &Term, r: &Term) -> Result<Thm> {
    mul_assoc()
        .all_elim(a0.clone())?
        .all_elim(x.clone())?
        .all_elim(r.clone())?
        .sym()? // a0·(x·r) = (a0·x)·r
        .trans(
            mul_comm()
                .all_elim(a0.clone())?
                .all_elim(x.clone())? // a0·x = x·a0
                .cong_arg(int_mul())?
                .cong_fn(r.clone())?, // (a0·x)·r = (x·a0)·r
        )?
        .trans(
            mul_assoc()
                .all_elim(x.clone())?
                .all_elim(a0.clone())?
                .all_elim(r.clone())?,
        ) // = x·(a0·r)
}

/// `⊢ a = x · a'` — bring an occurrence of `x` to the front of right-nested `a`.
fn imul_bring_front(a: &Term, x: &Term) -> Result<Thm> {
    let (a0, a_rest) =
        as_imul(a).ok_or_else(|| Error::ConnectiveRule("imul_bring_front: leaf".into()))?;
    if a0 == *x {
        return Thm::refl(a.clone());
    }
    if as_imul(&a_rest).is_none() {
        return mul_comm().all_elim(a0)?.all_elim(a_rest); // a0·x = x·a0
    }
    let br = imul_bring_front(&a_rest, x)?; // a_rest = x · a_rest'
    let a_rest_p = as_imul(br.concl().as_eq().ok_or(Error::NotAnEquation)?.1)
        .ok_or_else(|| Error::ConnectiveRule("imul_bring_front: shape".into()))?
        .1;
    icong_mul_r(&a0, br)?.trans(imul_swap_front2(&a0, x, &a_rest_p)?)
}

/// `⊢ a = b` for right-nested `a`, `b` over the same leaf multiset.
fn imul_permute_eq(a: &Term, b: &Term) -> Result<Thm> {
    if a == b {
        return Thm::refl(a.clone());
    }
    let (b0, b_rest) =
        as_imul(b).ok_or_else(|| Error::ConnectiveRule("imul_permute_eq: leaf".into()))?;
    let bring = imul_bring_front(a, &b0)?; // a = b0 · a_rest
    let a_rest = as_imul(bring.concl().as_eq().ok_or(Error::NotAnEquation)?.1)
        .ok_or_else(|| Error::ConnectiveRule("imul_permute_eq: shape".into()))?
        .1;
    bring.trans(icong_mul_r(&b0, imul_permute_eq(&a_rest, &b_rest)?)?)
}

/// **Multiplicative normalisation.** `⊢ lhs = rhs` whenever `lhs`/`rhs` are
/// `·`-trees over the same multiset of `int` leaves (re-associate both right,
/// then permute). Errors if the leaf multisets differ.
pub fn prove_imul_eq(lhs: &Term, rhs_t: &Term) -> Result<Thm> {
    let el = imul_right_nest(lhs)?;
    let er = imul_right_nest(rhs_t)?;
    let (rl, rr) = (
        el.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone(),
        er.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone(),
    );
    let perm = imul_permute_eq(&rl, &rr)?;
    el.trans(perm)?.trans(er.sym()?)
}

// ----------------------------------------------------------------------------
// Instance-level convenience wrappers (used by `init::rat`'s mediant lift).
// ----------------------------------------------------------------------------

/// `⊢ a·(b+c) = a·b + a·c` — `distrib` specialised.
pub fn distrib_at(a: &Term, b: &Term, c: &Term) -> Result<Thm> {
    distrib()
        .all_elim(a.clone())?
        .all_elim(b.clone())?
        .all_elim(c.clone())
}

/// `⊢ (a+b)·c = a·c + b·c` — right distributivity (from `mul_comm` + `distrib`).
pub fn distrib_r_at(a: &Term, b: &Term, c: &Term) -> Result<Thm> {
    let comm = mul_comm()
        .all_elim(add(a.clone(), b.clone()))?
        .all_elim(c.clone())?; // (a+b)·c = c·(a+b)
    let dist = distrib_at(c, a, b)?; // c·(a+b) = c·a + c·b
    let ca = mul_comm().all_elim(c.clone())?.all_elim(a.clone())?; // c·a = a·c
    let cb = mul_comm().all_elim(c.clone())?.all_elim(b.clone())?; // c·b = b·c
    comm.trans(dist)?
        .trans(Thm::refl(int_add())?.cong_app(ca)?.cong_app(cb)?)
}

/// `⊢ (k+x < k+y) = (x < y)` — left-cancellation, from [`lt_add_cancel_iff`]
/// (`x+k<y+k`) commuted on both sides.
pub fn lt_add_cancel_left_at(k: &Term, x: &Term, y: &Term) -> Result<Thm> {
    let base = lt_add_cancel_iff()
        .all_elim(x.clone())?
        .all_elim(y.clone())?
        .all_elim(k.clone())?; // (x+k < y+k) = (x<y)
    // base LHS is `x+k < y+k`; rewrite `x+k ↦ k+x`, `y+k ↦ k+y`.
    let cx = add_comm().all_elim(x.clone())?.all_elim(k.clone())?; // x+k = k+x
    let cy = add_comm().all_elim(y.clone())?.all_elim(k.clone())?; // y+k = k+y
    base.lhs_conv(|t| rewrite_seq_int(t, &[cx, cy]))
}

/// `⊢ (x+k < y+k) = (x < y)` — right-cancellation ([`lt_add_cancel_iff`]).
pub fn lt_add_cancel_right_at(x: &Term, y: &Term, k: &Term) -> Result<Thm> {
    lt_add_cancel_iff()
        .all_elim(x.clone())?
        .all_elim(y.clone())?
        .all_elim(k.clone())
}

/// Apply each `eqs[i]` (`rw_all`) to the running RHS of an equation in turn.
fn rewrite_seq_int(t: &Term, eqs: &[Thm]) -> Result<Thm> {
    rewrite_seq_int_with(t, eqs, &mut ())
}

/// [`rewrite_seq_int`] routing every rewrite through a caller-supplied interner — share
/// one `cons` across a whole proof's rewrites.
fn rewrite_seq_int_with<C: covalence_core::term::TrustedCons + ?Sized>(
    t: &Term,
    eqs: &[Thm],
    cons: &mut C,
) -> Result<Thm> {
    let mut acc = Thm::refl(t.clone())?;
    for eq in eqs {
        let cur = acc.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone();
        acc = acc.trans(cur.rw_all_with(eq, cons)?)?;
    }
    Ok(acc)
}

/// `⊢ rep(abs z) = z` for an `int` value `z` with `pos : ⊢ 0 < z` — the
/// `int.pos` wrapper is faithful on positives ([`Thm::spec_rep_abs_fwd`]).
pub fn int_pos_round_trip_at(z: &Term, pos: Thm) -> Result<Thm> {
    use covalence_hol_eval::defs::int_pos_spec;
    let spec = int_pos_spec();
    let fwd = Thm::spec_rep_abs_fwd(spec, Vec::<Type>::new(), z.clone())?; // P z ⟹ rep(abs z) = z
    let prem = fwd
        .concl()
        .as_app()
        .ok_or_else(|| Error::ConnectiveRule("int_pos_round_trip_at: ⟹ shape".into()))?
        .0
        .as_app()
        .ok_or_else(|| Error::ConnectiveRule("int_pos_round_trip_at: ⟹ shape".into()))?
        .1
        .clone(); // (λx. 0<x) z
    let prem_thm = Thm::beta_conv(prem)?.sym()?.eq_mp(pos)?; // ⊢ P z
    fwd.imp_elim(prem_thm)
}

/// `⊢ 0 < 1` on `int` — the base positivity fact (the `int.pos` witness).
fn lt_succ_zero_one() -> Result<Thm> {
    // `int.lt 0 1` reduces to a `nat` comparison; let the literal reducer +
    // component machinery decide it.
    lt(lit(0), lit(1)).prove_true()
}

/// `⊢ ∀a. 0 · a = 0` — left zero, from `mul_zero` + `mul_comm`.
fn zero_mul() -> Result<Thm> {
    let a = var("a");
    mul_comm()
        .all_elim(lit(0))?
        .all_elim(a.clone())? // 0·a = a·0
        .trans(mul_zero().all_elim(a.clone())?)? // = 0
        .all_intro("a", int())
}

cached_thm! {
    /// `⊢ ∀a b:int.pos. 0 < rep a · rep b` — a product of strictly-positive
    /// integers is strictly positive. `lt_mul_pos` at `0 < rep a` scaled by
    /// the positive `rep b`, with `0 · rep b = 0`.
    pub fn int_pos_prod_pos() -> Result<Thm> {
        use covalence_hol_eval::defs::int_pos_ty;
        let (a, b) = (Term::free("a", int_pos_ty()), Term::free("b", int_pos_ty()));
        let rep = Term::spec_rep(covalence_hol_eval::defs::int_pos_spec(), Vec::<Type>::new());
        let (ra, rb) = (Term::app(rep.clone(), a.clone()), Term::app(rep, b.clone()));
        let pos_a = int_pos_pos().all_elim(a.clone())?; // 0 < rep a
        let pos_b = int_pos_pos().all_elim(b.clone())?; // 0 < rep b
        // 0 < rep a ⟹ (with 0 < rep b) ⟹ 0·rep b < rep a · rep b.
        let scaled = lt_mul_pos()
            .all_elim(lit(0))?
            .all_elim(ra.clone())?
            .all_elim(rb.clone())?
            .imp_elim(pos_b)?
            .imp_elim(pos_a)?; // 0·rep b < rep a · rep b
        scaled
            .rewrite(&zero_mul()?.all_elim(rb.clone())?)? // 0 < rep a · rep b
            .all_intro("b", int_pos_ty())?
            .all_intro("a", int_pos_ty())
    }
}

cached_thm! {
    /// `⊢ ∀a b:int.pos. rep(abs(rep a · rep b)) = rep a · rep b` — products of
    /// positive denominators round-trip through the `int.pos` wrapper, by the
    /// conditional carrier-side round-trip ([`Thm::spec_rep_abs_fwd`]) whose
    /// premise `0 < rep a · rep b` is [`int_pos_prod_pos`]. Relocated here from
    /// `init::rat` (`pos_prod_rt`).
    pub fn int_pos_prod_rt() -> Result<Thm> {
        use covalence_hol_eval::defs::{int_pos_spec, int_pos_ty};
        let spec = int_pos_spec();
        let (a, b) = (Term::free("a", int_pos_ty()), Term::free("b", int_pos_ty()));
        let rep = Term::spec_rep(spec.clone(), Vec::<Type>::new());
        let (ra, rb) = (Term::app(rep.clone(), a.clone()), Term::app(rep, b.clone()));
        let prod = mul(ra.clone(), rb.clone());
        // P(prod) = (λx. 0<x) prod — supply from int_pos_prod_pos via β.
        let fwd = Thm::spec_rep_abs_fwd(spec.clone(), Vec::<Type>::new(), prod.clone())?;
        let prem = fwd
            .concl()
            .as_app()
            .ok_or_else(|| Error::ConnectiveRule("int_pos_prod_rt: ⟹ shape".into()))?
            .0
            .as_app()
            .ok_or_else(|| Error::ConnectiveRule("int_pos_prod_rt: ⟹ shape".into()))?
            .1
            .clone(); // P prod = (λx. 0<x) prod
        let pos = int_pos_prod_pos().all_elim(a.clone())?.all_elim(b.clone())?; // 0 < prod
        let prem_thm = prem.reduce()?.sym()?.eq_mp(pos)?; // ⊢ P prod
        fwd.imp_elim(prem_thm)? // rep(abs prod) = prod
            .all_intro("b", int_pos_ty())?
            .all_intro("a", int_pos_ty())
    }
}

cached_thm! {
    /// `⊢ rep(abs 1) = 1` — the canonical denominator `1` round-trips through
    /// `int.pos`, by [`Thm::spec_rep_abs_fwd`] at `1` with premise `0 < 1`.
    /// Relocated here from `init::rat` (`one_pos_rt`).
    pub fn int_pos_one_rt() -> Result<Thm> {
        use covalence_hol_eval::defs::int_pos_spec;
        let spec = int_pos_spec();
        let fwd = Thm::spec_rep_abs_fwd(spec.clone(), Vec::<Type>::new(), lit(1))?;
        let prem = fwd
            .concl()
            .as_app()
            .ok_or_else(|| Error::ConnectiveRule("int_pos_one_rt: ⟹ shape".into()))?
            .0
            .as_app()
            .ok_or_else(|| Error::ConnectiveRule("int_pos_one_rt: ⟹ shape".into()))?
            .1
            .clone(); // P 1 = (λx. 0<x) 1
        // Pure β (the literal reducer would over-evaluate `0<1` to `T`).
        let prem_thm = Thm::beta_conv(prem)?.sym()?.eq_mp(lt_succ_zero_one()?)?; // ⊢ P 1
        fwd.imp_elim(prem_thm) // rep(abs 1) = 1
    }
}

// ============================================================================
// Discreteness — the integer-specific axiom
// ============================================================================

cached_thm! {
    /// `⊢ ∀a b. (a < b) = (a + 1 ≤ b)` — **proved**. Both unfold to a `nat`
    /// comparison on `X = fa+sb`, `Y = fb+sa`: `a<b ↦ X<Y` and `a+1≤b ↦
    /// S X ≤ Y`, bridged by `nat::lt_iff_succ_le`.
    pub fn lt_succ() -> Result<Thm> {
        let (a, b) = (var("a"), var("b"));
        let (ra, rb) = (recon_mk(&a)?, recon_mk(&b)?);
        let (fa, sa) = (fcomp(&a), scomp(&a));
        let (fb, sb) = (fcomp(&b), scomp(&b));
        let (x, y) = (nat::add(fa.clone(), sb.clone()), nat::add(fb.clone(), sa.clone()));

        let ra1 = add_via_components(&ra, &lit1_mk()?)?; // a+1 = MK(fa+1)(sa+0)
        let dle = le_via_components(&ra1, &rb)?; // int.le(a+1)b = nat.le((fa+1)+sb)(fb+(sa+0))
        let dlt = lt_via_components(&ra, &rb)?; // int.lt a b = nat.lt(X)(Y)
        let lisl = nat::lt_iff_succ_le()
            .all_elim(x.clone())?
            .all_elim(y.clone())?; // (X<Y) = (S X ≤ Y)

        // S X = (fa+1)+sb ; Y = fb+(sa+0).
        let sx_eq = nat::add_step()
            .all_elim(fa.clone())?
            .all_elim(sb.clone())?
            .sym()? // S(fa+sb) = S fa + sb
            .trans(
                Thm::refl(nat::nat_add())?
                    .cong_app(nat::add_one_succ(&fa)?.sym()?)? // S fa = fa+1
                    .cong_fn(sb.clone())?, // S fa + sb = (fa+1)+sb
            )?;
        let y_eq = cong_add_r(&fb, nat::add_zero().all_elim(sa.clone())?.sym()?)?; // fb+sa = fb+(sa+0)
        let bridge = Thm::refl(nat::nat_le())?
            .cong_app(sx_eq)?
            .cong_app(y_eq)?; // (S X ≤ Y) = ((fa+1)+sb ≤ fb+(sa+0))

        dlt.trans(lisl)?
            .trans(bridge)?
            .trans(dle.sym()?)? // (a<b) = (a+1 ≤ b)
            .all_intro("b", int())?
            .all_intro("a", int())
    }
}

// ============================================================================
// The `intprim` seam env — operators + component-layer givens for `int.cov`
// ============================================================================
//
// `int := (nat × nat) / ~`. The ring/order axioms are proved in Rust above
// through the quotient machinery (`recon` / `mk_int` / `add_class` / …). To
// re-prove them in `int.cov` *without* re-deriving the quotient, we expose the
// `MK(f, s)` component layer through three honest **operators** —
//
//   int.mk : nat → nat → int   (`MK(f, s) = mk_int (pair f s)`)
//   int.fc : int → nat         (`fst (rep_pair a)`)
//   int.sc : int → nat         (`snd (rep_pair a)`)
//
// — and a handful of `∀`-closed **seam lemmas** over them (reconstruction,
// per-op `*_mk` computation rules, the order `*_mk` rules, the `int.mk`
// equality criterion, literal coherence). These cross the abs/rep boundary
// via the quotient laws, so they stay Rust-proved givens (the `set.cov`
// `mem_*`/`ext` pattern); `int.cov` proves the ordered ring over them and the
// imported `nat` algebra, never mentioning `mk_int`/`rep_pair`/`abs`/`rep`.

/// `int.mk ≔ λf s. MK(f, s)` — the component constructor as a closed operator.
fn int_mk_op() -> Term {
    let (f, s) = (
        Term::free("__f", Type::nat()),
        Term::free("__s", Type::nat()),
    );
    let body = mkfs(&f, &s);
    let inner = Term::abs(Type::nat(), subst::close(&body, "__s"));
    Term::abs(Type::nat(), subst::close(&inner, "__f"))
}
/// `int.fc ≔ λa. fst (rep_pair a)` — the first-component destructor.
fn int_fc_op() -> Term {
    let a = Term::free("__a", int());
    Term::abs(int(), subst::close(&fcomp(&a), "__a"))
}
/// `int.sc ≔ λa. snd (rep_pair a)` — the second-component destructor.
fn int_sc_op() -> Term {
    let a = Term::free("__a", int());
    Term::abs(int(), subst::close(&scomp(&a), "__a"))
}

/// `int.mk f s` as an operator application (β-redex over [`int_mk_op`]).
fn mk_app(f: &Term, s: &Term) -> Term {
    Term::app(Term::app(int_mk_op(), f.clone()), s.clone())
}
/// `int.fc a` / `int.sc a` as operator applications.
fn fc_app(a: &Term) -> Term {
    Term::app(int_fc_op(), a.clone())
}
fn sc_app(a: &Term) -> Term {
    Term::app(int_sc_op(), a.clone())
}

/// `⊢ int.mk f s = MK(f, s)` — the two-step β reconciliation of the operator
/// application with the internal `mkfs` form. Lets the Rust `*_mk` lemmas
/// (phrased on `mkfs`) be restated on the operator.
fn mk_beta(f: &Term, s: &Term) -> Result<Thm> {
    // Two β-steps only (NOT full `reduce`, which would over-reduce the
    // un-reduced `int_rel` redex inside `mkfs`): outer app then inner app.
    let _ = mk_app(f, s); // the redex this proof reconciles
    let outer = Thm::beta_conv(Term::app(int_mk_op(), f.clone()))?; // (λf s. mkfs) f = λs. mkfs[f]
    let applied = outer.cong_fn(s.clone())?; // (… ) s = (λs. mkfs[f]) s
    let inner = Thm::beta_conv(dest_eq(&applied)?.1)?; // (λs. mkfs[f]) s = mkfs[f,s]
    applied.trans(inner)
}
/// `⊢ int.fc a = fst (rep_pair a)`.
fn fc_beta(a: &Term) -> Result<Thm> {
    Thm::beta_conv(fc_app(a))
}
/// `⊢ int.sc a = snd (rep_pair a)`.
fn sc_beta(a: &Term) -> Result<Thm> {
    Thm::beta_conv(sc_app(a))
}

/// Rewrite every internal `MK(·,·)` / `fst(rep_pair ·)` / `snd(rep_pair ·)`
/// occurrence in `thm` back to the operator forms `int.mk` / `int.fc` /
/// `int.sc`, for the listed component pairs `(f, s)` and ints `a`. The bridge
/// that turns a Rust component-layer theorem into an operator-form given.
fn to_ops(thm: Thm, mks: &[(&Term, &Term)], comps: &[&Term]) -> Result<Thm> {
    let mut t = thm;
    // `mkfs(·,·) ← int.mk · ·` FIRST (the `mk_beta` LHS components are still in
    // their internal `fst(rep_pair ·)` form here), then collapse those
    // components to `int.fc`/`int.sc`.
    for (f, s) in mks {
        t = t.rewrite(&mk_beta(f, s)?.sym()?)?;
    }
    for a in comps {
        // `fst(rep_pair a) ← int.fc a` and `snd(rep_pair a) ← int.sc a`.
        t = t.rewrite(&fc_beta(a)?.sym()?)?;
        t = t.rewrite(&sc_beta(a)?.sym()?)?;
    }
    Ok(t)
}

/// `⊢ (int.mk fa sa = int.mk fb sb) = (fa + sb = fb + sa)` — the `int.mk`
/// equality criterion (the Grothendieck relation on components). Forward by
/// [`class_eq_to_nat`], backward by [`rel_of_pairs`] + `class_intro`.
fn mk_eq_iff(fa: &Term, sa: &Term, fb: &Term, sb: &Term) -> Result<Thm> {
    let lhs = mkfs(fa, sa).equals(mkfs(fb, sb))?; // MK fa sa = MK fb sb
    let rhs = nat::add(fa.clone(), sb.clone()).equals(nat::add(fb.clone(), sa.clone()))?; // X = Y
    // forward: {MK = MK} ⊢ X = Y.
    let fwd = class_eq_to_nat(Thm::assume(lhs.clone())?, fa, sa, fb, sb)?;
    // backward: {X = Y} ⊢ MK = MK.
    let rel = rel_of_pairs(fa, sa, fb, sb, Thm::assume(rhs.clone())?)?;
    let bwd = quotient::class_intro(&spec(), &[], &nn(), &int_rel_symm(), &int_rel_trans(), rel)?;
    bwd.deduct_antisym(fwd) // ⊢ (MK = MK) = (X = Y)
}

/// The `∀`-closure helper: generalise a four-component lemma over
/// `fa sa fb sb : nat`.
fn gen4(thm: Thm) -> Result<Thm> {
    thm.all_intro("sb", Type::nat())?
        .all_intro("fb", Type::nat())?
        .all_intro("sa", Type::nat())?
        .all_intro("fa", Type::nat())
}

// ============================================================================
// The nat ↪ int bridge — `natToInt` order coherence + nonneg reconstruction
// ============================================================================
//
// S5 ordinal support (`notes/vibes/lisp/acl2-s5-design.md` §4): `int` `<`/`≤`
// is only proved a linear order, and no induction principle reaches `int`.
// These lemmas identify the nonnegative fragment with `nat` through
// `natToInt` so `nat` strong induction transports (the `nonneg_si_on` driver
// in `init/acl2/ordinal.rs`). They live here because they need the private
// quotient recon layer (`recon_mk` / `le_mk` / `lit0_mk` / `succ_mk`).

/// `natToInt n : int`.
fn n2i(n: Term) -> Term {
    Term::app(covalence_hol_eval::defs::nat_to_int(), n)
}

/// `⊢ natToInt t = natRec ⌜0⌝ (λ_:nat. intSucc) t` — δ-unfold `natToInt`
/// through `iter`, weakly β-reduced (a `natRec` application at a free
/// count is left intact).
fn n2i_unfold(t: &Term) -> Result<Thm> {
    let d1 = n2i(t.clone())
        .delta_all(covalence_hol_eval::defs::nat_to_int_spec().symbol())?
        .rhs_conv(|u| u.reduce())?;
    let cur = dest_eq(&d1)?.1;
    let d2 = cur
        .delta_all(covalence_hol_eval::defs::iter_spec().symbol())?
        .rhs_conv(|u| u.reduce())?;
    d1.trans(d2)
}

/// `⊢ ∀n. natToInt (S n) = intSucc (natToInt n)` — the recursion step,
/// through the `nat` recursion theorem at result type `int`
/// ([`crate::init::recursion::rec_holds_proof_at`]).
fn n2i_succ() -> Result<Thm> {
    let k = Term::free("k", Type::nat());
    let u = n2i_unfold(&nat::succ(k.clone()))?; // natToInt (S k) = natRec z f (S k)
    // Parse `natRec z f (S k)` for the exact `z` / `f` the unfold produced.
    let (_, rhs) = dest_eq(&u)?;
    let (zf, _sk) = rhs.as_app().ok_or(Error::NotAnEquation)?;
    let (z_hd, f) = zf.as_app().ok_or(Error::NotAnEquation)?;
    let (_, z) = z_hd.as_app().ok_or(Error::NotAnEquation)?;
    let re = crate::init::recursion::rec_holds_proof_at(&int())?
        .all_elim(z.clone())?
        .all_elim(f.clone())?
        .and_elim_r()?
        .all_elim(k.clone())? // natRec z f (S k) = f k (natRec z f k)
        .rhs_conv(|t| t.reduce())?; // = intSucc (natRec z f k)
    let fold = n2i_unfold(&k)?.sym()?; // natRec z f k = natToInt k
    u.trans(re)?
        .rhs_conv(|t| t.rw_all(&fold))?
        .all_intro("k", Type::nat())
}

cached_thm! {
    /// `⊢ ∀n. natToInt n = MK n 0` — `natToInt` in component form, by
    /// `nat` induction through [`lit0_mk`] / [`succ_mk`].
    pub(crate) fn n2i_mk() -> Result<Thm> {
        let motive = {
            let n = Term::free("n", Type::nat());
            let body = n2i(n.clone()).equals(mkfs(&n, &nat::zero()))?;
            Term::abs(Type::nat(), subst::close(&body, "n"))
        };
        // base: natToInt 0 = ⌜0⌝ (literal cert) = MK 0 0.
        let base = crate::init::eq::beta_expand(
            &motive,
            nat::zero(),
            n2i(nat::zero()).reduce()?.trans(lit0_mk()?)?,
        )?;
        // step: {motive k} ⊢ motive (S k).
        let step = {
            let k = Term::free("k", Type::nat());
            let ih_redex = Term::app(motive.clone(), k.clone());
            let ih = crate::init::eq::beta_reduce(Thm::assume(ih_redex.clone())?)?; // natToInt k = MK k 0
            let eq = n2i_succ()?
                .all_elim(k.clone())? // natToInt (S k) = intSucc (natToInt k)
                .rhs_conv(|t| t.rw_all(&ih))? // = intSucc (MK k 0)
                .trans(succ_mk(&k, &nat::zero())?)?; // = MK (S k) 0
            crate::init::eq::beta_expand(&motive, nat::succ(k), eq)?.imp_intro(&ih_redex)?
        };
        crate::init::ext::nat_induct(base, step)
    }
}

/// `⊢ natToInt n = MK n 0` at a fixed `n` — [`n2i_mk`] instantiated and
/// top-β-reduced (single contraction only: the `mk_int` class bodies must
/// stay in their unreduced `mk_class` shape for the component machinery).
fn n2i_mk_at(n: &Term) -> Result<Thm> {
    crate::init::eq::beta_reduce(n2i_mk().all_elim(n.clone())?)
}

/// `⊢ nat.le (0+0) (n+0) = nat.le 0 n`-style cleanup: rewrite `0 + x = x`
/// and `x + 0 = x` (both `nat`) inside a conclusion.
fn nat_add_units(thm: Thm, zero_plus: &Term, plus_zero: &Term) -> Result<Thm> {
    thm.rewrite(&nat::add_base().all_elim(zero_plus.clone())?)?
        .rewrite(&nat::add_zero().all_elim(plus_zero.clone())?)
}

cached_thm! {
    /// `⊢ ∀m n. intLt (natToInt m) (natToInt n) = natLt m n` — `natToInt`
    /// preserves **and reflects** the strict order (the two-way form; the
    /// design's `nat_to_int_lt` is its forward reading).
    pub(crate) fn n2i_lt_iff() -> Result<Thm> {
        let (m, n) = (Term::free("m", Type::nat()), Term::free("n", Type::nat()));
        let rm = n2i_mk_at(&m)?; // natToInt m = MK m 0
        let rn = n2i_mk_at(&n)?;
        let de = lt_via_components(&rm, &rn)?; // intLt (n2i m)(n2i n) = nat.lt (m+0)(n+0)
        let de = de
            .rewrite(&nat::add_zero().all_elim(m.clone())?)?
            .rewrite(&nat::add_zero().all_elim(n.clone())?)?; // = natLt m n
        de.all_intro("n", Type::nat())?.all_intro("m", Type::nat())
    }
}

cached_thm! {
    /// `⊢ ∀n:nat. intLe ⌜0⌝ (natToInt n)` — `natToInt` lands in the
    /// nonnegative fragment (design §4, lemma 1).
    pub fn nat_to_int_nonneg() -> Result<Thm> {
        let n = Term::free("n", Type::nat());
        let rn = n2i_mk_at(&n)?; // natToInt n = MK n 0
        let de = le_via_components(&lit0_mk()?, &rn)?; // (0 ≤ natToInt n) = nat.le (0+0)(n+0)
        let de = nat_add_units(de, &nat::zero(), &n)?; // = nat.le 0 n
        de.sym()?
            .eq_mp(nat::le_zero().all_elim(n.clone())?)? // 0 ≤ natToInt n
            .all_intro("n", Type::nat())
    }
}

cached_thm! {
    /// `⊢ ∀m n. natLt m n ⟹ intLt (natToInt m) (natToInt n)` — strict
    /// monotonicity (design §4, lemma 2; reflection is [`n2i_lt_iff`]'s
    /// other direction).
    pub fn nat_to_int_lt() -> Result<Thm> {
        let (m, n) = (Term::free("m", Type::nat()), Term::free("n", Type::nat()));
        let iff = n2i_lt_iff().all_elim(m.clone())?.all_elim(n.clone())?;
        let hyp = Term::app(Term::app(nat::nat_lt(), m.clone()), n.clone());
        iff.sym()?
            .eq_mp(Thm::assume(hyp.clone())?)?
            .imp_intro(&hyp)?
            .all_intro("n", Type::nat())?
            .all_intro("m", Type::nat())
    }
}

cached_thm! {
    /// `⊢ ∀i:int. ⌜0⌝ ≤ i ⟹ ∃n:nat. i = natToInt n` — every nonnegative
    /// `int` is a `nat` image (design §4, lemma 3): recon `i = MK fa sa`,
    /// unfold `0 ≤ i` to `sa ≤ fa` on representatives, and witness
    /// `n := fa - sa` through `nat::le_add_sub`.
    pub fn int_nonneg_nat() -> Result<Thm> {
        let a = var("a");
        let ra = recon_mk(&a)?; // a = MK fa sa
        let (fa, sa) = (fcomp(&a), scomp(&a));
        let hyp = le(lit(0), a.clone());
        // (0 ≤ a) = (sa ≤ fa) on components.
        let de = le_via_components(&lit0_mk()?, &ra)?; // = nat.le (0+sa)(fa+0)
        let de = nat_add_units(de, &sa, &fa)?; // = nat.le sa fa
        let hle = de.eq_mp(Thm::assume(hyp.clone())?)?; // {0≤a} ⊢ sa ≤ fa
        // Witness w := fa - sa;   fa + 0 = w + sa.
        let w = nat::sub(fa.clone(), sa.clone());
        let sw = nat::le_add_sub()
            .all_elim(sa.clone())?
            .all_elim(fa.clone())?
            .imp_elim(hle)?; // sa + (fa - sa) = fa
        let wsa = nat::add_comm()
            .all_elim(w.clone())?
            .all_elim(sa.clone())?
            .trans(sw)?; // w + sa = fa
        let g = nat::add_zero()
            .all_elim(fa.clone())?
            .trans(wsa.sym()?)?; // fa + 0 = w + sa
        let rel = rel_of_pairs(&fa, &sa, &w, &nat::zero(), g)?;
        let cls =
            quotient::class_intro(&spec(), &[], &nn(), &int_rel_symm(), &int_rel_trans(), rel)?;
        let eq = ra
            .trans(cls)? // a = MK w 0
            .trans(n2i_mk_at(&w)?.sym()?)?; // = natToInt w
        // ∃n. a = natToInt n.
        let pred = {
            let nv = Term::free("__nn", Type::nat());
            let body = a.clone().equals(n2i(nv.clone()))?;
            Term::abs(Type::nat(), subst::close(&body, "__nn"))
        };
        let applied = crate::init::eq::beta_expand(&pred, w.clone(), eq)?; // (λn. a = natToInt n) w
        logic::exists_intro(pred, w, applied)?
            .imp_intro(&hyp)?
            .all_intro("a", int())
    }
}

/// The `intprim` seam environment imported by `int.cov`: the `int` operators
/// (monomorphic — `int` is a ground type), the component constructor /
/// destructors, and the **seam** lemmas (reconstruction, the per-op `*_mk`
/// computation rules, the order `*_mk` rules, the `int.mk` equality criterion,
/// literal coherence) in `∀`-closed form. These cross the quotient boundary,
/// so they stay Rust-proved givens; `int.cov` proves the ordered ring over
/// them (plus the imported `nat` algebra) and never mentions the quotient.
///
/// All symbols are **bare** (`add`/`mk`/`fc`/`recon`/`add_mk`/…): `int.cov`
/// brings them in QUALIFIED via `(#use (#alias intprim int))` — so they read
/// as `int.add`/`int.mk`/`int.recon`/… in the proofs — and re-exports them the
/// same way via `(#provide (#alias intprim int))`, so a downstream `.cov` that
/// imports just `int` references `int.*` directly (no separate `intprim`).
pub fn int_env() -> crate::script::Env {
    use crate::script::{ConstDef, Env};
    let mut e = Env::empty();

    // -- operators (monomorphic; `int` is ground) -----------------------
    //
    // Bare names: `int.cov` brings them in QUALIFIED via
    // `(#use (#alias intprim int))` (so they read as `int.add`/`int.mk`/…
    // inside the proofs) AND re-exports them the same way via
    // `(#provide (#alias intprim int))`, so a downstream `.cov` that imports
    // just `int` references `int.*` directly — no separate `intprim` import.
    e.define_const("add", ConstDef::Op(int_add()));
    e.define_const("mul", ConstDef::Op(int_mul()));
    e.define_const("neg", ConstDef::Op(int_neg()));
    e.define_const("sub", ConstDef::Op(int_sub()));
    e.define_const("succ", ConstDef::Op(int_succ()));
    e.define_const("le", ConstDef::Op(int_le()));
    e.define_const("lt", ConstDef::Op(int_lt()));
    e.define_const("mk", ConstDef::Op(int_mk_op()));
    e.define_const("fc", ConstDef::Op(int_fc_op()));
    e.define_const("sc", ConstDef::Op(int_sc_op()));
    // literals (opaque kernel int leaves)
    e.define_const("0", ConstDef::Op(lit(0)));
    e.define_const("1", ConstDef::Op(lit(1)));

    // canonical free components / ints for the `∀`-closed givens.
    let natv = |n: &str| Term::free(n, Type::nat());
    let (fa, sa) = (natv("fa"), natv("sa"));
    let (fb, sb) = (natv("fb"), natv("sb"));
    let a = var("a");

    // recon : ⊢ ∀a. a = int.mk (int.fc a) (int.sc a)
    e.define_lemma(
        "recon",
        to_ops(recon_mk(&a).unwrap(), &[(&fcomp(&a), &scomp(&a))], &[&a])
            .unwrap()
            .all_intro("a", int())
            .unwrap(),
    );

    // add_mk : ⊢ ∀fa sa fb sb. int.add (mk fa sa)(mk fb sb) = mk (fa+fb)(sa+sb)
    e.define_lemma(
        "add.mk",
        gen4(
            to_ops(
                add_mk(&fa, &sa, &fb, &sb).unwrap(),
                &[
                    (&fa, &sa),
                    (&fb, &sb),
                    (
                        &nat::add(fa.clone(), fb.clone()),
                        &nat::add(sa.clone(), sb.clone()),
                    ),
                ],
                &[],
            )
            .unwrap(),
        )
        .unwrap(),
    );

    // mul_mk : ⊢ ∀…. int.mul (mk fa sa)(mk fb sb)
    //              = mk (fa·fb+sa·sb)(fa·sb+sa·fb)
    e.define_lemma(
        "mul.mk",
        gen4(
            to_ops(
                mul_mk(&fa, &sa, &fb, &sb).unwrap(),
                &[
                    (&fa, &sa),
                    (&fb, &sb),
                    (
                        &nat::add(
                            nat::mul(fa.clone(), fb.clone()),
                            nat::mul(sa.clone(), sb.clone()),
                        ),
                        &nat::add(
                            nat::mul(fa.clone(), sb.clone()),
                            nat::mul(sa.clone(), fb.clone()),
                        ),
                    ),
                ],
                &[],
            )
            .unwrap(),
        )
        .unwrap(),
    );

    // neg_mk : ⊢ ∀fa sa. int.neg (mk fa sa) = mk sa fa
    e.define_lemma(
        "neg.mk",
        to_ops(neg_mk(&fa, &sa).unwrap(), &[(&fa, &sa), (&sa, &fa)], &[])
            .unwrap()
            .all_intro("sa", Type::nat())
            .unwrap()
            .all_intro("fa", Type::nat())
            .unwrap(),
    );

    // sub_mk : ⊢ ∀…. int.sub (mk fa sa)(mk fb sb) = mk (fa+sb)(sa+fb)
    e.define_lemma(
        "sub.mk",
        gen4(
            to_ops(
                sub_mk(&fa, &sa, &fb, &sb).unwrap(),
                &[
                    (&fa, &sa),
                    (&fb, &sb),
                    (
                        &nat::add(fa.clone(), sb.clone()),
                        &nat::add(sa.clone(), fb.clone()),
                    ),
                ],
                &[],
            )
            .unwrap(),
        )
        .unwrap(),
    );

    // lt_mk : ⊢ ∀…. int.lt (mk fa sa)(mk fb sb) = nat.lt (fa+sb)(fb+sa)
    e.define_lemma(
        "lt.mk",
        gen4(
            to_ops(
                lt_mk(&fa, &sa, &fb, &sb).unwrap(),
                &[(&fa, &sa), (&fb, &sb)],
                &[],
            )
            .unwrap(),
        )
        .unwrap(),
    );

    // le_mk : ⊢ ∀…. int.le (mk fa sa)(mk fb sb) = nat.le (fa+sb)(fb+sa)
    e.define_lemma(
        "le.mk",
        gen4(
            to_ops(
                le_mk(&fa, &sa, &fb, &sb).unwrap(),
                &[(&fa, &sa), (&fb, &sb)],
                &[],
            )
            .unwrap(),
        )
        .unwrap(),
    );

    // mk_eq : ⊢ ∀…. (int.mk fa sa = int.mk fb sb) = (fa+sb = fb+sa)
    e.define_lemma(
        "mk.eq",
        gen4(
            to_ops(
                mk_eq_iff(&fa, &sa, &fb, &sb).unwrap(),
                &[(&fa, &sa), (&fb, &sb)],
                &[],
            )
            .unwrap(),
        )
        .unwrap(),
    );

    // lit0 : ⊢ int.0 = int.mk 0 0   ;   lit1 : ⊢ int.1 = int.mk 1 0
    e.define_lemma(
        "lit0",
        to_ops(lit0_mk().unwrap(), &[(&nat::zero(), &nat::zero())], &[]).unwrap(),
    );
    e.define_lemma(
        "lit1",
        to_ops(
            lit1_mk().unwrap(),
            &[(&covalence_hol_eval::mk_nat(1u64), &nat::zero())],
            &[],
        )
        .unwrap(),
    );

    e
}

crate::cov_theory! {
    /// `int` ordered-ring axioms ported to `int.cov`, over `core` + `logic` +
    /// the imported `nat` algebra + the `intprim` seam env. The seam env is
    /// re-exported through the `int` namespace (`#provide (#alias intprim int)`),
    /// so downstream `.cov` imports just `int` to reach `int.*`.
    pub mod cov from "int.cov" {
        import "core" = crate::script::Env::core();
        import "logic" = crate::init::logic::cov::env();
        import "nat" = crate::init::nat::cov::env();
        import "natrec" = crate::init::nat::natrec_env();
        import "intprim" = crate::init::int::int_env();
        "add.comm"      => pub fn add_comm_cov;
        "add.assoc"     => pub fn add_assoc_cov;
        "add.zero"      => pub fn add_zero_cov;
        "add.neg"       => pub fn add_neg_cov;
        "sub.def"       => pub fn sub_def_cov;
        "mul.comm"      => pub fn mul_comm_cov;
        "mul.one"       => pub fn mul_one_cov;
        "mul.zero"      => pub fn mul_zero_cov;
        "distrib"       => pub fn distrib_cov;
        "lt.irrefl"     => pub fn lt_irrefl_cov;
        "lt.trans"      => pub fn lt_trans_cov;
        "lt.trichotomy" => pub fn lt_trichotomy_cov;
        "le.def"        => pub fn le_def_cov;
        "lt.add_mono"   => pub fn lt_add_mono_cov;
        "lt.succ"       => pub fn lt_succ_cov;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// **S5 G2 №6 (the nat ↪ int bridge):** the three designed lemmas,
    /// closed with exact statements (`acl2-s5-design.md` §4).
    #[test]
    fn t_nat_int_bridge() {
        let (m, n) = (Term::free("m", Type::nat()), Term::free("n", Type::nat()));
        let a = var("a");

        // ⊢ ∀n. 0 ≤ natToInt n.
        let nonneg = nat_to_int_nonneg();
        assert!(nonneg.hyps().is_empty());
        let expected = le(lit(0), n2i(n.clone())).forall("n", Type::nat()).unwrap();
        assert_eq!(nonneg.concl(), &expected);

        // ⊢ ∀m n. natLt m n ⟹ intLt (natToInt m) (natToInt n).
        let mono = nat_to_int_lt();
        assert!(mono.hyps().is_empty());
        let natlt = Term::app(Term::app(nat::nat_lt(), m.clone()), n.clone());
        let expected = natlt
            .imp(lt(n2i(m.clone()), n2i(n.clone())))
            .unwrap()
            .forall("n", Type::nat())
            .unwrap()
            .forall("m", Type::nat())
            .unwrap();
        assert_eq!(mono.concl(), &expected);

        // ⊢ ∀a. 0 ≤ a ⟹ ∃n. a = natToInt n.
        let recon = int_nonneg_nat();
        assert!(recon.hyps().is_empty());
        let pred = {
            let nv = Term::free("__nn", Type::nat());
            let body = a.clone().equals(n2i(nv.clone())).unwrap();
            Term::abs(Type::nat(), subst::close(&body, "__nn"))
        };
        let ex = Term::app(covalence_hol_eval::defs::exists(Type::nat()), pred);
        let expected = le(lit(0), a.clone())
            .imp(ex)
            .unwrap()
            .forall("a", int())
            .unwrap();
        assert_eq!(recon.concl(), &expected);

        // The two-way order coherence (driver seam): exact statement.
        let iff = n2i_lt_iff();
        assert!(iff.hyps().is_empty());
        let natlt = Term::app(Term::app(nat::nat_lt(), m.clone()), n.clone());
        let expected = lt(n2i(m.clone()), n2i(n.clone()))
            .equals(natlt)
            .unwrap()
            .forall("n", Type::nat())
            .unwrap()
            .forall("m", Type::nat())
            .unwrap();
        assert_eq!(iff.concl(), &expected);
    }

    #[test]
    fn int_cov_matches_rust() {
        // Each ported `int.cov` ordered-ring axiom states exactly the Rust
        // conclusion (same checked theorem, two proofs) and is hypothesis-free.
        let pairs: [(Thm, Thm); 15] = [
            (cov::add_comm_cov(), add_comm()),
            (cov::mul_comm_cov(), mul_comm()),
            (cov::add_assoc_cov(), add_assoc()),
            (cov::add_zero_cov(), add_zero()),
            (cov::add_neg_cov(), add_neg()),
            (cov::sub_def_cov(), sub_def()),
            (cov::mul_one_cov(), mul_one()),
            (cov::mul_zero_cov(), mul_zero()),
            (cov::distrib_cov(), distrib()),
            (cov::lt_irrefl_cov(), lt_irrefl()),
            (cov::lt_trans_cov(), lt_trans()),
            (cov::lt_trichotomy_cov(), lt_trichotomy()),
            (cov::le_def_cov(), le_def()),
            (cov::lt_add_mono_cov(), lt_add_mono()),
            (cov::lt_succ_cov(), lt_succ()),
        ];
        for (c, r) in pairs {
            assert!(c.hyps().is_empty(), "ported int.cov axiom is genuine");
            assert_eq!(c.concl(), r.concl());
        }
    }

    #[test]
    fn the_whole_ordered_ring_is_proved() {
        // Every `int` ordered-ring axiom is now a genuine (hypothesis-free)
        // theorem — no `Thm::assume` postulates remain.
        let axioms = [
            add_comm(),
            add_assoc(),
            add_zero(),
            add_neg(),
            sub_def(),
            mul_comm(),
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
        ];
        for ax in axioms {
            assert!(ax.hyps().is_empty(), "an int ordered-ring axiom is genuine");
            assert!(ax.concl().type_of().unwrap().is_bool());
        }
    }

    #[test]
    fn lt_mul_pos_is_a_genuine_theorem() {
        let (a, b, c) = (var("a"), var("b"), var("c"));
        let thm = lt_mul_pos();
        assert!(
            thm.hyps().is_empty(),
            "int::lt_mul_pos is proved, not postulated"
        );
        let inst = elim3(thm, &a, &b, &c).unwrap();
        let expected = lt(lit(0), c.clone())
            .imp(
                lt(a.clone(), b.clone())
                    .imp(lt(mul(a, c.clone()), mul(b, c)))
                    .unwrap(),
            )
            .unwrap();
        assert_eq!(inst.concl(), &expected);
    }

    #[test]
    fn order_axioms_are_genuine() {
        let (a, b, c) = (var("a"), var("b"), var("c"));
        // lt_irrefl: ¬(a<a).
        assert_eq!(
            lt_irrefl().all_elim(a.clone()).unwrap().concl(),
            &lt(a.clone(), a.clone()).not().unwrap()
        );
        // lt_trans: a<b ⟹ b<c ⟹ a<c.
        let trans = lt_trans()
            .all_elim(a.clone())
            .unwrap()
            .all_elim(b.clone())
            .unwrap()
            .all_elim(c.clone())
            .unwrap();
        assert_eq!(
            trans.concl(),
            &lt(a.clone(), b.clone())
                .imp(
                    lt(b.clone(), c.clone())
                        .imp(lt(a.clone(), c.clone()))
                        .unwrap()
                )
                .unwrap()
        );
        // le_def: (a≤b) = (a<b ∨ a=b).
        let led = le_def()
            .all_elim(a.clone())
            .unwrap()
            .all_elim(b.clone())
            .unwrap();
        assert_eq!(
            led.concl(),
            &le(a.clone(), b.clone())
                .equals(
                    lt(a.clone(), b.clone())
                        .or(a.clone().equals(b.clone()).unwrap())
                        .unwrap()
                )
                .unwrap()
        );
        // lt_succ: (a<b) = (a+1 ≤ b).
        let lsucc = lt_succ()
            .all_elim(a.clone())
            .unwrap()
            .all_elim(b.clone())
            .unwrap();
        assert_eq!(
            lsucc.concl(),
            &lt(a.clone(), b.clone())
                .equals(le(add(a.clone(), lit(1)), b.clone()))
                .unwrap()
        );
        for t in [
            lt_irrefl(),
            lt_trans(),
            lt_trichotomy(),
            le_def(),
            lt_add_mono(),
            lt_succ(),
        ] {
            assert!(t.hyps().is_empty(), "int order facts are genuine");
            assert!(t.concl().type_of().unwrap().is_bool());
        }
    }

    #[test]
    fn integral_domain_cancellation_is_genuine() {
        use covalence_hol_eval::defs::int_pos_ty;
        // int_mul_rcancel: ∀x y d. ¬(d=0) ⟹ x·d = y·d ⟹ x=y.
        let (x, y, d) = (var("x"), var("y"), var("d"));
        let rc = int_mul_rcancel();
        assert!(rc.hyps().is_empty(), "int_mul_rcancel is proved");
        let inst = rc
            .all_elim(x.clone())
            .unwrap()
            .all_elim(y.clone())
            .unwrap()
            .all_elim(d.clone())
            .unwrap();
        let expected = d
            .clone()
            .equals(lit(0))
            .unwrap()
            .not()
            .unwrap()
            .imp(
                mul(x.clone(), d.clone())
                    .equals(mul(y.clone(), d.clone()))
                    .unwrap()
                    .imp(x.clone().equals(y.clone()).unwrap())
                    .unwrap(),
            )
            .unwrap();
        assert_eq!(inst.concl(), &expected);

        // int_pos_pos / int_pos_nonzero: ∀p:int.pos. 0 < rep p / ¬(rep p = 0).
        let p = Term::free("p", int_pos_ty());
        let rep = Term::spec_rep(covalence_hol_eval::defs::int_pos_spec(), Vec::<Type>::new());
        let rep_p = Term::app(rep, p.clone());
        let pos = int_pos_pos();
        assert!(pos.hyps().is_empty(), "int_pos_pos is proved");
        assert_eq!(
            pos.all_elim(p.clone()).unwrap().concl(),
            &lt(lit(0), rep_p.clone())
        );
        let nz = int_pos_nonzero();
        assert!(nz.hyps().is_empty(), "int_pos_nonzero is proved");
        assert_eq!(
            nz.all_elim(p.clone()).unwrap().concl(),
            &rep_p.equals(lit(0)).unwrap().not().unwrap()
        );
    }

    #[test]
    fn add_helpers_are_genuine() {
        let (a, b, k) = (var("a"), var("b"), var("k"));
        let ap = add_pos();
        assert!(ap.hyps().is_empty(), "add_pos is proved");
        assert_eq!(
            ap.all_elim(a.clone())
                .unwrap()
                .all_elim(b.clone())
                .unwrap()
                .concl(),
            &lt(lit(0), a.clone())
                .imp(
                    lt(lit(0), b.clone())
                        .imp(lt(lit(0), add(a.clone(), b.clone())))
                        .unwrap()
                )
                .unwrap()
        );
        let ci = lt_add_cancel_iff();
        assert!(ci.hyps().is_empty(), "lt_add_cancel_iff is proved");
        assert_eq!(
            ci.all_elim(a.clone())
                .unwrap()
                .all_elim(b.clone())
                .unwrap()
                .all_elim(k.clone())
                .unwrap()
                .concl(),
            &lt(add(a.clone(), k.clone()), add(b.clone(), k.clone()))
                .equals(lt(a, b))
                .unwrap()
        );
    }

    #[test]
    fn lt_mul_pos_iff_is_genuine() {
        let (x, y, c) = (var("x"), var("y"), var("c"));
        let t = lt_mul_pos_iff();
        assert!(t.hyps().is_empty(), "lt_mul_pos_iff is proved");
        let inst = t
            .all_elim(x.clone())
            .unwrap()
            .all_elim(y.clone())
            .unwrap()
            .all_elim(c.clone())
            .unwrap();
        let expected = lt(lit(0), c.clone())
            .imp(
                lt(mul(x.clone(), c.clone()), mul(y.clone(), c.clone()))
                    .equals(lt(x.clone(), y.clone()))
                    .unwrap(),
            )
            .unwrap();
        assert_eq!(inst.concl(), &expected);
    }

    #[test]
    fn int_pos_round_trips_are_genuine() {
        use covalence_hol_eval::defs::{int_pos_spec, int_pos_ty};
        // int_pos_one_rt: rep(abs 1) = 1.
        let one_rt = int_pos_one_rt();
        assert!(one_rt.hyps().is_empty(), "int_pos_one_rt is proved");
        let rep = Term::spec_rep(int_pos_spec(), Vec::<Type>::new());
        let abs = Term::spec_abs(int_pos_spec(), Vec::<Type>::new());
        assert_eq!(
            one_rt.concl(),
            &Term::app(rep.clone(), Term::app(abs.clone(), lit(1)))
                .equals(lit(1))
                .unwrap()
        );
        // int_pos_prod_rt: ∀a b. rep(abs(rep a · rep b)) = rep a · rep b.
        let prod_rt = int_pos_prod_rt();
        assert!(prod_rt.hyps().is_empty(), "int_pos_prod_rt is proved");
        let (a, b) = (Term::free("a", int_pos_ty()), Term::free("b", int_pos_ty()));
        let (ra, rb) = (
            Term::app(rep.clone(), a.clone()),
            Term::app(rep.clone(), b.clone()),
        );
        let prod = mul(ra, rb);
        assert_eq!(
            prod_rt.all_elim(a).unwrap().all_elim(b).unwrap().concl(),
            &Term::app(rep, Term::app(abs, prod.clone()))
                .equals(prod)
                .unwrap()
        );
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

        // mul_class: ⊢ int.mul (mk_int u)(mk_int v) = mk_int(mul_pair u v).
        let mc = mul_class(&u, &v).expect("mul_class (well-definedness)");
        assert!(mc.hyps().is_empty(), "mul_class is genuine");
        let (l, r) = mc.concl().as_eq().unwrap();
        assert_eq!(l, &mul(mk_int(&u), mk_int(&v)));
        assert_eq!(r, &mk_int(&mul_pair(&u, &v)));
    }

    #[test]
    fn add_comm_is_a_genuine_theorem() {
        let thm = add_comm();
        assert!(
            thm.hyps().is_empty(),
            "int::add.comm is proved, not postulated"
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
    fn distrib_is_a_genuine_theorem() {
        let thm = distrib();
        assert!(
            thm.hyps().is_empty(),
            "int::distrib is proved, not postulated"
        );
        let (a, b, c) = (var("a"), var("b"), var("c"));
        let inst = elim3(thm, &a, &b, &c).unwrap();
        let expected = mul(a.clone(), add(b.clone(), c.clone()))
            .equals(add(mul(a.clone(), b), mul(a, c)))
            .unwrap();
        assert_eq!(inst.concl(), &expected);
    }

    #[test]
    fn mul_assoc_is_a_genuine_theorem() {
        let thm = mul_assoc();
        assert!(
            thm.hyps().is_empty(),
            "int::mul.assoc is proved, not postulated"
        );
        let (a, b, c) = (var("a"), var("b"), var("c"));
        let inst = elim3(thm, &a, &b, &c).unwrap();
        let expected = mul(mul(a.clone(), b.clone()), c.clone())
            .equals(mul(a, mul(b, c)))
            .unwrap();
        assert_eq!(inst.concl(), &expected);
    }

    #[test]
    fn mul_unit_and_zero_are_genuine() {
        // mul_one: ∀a. a*1 = a ; mul_zero: ∀a. a*0 = 0.
        let a = var("a");
        let one = mul_one();
        assert!(one.hyps().is_empty(), "int::mul.one is proved");
        assert_eq!(
            one.all_elim(a.clone()).unwrap().concl(),
            &mul(a.clone(), lit(1)).equals(a.clone()).unwrap()
        );
        let z = mul_zero();
        assert!(z.hyps().is_empty(), "int::mul.zero is proved");
        assert_eq!(
            z.all_elim(a.clone()).unwrap().concl(),
            &mul(a, lit(0)).equals(lit(0)).unwrap()
        );
    }

    #[test]
    fn add_assoc_is_a_genuine_theorem() {
        let thm = add_assoc();
        assert!(
            thm.hyps().is_empty(),
            "int::add.assoc is proved, not postulated"
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
            "int::sub.def is proved, not postulated"
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
        assert!(z.hyps().is_empty(), "int::add.zero is proved");
        assert_eq!(
            z.all_elim(a.clone()).unwrap().concl(),
            &add(a.clone(), lit(0)).equals(a.clone()).unwrap()
        );
        let ninv = add_neg();
        assert!(ninv.hyps().is_empty(), "int::add.neg is proved");
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
            "int::mul.comm is proved, not postulated"
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
            .expect("specialize add.comm");
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
        assert!(inst.concl().as_eq().is_some(), "le.def body is `(≤) = (…)`");
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
        let spec = covalence_hol_eval::defs::int_ty_spec();
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
        let spec = covalence_hol_eval::defs::int_ty_spec();
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
