//! `real` theorems: the Dedekind-cut construction of the reals, built on
//! [`init::rat`](crate::init::rat).
//!
//! ## The construction
//!
//! `real := close rat ratLe` ([`real_spec`]) is the type of **upper
//! Dedekind cuts** — defined here in the shell, not the kernel catalogue
//! (see [`real_spec`] for why). A real is a non-empty subset of
//! `rat` that is upward-closed under `≤`. The carrier of the subtype is
//! the powerset `rat → bool`, and the selector predicate (the `close`
//! predicate, [`cut_pred`]) is
//!
//! ```text
//!     λS. (∀x y. ratLe x y ⟹ S x ⟹ S y) ∧ (∃x. S x)
//! ```
//!
//! — "`S` is upward-closed under `≤` and non-empty". We bridge a real and
//! its cut-set with the kernel subtype coercions: [`mk_real`] (`abs`)
//! wraps a cut-set into a real and [`cut_of`] (`rep`) recovers it.
//!
//! The **principal cut** of a rational `q` is its up-set `{x | q ≤ x}`,
//! written η-cleanly as the partial application `ratLe q : rat → bool`
//! (so `(ratLe q) x` is `ratLe q x` with no stray β-redex). [`of_rat`]
//! embeds `rat` into `real` this way; [`real_zero`] / [`real_one`] are the
//! principal cuts of `0` / `1`.
//!
//! ## Status
//!
//! - **Scaffolding** (this layer): the coercions, [`of_rat`], the order
//!   [`real_le`] (reverse inclusion of cut-sets), and [`real_zero`] /
//!   [`real_one`].
//! - **Order: `≤` is a partial order** — [`le_refl`], [`le_trans`],
//!   [`le_antisym`] are **fully proved with no postulates**: reverse
//!   inclusion of cut-sets makes reflexivity / transitivity pure logic, and
//!   antisymmetry pure subtype structure (mutual inclusion ⟹ equal cut-sets
//!   by extensionality ⟹ equal reals by the round-trip [`Thm::spec_abs_rep`]).
//!   [`of_rat_mono`] — the principal-cut embedding is monotone — is proved
//!   too (genuine *modulo* the `rat` order postulates it consumes).
//! - **`is_cut`** — `⊢ cut_pred (ratLe q)`, that every principal up-set is
//!   a genuine cut — is **proved** from the `rat` `≤` toolkit
//!   (`le_trans` for upward closure, `le_refl` for non-emptiness).
//! - **[`zero_ne_one`]** — `⊢ ¬(0 = 1)` — is **proved**: distinct
//!   principal cuts (the rational `0` lies in `ratLe 0` but not `ratLe 1`,
//!   by `not_one_le_zero`), transported through the subtype `rep`/`abs`.
//! - **[`complete`]** — the least-upper-bound property — is **derived**
//!   from the supremum-cut postulates ([`sup_is_ub`], [`sup_is_least`]),
//!   exactly as `rat::dense` is derived from the mediant postulates: the
//!   supremum is the *intersection of the cut-sets* ([`real_sup`]).

use std::sync::LazyLock;

use covalence_core::defs::TypeSpec;
use covalence_core::{Result, Term, Thm, Type, subst};
use smol_str::SmolStr;

use crate::init::ext::{TermExt, ThmExt};
use crate::init::{cat, logic, rat};

// ============================================================================
// The `real` type — a shell-defined Dedekind-cut construction
// ============================================================================
//
// `real := close rat ratLe` lives here in the shell, **not** in the kernel
// catalogue (`covalence-core`): the reals are not needed for the kernel's
// binary-data / float substrate (rationals suffice), so they are built as an
// ordinary derived `close`-subtype over the `rat` order. The kernel's
// witness-free subtype laws (`spec_abs_rep`, `spec_rep_abs_fwd`) apply to it
// exactly as to any `close` spec — no kernel support is required.

/// `real := close rat ratLe` — Dedekind cuts (upper cuts). Carrier is
/// `rat → bool`; the `close` selector predicate enforces upward closure
/// under `ratLe` plus non-emptiness.
pub fn real_spec() -> TypeSpec {
    static LAZY: LazyLock<TypeSpec> = LazyLock::new(|| {
        TypeSpec::close(SmolStr::new_static("real"), rat::rat_ty(), rat::rat_le())
    });
    LAZY.clone()
}
/// `real` as a 0-ary [`Type`].
pub fn real_ty() -> Type {
    static LAZY: LazyLock<Type> = LazyLock::new(|| Type::spec(real_spec(), vec![]));
    LAZY.clone()
}
/// Alias for [`real_ty`] (the catalogue-style name).
pub fn real_type() -> Type {
    real_ty()
}

// ============================================================================
// Coercions and small term helpers
// ============================================================================

/// `real` — the reals type.
fn real() -> Type {
    real_ty()
}

/// `rat` — the base type of the cuts.
fn ratt() -> Type {
    rat::rat_ty()
}

/// `abs : (rat→bool) → real` — wrap a cut-set into a real.
fn real_abs() -> Term {
    Term::spec_abs(real_spec(), Vec::new())
}
/// `rep : real → (rat→bool)` — the cut-set of a real.
fn real_rep() -> Term {
    Term::spec_rep(real_spec(), Vec::new())
}

/// `mkReal S ≔ abs S` — the real whose cut-set is `S : rat→bool`.
fn mk_real(s: Term) -> Term {
    Term::app(real_abs(), s)
}
/// `cutOf r ≔ rep r : rat→bool` — the cut-set of the real `r`.
fn cut_of(r: Term) -> Term {
    Term::app(real_rep(), r)
}

/// The `close`/cut selector predicate `P : (rat→bool) → bool` — the
/// `real` subtype's `tm()`.
fn cut_pred() -> Term {
    real_spec()
        .tm()
        .expect("real is a close-subtype with a selector predicate")
        .clone()
}

/// `ratLe q : rat → bool` — the principal upper cut `{x | q ≤ x}` of a
/// rational `q`, η-cleanly as a partial application.
fn upper_cut(q: Term) -> Term {
    Term::app(rat::rat_le(), q)
}

// ============================================================================
// Embedding ℚ ↪ ℝ and the order
// ============================================================================

/// `of_rat : rat → real` ≡ `λq. mkReal (ratLe q)` — the principal-cut
/// embedding of the rationals.
pub fn of_rat() -> Term {
    let q = Term::free("q", ratt());
    let body = mk_real(upper_cut(q.clone()));
    Term::abs(ratt(), subst::close(&body, "q"))
}

/// `0 : real` ≡ the principal cut of `rat`'s `0`.
pub fn real_zero() -> Term {
    mk_real(upper_cut(rat::rat_zero()))
}

/// `1 : real` ≡ the principal cut of `rat`'s `1`.
pub fn real_one() -> Term {
    mk_real(upper_cut(rat::rat_one()))
}

/// `realLe : real → real → bool` ≡ `λr s. ∀q. cutOf s q ⟹ cutOf r q` —
/// the order on reals as **reverse inclusion** of cut-sets (a larger real
/// has a smaller up-set).
pub fn real_le() -> Term {
    let (r, s) = (Term::free("r", real()), Term::free("s", real()));
    let q = Term::free("q", ratt());
    let body = Term::app(cut_of(s.clone()), q.clone())
        .imp(Term::app(cut_of(r.clone()), q))
        .expect("real_le: body")
        .forall("q", ratt())
        .expect("real_le: ∀q");
    Term::abs(
        real(),
        subst::close(&Term::abs(real(), subst::close(&body, "s")), "r"),
    )
}

/// `r ≤ s` on `real`.
fn rle(r: Term, s: Term) -> Term {
    Term::app(Term::app(real_le(), r), s)
}

/// `ratLe a b` — a rational `≤` atom.
fn rat_le_app(a: &Term, b: &Term) -> Term {
    Term::app(Term::app(rat::rat_le(), a.clone()), b.clone())
}

// ============================================================================
// `realLe` is a partial order — fully proved, no postulates
// ============================================================================
//
// `realLe` is reverse inclusion of cut-sets, so the order laws are pure
// logic on that definition (reflexivity / transitivity) and pure subtype
// structure (antisymmetry: equal cut-sets ⟹ equal reals, via the kernel
// round-trip `spec_abs_rep` + function extensionality). None of them touch
// the `rat`/order postulates — this is the genuine analogue of `rat`'s `≤`
// toolkit, one level up. (`init::rat`'s `le_refl`/`le_trans` rest on the
// `rat` order postulates; the `real` ones rest on nothing.)

/// `⊢ r ≤ s` → `⊢ ∀q. cutOf s q ⟹ cutOf r q` — the β-reduced order body.
fn reduce_le(thm: Thm) -> Result<Thm> {
    thm.concl().reduce()?.eq_mp(thm)
}

/// `⊢ ∀q. cutOf s q ⟹ cutOf r q` → `⊢ r ≤ s`, for the application `r ≤ s`.
fn expand_le(body: Thm, app: &Term) -> Result<Thm> {
    app.reduce()?.sym()?.eq_mp(body)
}

cached_thm! {
    /// `⊢ ∀r. r ≤ r` — reflexivity. `r ≤ r` is `∀q. cutOf r q ⟹ cutOf r q`,
    /// the identity implication.
    pub fn le_refl() -> Thm {
        le_refl_impl().expect("real::le_refl")
    }
}
fn le_refl_impl() -> Result<Thm> {
    let r = Term::free("r", real());
    let crq = Term::app(cut_of(r.clone()), Term::free("q", ratt()));
    let body = Thm::assume(crq.clone())?
        .imp_intro(&crq)?
        .all_intro("q", ratt())?; // ⊢ ∀q. cutOf r q ⟹ cutOf r q
    expand_le(body, &rle(r.clone(), r.clone()))?.all_intro("r", real())
}

cached_thm! {
    /// `⊢ ∀r s t. r ≤ s ⟹ s ≤ t ⟹ r ≤ t` — transitivity. Reverse inclusion
    /// composes: `cutOf t q ⟹ cutOf s q ⟹ cutOf r q`.
    pub fn le_trans() -> Thm {
        le_trans_impl().expect("real::le_trans")
    }
}
fn le_trans_impl() -> Result<Thm> {
    let (r, s, t) = (
        Term::free("r", real()),
        Term::free("s", real()),
        Term::free("t", real()),
    );
    let (hrs, hst) = (rle(r.clone(), s.clone()), rle(s.clone(), t.clone()));
    let brs = reduce_le(Thm::assume(hrs.clone())?)?; // {r≤s} ⊢ ∀q. cutOf s q ⟹ cutOf r q
    let bst = reduce_le(Thm::assume(hst.clone())?)?; // {s≤t} ⊢ ∀q. cutOf t q ⟹ cutOf s q

    let q = Term::free("q", ratt());
    let rs_q = brs.all_elim(q.clone())?; // cutOf s q ⟹ cutOf r q
    let st_q = bst.all_elim(q.clone())?; // cutOf t q ⟹ cutOf s q
    let ctq = Term::app(cut_of(t.clone()), q); // cutOf t q
    // {cutOf t q} ⊢ cutOf r q, threading through cutOf s q.
    let crq = rs_q.imp_elim(st_q.imp_elim(Thm::assume(ctq.clone())?)?)?;
    let goal_body = crq.imp_intro(&ctq)?.all_intro("q", ratt())?;

    expand_le(goal_body, &rle(r.clone(), t.clone()))?
        .imp_intro(&hst)?
        .imp_intro(&hrs)?
        .all_intro("t", real())?
        .all_intro("s", real())?
        .all_intro("r", real())
}

cached_thm! {
    /// `⊢ ∀r s. r ≤ s ⟹ s ≤ r ⟹ r = s` — antisymmetry. Mutual reverse
    /// inclusion makes the two cut-sets pointwise-equal; function
    /// extensionality lifts that to `cutOf r = cutOf s`, and the subtype
    /// round-trip [`Thm::spec_abs_rep`] (`abs (rep x) = x`) turns equal
    /// cut-sets into equal reals.
    pub fn le_antisym() -> Thm {
        le_antisym_impl().expect("real::le_antisym")
    }
}
fn le_antisym_impl() -> Result<Thm> {
    let (r, s) = (Term::free("r", real()), Term::free("s", real()));
    let (hrs, hsr) = (rle(r.clone(), s.clone()), rle(s.clone(), r.clone()));
    let brs = reduce_le(Thm::assume(hrs.clone())?)?; // {r≤s} ⊢ ∀q. cutOf s q ⟹ cutOf r q
    let bsr = reduce_le(Thm::assume(hsr.clone())?)?; // {s≤r} ⊢ ∀q. cutOf r q ⟹ cutOf s q

    let q = Term::free("q", ratt());
    let rs_q = brs.all_elim(q.clone())?; // cutOf s q ⟹ cutOf r q
    let sr_q = bsr.all_elim(q.clone())?; // cutOf r q ⟹ cutOf s q
    let crq = Term::app(cut_of(r.clone()), q.clone());
    let csq = Term::app(cut_of(s.clone()), q);
    let from_s = rs_q.imp_elim(Thm::assume(csq.clone())?)?; // {cutOf s q} ⊢ cutOf r q
    let from_r = sr_q.imp_elim(Thm::assume(crq.clone())?)?; // {cutOf r q} ⊢ cutOf s q
    let pointwise = from_s.deduct_antisym(from_r)?; // ⊢ cutOf r q = cutOf s q

    // Extensionality: ⊢ cutOf r = cutOf s, i.e. rep r = rep s.
    let reps_eq = cat::fun_ext(pointwise, "q", &ratt())?;
    let abs_eq = reps_eq.cong_arg(real_abs())?; // ⊢ abs (rep r) = abs (rep s)
    let r_eq = Thm::spec_abs_rep(real_spec(), Vec::new(), r.clone())?; // ⊢ abs (rep r) = r
    let s_eq = Thm::spec_abs_rep(real_spec(), Vec::new(), s.clone())?; // ⊢ abs (rep s) = s
    let rs_eq = r_eq.sym()?.trans(abs_eq)?.trans(s_eq)?; // ⊢ r = s

    rs_eq
        .imp_intro(&hsr)?
        .imp_intro(&hrs)?
        .all_intro("s", real())?
        .all_intro("r", real())
}

cached_thm! {
    /// `⊢ ∀a b. ratLe a b ⟹ of_rat a ≤ of_rat b` — the principal-cut
    /// embedding is **monotone**. Reverse inclusion: `a ≤ b` shrinks the
    /// up-set, so `{x | b ≤ x} ⊆ {x | a ≤ x}` (by `rat::le_trans`). The
    /// cut-sets are recovered through the subtype round-trip
    /// ([`Thm::spec_rep_abs_fwd`] discharged by [`is_cut`]). Genuine *modulo*
    /// the `rat` order postulates `rat::le_trans` / `is_cut` rest on.
    pub fn of_rat_mono() -> Thm {
        of_rat_mono_impl().expect("real::of_rat_mono")
    }
}
fn of_rat_mono_impl() -> Result<Thm> {
    let (a, b) = (Term::free("a", ratt()), Term::free("b", ratt()));
    let hyp = rat_le_app(&a, &b); // ratLe a b
    let (ra, rb) = (mk_real(upper_cut(a.clone())), mk_real(upper_cut(b.clone())));

    // cutOf(ra) = upper_cut a  and  cutOf(rb) = upper_cut b (round-trip).
    let ca = Thm::spec_rep_abs_fwd(real_spec(), Vec::new(), upper_cut(a.clone()))?
        .imp_elim(is_cut(&a)?)?;
    let cb = Thm::spec_rep_abs_fwd(real_spec(), Vec::new(), upper_cut(b.clone()))?
        .imp_elim(is_cut(&b)?)?;

    let q = Term::free("q", ratt());
    let cutrb_q = Term::app(cut_of(rb.clone()), q.clone());
    // {cutOf(rb) q} ⊢ ratLe b q  (rewrite the cut-set to the up-set, at q).
    let lbq = cb
        .cong_fn(q.clone())?
        .eq_mp(Thm::assume(cutrb_q.clone())?)?;
    // {ratLe a b, cutOf(rb) q} ⊢ ratLe a q.
    let laq = rat::le_trans()
        .all_elim(a.clone())?
        .all_elim(b.clone())?
        .all_elim(q.clone())?
        .imp_elim(Thm::assume(hyp.clone())?)?
        .imp_elim(lbq)?;
    // Rewrite back: ratLe a q is `cutOf(ra) q`.
    let cutra_q = ca.cong_fn(q.clone())?.sym()?.eq_mp(laq)?; // ⊢ cutOf(ra) q
    let body = cutra_q.imp_intro(&cutrb_q)?.all_intro("q", ratt())?;
    let le_ra_rb = expand_le(body, &rle(ra.clone(), rb.clone()))?; // {hyp} ⊢ ra ≤ rb

    // ra = of_rat a, rb = of_rat b (β), so rewrite into the embedding form.
    let oa = Thm::beta_conv(Term::app(of_rat(), a.clone()))?; // ⊢ of_rat a = ra
    let ob = Thm::beta_conv(Term::app(of_rat(), b.clone()))?; // ⊢ of_rat b = rb
    le_ra_rb
        .rewrite(&oa.sym()?)?
        .rewrite(&ob.sym()?)? // {hyp} ⊢ of_rat a ≤ of_rat b
        .imp_intro(&hyp)?
        .all_intro("b", ratt())?
        .all_intro("a", ratt())
}

// ============================================================================
// Principal up-sets are genuine cuts
// ============================================================================

/// `⊢ cut_pred (ratLe q)` — every principal up-set `{x | q ≤ x}` is a
/// Dedekind cut. **Proved** from the `rat` `≤` toolkit: upward closure is
/// `le_trans` (`q ≤ x` and `x ≤ y` give `q ≤ y`), non-emptiness is
/// `le_refl` (the witness `q` lies in its own up-set).
///
/// The conclusion is the *un-reduced* redex `cut_pred (ratLe q)` — exactly
/// the antecedent [`Thm::spec_rep_abs_fwd`] expects — obtained by proving
/// the β-reduced conjunction and transporting back across `beta_conv`.
fn is_cut(q: &Term) -> Result<Thm> {
    let s = upper_cut(q.clone()); // ratLe q : rat→bool
    let pred_app = Term::app(cut_pred(), s);
    let conv = Thm::beta_conv(pred_app)?; // ⊢ pred_app = (closed ∧ nonempty)
    let clean = conv
        .concl()
        .as_eq()
        .expect("beta_conv yields an equation")
        .1
        .clone();

    // clean = and closed nonempty = App(App(and, closed), nonempty).
    let (and_closed, nonempty_t) = clean.as_app().expect("clean is a conjunction");
    let closed_t = and_closed
        .as_app()
        .expect("clean is a conjunction")
        .1
        .clone();
    let nonempty_t = nonempty_t.clone();

    // closed: ∀x y. x≤y ⟹ q≤x ⟹ q≤y, via le_trans q x y (antecedents reordered).
    let closed_thm = {
        let (x, y) = (Term::free("x", ratt()), Term::free("y", ratt()));
        let xy = rat_le_app(&x, &y);
        let qx = rat_le_app(q, &x);
        let qy = rat::le_trans()
            .all_elim(q.clone())?
            .all_elim(x.clone())?
            .all_elim(y.clone())?
            .imp_elim(Thm::assume(qx.clone())?)?
            .imp_elim(Thm::assume(xy.clone())?)?; // {q≤x, x≤y} ⊢ q≤y
        qy.imp_intro(&qx)?
            .imp_intro(&xy)?
            .all_intro("y", ratt())?
            .all_intro("x", ratt())?
    };

    // nonempty: ∃x. q≤x, witness q, proof le_refl q (β-expanded to `pred q`).
    let nonempty_thm = {
        let pred = nonempty_t
            .as_app()
            .expect("nonempty is `exists pred`")
            .1
            .clone();
        let refl = rat::le_refl().all_elim(q.clone())?; // ⊢ q≤q
        let pf = Thm::beta_conv(Term::app(pred.clone(), q.clone()))?
            .sym()?
            .eq_mp(refl)?; // ⊢ pred q
        logic::exists_intro(pred, q.clone(), pf)? // ⊢ ∃x. q≤x
    };

    // Re-assemble the conjunction and transport back to the redex.
    debug_assert_eq!(closed_thm.concl(), &closed_t);
    let p_clean = closed_thm.and_intro(nonempty_thm)?; // ⊢ closed ∧ nonempty
    conv.sym()?.eq_mp(p_clean) // ⊢ cut_pred (ratLe q)
}

// ============================================================================
// 0 ≠ 1
// ============================================================================

cached_thm! {
    /// `⊢ ¬(0 = 1)` — zero and one are distinct reals.
    ///
    /// **Proved.** The principal cuts `ratLe 0` and `ratLe 1` differ at the
    /// rational `0`: `0 ≤ 0` holds (`le_refl`) but `1 ≤ 0` does not
    /// (`not_one_le_zero`). Assuming `0 = 1`, congruence under `rep` plus
    /// the subtype round-trip [`Thm::spec_rep_abs_fwd`] (discharged by
    /// [`is_cut`]) collapses the two cut-sets, so `0 ≤ 0 = 1 ≤ 0`,
    /// contradicting `not_one_le_zero`. Genuine *modulo* the `rat` order
    /// postulates `is_cut` / `not_one_le_zero` rest on.
    pub fn zero_ne_one() -> Thm {
        zero_ne_one_impl().expect("real zero_ne_one")
    }
}
fn zero_ne_one_impl() -> Result<Thm> {
    let (zero, one) = (rat::rat_zero(), rat::rat_one());
    let (s0, s1) = (upper_cut(zero.clone()), upper_cut(one.clone()));
    let eq01 = real_zero().equals(real_one())?; // abs s0 = abs s1

    // rep both sides of the assumed equality.
    let reps_eq = Thm::assume(eq01.clone())?.cong_arg(real_rep())?; // {eq} ⊢ rep(abs s0)=rep(abs s1)
    // rep(abs sᵢ) = sᵢ, the subtype round-trip discharged by `is_cut`.
    let r0 = Thm::spec_rep_abs_fwd(real_spec(), Vec::new(), s0)?.imp_elim(is_cut(&zero)?)?;
    let r1 = Thm::spec_rep_abs_fwd(real_spec(), Vec::new(), s1)?.imp_elim(is_cut(&one)?)?;
    let sets_eq = r0.sym()?.trans(reps_eq)?.trans(r1)?; // {eq} ⊢ s0 = s1

    // Evaluate both cut-sets at the rational 0: (0≤0) = (1≤0).
    let at0 = sets_eq.cong_fn(zero.clone())?; // {eq} ⊢ ratLe 0 0 = ratLe 1 0
    let le00 = rat::le_refl().all_elim(zero.clone())?; // ⊢ ratLe 0 0
    let le10 = at0.eq_mp(le00)?; // {eq} ⊢ ratLe 1 0

    // ¬(1≤0) gives the contradiction.
    rat::not_one_le_zero()
        .not_elim(le10)? // {eq, …} ⊢ F
        .imp_intro(&eq01)?
        .not_intro() // ⊢ ¬(0 = 1)
}

// ============================================================================
// Completeness — the least-upper-bound property
// ============================================================================
//
// Derived from the supremum-cut postulates exactly as `rat::dense` is
// derived from the mediant postulates: the least upper bound of a set `A`
// of reals is the **intersection of their cut-sets**, `real_sup A`, and the
// two postulated leaves assert that this intersection *is* an upper bound
// and *is* the least one. Both unfold to set/order facts about the cuts,
// blocked on the same `rat`/order theory the rest of the tower waits on
// (`SKELETONS.md`); `complete` itself is a genuine derivation from them.

/// Postulate a `real` axiom: `{t} ⊢ t` (self-flagged audit trail, as in
/// `init::int` / `init::rat`).
fn axiom(t: Term) -> Thm {
    Thm::assume(t).expect("init::real::axiom: term must be bool-typed")
}

/// `real → bool` — a set of reals.
fn real_set() -> Type {
    Type::fun(real(), Type::bool())
}

/// `is_ub A u ≔ ∀a. A a ⟹ a ≤ u` — `u` is an upper bound of `A`.
fn is_ub(a_set: &Term, u: &Term) -> Term {
    let a = Term::free("a", real());
    Term::app(a_set.clone(), a.clone())
        .imp(rle(a, u.clone()))
        .expect("is_ub: body")
        .forall("a", real())
        .expect("is_ub: ∀a")
}

/// `is_lub A s ≔ is_ub A s ∧ (∀u. is_ub A u ⟹ s ≤ u)` — `s` is the least
/// upper bound of `A`.
fn is_lub(a_set: &Term, s: &Term) -> Term {
    let u = Term::free("u", real());
    let least = is_ub(a_set, &u)
        .imp(rle(s.clone(), u))
        .expect("is_lub: least body")
        .forall("u", real())
        .expect("is_lub: ∀u");
    is_ub(a_set, s).and(least).expect("is_lub: conjunction")
}

/// `nonempty A ≔ ∃a. A a`.
fn nonempty(a_set: &Term) -> Term {
    let a = Term::free("a", real());
    Term::app(a_set.clone(), a)
        .exists("a", real())
        .expect("nonempty: ∃a")
}

/// `bounded A ≔ ∃u. is_ub A u` — `A` is bounded above.
fn bounded(a_set: &Term) -> Term {
    let u = Term::free("u", real());
    is_ub(a_set, &u).exists("u", real()).expect("bounded: ∃u")
}

/// `realSup : (real→bool) → real` ≡ `λA. mkReal (λq. ∀a. A a ⟹ cutOf a q)`
/// — the supremum as the **intersection of the cut-sets** of the members
/// of `A` (for upper cuts, sup = intersection).
pub fn real_sup() -> Term {
    let a_set = Term::free("A", real_set());
    let q = Term::free("q", ratt());
    let a = Term::free("a", real());
    let inner = Term::app(a_set.clone(), a.clone())
        .imp(Term::app(cut_of(a), q.clone()))
        .expect("real_sup: ∀a body")
        .forall("a", real())
        .expect("real_sup: ∀a");
    let cutset = Term::abs(ratt(), subst::close(&inner, "q")); // λq. ∀a. A a ⟹ rep a q
    let body = mk_real(cutset);
    Term::abs(real_set(), subst::close(&body, "A"))
}
/// `realSup A` applied.
fn sup(a_set: &Term) -> Term {
    Term::app(real_sup(), a_set.clone())
}

/// `⊢ ∀A. nonempty A ⟹ bounded A ⟹ is_ub A (realSup A)` — the supremum
/// cut is an upper bound. **Postulated** (audit hyp); unfolds to "a
/// rational in every member-cut is `≥` every member" — a set/order fact
/// about the cuts (`SKELETONS.md`).
pub fn sup_is_ub() -> Thm {
    let a_set = Term::free("A", real_set());
    let concl = is_ub(&a_set, &sup(&a_set));
    let body = nonempty(&a_set)
        .imp(bounded(&a_set).imp(concl).expect("sup_is_ub inner"))
        .expect("sup_is_ub");
    axiom(body.forall("A", real_set()).expect("sup_is_ub: ∀A"))
}

/// `⊢ ∀A. nonempty A ⟹ bounded A ⟹ ∀u. is_ub A u ⟹ realSup A ≤ u` — the
/// supremum cut is the *least* upper bound. **Postulated** (audit hyp);
/// unfolds to "the intersection-cut contains every upper-bound cut" — the
/// dual set/order fact (`SKELETONS.md`).
pub fn sup_is_least() -> Thm {
    let a_set = Term::free("A", real_set());
    let u = Term::free("u", real());
    let inner = is_ub(&a_set, &u)
        .imp(rle(sup(&a_set), u))
        .expect("sup_is_least: u body")
        .forall("u", real())
        .expect("sup_is_least: ∀u");
    let body = nonempty(&a_set)
        .imp(bounded(&a_set).imp(inner).expect("sup_is_least inner"))
        .expect("sup_is_least");
    axiom(body.forall("A", real_set()).expect("sup_is_least: ∀A"))
}

cached_thm! {
    /// `⊢ ∀A. nonempty A ⟹ bounded A ⟹ ∃s. is_lub A s` — **the reals are
    /// complete** (the least-upper-bound property).
    ///
    /// A genuine derivation: the witness is the supremum cut [`real_sup`]
    /// `A` (the intersection of the members' cut-sets); [`sup_is_ub`] and
    /// [`sup_is_least`] are its two least-upper-bound properties, packaged
    /// by `∧`- and `∃`-introduction. The only postulated leaves are those
    /// two; discharging them makes this hypothesis-free. (Same shape as
    /// `rat::dense` over its mediant postulates.)
    pub fn complete() -> Thm {
        complete_impl().expect("completeness derivation")
    }
}
fn complete_impl() -> Result<Thm> {
    let a_set = Term::free("A", real_set());
    let (ne, bd) = (nonempty(&a_set), bounded(&a_set));
    let s = sup(&a_set);

    // {ne, bd} ⊢ is_ub A s   and   {ne, bd} ⊢ ∀u. is_ub A u ⟹ s ≤ u.
    let ub = sup_is_ub()
        .all_elim(a_set.clone())?
        .imp_elim(Thm::assume(ne.clone())?)?
        .imp_elim(Thm::assume(bd.clone())?)?;
    let least = sup_is_least()
        .all_elim(a_set.clone())?
        .imp_elim(Thm::assume(ne.clone())?)?
        .imp_elim(Thm::assume(bd.clone())?)?;
    let lub = ub.and_intro(least)?; // {ne, bd} ⊢ is_lub A s

    // ∃s. is_lub A s, with witness the supremum cut.
    let s_var = Term::free("s", real());
    let pred = Term::abs(real(), subst::close(&is_lub(&a_set, &s_var), "s"));
    let pf = Thm::beta_conv(Term::app(pred.clone(), s.clone()))?
        .sym()?
        .eq_mp(lub)?; // {ne, bd} ⊢ pred s
    let ex = logic::exists_intro(pred, s, pf)?; // {ne, bd} ⊢ ∃s. is_lub A s

    ex.imp_intro(&bd)?
        .imp_intro(&ne)?
        .all_intro("A", real_set())
}

// ============================================================================
// The `realprim` seam env — operators + the abs/rep-crossing seam lemmas
// ============================================================================
//
// `real := close rat ratLe` is a `close`-subtype, so `real.cov` re-proves the
// `realLe` partial-order laws over the cut-set seam WITHOUT touching abs/rep:
// the seam is exposed as honest **operators** —
//
//   real.le    : real → real → bool   (`real_le`)
//   real.cutOf : real → rat → bool    (`rep`, the cut-set of a real)
//   real.mk    : (rat→bool) → real    (`abs`, wrap a cut-set into a real)
//   real.ofRat : rat → real           (`of_rat`, the principal-cut embedding)
//
// — plus a handful of `∀`-closed **seam lemmas** that cross the boundary via
// the kernel's witness-free subtype laws, Rust-proved as givens (the `set.cov`
// `mem_*`/`ext` pattern). `real.cov` proves the order laws over them + the
// imported `rat` order facts, never mentioning the kernel `abs`/`rep`.

/// `⊢ ∀r s. real.le r s = (∀q. real.cutOf s q ⟹ real.cutOf r q)` — the order
/// definition, unfolded to reverse cut-set inclusion. `real.cov`'s `le_refl` /
/// `le_trans` / `le_antisym` all pivot on this β-equation.
fn le_unfold_given() -> Result<Thm> {
    let (r, s) = (Term::free("r", real()), Term::free("s", real()));
    rle(r.clone(), s.clone())
        .reduce()? // ⊢ real.le r s = (∀q. cutOf s q ⟹ cutOf r q)
        .all_intro("s", real())?
        .all_intro("r", real())
}

/// `⊢ ∀r. real.mk (real.cutOf r) = r` — the subtype round-trip (`abs (rep r) =
/// r`), the only abs/rep fact `le_antisym` needs (equal cut-sets ⟹ equal
/// reals).
fn abs_rep_given() -> Result<Thm> {
    let r = Term::free("r", real());
    Thm::spec_abs_rep(real_spec(), Vec::new(), r.clone())?.all_intro("r", real())
}

/// The `realprim` seam environment imported by `real.cov`: the `real` order /
/// cut operators (monomorphic — `real` is a ground type) and the seam lemmas
/// (`le.unfold`, `abs_rep`) in `∀`-closed form. These cross the subtype
/// boundary, so they stay Rust-proved givens; `real.cov` proves the `realLe`
/// partial order over them.
pub fn real_env() -> crate::script::Env {
    use crate::script::{ConstDef, Env};
    let mut e = Env::empty();

    // operators (monomorphic; `real` is ground)
    e.define_const("real.le", ConstDef::Op(real_le()));
    e.define_const("real.cutOf", ConstDef::Op(real_rep()));
    e.define_const("real.mk", ConstDef::Op(real_abs()));
    e.define_const("real.ofRat", ConstDef::Op(of_rat()));
    e.define_const("real.zero", ConstDef::Op(real_zero()));
    e.define_const("real.one", ConstDef::Op(real_one()));

    // seam givens (dotted, matching the `real.cov` surface)
    e.define_lemma(
        "real.le.unfold",
        le_unfold_given().expect("real le.unfold given"),
    );
    e.define_lemma("real.abs_rep", abs_rep_given().expect("real abs_rep given"));
    e
}

crate::cov_theory! {
    /// `realLe` partial-order laws ported to `real.cov`, over `core` + `logic`
    /// + the `realprim` seam env. The seam env is re-exported through the
    /// `real` namespace (`#provide (#alias realprim real)`), so a downstream
    /// `.cov` imports just `real` to reach `real.*`. The `sup_is_ub` /
    /// `sup_is_least` / `complete` postulates are NOT ported (see SKELETONS.md).
    pub mod cov from "real.cov" {
        import "core" = crate::script::Env::core();
        import "logic" = crate::init::logic::cov::env();
        import "realprim" = crate::init::real::real_env();
        "le.refl"    => pub fn le_refl_cov;
        "le.trans"   => pub fn le_trans_cov;
        "le.antisym" => pub fn le_antisym_cov;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `rat → bool` — the powerset carrier a cut-set lives in.
    fn powerset() -> Type {
        Type::fun(ratt(), Type::bool())
    }

    #[test]
    fn real_ty_is_a_zero_ary_spec() {
        use covalence_core::ty::TypeKind;
        // `real` is the shell-defined `close` spec (no longer in the kernel
        // catalogue), a 0-ary spec type and not bool.
        assert_eq!(real(), real_ty());
        assert!(matches!(real().kind(), TypeKind::Spec(_, args) if args.is_empty()));
        assert!(!real().is_bool());
    }

    #[test]
    fn carrier_is_the_rational_powerset() {
        // abs : (rat→bool) → real ; rep : real → (rat→bool).
        assert_eq!(real_abs().type_of().unwrap(), Type::fun(powerset(), real()));
        assert_eq!(real_rep().type_of().unwrap(), Type::fun(real(), powerset()));
    }

    #[test]
    fn embedding_and_constants_have_expected_types() {
        assert_eq!(of_rat().type_of().unwrap(), Type::fun(ratt(), real()));
        assert_eq!(real_zero().type_of().unwrap(), real());
        assert_eq!(real_one().type_of().unwrap(), real());
    }

    #[test]
    fn real_le_is_a_binary_relation() {
        assert_eq!(
            real_le().type_of().unwrap(),
            Type::fun(real(), Type::fun(real(), Type::bool()))
        );
        // `r ≤ s` is a bool.
        let (r, s) = (Term::free("r", real()), Term::free("s", real()));
        assert!(rle(r, s).type_of().unwrap().is_bool());
    }

    #[test]
    fn is_cut_proves_a_principal_up_set_is_a_cut() {
        // A concrete rational (`is_cut` is only ever called on closed
        // rationals; `exists_intro` reserves the name `q` internally).
        let q = rat::rat_zero();
        let thm = is_cut(&q).expect("is_cut q");
        // Conclusion is exactly the redex `cut_pred (ratLe q)`.
        assert_eq!(thm.concl(), &Term::app(cut_pred(), upper_cut(q)));
        assert!(thm.concl().type_of().unwrap().is_bool());
    }

    #[test]
    fn le_is_a_partial_order_and_genuine() {
        // reflexivity / transitivity / antisymmetry are all hypothesis-free
        // (no postulates — pure cut-set reverse-inclusion structure).
        for t in [le_refl(), le_trans(), le_antisym()] {
            assert!(t.hyps().is_empty(), "real `≤` order laws are fully proved");
            assert!(t.concl().type_of().unwrap().is_bool());
        }

        let (r, s, t) = (
            Term::free("r", real()),
            Term::free("s", real()),
            Term::free("t", real()),
        );
        // refl specialises to `r ≤ r`.
        assert_eq!(
            le_refl().all_elim(r.clone()).unwrap().concl(),
            &rle(r.clone(), r.clone())
        );
        // trans specialises to `r ≤ s ⟹ s ≤ t ⟹ r ≤ t`.
        let tr = le_trans()
            .all_elim(r.clone())
            .unwrap()
            .all_elim(s.clone())
            .unwrap()
            .all_elim(t.clone())
            .unwrap();
        let expected_tr = rle(r.clone(), s.clone())
            .imp(
                rle(s.clone(), t.clone())
                    .imp(rle(r.clone(), t.clone()))
                    .unwrap(),
            )
            .unwrap();
        assert_eq!(tr.concl(), &expected_tr);
        // antisym specialises to `r ≤ s ⟹ s ≤ r ⟹ r = s`.
        let anti = le_antisym()
            .all_elim(r.clone())
            .unwrap()
            .all_elim(s.clone())
            .unwrap();
        let expected_anti = rle(r.clone(), s.clone())
            .imp(
                rle(s.clone(), r.clone())
                    .imp(r.clone().equals(s.clone()).unwrap())
                    .unwrap(),
            )
            .unwrap();
        assert_eq!(anti.concl(), &expected_anti);
    }

    #[test]
    fn of_rat_is_monotone() {
        let thm = of_rat_mono();
        // Shape: ∀a b. ratLe a b ⟹ of_rat a ≤ of_rat b.
        let (a, b) = (Term::free("a", ratt()), Term::free("b", ratt()));
        let inst = thm
            .clone()
            .all_elim(a.clone())
            .unwrap()
            .all_elim(b.clone())
            .unwrap();
        let oa = Term::app(of_rat(), a.clone());
        let ob = Term::app(of_rat(), b.clone());
        let expected = rat_le_app(&a, &b).imp(rle(oa, ob)).unwrap();
        assert_eq!(inst.concl(), &expected);
        // Genuine modulo the rat-order postulates: no equation hyp, all bool.
        for h in thm.hyps() {
            assert!(h.type_of().unwrap().is_bool());
        }
    }

    #[test]
    fn zero_is_distinct_from_one() {
        let thm = zero_ne_one();
        // Statement: ¬(0 = 1).
        assert_eq!(
            thm.concl(),
            &real_zero().equals(real_one()).unwrap().not().unwrap()
        );
        // Genuine modulo the rat-order postulates: the assumed `0 = 1` is
        // discharged, so no equation hypothesis remains — only bool
        // (postulate) hyps.
        let eq01 = real_zero().equals(real_one()).unwrap();
        assert!(
            !thm.hyps().iter().any(|h| h == &eq01),
            "the assumed equality is discharged"
        );
        for h in thm.hyps() {
            assert!(h.type_of().unwrap().is_bool());
        }
    }

    #[test]
    fn sup_postulates_and_completeness_are_well_formed() {
        // real_sup : (real→bool) → real.
        assert_eq!(real_sup().type_of().unwrap(), Type::fun(real_set(), real()));
        // The two sup postulates are self-flagged bool statements.
        for ax in [sup_is_ub(), sup_is_least()] {
            assert!(ax.concl().type_of().unwrap().is_bool());
            assert!(ax.hyps().iter().any(|h| h == ax.concl()));
        }
    }

    #[test]
    fn completeness_is_derived_from_the_sup_postulates() {
        let thm = complete();
        // Shape: ∀A. nonempty A ⟹ bounded A ⟹ ∃s. is_lub A s. Specialise A.
        let a_set = Term::free("A", real_set());
        let inst = thm.clone().all_elim(a_set.clone()).unwrap();
        let s = Term::free("s", real());
        let pred = Term::abs(real(), subst::close(&is_lub(&a_set, &s), "s"));
        let exists_lub = Term::app(covalence_core::defs::exists(real()), pred);
        let expected = nonempty(&a_set)
            .imp(bounded(&a_set).imp(exists_lub).unwrap())
            .unwrap();
        assert_eq!(inst.concl(), &expected);

        // Genuine modulo exactly the two sup postulates: those are the only
        // hypotheses (each a bool statement).
        assert_eq!(thm.hyps().len(), 2, "only the two sup postulates remain");
        for h in thm.hyps() {
            assert!(h.type_of().unwrap().is_bool());
        }
    }

    #[test]
    fn cut_pred_is_the_close_predicate() {
        // cut_pred : (rat→bool) → bool.
        assert_eq!(
            cut_pred().type_of().unwrap(),
            Type::fun(powerset(), Type::bool())
        );
        // It applies to a principal cut to give a bool statement.
        let p = Term::app(cut_pred(), upper_cut(rat::rat_zero()));
        assert!(p.type_of().unwrap().is_bool());
    }

    // -- `.cov` ports: each `cov::X` is conclusion-equal to its Rust `super::X`
    //    and just as genuine (the partial-order laws are hypothesis-free). ----

    #[test]
    fn cov_le_refl_matches_rust_and_is_genuine() {
        let c = cov::le_refl_cov();
        assert_eq!(c.concl(), le_refl().concl());
        assert!(
            c.hyps().is_empty(),
            "le.refl is fully proved (no postulates)"
        );
        assert!(c.has_no_obs());
    }

    #[test]
    fn cov_le_trans_matches_rust_and_is_genuine() {
        let c = cov::le_trans_cov();
        assert_eq!(c.concl(), le_trans().concl());
        assert!(
            c.hyps().is_empty(),
            "le.trans is fully proved (no postulates)"
        );
        assert!(c.has_no_obs());
    }

    #[test]
    fn cov_le_antisym_matches_rust_and_is_genuine() {
        let c = cov::le_antisym_cov();
        assert_eq!(c.concl(), le_antisym().concl());
        assert!(
            c.hyps().is_empty(),
            "le.antisym is fully proved (no postulates)"
        );
        assert!(c.has_no_obs());
    }
}
