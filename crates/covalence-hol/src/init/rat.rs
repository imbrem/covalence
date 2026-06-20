//! `rat` theorems: the `defs/rat.rs` catalogue re-exported, plus the
//! quotient scaffolding for HOL `rat := (int × int.pos) / ~` — mirroring
//! how [`init::int`] pairs the `int` definitions with the Grothendieck
//! quotient machinery, one level up.
//!
//! [`init::int`]: crate::init::int
//!
//! ## The construction
//!
//! A pair `(a, b) : int × int.pos` represents the rational `a / b` with a
//! strictly-positive denominator (so it is always nonzero and the sign
//! lives in the numerator), and pairs are identified by
//! cross-multiplication:
//!
//! ```text
//!     (a, b) ~ (c, d)  ⟺  a · d = c · b
//! ```
//!
//! `rat` is the quotient of `prod int int.pos` by that relation; the
//! carrier is `(prod int int.pos) → bool` (a class is the set of
//! equivalent numerator/denominator pairs). The bridge between a
//! representative pair and its class reuses the generic
//! [`init::quotient`](crate::init::quotient) machinery exactly as `int`
//! does over `nat × nat`.
//!
//! ## Status
//!
//! This module is built up in layers, mirroring `init::int`:
//!
//! - **Quotient relation.** [`rat_rel`] is the cross-multiplication
//!   relation, structurally the term `defs/rat.rs` quotients by.
//!   [`rat_rel_refl`] / [`rat_rel_symm`] are **proved** (`int`-equation
//!   `refl` / `sym`); [`rat_rel_trans`] is **postulated** — it is the one
//!   piece that needs `int` *multiplicative cancellation by a positive*,
//!   an `int` fact not yet discharged (see `SKELETONS.md`).
//! - **Maps in.** [`of_int`] (`a ↦ a/1`) and [`of_nat`] (`= of_int ∘
//!   nat.toInt`, by composition) embed the integers and naturals.
//! - **Ring / order.** The field operations ([`rat_zero`], [`rat_one`],
//!   [`rat_add`], [`rat_sub`], [`rat_neg`], [`rat_mul`], [`rat_inv`],
//!   [`rat_div`]) and the strict order
//!   ([`rat_lt`]) are defined at the representative level. [`add_comm`] /
//!   [`mul_comm`] are **proved** — on the nose, exactly as `init::int`'s
//!   are, since the ops are componentwise on representatives (so equal
//!   representative pairs lift to equal classes by congruence, needing only
//!   the proved `int` commutativity facts, not the blocked cancellation).
//!   The remaining ordered-field axioms over them are **postulated** (same
//!   audit-trail style as `init::int`), pending the quotient derivations. On
//!   top of those, a
//!   small `≤` toolkit is **derived**: [`le_refl`], [`lt_imp_le`],
//!   [`le_trans`], and [`not_one_le_zero`] (from [`le_def`] + the strict
//!   facts + the one base postulate [`zero_lt_one`]). These are what the
//!   `real` Dedekind-cut construction in [`init::real`](crate::init::real)
//!   consumes.
//! - **Density.** [`dense`] — `∀x y. x < y ⟹ ∃z. x < z ∧ z < y` — is
//!   **derived** from the two mediant-inequality postulates via the
//!   mediant `(a+c)/(b+d)`, the witness that needs no division.

use covalence_core::defs::{fst, int_pos_spec, int_pos_ty, prod, snd};
use covalence_core::{Error, Result, Term, Thm, Type, subst};

use crate::init::ext::{TermExt, ThmExt};
use crate::init::{int, logic, nat};

// Re-export the `defs/rat.rs` catalogue (the type handles + the declared
// `ratLe` order constant; bodies stay in `covalence_core::defs`).
pub use covalence_core::defs::{rat_le, rat_le_spec, rat_spec, rat_ty};

// ============================================================================
// Small term helpers (private — the public surface is theorems / maps)
// ============================================================================

/// `rat` — the rationals type.
fn rat() -> Type {
    rat_ty()
}

/// `int × int.pos` — the numerator/denominator representative carrier.
fn ip_pair() -> Type {
    prod(Type::int(), int_pos_ty())
}

/// `fst p : int` — the numerator of a representative pair.
fn num(p: &Term) -> Term {
    Term::app(fst(Type::int(), int_pos_ty()), p.clone())
}

/// `rep (snd p) : int` — the (positive) denominator of a representative
/// pair, coerced from `int.pos` down to its underlying `int`.
fn den(p: &Term) -> Term {
    let d_pos = Term::app(snd(Type::int(), int_pos_ty()), p.clone());
    let rep = Term::spec_rep(int_pos_spec(), Vec::new());
    Term::app(rep, d_pos)
}

/// `a · b` on `int`.
fn imul(a: Term, b: Term) -> Term {
    Term::app(Term::app(int::int_mul(), a), b)
}

/// `λp q. num p · den q = num q · den p` — the cross-multiplication
/// relation carving `rat`. Structurally the same term `defs/rat.rs`
/// quotients by.
pub fn rat_rel() -> Term {
    let pair_ty = ip_pair();
    let (p, q) = (
        Term::free("p", pair_ty.clone()),
        Term::free("q", pair_ty.clone()),
    );
    let body = imul(num(&p), den(&q))
        .equals(imul(num(&q), den(&p)))
        .expect("rat_rel: body");
    let inner = Term::abs(pair_ty.clone(), covalence_core::subst::close(&body, "q"));
    Term::abs(pair_ty, covalence_core::subst::close(&inner, "p"))
}

/// `rat_rel p q` as an (un-reduced) application — the shape
/// [`quotient::class_intro`](crate::init::quotient::class_intro) reads
/// its relation in.
fn rel_app(p: &Term, q: &Term) -> Term {
    Term::app(Term::app(rat_rel(), p.clone()), q.clone())
}

/// `mkRat p ≔ abs (λq. rat_rel p q)` — the rational whose class is `[p]`,
/// for a representative pair term `p : int × int.pos`.
fn mk_rat(p: &Term) -> Term {
    crate::init::quotient::mk_class(&rat_spec(), &[], &ip_pair(), &rat_rel(), p)
}

/// `⊢ rat_rel p q` → `⊢ <β-reduced cross-mult equation>`.
fn reduce_rel(thm: Thm) -> Result<Thm> {
    thm.concl().reduce()?.eq_mp(thm)
}

/// `⊢ <β-reduced cross-mult equation>` → `⊢ rat_rel p q`, for the given
/// application.
fn expand_rel(eq: Thm, app: &Term) -> Result<Thm> {
    app.reduce()?.sym()?.eq_mp(eq)
}

/// `1 : int.pos` — the abstraction of the `int` literal `1`. The
/// canonical denominator for the integer / rational embeddings.
fn one_pos() -> Term {
    Term::app(
        Term::spec_abs(int_pos_spec(), Vec::new()),
        Term::int_lit(1i128),
    )
}

/// `pair a b : int × int.pos`.
fn ip(a: Term, b: Term) -> Term {
    Term::app(
        Term::app(covalence_core::defs::pair(Type::int(), int_pos_ty()), a),
        b,
    )
}

/// Postulate a `rat` axiom: `{t} ⊢ t`. The self-hypothesis is the audit
/// trail — every proof built on it carries it, flagging the unproved leaf
/// until the quotient derivation discharges it (cf. `init::int::axiom`).
fn axiom(t: Term) -> Thm {
    Thm::assume(t).expect("init::rat::axiom: term must be bool-typed")
}

// ============================================================================
// `int` facts the quotient theory consumes — now **proved in `init::int`**
// ============================================================================
//
// `rat_rel_trans` cancels the common strictly-positive denominator with two
// `int` facts: right-cancellation by a nonzero factor and positivity of the
// `int.pos` denominators. Both used to be postulated here (self-flagged via
// `axiom`); they are now **genuine theorems** discharged in [`init::int`]
// ([`int::int_mul_rcancel`] / [`int::int_pos_nonzero`]) from the proved
// ordered-ring/order theory, so the thin re-exports below carry no hypothesis.

/// A free `int` variable.
fn ivar(name: &str) -> Term {
    Term::free(name, Type::int())
}

/// `0 : int`.
fn izero() -> Term {
    Term::int_lit(0i128)
}

/// `⊢ ∀x y d. ¬(d = 0) ⟹ x·d = y·d ⟹ x = y` — `int` integral-domain
/// right-cancellation, **proved** in [`int::int_mul_rcancel`].
fn int_mul_rcancel() -> Thm {
    int::int_mul_rcancel()
}

/// `⊢ ∀p:int.pos. ¬(rep p = 0)` — positive denominators are nonzero,
/// **proved** in [`int::int_pos_nonzero`].
fn int_pos_nonzero() -> Thm {
    int::int_pos_nonzero()
}

// ============================================================================
// `rat_rel` is an equivalence — proved (trans modulo the postulated int facts)
// ============================================================================
//
// `refl` / `symm` are pure `int`-equation manipulations of the cross-
// multiplication body and are **proved** outright. `trans` is now **proved**
// too — the Grothendieck-style cancellation argument (multiply the two
// defining equations through, rearrange by `int` comm/assoc so the common
// `den q` factor lines up, then cancel it) — resting on the postulated
// `int` facts [`int_mul_rcancel`] and [`int_pos_nonzero`] above.

/// `⊢ (x·a)·b = (x·b)·a` on `int` — swap the last two factors of a
/// left-associated triple (associate, commute, re-associate).
fn swap_last_two(x: &Term, a: &Term, b: &Term) -> Result<Thm> {
    let assoc1 = int::mul_assoc()
        .all_elim(x.clone())?
        .all_elim(a.clone())?
        .all_elim(b.clone())?; // (x·a)·b = x·(a·b)
    let comm = int::mul_comm().all_elim(a.clone())?.all_elim(b.clone())?; // a·b = b·a
    let cong = comm.cong_arg(Term::app(int::int_mul(), x.clone()))?; // x·(a·b) = x·(b·a)
    let assoc2 = int::mul_assoc()
        .all_elim(x.clone())?
        .all_elim(b.clone())?
        .all_elim(a.clone())?; // (x·b)·a = x·(b·a)
    assoc1.trans(cong)?.trans(assoc2.sym()?)
}

/// `⊢ x = y` → `⊢ x·c = y·c` (right-multiply both sides of an `int` equation).
fn mul_r(eq: Thm, c: &Term) -> Result<Thm> {
    eq.cong_arg(int::int_mul())?.cong_fn(c.clone())
}

cached_thm! {
    /// `⊢ ∀p. rat_rel p p` — reflexivity (`num p · den p = num p · den p`).
    pub fn rat_rel_refl() -> Thm {
        rat_rel_refl_impl().expect("rat_rel_refl")
    }
}
fn rat_rel_refl_impl() -> Result<Thm> {
    let p = Term::free("p", ip_pair());
    let reduced = Thm::refl(imul(num(&p), den(&p)))?;
    expand_rel(reduced, &rel_app(&p, &p))?.all_intro("p", ip_pair())
}

cached_thm! {
    /// `⊢ ∀p q. rat_rel p q ⟹ rat_rel q p` — symmetry (`sym` of the
    /// defining cross-multiplication equation).
    pub fn rat_rel_symm() -> Thm {
        rat_rel_symm_impl().expect("rat_rel_symm")
    }
}
fn rat_rel_symm_impl() -> Result<Thm> {
    let (p, q) = (Term::free("p", ip_pair()), Term::free("q", ip_pair()));
    let hyp = rel_app(&p, &q);
    let flipped = reduce_rel(Thm::assume(hyp.clone())?)?.sym()?; // ⊢ num q·den p = num p·den q
    expand_rel(flipped, &rel_app(&q, &p))?
        .imp_intro(&hyp)?
        .all_intro("q", ip_pair())?
        .all_intro("p", ip_pair())
}

cached_thm! {
    /// `⊢ ∀p q r. rat_rel p q ⟹ rat_rel q r ⟹ rat_rel p r` —
    /// transitivity, **proved** modulo the postulated `int` facts.
    ///
    /// From `num p · den q = num q · den p` and `num q · den r =
    /// num r · den q`, right-multiply the first by `den r` and the second
    /// by `den p`, rearrange by `int` comm/assoc ([`swap_last_two`]) so the
    /// common `den q` lines up — giving `(num p · den r) · den q =
    /// (num r · den p) · den q` — then cancel the strictly-positive `den q`
    /// ([`int_mul_rcancel`] + [`int_pos_nonzero`]).
    pub fn rat_rel_trans() -> Thm {
        rat_rel_trans_impl().expect("rat_rel_trans")
    }
}
fn rat_rel_trans_impl() -> Result<Thm> {
    let (p, q, r) = (
        Term::free("p", ip_pair()),
        Term::free("q", ip_pair()),
        Term::free("r", ip_pair()),
    );
    let (h1, h2) = (rel_app(&p, &q), rel_app(&q, &r));
    let e1 = reduce_rel(Thm::assume(h1.clone())?)?; // num p·den q = num q·den p
    let e2 = reduce_rel(Thm::assume(h2.clone())?)?; // num q·den r = num r·den q

    let (np, dp) = (num(&p), den(&p));
    let (nq, dq) = (num(&q), den(&q));
    let (nr, dr) = (num(&r), den(&r));

    // (np·dr)·dq = (np·dq)·dr = (nq·dp)·dr = (nq·dr)·dp = (nr·dq)·dp = (nr·dp)·dq.
    let chain = swap_last_two(&np, &dq, &dr)?
        .sym()?
        .trans(mul_r(e1, &dr)?)?
        .trans(swap_last_two(&nq, &dp, &dr)?)?
        .trans(mul_r(e2, &dp)?)?
        .trans(swap_last_two(&nr, &dq, &dp)?)?; // ⊢ (np·dr)·dq = (nr·dp)·dq

    // Cancel the positive den q.
    let nonzero = int_pos_nonzero().all_elim(den_pos(&q))?; // ¬(den q = 0)
    let reduced = int_mul_rcancel()
        .all_elim(imul(np.clone(), dr.clone()))?
        .all_elim(imul(nr.clone(), dp.clone()))?
        .all_elim(dq.clone())?
        .imp_elim(nonzero)?
        .imp_elim(chain)?; // ⊢ num p·den r = num r·den p

    expand_rel(reduced, &rel_app(&p, &r))?
        .imp_intro(&h2)?
        .imp_intro(&h1)?
        .all_intro("r", ip_pair())?
        .all_intro("q", ip_pair())?
        .all_intro("p", ip_pair())
}

// ============================================================================
// Maps in: ℤ ↪ ℚ and ℕ ↪ ℚ (the latter by composition)
// ============================================================================

/// `of_int : int → rat` ≡ `λa. mkRat (a, 1)` — the ring embedding of the
/// integers (numerator `a`, denominator `1`).
pub fn of_int() -> Term {
    let a = Term::free("a", Type::int());
    let body = mk_rat(&ip(a.clone(), one_pos()));
    Term::abs(Type::int(), subst::close(&body, "a"))
}

/// `of_nat : nat → rat` ≡ `λn. of_int (nat.toInt n)` — the embedding of
/// the naturals, **by composition** through `of_int` and the nat→int
/// coercion.
pub fn of_nat() -> Term {
    let n = Term::free("n", Type::nat());
    let body = Term::app(of_int(), Term::app(nat::nat_to_int(), n.clone()));
    Term::abs(Type::nat(), subst::close(&body, "n"))
}

cached_thm! {
    /// `⊢ ∀n. of_nat n = of_int (nat.toInt n)` — the naturals embed
    /// through the integers (the defining composition, by β).
    pub fn of_nat_via_int() -> Thm {
        of_nat_via_int_impl().expect("of_nat_via_int")
    }
}
fn of_nat_via_int_impl() -> Result<Thm> {
    let n = Term::free("n", Type::nat());
    let redex = Term::app(of_nat(), n.clone()); // (λn. of_int (toInt n)) n
    Thm::beta_conv(redex)?.all_intro("n", Type::nat())
}

// ============================================================================
// Field operations — defined at the representative level
// ============================================================================
//
// Each op picks a representative pair from its argument(s) via `repPair`,
// computes on the `int` numerator/denominator components, and re-quotients
// with `mkRat`. The denominators are kept strictly positive: a product of
// positives is positive, so `to_pos` re-wraps an `int` denominator into
// `int.pos` (the *value* is positive; a proof of that positivity is part
// of the downstream quotient derivations, not needed to build the term).

/// `repPair x ≔ ε(λp. rep x p)` — a representative pair drawn from the
/// class of the rat term `x`.
fn rep_pair(x: Term) -> Term {
    let pair_ty = ip_pair();
    let rep = Term::spec_rep(rat_spec(), Vec::new());
    let rep_x = Term::app(rep, x); // (int×int.pos) → bool
    let p = Term::free("p", pair_ty.clone());
    let pred = Term::abs(pair_ty.clone(), subst::close(&Term::app(rep_x, p), "p"));
    Term::app(Term::select_op(pair_ty), pred)
}

/// `snd p : int.pos` — the denominator of a representative pair as an
/// `int.pos` (not coerced down to `int`).
fn den_pos(p: &Term) -> Term {
    Term::app(snd(Type::int(), int_pos_ty()), p.clone())
}

/// `abs z : int.pos` — re-wrap an `int` as `int.pos` (used for the
/// always-positive product denominators).
fn to_pos(z: Term) -> Term {
    Term::app(Term::spec_abs(int_pos_spec(), Vec::new()), z)
}

/// `a + b` on `int`.
fn iadd(a: Term, b: Term) -> Term {
    Term::app(Term::app(int::int_add(), a), b)
}

/// `a - b` on `int`.
fn isub(a: Term, b: Term) -> Term {
    Term::app(Term::app(int::int_sub(), a), b)
}

/// `mkRat (build px py)` for a binary op: `px = repPair x`, `py = repPair y`.
fn binary_rat(build: impl Fn(&Term, &Term) -> Term) -> Term {
    let (x, y) = (Term::free("x", rat()), Term::free("y", rat()));
    let body = mk_rat(&build(&rep_pair(x.clone()), &rep_pair(y.clone())));
    Term::abs(
        rat(),
        subst::close(&Term::abs(rat(), subst::close(&body, "y")), "x"),
    )
}

/// `0 : rat` ≡ `mkRat (0, 1)`.
pub fn rat_zero() -> Term {
    mk_rat(&ip(Term::int_lit(0i128), one_pos()))
}

/// `1 : rat` ≡ `mkRat (1, 1)`.
pub fn rat_one() -> Term {
    mk_rat(&ip(Term::int_lit(1i128), one_pos()))
}

/// `ratAdd : rat → rat → rat` ≡ `(a/b) + (c/d) = (a·d + c·b)/(b·d)`.
pub fn rat_add() -> Term {
    binary_rat(|px, py| {
        let n = iadd(imul(num(px), den(py)), imul(num(py), den(px)));
        ip(n, to_pos(imul(den(px), den(py))))
    })
}

/// `ratMul : rat → rat → rat` ≡ `(a/b) · (c/d) = (a·c)/(b·d)`.
pub fn rat_mul() -> Term {
    binary_rat(|px, py| ip(imul(num(px), num(py)), to_pos(imul(den(px), den(py)))))
}

/// `ratNeg : rat → rat` ≡ `-(a/b) = (-a)/b` (denominator unchanged).
pub fn rat_neg() -> Term {
    let x = Term::free("x", rat());
    let px = rep_pair(x.clone());
    let neg_num = Term::app(int::int_neg(), num(&px));
    let body = mk_rat(&ip(neg_num, den_pos(&px)));
    Term::abs(rat(), subst::close(&body, "x"))
}

/// `ratSub : rat → rat → rat` ≡ `(a/b) - (c/d) = (a·d - c·b)/(b·d)` —
/// numerator by `int` subtraction, denominator the common positive product
/// (the additive companion of [`rat_add`]).
pub fn rat_sub() -> Term {
    binary_rat(|px, py| {
        let n = isub(imul(num(px), den(py)), imul(num(py), den(px)));
        ip(n, to_pos(imul(den(px), den(py))))
    })
}

/// `ratInv : rat → rat` ≡ `(a/b)⁻¹ = (sgn a · b)/(sgn a · a)` — the
/// multiplicative inverse (`b/a` with the sign moved onto the numerator so
/// the denominator `sgn a · a = |a|` stays strictly positive). Junk at
/// `0` (`sgn 0 · 0 = 0`), as the field inverse of `0` is unconstrained.
pub fn rat_inv() -> Term {
    let x = Term::free("x", rat());
    let px = rep_pair(x.clone());
    let (a, b) = (num(&px), den(&px));
    let sgn = Term::app(int::int_sgn(), a.clone());
    let new_num = imul(sgn.clone(), b); // sgn(a)·b
    let new_den = to_pos(imul(sgn, a)); // sgn(a)·a = |a| > 0
    let body = mk_rat(&ip(new_num, new_den));
    Term::abs(rat(), subst::close(&body, "x"))
}

/// `ratDiv : rat → rat → rat` ≡ `x / y = x · y⁻¹` — division as
/// multiplication by the inverse (so `x / 0 = x · 0⁻¹` inherits the
/// junk inverse of `0`).
pub fn rat_div() -> Term {
    let (x, y) = (Term::free("x", rat()), Term::free("y", rat()));
    let inv_y = Term::app(rat_inv(), y.clone());
    let body = Term::app(Term::app(rat_mul(), x.clone()), inv_y);
    Term::abs(
        rat(),
        subst::close(&Term::abs(rat(), subst::close(&body, "y")), "x"),
    )
}

// ============================================================================
// On-the-nose proof machinery (`add_comm` / `mul_comm`)
// ============================================================================
//
// `ratAdd` / `ratMul` are componentwise on representatives, so — exactly as
// `init::int::add_comm` / `mul_comm` commute on the nose over `nat` — their
// commutativity needs no quotient lifting at all: the two representative
// *pairs* are provably equal (numerator by `int::add_comm` / `int::mul_comm`,
// denominator by `int::mul_comm` under the `int.pos` re-wrap), and equal
// representatives give equal classes by pure congruence under `mkRat`. This
// rests only on the **proved** `int` commutativity facts, not on the
// `int` cancellation that `rat_rel_trans` (and the rest of the ring/order
// theory) is blocked on.

/// β-reduce a binary shell op `op = λx y. body` applied to `a`, `b` down to
/// `body[x:=a][y:=b]` *without* descending into the body: returns
/// `⊢ op a b = body[x:=a][y:=b]`. (`reduce` would also fire the `mkRat`
/// redexes inside the body; here we want the un-reduced `mkRat P` form so
/// the congruence lift below can target the representative pair.)
fn binary_beta(op: Term, a: Term, b: Term) -> Result<Thm> {
    let head = Term::app(op, a); // (λx y. body) a
    let applied = Thm::beta_conv(head)?.cong_fn(b)?; // ⊢ op a b = (λy. body_a) b
    let rhs = applied
        .concl()
        .as_eq()
        .ok_or(Error::NotAnEquation)?
        .1
        .clone();
    applied.trans(Thm::beta_conv(rhs)?) // ⊢ op a b = body_a[y:=b]
}

/// From `⊢ n1 = n2` and `⊢ d1 = d2` build `⊢ pair n1 d1 = pair n2 d2` at
/// `int × int.pos` — congruence of the representative pair in both slots.
fn pair_cong(num_eq: Thm, den_eq: Thm) -> Result<Thm> {
    let pair_op = covalence_core::defs::pair(Type::int(), int_pos_ty());
    let d1 = den_eq
        .concl()
        .as_eq()
        .ok_or(Error::NotAnEquation)?
        .0
        .clone();
    // ⊢ pair n1 d1 = pair n2 d1, then ⊢ pair n2 d1 = pair n2 d2.
    let left = num_eq.cong_arg(pair_op)?.cong_fn(d1)?;
    // `pair n2` — the function side to rewrite the denominator under.
    let pair_n2 = left
        .concl()
        .as_eq()
        .ok_or(Error::NotAnEquation)?
        .1
        .as_app()
        .ok_or(Error::NotAnEquation)?
        .0
        .clone();
    let right = den_eq.cong_arg(pair_n2)?;
    left.trans(right)
}

/// Lift `⊢ P = Q` (an equation between representative pairs) to
/// `⊢ mkRat P = mkRat Q` by congruence — `mkRat p = abs (λq. rat_rel p q)`,
/// so equal `p` give equal class-sets and hence equal classes. Reconstructs
/// `quotient::mk_class`'s structure exactly (bound name `_q`).
fn lift_to_class(pq: Thm) -> Result<Thm> {
    let q = Term::free("_q", ip_pair());
    let pointwise = pq.cong_arg(rat_rel())?.cong_fn(q)?; // ⊢ rat_rel P _q = rat_rel Q _q
    let classes = pointwise.abs("_q", ip_pair())?; // ⊢ (λ_q. rat_rel P _q) = (λ_q. rat_rel Q _q)
    classes.cong_arg(Term::spec_abs(rat_spec(), Vec::new())) // ⊢ mkRat P = mkRat Q
}

/// `int.pos` re-wrap as a *function* — the `f` for `cong_arg` when rewriting
/// underneath `to_pos`.
fn to_pos_fn() -> Term {
    Term::spec_abs(int_pos_spec(), Vec::new())
}

// ============================================================================
// Quotient-lifting machinery for the ring axioms
// ============================================================================
//
// The rat analogue of `init::int`'s `recon` + MK-component layer + per-op
// computation/well-definedness rules. Each `rat` op picks representative
// pairs, computes on the `int` numerator / `int.pos` denominator components,
// and re-quotients. Op denominators are re-wrapped via `to_pos`
// (= `abs : int → int.pos`); simplifying a result denominator back to its
// `int` value uses the **postulated** `int.pos` product round-trip below
// (pending `int.pos` positivity in `init::int`).

/// `(0, 1) : int × int.pos` — base witness for `recon`'s non-emptiness side.
fn ip_witness() -> Term {
    ip(izero(), one_pos())
}

/// **Quotient induction.** `⊢ a = mk_rat (rep_pair a)` for any `a : rat`.
fn rat_recon(a: &Term) -> Result<Thm> {
    crate::init::quotient::recon(
        &rat_spec(),
        &[],
        &ip_pair(),
        &rat_rel(),
        &rat_rel_refl(),
        &rat_rel_symm(),
        &rat_rel_trans(),
        &ip_witness(),
        a,
    )
}

/// `⊢ rat_rel p (rep_pair (mk_rat p))` — the chosen representative of `[p]`
/// is `~`-related to `p`.
fn round_trip(p: &Term) -> Result<Thm> {
    crate::init::quotient::round_trip(&rat_spec(), &[], &ip_pair(), &rat_rel(), &rat_rel_refl(), p)
}

/// `MK(f, d) ≔ mk_rat (pair f d)` for `f : int`, `d : int.pos`.
fn mkfs(f: &Term, d: &Term) -> Term {
    mk_rat(&ip(f.clone(), d.clone()))
}
/// `fst (rep_pair a) : int` — the numerator component of `a`'s representative.
fn rfst(a: &Term) -> Term {
    num(&rep_pair(a.clone()))
}
/// `snd (rep_pair a) : int.pos` — the denominator component.
fn rden(a: &Term) -> Term {
    den_pos(&rep_pair(a.clone()))
}

/// **Reconstruction in component form.** `⊢ a = MK(fst(rep_pair a),
/// snd(rep_pair a))` — `recon` followed by surjective pairing of the
/// representative.
fn recon_mk(a: &Term) -> Result<Thm> {
    let rp = rep_pair(a.clone());
    let surj = crate::init::prod::surjective_pairing(&Type::int(), &int_pos_ty(), &rp)?; // pair(fst rp)(snd rp) = rp
    rat_recon(a)?.rhs_conv(|t| t.rw_all(&surj.sym()?))
}

/// Parse a `rat_rel x y` application into `(x, y)`.
fn dest_rel_app(t: &Term) -> Result<(Term, Term)> {
    let (rel_x, y) = t.as_app().ok_or(Error::NotAnEquation)?;
    let (_rel, x) = rel_x.as_app().ok_or(Error::NotAnEquation)?;
    Ok((x.clone(), y.clone()))
}

/// Split an equation theorem `⊢ l = r` into `(l, r)`.
fn dest_eq(thm: &Thm) -> Result<(Term, Term)> {
    let (l, r) = thm.concl().as_eq().ok_or(Error::NotAnEquation)?;
    Ok((l.clone(), r.clone()))
}

/// From `MK(f, d) = mk_rat(ip f d)`, read off `(f, d)`.
fn mk_components(mk: &Term) -> Result<(Term, Term)> {
    let lam = mk.as_app().ok_or(Error::NotAnEquation)?.1.clone(); // λ_q. rat_rel (ip f d) _q
    let body = lam.as_abs().ok_or(Error::NotAnEquation)?.1.clone(); // rat_rel (ip f d) #0
    let rel_p = body.as_app().ok_or(Error::NotAnEquation)?.0.clone(); // rat_rel (ip f d)
    let p = rel_p.as_app().ok_or(Error::NotAnEquation)?.1.clone(); // ip f d
    let (pair_f, d) = p.as_app().ok_or(Error::NotAnEquation)?;
    let f = pair_f.as_app().ok_or(Error::NotAnEquation)?.1.clone();
    Ok((f, d.clone()))
}

/// `⊢ (a·b)·(c·d) = (a·c)·(b·d)` on `int` (assoc/comm interchange).
fn imul_interchange(a: &Term, b: &Term, c: &Term, d: &Term) -> Result<Thm> {
    let s1 = int::mul_assoc()
        .all_elim(a.clone())?
        .all_elim(b.clone())?
        .all_elim(imul(c.clone(), d.clone()))?; // (a·b)·(c·d) = a·(b·(c·d))
    let inner = int::mul_assoc()
        .all_elim(b.clone())?
        .all_elim(c.clone())?
        .all_elim(d.clone())?
        .sym()? // b·(c·d) = (b·c)·d
        .trans(mul_r(
            int::mul_comm().all_elim(b.clone())?.all_elim(c.clone())?,
            d,
        )?)? // = (c·b)·d
        .trans(
            int::mul_assoc()
                .all_elim(c.clone())?
                .all_elim(b.clone())?
                .all_elim(d.clone())?,
        )?; // = c·(b·d)
    let s2 = inner.cong_arg(Term::app(int::int_mul(), a.clone()))?; // a·(b·(c·d)) = a·(c·(b·d))
    let s3 = int::mul_assoc()
        .all_elim(a.clone())?
        .all_elim(c.clone())?
        .all_elim(imul(b.clone(), d.clone()))?
        .sym()?; // a·(c·(b·d)) = (a·c)·(b·d)
    s1.trans(s2)?.trans(s3)
}

/// `⊢ a·b = a'·b'` from `⊢ a = a'` and `⊢ b = b'` (int product congruence).
fn imul_cong(ea: Thm, eb: Thm) -> Result<Thm> {
    Thm::refl(int::int_mul())?.cong_app(ea)?.cong_app(eb)
}

/// `⊢ ∀a b:int.pos. rep(to_pos(rep a · rep b)) = rep a · rep b` — products of
/// positive denominators round-trip through `int.pos`, **proved** in
/// [`int::int_pos_prod_rt`] (`0 < rep a · rep b`, so the wrapper is faithful).
fn pos_prod_rt() -> Thm {
    int::int_pos_prod_rt()
}

/// `⊢ rep(one_pos) = 1` — the canonical denominator `1` round-trips,
/// **proved** in [`int::int_pos_one_rt`] (`0 < 1`).
fn one_pos_rt() -> Thm {
    int::int_pos_one_rt()
}

/// `⊢ rep(to_pos(den x · den y)) = den x · den y` — [`pos_prod_rt`] at the
/// `int.pos` denominators of the representative pairs `x`, `y` (`den_pos =
/// snd`, and `den = rep ∘ snd` lines up).
fn den_prod_rt(x: &Term, y: &Term) -> Result<Thm> {
    pos_prod_rt().all_elim(den_pos(x))?.all_elim(den_pos(y))
}

/// `⊢ t = t'` applying each `eqs[i]` (`rw_all`) to the running RHS in turn.
fn rewrite_seq(t: &Term, eqs: &[Thm]) -> Result<Thm> {
    let mut acc = Thm::refl(t.clone())?;
    for eq in eqs {
        let cur = acc.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone();
        acc = acc.trans(cur.rw_all(eq)?)?;
    }
    Ok(acc)
}

/// `⊢ rat_rel (ip a1 a2) (ip b1 b2)` from the cross-multiplication fact
/// `g : ⊢ a1 · rep b2 = b1 · rep a2` (`a2`, `b2 : int.pos`). Bridges the
/// `rat_rel` body's stuck `fst`/`snd` via the proven prod projections.
fn rel_of_pairs(a1: &Term, a2: &Term, b1: &Term, b2: &Term, g: Thm) -> Result<Thm> {
    let (i, pp) = (Type::int(), int_pos_ty());
    let app = rel_app(&ip(a1.clone(), a2.clone()), &ip(b1.clone(), b2.clone()));
    let beta = app.reduce()?; // ⊢ app = (fst pa · rep(snd pb) = fst pb · rep(snd pa))
    let br = beta.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone();
    let projs = [
        crate::init::prod::fst_pair(&i, &pp, a1, a2)?,
        crate::init::prod::snd_pair(&i, &pp, b1, b2)?,
        crate::init::prod::fst_pair(&i, &pp, b1, b2)?,
        crate::init::prod::snd_pair(&i, &pp, a1, a2)?,
    ];
    let proj_eq = rewrite_seq(&br, &projs)?; // ⊢ br = (a1·rep b2 = b1·rep a2)
    beta.trans(proj_eq)?.sym()?.eq_mp(g)
}

/// **Multiplicative well-definedness.** From `⊢ rat_rel x x'`, `⊢ rat_rel
/// y y'` conclude `⊢ rat_rel (mul_pair x y) (mul_pair x' y')`. Clean `int`
/// interchange: `(nx·ny)·(dx'·dy') = (nx·dx')·(ny·dy') = (nx'·dx)·(ny'·dy)
/// = (nx'·ny')·(dx·dy)` (hypotheses substituted in the middle), over the
/// round-tripped denominators.
fn mul_pair_cong(h1: Thm, h2: Thm) -> Result<Thm> {
    let (x, xp) = dest_rel_app(h1.concl())?;
    let (y, yp) = dest_rel_app(h2.concl())?;
    let e1 = reduce_rel(h1)?; // nx·dx' = nx'·dx
    let e2 = reduce_rel(h2)?; // ny·dy' = ny'·dy
    let (nx, dx, nxp, dxp) = (num(&x), den(&x), num(&xp), den(&xp));
    let (ny, dy, nyp, dyp) = (num(&y), den(&y), num(&yp), den(&yp));

    let g_clean = imul_interchange(&nx, &ny, &dxp, &dyp)? // (nx·ny)·(dx'·dy') = (nx·dx')·(ny·dy')
        .trans(imul_cong(e1, e2)?)? // = (nx'·dx)·(ny'·dy)
        .trans(imul_interchange(&nxp, &dx, &nyp, &dy)?)?; // = (nx'·ny')·(dx·dy)

    // Re-introduce round-tripped denominators on each side.
    let rt_xy = den_prod_rt(&x, &y)?; // rep(to_pos(dx·dy)) = dx·dy
    let rt_xpyp = den_prod_rt(&xp, &yp)?; // rep(to_pos(dx'·dy')) = dx'·dy'
    let g = g_clean
        .lhs_conv(|t| t.rw_all(&rt_xpyp.sym()?))? // dx'·dy' ↦ rep(to_pos(dx'·dy'))
        .rhs_conv(|t| t.rw_all(&rt_xy.sym()?))?; // dx·dy ↦ rep(to_pos(dx·dy))

    rel_of_pairs(
        &imul(nx, ny),
        &to_pos(imul(dx, dy)),
        &imul(nxp, nyp),
        &to_pos(imul(dxp, dyp)),
        g,
    )
}

/// **Multiplicative computation rule.** `⊢ ratMul (mk_rat p) (mk_rat q) =
/// mk_rat (mul_pair p q)`.
fn mul_class(p: &Term, q: &Term) -> Result<Thm> {
    let (mp, mq) = (mk_rat(p), mk_rat(q));
    let dl = binary_beta(rat_mul(), mp.clone(), mq.clone())?; // = mk_rat(mul_pair RPp RPq)
    // Read the chosen representatives from `round_trip` (capture-safe), so
    // they match `binary_beta`'s; reconstructing via `rep_pair(mk_rat p)`
    // would capture a free `p`.
    let (rt_p, rt_q) = (round_trip(p)?, round_trip(q)?); // rat_rel p RPp, rat_rel q RPq
    let (_, rpp) = dest_rel_app(rt_p.concl())?;
    let (_, rpq) = dest_rel_app(rt_q.concl())?;
    let rpp_p = rat_rel_symm()
        .all_elim(p.clone())?
        .all_elim(rpp.clone())?
        .imp_elim(rt_p)?; // rat_rel RPp p
    let rpq_q = rat_rel_symm()
        .all_elim(q.clone())?
        .all_elim(rpq.clone())?
        .imp_elim(rt_q)?; // rat_rel RPq q
    let cong = mul_pair_cong(rpp_p, rpq_q)?; // rat_rel (mul_pair RPp RPq)(mul_pair p q)
    let lift = crate::init::quotient::class_intro(
        &rat_spec(),
        &[],
        &ip_pair(),
        &rat_rel_symm(),
        &rat_rel_trans(),
        cong,
    )?;
    dl.trans(lift)
}

/// **Multiplication in component form.** `⊢ ratMul (MK fa da)(MK fb db) =
/// MK (fa·fb) (to_pos(rep da · rep db))`.
fn mul_mk(fa: &Term, da: &Term, fb: &Term, db: &Term) -> Result<Thm> {
    let (pa, pb) = (ip(fa.clone(), da.clone()), ip(fb.clone(), db.clone()));
    let mc = mul_class(&pa, &pb)?;
    let (i, pp) = (Type::int(), int_pos_ty());
    let projs = [
        crate::init::prod::fst_pair(&i, &pp, fa, da)?,
        crate::init::prod::fst_pair(&i, &pp, fb, db)?,
        crate::init::prod::snd_pair(&i, &pp, fa, da)?,
        crate::init::prod::snd_pair(&i, &pp, fb, db)?,
    ];
    mc.rhs_conv(|t| rewrite_seq(t, &projs))
}

/// `⊢ MK f d = MK f' d'` from `⊢ f = f'` and `⊢ d = d'`.
fn mkfs_cong(f_eq: Thm, d_eq: Thm) -> Result<Thm> {
    let (f, d) = (
        f_eq.concl().as_eq().ok_or(Error::NotAnEquation)?.0.clone(),
        d_eq.concl().as_eq().ok_or(Error::NotAnEquation)?.0.clone(),
    );
    rewrite_seq(&mkfs(&f, &d), &[f_eq, d_eq])
}

/// `⊢ ratMul a b = MK (fa·fb) (to_pos(rep da · rep db))`, where `ra : a = MK
/// fa da`, `rb : b = MK fb db`.
fn mul_via_components(ra: &Thm, rb: &Thm) -> Result<Thm> {
    let (_a, ma) = dest_eq(ra)?;
    let (_b, mb) = dest_eq(rb)?;
    let (fa, da) = mk_components(&ma)?;
    let (fb, db) = mk_components(&mb)?;
    Thm::refl(rat_mul())?
        .cong_app(ra.clone())?
        .cong_app(rb.clone())?
        .trans(mul_mk(&fa, &da, &fb, &db)?)
}

// ---- order computation / well-definedness ----

/// `⊢ 0 < den x · den y` — the product of two positive denominators is
/// positive ([`int::int_pos_prod_pos`] at the `int.pos` denominators).
fn den_prod_pos(x: &Term, y: &Term) -> Result<Thm> {
    int::int_pos_prod_pos()
        .all_elim(den_pos(x))?
        .all_elim(den_pos(y))
}

/// `⊢ src = dst` for two `int` `·`-trees that become equal **after** the
/// substitution `g : ⊢ a = b`: normalise `src` to a form containing `a`,
/// apply `g`, then normalise to `dst`. `lhs_grp`/`rhs_grp` are the two
/// `·`-trees over the full leaf multiset that bracket `a` (resp. `b`) — i.e.
/// `src ≡ lhs_grp[…a…]` and `dst ≡ rhs_grp[…b…]` up to `·`-AC.
fn imul_subst(src: &Term, lhs_grp: &Term, g: Thm, rhs_grp: &Term, dst: &Term) -> Result<Thm> {
    int::prove_imul_eq(src, lhs_grp)? // src = lhs_grp
        .trans(g)? // = rhs_grp (the substituted form)
        .trans(int::prove_imul_eq(rhs_grp, dst)?) // = dst
}

/// **Order well-definedness.** From `⊢ rat_rel x x'` and `⊢ rat_rel y y'`
/// conclude `⊢ int.lt (nx·dy)(ny·dx) = int.lt (nx'·dy')(ny'·dx')` — the
/// cross-multiplication comparison is invariant under the choice of
/// representative.
///
/// Scale both arguments by the positive `dx'·dy'` ([`int::lt_mul_pos_iff`]),
/// rearrange each scaled product through the two `rat_rel` equations
/// (`nx·dx' = nx'·dx`, `ny·dy' = ny'·dy`) into the `(…)·(dx·dy)` form (the
/// `·`-AC reshuffles by [`int::prove_imul_eq`]), then unscale by the positive
/// `dx·dy`.
fn lt_pair_cong(h1: Thm, h2: Thm) -> Result<Thm> {
    let (x, xp) = dest_rel_app(h1.concl())?;
    let (y, yp) = dest_rel_app(h2.concl())?;
    let e1 = reduce_rel(h1)?; // nx·dx' = nx'·dx
    let e2 = reduce_rel(h2)?; // ny·dy' = ny'·dy
    let (nx, dx, nxp, dxp) = (num(&x), den(&x), num(&xp), den(&xp));
    let (ny, dy, nyp, dyp) = (num(&y), den(&y), num(&yp), den(&yp));

    let l1 = imul(nx.clone(), dy.clone()); // nx·dy
    let l2 = imul(ny.clone(), dx.clone()); // ny·dx
    let r1 = imul(nxp.clone(), dyp.clone()); // nx'·dy'
    let r2 = imul(nyp.clone(), dxp.clone()); // ny'·dx'

    let c = imul(dxp.clone(), dyp.clone()); // dx'·dy'  (>0)
    let cc = imul(dx.clone(), dy.clone()); // dx·dy   (>0)
    let pos_c = den_prod_pos(&xp, &yp)?; // 0 < dx'·dy'
    let pos_cc = den_prod_pos(&x, &y)?; // 0 < dx·dy

    // int.lt l1 l2 = int.lt (l1·c)(l2·c)   (scale by c).
    let scale = int::lt_mul_pos_iff()
        .all_elim(l1.clone())?
        .all_elim(l2.clone())?
        .all_elim(c.clone())?
        .imp_elim(pos_c)?
        .sym()?; // int.lt l1 l2 = int.lt (l1·c)(l2·c)

    // l1·c = r1·cc   (substitute e1: nx·dx' ↦ nx'·dx).
    let l1c_src = imul(l1.clone(), c.clone());
    let r1cc = imul(r1.clone(), cc.clone());
    let l1c = imul_subst(
        &l1c_src,
        &imul(imul(nx.clone(), dxp.clone()), imul(dy.clone(), dyp.clone())), // (nx·dx')·(dy·dy')
        imul_cong(e1.clone(), Thm::refl(imul(dy.clone(), dyp.clone()))?)?, // = (nx'·dx)·(dy·dy')
        &imul(imul(nxp.clone(), dx.clone()), imul(dy.clone(), dyp.clone())), // (nx'·dx)·(dy·dy')
        &r1cc,
    )?; // l1·c = r1·cc

    // l2·c = r2·cc   (substitute e2: ny·dy' ↦ ny'·dy).
    let l2c_src = imul(l2.clone(), c.clone());
    let r2cc = imul(r2.clone(), cc.clone());
    let l2c = imul_subst(
        &l2c_src,
        &imul(imul(ny.clone(), dyp.clone()), imul(dx.clone(), dxp.clone())), // (ny·dy')·(dx·dx')
        imul_cong(e2.clone(), Thm::refl(imul(dx.clone(), dxp.clone()))?)?, // = (ny'·dy)·(dx·dx')
        &imul(imul(nyp.clone(), dy.clone()), imul(dx.clone(), dxp.clone())), // (ny'·dy)·(dx·dx')
        &r2cc,
    )?; // l2·c = r2·cc

    // int.lt (l1·c)(l2·c) = int.lt (r1·cc)(r2·cc)  (rewrite both args).
    let scaled_eq = scale
        .trans(Thm::refl(int::int_lt())?.cong_app(l1c)?.cong_app(l2c)?)?; // int.lt l1 l2 = int.lt (r1·cc)(r2·cc)

    // int.lt (r1·cc)(r2·cc) = int.lt r1 r2  (unscale by cc).
    let unscale = int::lt_mul_pos_iff()
        .all_elim(r1.clone())?
        .all_elim(r2.clone())?
        .all_elim(cc.clone())?
        .imp_elim(pos_cc)?; // int.lt (r1·cc)(r2·cc) = int.lt r1 r2

    scaled_eq.trans(unscale) // int.lt l1 l2 = int.lt r1 r2
}

/// **Order computation rule.** `⊢ ratLt (mk_rat p) (mk_rat q) =
/// int.lt (num p · den q) (num q · den p)`. β-reduce `ratLt` at the chosen
/// representatives, then rewrite them back to `p`/`q` by [`lt_pair_cong`]
/// (the comparison is representative-invariant).
fn lt_class(p: &Term, q: &Term) -> Result<Thm> {
    let (mp, mq) = (mk_rat(p), mk_rat(q));
    let dl = binary_beta(rat_lt(), mp.clone(), mq.clone())?; // ratLt mp mq = int.lt(n_RPp·d_RPq)(n_RPq·d_RPp)
    let (rt_p, rt_q) = (round_trip(p)?, round_trip(q)?); // rat_rel p RPp, rat_rel q RPq
    let (_, rpp) = dest_rel_app(rt_p.concl())?;
    let (_, rpq) = dest_rel_app(rt_q.concl())?;
    let rpp_p = rat_rel_symm()
        .all_elim(p.clone())?
        .all_elim(rpp.clone())?
        .imp_elim(rt_p)?; // rat_rel RPp p
    let rpq_q = rat_rel_symm()
        .all_elim(q.clone())?
        .all_elim(rpq.clone())?
        .imp_elim(rt_q)?; // rat_rel RPq q
    let cong = lt_pair_cong(rpp_p, rpq_q)?; // int.lt(n_RPp·d_RPq)(n_RPq·d_RPp) = int.lt(np·dq)(nq·dp)
    dl.trans(cong)
}

/// **Order in component form.** `⊢ ratLt a b = int.lt (fa · rep db)(fb · rep da)`,
/// where `ra : a = MK fa da`, `rb : b = MK fb db`. Rewrite `a`/`b` to their `MK`
/// forms, apply [`lt_class`], then resolve the `pair` projections.
fn lt_via_components(ra: &Thm, rb: &Thm) -> Result<Thm> {
    let (_a, ma) = dest_eq(ra)?;
    let (_b, mb) = dest_eq(rb)?;
    let (fa, da) = mk_components(&ma)?;
    let (fb, db) = mk_components(&mb)?;
    let (pa, pb) = (ip(fa.clone(), da.clone()), ip(fb.clone(), db.clone()));
    let lc = lt_class(&pa, &pb)?; // ratLt (mk_rat pa)(mk_rat pb) = int.lt(num pa·den pb)(num pb·den pa)
    let (i, pp) = (Type::int(), int_pos_ty());
    // num/den of the explicit pairs `pa`,`pb` reduce by the prod projections.
    let projs = [
        crate::init::prod::fst_pair(&i, &pp, &fa, &da)?, // fst pa = fa
        crate::init::prod::fst_pair(&i, &pp, &fb, &db)?, // fst pb = fb
        crate::init::prod::snd_pair(&i, &pp, &fa, &da)?, // snd pa = da
        crate::init::prod::snd_pair(&i, &pp, &fb, &db)?, // snd pb = db
    ];
    let lc_clean = lc.rhs_conv(|t| rewrite_seq(t, &projs))?;
    // ratLt a b = ratLt (mk_rat pa)(mk_rat pb), since a = MK fa da = mk_rat pa.
    Thm::refl(rat_lt())?
        .cong_app(ra.clone())?
        .cong_app(rb.clone())?
        .trans(lc_clean)
}

// ---- additive computation / well-definedness ----

/// `⊢ a + b = a' + b'` from `⊢ a = a'`, `⊢ b = b'` (int sum congruence).
fn iadd_cong(ea: Thm, eb: Thm) -> Result<Thm> {
    Thm::refl(int::int_add())?.cong_app(ea)?.cong_app(eb)
}
/// `⊢ w·x = w·y` from `⊢ x = y` (left-multiply by `w` on `int`).
fn imul_l_cong(w: &Term, e: Thm) -> Result<Thm> {
    e.cong_arg(Term::app(int::int_mul(), w.clone()))
}
/// `⊢ (a+b)·c = a·c + b·c` — right distributivity on `int` (from the proved
/// left `distrib` + `mul_comm`).
fn idistrib_r(a: &Term, b: &Term, c: &Term) -> Result<Thm> {
    let comm = int::mul_comm()
        .all_elim(iadd(a.clone(), b.clone()))?
        .all_elim(c.clone())?; // (a+b)·c = c·(a+b)
    let dist = int::distrib()
        .all_elim(c.clone())?
        .all_elim(a.clone())?
        .all_elim(b.clone())?; // c·(a+b) = c·a + c·b
    let ca = int::mul_comm().all_elim(c.clone())?.all_elim(a.clone())?; // c·a = a·c
    let cb = int::mul_comm().all_elim(c.clone())?.all_elim(b.clone())?; // c·b = b·c
    comm.trans(dist)?.trans(iadd_cong(ca, cb)?)
}

/// **Additive well-definedness.** From `⊢ rat_rel x x'`, `⊢ rat_rel y y'`
/// conclude `⊢ rat_rel (add_pair x y) (add_pair x' y')`. Split the numerator
/// product by `idistrib_r`, re-pair the four factors of each summand by
/// `imul_interchange` (+`mul_comm`) substituting the two hypotheses, over the
/// round-tripped denominators.
fn add_pair_cong(h1: Thm, h2: Thm) -> Result<Thm> {
    let (x, xp) = dest_rel_app(h1.concl())?;
    let (y, yp) = dest_rel_app(h2.concl())?;
    let e1 = reduce_rel(h1)?; // nx·dx' = nx'·dx
    let e2 = reduce_rel(h2)?; // ny·dy' = ny'·dy
    let (nx, dx, nxp, dxp) = (num(&x), den(&x), num(&xp), den(&xp));
    let (ny, dy, nyp, dyp) = (num(&y), den(&y), num(&yp), den(&yp));

    let comm = |u: &Term, v: &Term| int::mul_comm().all_elim(u.clone())?.all_elim(v.clone());

    // Term1: (nx·dy)·(dx'·dy') = (nx'·dy')·(dx·dy).
    let t1 = imul_interchange(&nx, &dy, &dxp, &dyp)? // = (nx·dx')·(dy·dy')
        .trans(mul_r(e1.clone(), &imul(dy.clone(), dyp.clone()))?)? // = (nx'·dx)·(dy·dy')
        .trans(imul_l_cong(
            &imul(nxp.clone(), dx.clone()),
            comm(&dy, &dyp)?,
        )?)? // = (nx'·dx)·(dy'·dy)
        .trans(imul_interchange(&nxp, &dx, &dyp, &dy)?)?; // = (nx'·dy')·(dx·dy)

    // Term2: (ny·dx)·(dx'·dy') = (ny'·dx')·(dx·dy).
    let t2 = imul_l_cong(&imul(ny.clone(), dx.clone()), comm(&dxp, &dyp)?)? // = (ny·dx)·(dy'·dx')
        .trans(imul_interchange(&ny, &dx, &dyp, &dxp)?)? // = (ny·dy')·(dx·dx')
        .trans(mul_r(e2.clone(), &imul(dx.clone(), dxp.clone()))?)? // = (ny'·dy)·(dx·dx')
        .trans(imul_l_cong(
            &imul(nyp.clone(), dy.clone()),
            comm(&dx, &dxp)?,
        )?)? // = (ny'·dy)·(dx'·dx)
        .trans(imul_interchange(&nyp, &dy, &dxp, &dx)?)? // = (ny'·dx')·(dy·dx)
        .trans(imul_l_cong(
            &imul(nyp.clone(), dxp.clone()),
            comm(&dy, &dx)?,
        )?)?; // = (ny'·dx')·(dx·dy)

    let (p1, p2) = (imul(nx.clone(), dy.clone()), imul(ny.clone(), dx.clone()));
    let (q1, q2) = (
        imul(nxp.clone(), dyp.clone()),
        imul(nyp.clone(), dxp.clone()),
    );
    let split_l = idistrib_r(&p1, &p2, &imul(dxp.clone(), dyp.clone()))?;
    let split_r = idistrib_r(&q1, &q2, &imul(dx.clone(), dy.clone()))?;
    let g_clean = split_l.trans(iadd_cong(t1, t2)?)?.trans(split_r.sym()?)?;

    let rt_xy = den_prod_rt(&x, &y)?; // rep(to_pos(dx·dy)) = dx·dy
    let rt_xpyp = den_prod_rt(&xp, &yp)?;
    let g = g_clean
        .lhs_conv(|t| t.rw_all(&rt_xpyp.sym()?))?
        .rhs_conv(|t| t.rw_all(&rt_xy.sym()?))?;

    rel_of_pairs(
        &iadd(imul(nx, dy.clone()), imul(ny, dx.clone())),
        &to_pos(imul(dx, dy)),
        &iadd(imul(nxp, dyp.clone()), imul(nyp, dxp.clone())),
        &to_pos(imul(dxp, dyp)),
        g,
    )
}

/// **Additive computation rule.** `⊢ ratAdd (mk_rat p) (mk_rat q) =
/// mk_rat (add_pair p q)`.
fn add_class(p: &Term, q: &Term) -> Result<Thm> {
    let (mp, mq) = (mk_rat(p), mk_rat(q));
    let dl = binary_beta(rat_add(), mp.clone(), mq.clone())?;
    let (rt_p, rt_q) = (round_trip(p)?, round_trip(q)?);
    let (_, rpp) = dest_rel_app(rt_p.concl())?;
    let (_, rpq) = dest_rel_app(rt_q.concl())?;
    let rpp_p = rat_rel_symm()
        .all_elim(p.clone())?
        .all_elim(rpp)?
        .imp_elim(rt_p)?;
    let rpq_q = rat_rel_symm()
        .all_elim(q.clone())?
        .all_elim(rpq)?
        .imp_elim(rt_q)?;
    let cong = add_pair_cong(rpp_p, rpq_q)?;
    let lift = crate::init::quotient::class_intro(
        &rat_spec(),
        &[],
        &ip_pair(),
        &rat_rel_symm(),
        &rat_rel_trans(),
        cong,
    )?;
    dl.trans(lift)
}

/// **Addition in component form.** `⊢ ratAdd (MK fa da)(MK fb db) =
/// MK (fa·rep db + fb·rep da) (to_pos(rep da · rep db))`.
fn add_mk(fa: &Term, da: &Term, fb: &Term, db: &Term) -> Result<Thm> {
    let (pa, pb) = (ip(fa.clone(), da.clone()), ip(fb.clone(), db.clone()));
    let ac = add_class(&pa, &pb)?;
    let (i, pp) = (Type::int(), int_pos_ty());
    let projs = [
        crate::init::prod::fst_pair(&i, &pp, fa, da)?,
        crate::init::prod::fst_pair(&i, &pp, fb, db)?,
        crate::init::prod::snd_pair(&i, &pp, fa, da)?,
        crate::init::prod::snd_pair(&i, &pp, fb, db)?,
    ];
    ac.rhs_conv(|t| rewrite_seq(t, &projs))
}

/// `⊢ ratAdd a b = MK (fa·rep db + fb·rep da) (to_pos(rep da · rep db))`,
/// from `ra : a = MK fa da`, `rb : b = MK fb db`.
fn add_via_components(ra: &Thm, rb: &Thm) -> Result<Thm> {
    let (_a, ma) = dest_eq(ra)?;
    let (_b, mb) = dest_eq(rb)?;
    let (fa, da) = mk_components(&ma)?;
    let (fb, db) = mk_components(&mb)?;
    Thm::refl(rat_add())?
        .cong_app(ra.clone())?
        .cong_app(rb.clone())?
        .trans(add_mk(&fa, &da, &fb, &db)?)
}

/// `⊢ ratNeg a = MK(int_neg(fst(rep_pair a)), snd(rep_pair a))` — negation in
/// component form. Pure β: `ratNeg` operates on the single representative
/// `rep_pair a` (negating the numerator, keeping the denominator), the same
/// representative `recon_mk a` uses, so no well-definedness is needed.
fn neg_via_components(a: &Term) -> Result<Thm> {
    Thm::beta_conv(Term::app(rat_neg(), a.clone()))
}

// ============================================================================
// `rat.cov` seam — named operators + ∀-quantified quotient-lift givens
// ============================================================================
//
// The `.cov` port (below) proves the rat commutative-ring laws over a
// `ratprim` env of GIVENS, exactly as `set.cov` works over `setprim` and
// `nat.cov` over `natrec`. The givens are the quotient seam — the rat analogue
// of int's: they package the heavy `recon`/component-computation/`class_intro`
// machinery into first-order `∀`-quantified lemmas the `.cov` proof can
// `all-elim`/`rw`/`trans` over, never itself mentioning abs/rep. They rest
// only on the **proved** int commutativity/associativity facts plus the same
// int round-trip stubs the Rust proofs use (`pos_prod_rt` / `one_pos_rt`).
//
// Named ops exposed to `.cov`:
//   rat.add rat.mul rat.neg rat.sub rat.lt rat.le rat.zero rat.one
//   rat.MK    : int → int.pos → rat        — `mkfs` as a closed λ
//   rat.num   : rat → int                  — `rfst` (numerator of the ε-rep)
//   rat.den   : rat → int.pos              — `rden_pos` (denominator of the rep)
//   rat.rep   : int.pos → int              — the int.pos carrier coercion
//   rat.topos : int → int.pos              — the int.pos re-wrap (`to_pos`)
//   int.add int.mul int.neg                — the int ops the components live in

/// `rat.MK ≔ λ(f:int)(d:int.pos). mk_rat (pair f d)` — the component
/// constructor as a closed term (so `.cov` can name it).
fn mk_op() -> Term {
    let (f, d) = (Term::free("f", Type::int()), Term::free("d", int_pos_ty()));
    let body = mkfs(&f, &d);
    Term::abs(
        Type::int(),
        subst::close(&Term::abs(int_pos_ty(), subst::close(&body, "d")), "f"),
    )
}

/// `rat.num ≔ λa. fst (rep_pair a)` — the numerator projection.
fn num_op() -> Term {
    let a = rvar("a");
    Term::abs(rat(), subst::close(&rfst(&a), "a"))
}

/// `rat.den ≔ λa. snd (rep_pair a)` — the (positive) denominator projection.
fn den_op() -> Term {
    let a = rvar("a");
    Term::abs(rat(), subst::close(&rden(&a), "a"))
}

/// `rat.rep` — the `int.pos → int` carrier coercion.
fn rep_op() -> Term {
    Term::spec_rep(int_pos_spec(), Vec::new())
}

/// `rat.topos` — the `int → int.pos` re-wrap (`to_pos`).
fn topos_op() -> Term {
    to_pos_fn()
}

fn mk_app(f: &Term, d: &Term) -> Term {
    Term::app(Term::app(mk_op(), f.clone()), d.clone())
}
fn rep_app_pos(d: &Term) -> Term {
    Term::app(rep_op(), d.clone())
}
/// `rat.num a` / `rat.den a` as *unreduced* named-op applications — the form
/// the `.cov` proofs write (and that the seam givens are phrased over).
fn num_app(a: &Term) -> Term {
    Term::app(num_op(), a.clone())
}
fn den_app(a: &Term) -> Term {
    Term::app(den_op(), a.clone())
}

/// `⊢ rat.MK f d = mkfs f d` — β-unfold `rat.MK` to the raw class form the
/// component lemmas are stated in. Used to bridge the named op and the
/// `mkfs`/`mk_class` internals.
fn mk_unfold(f: &Term, d: &Term) -> Result<Thm> {
    binary_beta(mk_op(), f.clone(), d.clone())
}

/// `⊢ ∀a. a = rat.MK (rat.num a) (rat.den a)` — quotient induction in named
/// component form (the `.cov` `recon` given). The `rat.num a` / `rat.den a`
/// are kept as **unreduced** named-op applications so the `.cov` proofs can
/// feed them verbatim into `add_mk` / `mul_mk` / `class_eq`.
fn recon_given() -> Result<Thm> {
    let a = rvar("a");
    let rm = recon_mk(&a)?; // a = mkfs (rfst a) (rden a)
    // Target: a = rat.MK (num_op a) (den_op a). Reduce that target's RHS down
    // to the `mkfs (rfst a)(rden a)` form `recon_mk` produced, then chain.
    let target_rhs = mk_app(&num_app(&a), &den_app(&a));
    let red = target_rhs.reduce()?; // rat.MK (num a)(den a) = mkfs (rfst a)(rden a)
    rm.trans(red.sym()?)?.all_intro("a", rat())
}

/// Build a `∀f1 d1 f2 d2. lhs = rhs` given from a binary component lemma that,
/// given free `(f1:int, d1:int.pos, f2:int, d2:int.pos)`, returns
/// `⊢ op (MK f1 d1) (MK f2 d2) = MK <num> <den>` — re-folding the raw `mkfs`
/// occurrences to the named `rat.MK`.
fn binop_mk_given(
    mk: impl Fn(&Term, &Term, &Term, &Term) -> Result<Thm>,
) -> Result<Thm> {
    let (f1, d1) = (ivar("f1"), Term::free("d1", int_pos_ty()));
    let (f2, d2) = (ivar("f2"), Term::free("d2", int_pos_ty()));
    // The Rust component lemma operates on `mkfs` arguments; restate it with
    // `rat.MK` on both the inputs and the output.
    let raw = mk(&f1, &d1, &f2, &d2)?; // op (mkfs f1 d1)(mkfs f2 d2) = mkfs N D
    let in1 = mk_unfold(&f1, &d1)?; // rat.MK f1 d1 = mkfs f1 d1
    let in2 = mk_unfold(&f2, &d2)?;
    // op (rat.MK f1 d1)(rat.MK f2 d2) = op (mkfs f1 d1)(mkfs f2 d2)
    let lhs = Thm::refl(op_head(raw.concl())?)?
        .cong_app(in1)?
        .cong_app(in2)?;
    let (n, d) = mk_components(&dest_eq(&raw)?.1)?;
    let out = mk_unfold(&n, &d)?.sym()?; // mkfs N D = rat.MK N D
    lhs.trans(raw)?
        .trans(out)?
        .all_intro("d2", int_pos_ty())?
        .all_intro("f2", Type::int())?
        .all_intro("d1", int_pos_ty())?
        .all_intro("f1", Type::int())
}

/// The binary operator head `op` of an equation `⊢ op _ _ = _`.
fn op_head(concl: &Term) -> Result<Term> {
    let (l, _r) = concl.as_eq().ok_or(Error::NotAnEquation)?;
    let (op_a, _b) = l.as_app().ok_or(Error::NotAnEquation)?;
    let (op, _a) = op_a.as_app().ok_or(Error::NotAnEquation)?;
    Ok(op.clone())
}

/// `⊢ ∀f1 d1 f2 d2. rat.add (rat.MK f1 d1)(rat.MK f2 d2)
///        = rat.MK (f1·rep d2 + f2·rep d1) (topos(rep d1 · rep d2))`.
fn add_mk_given() -> Result<Thm> {
    binop_mk_given(add_mk)
}
/// `⊢ ∀f1 d1 f2 d2. rat.mul (rat.MK f1 d1)(rat.MK f2 d2)
///        = rat.MK (f1·f2) (topos(rep d1 · rep d2))`.
fn mul_mk_given() -> Result<Thm> {
    binop_mk_given(mul_mk)
}

/// `⊢ ∀f d. rat.neg (rat.MK f d) = rat.MK (int.neg f) d`.
fn neg_mk_given() -> Result<Thm> {
    let (f, d) = (ivar("f"), Term::free("d", int_pos_ty()));
    let mkfd = mk_app(&f, &d);
    // neg (rat.MK f d) = neg (mkfs f d)  [unfold the input]
    let unfold_in = Thm::refl(rat_neg())?.cong_app(mk_unfold(&f, &d)?)?;
    let raw = neg_via_components(&mkfs(&f, &d))?; // neg (mkfs f d) = mkfs (int.neg (num (rep_pair(mkfs f d)))) …
    // `neg_via_components` reps a fresh `mkfs f d`; rather than chase its rep,
    // state neg_mk directly from the on-paper law via `add_mk`'s sibling: the
    // representative of `mkfs f d` is `~`-related to `(f, d)`, and `ratNeg`
    // negates the numerator keeping the denominator. We instead expose the
    // *defining* β-fact, which is what the Rust `add_neg` proof consumes.
    let _ = (mkfd, unfold_in, raw);
    // The Rust `add_neg` proof uses `neg_via_components(&a)` on the *variable*
    // `a`, not on a `mkfs`, so the `.cov` `add_neg` port mirrors that by
    // `recon`-then-neg. Expose the raw β-fact `∀a. neg a = mkfs (int.neg (num
    // (rep_pair a))) (snd (rep_pair a))` re-folded to named ops.
    let a = rvar("a");
    let nv = neg_via_components(&a)?; // neg a = mkfs (int.neg (rfst a)) (rden a)
    let (n, dd) = mk_components(&dest_eq(&nv)?.1)?;
    let fold = mk_unfold(&n, &dd)?.sym()?;
    nv.trans(fold)?.all_intro("a", rat())
}

/// `⊢ rat.zero = rat.MK 0 one_pos` and `⊢ rat.one = rat.MK 1 one_pos`.
fn zero_given() -> Result<Thm> {
    let mk = mk_unfold(&izero(), &one_pos())?.sym()?; // mkfs 0 one_pos = rat.MK 0 one_pos
    Thm::refl(rat_zero())?.trans(mk) // rat_zero = mkfs 0 one_pos = rat.MK 0 one_pos
}
fn one_given() -> Result<Thm> {
    let mk = mk_unfold(&Term::int_lit(1i128), &one_pos())?.sym()?;
    Thm::refl(rat_one())?.trans(mk)
}

/// `⊢ ∀f1 d1 f2 d2. (f1 · rep d2 = f2 · rep d1) ⟹ rat.MK f1 d1 = rat.MK f2 d2`
/// — the quotient class-equality law (cross-multiplication ⟹ equal classes),
/// the `.cov` `class_eq` given. Internally: `rel_of_pairs` + `class_intro`.
fn class_eq_given() -> Result<Thm> {
    let (f1, d1) = (ivar("f1"), Term::free("d1", int_pos_ty()));
    let (f2, d2) = (ivar("f2"), Term::free("d2", int_pos_ty()));
    let cross = imul(f1.clone(), rep_app_pos(&d2))
        .equals(imul(f2.clone(), rep_app_pos(&d1)))
        .expect("class_eq: cross-mult body");
    let g = Thm::assume(cross.clone())?;
    let rel = rel_of_pairs(&f1, &d1, &f2, &d2, g)?; // rat_rel (ip f1 d1)(ip f2 d2)
    let cls = crate::init::quotient::class_intro(
        &rat_spec(),
        &[],
        &ip_pair(),
        &rat_rel_symm(),
        &rat_rel_trans(),
        rel,
    )?; // mk_rat(ip f1 d1) = mk_rat(ip f2 d2)
    // Re-fold the raw `mk_rat(ip …)` classes to `rat.MK …`.
    let l = mk_unfold(&f1, &d1)?.sym()?; // mkfs f1 d1 = rat.MK f1 d1
    let r = mk_unfold(&f2, &d2)?.sym()?;
    let eq = l.sym()?.trans(cls)?.trans(r)?; // rat.MK f1 d1 = rat.MK f2 d2
    eq.imp_intro(&cross)?
        .all_intro("d2", int_pos_ty())?
        .all_intro("f2", Type::int())?
        .all_intro("d1", int_pos_ty())?
        .all_intro("f1", Type::int())
}

/// `⊢ ∀d1 d2:int.pos. rep (topos (rep d1 · rep d2)) = rep d1 · rep d2` — the
/// positive-product round-trip (`pos_prod_rt`), already ∀-quantified.
fn pos_prod_rt_given() -> Thm {
    pos_prod_rt()
}

/// `⊢ rep one_pos = 1` — the canonical denominator round-trip (`one_pos_rt`).
fn one_pos_rt_given() -> Thm {
    one_pos_rt()
}

/// `⊢ ∀a b c:int. (a + b) · c = a·c + b·c` — int right-distributivity
/// (`idistrib_r`: from the proved left `int.distrib` + `int.mul_comm`), the
/// `.cov` `int_distrib_r` given. Lets `add_neg`'s numerator factor out
/// `rep(den a)`.
fn int_distrib_r_given() -> Result<Thm> {
    let (a, b, c) = (ivar("a"), ivar("b"), ivar("c"));
    idistrib_r(&a, &b, &c)?
        .all_intro("c", Type::int())?
        .all_intro("b", Type::int())?
        .all_intro("a", Type::int())
}

/// `⊢ ∀d:int.pos. 0 · rep d = 0` — left-zero on a positive denominator
/// (`int_mul_comm` + `int_mul_zero`), the `.cov` `zero_times` given. Lets the
/// `mul_zero` / `add_neg` cross-multiplications collapse both sides to `0`.
fn zero_times_given() -> Result<Thm> {
    let d = Term::free("d", int_pos_ty());
    let repd = rep_app_pos(&d);
    let body = int::mul_comm()
        .all_elim(izero())?
        .all_elim(repd.clone())? // 0·rep d = rep d·0
        .trans(int::mul_zero().all_elim(repd)?)?; // = 0
    body.all_intro("d", int_pos_ty())
}

/// `⊢ ∀a. rat.lt a a = int.lt (num a · rep(den a)) (num a · rep(den a))` — the
/// reflexive instance of `ratLt` reduced to the `int` comparison on the
/// (single) cross-product, in **named-op** form (the `.cov` `lt_self` given).
fn lt_self_given() -> Result<Thm> {
    let a = rvar("a");
    let red = rlt(a.clone(), a.clone()).reduce()?; // rat.lt a a = int_lt X X (reduced)
    // X (named): num a · rep(den a).
    let xn = imul(num_app(&a), rep_app_pos(&den_app(&a)));
    let target_rhs = ilt(xn.clone(), xn);
    let red2 = target_rhs.reduce()?; // int.lt (named X X) = int_lt X X (reduced)
    red.trans(red2.sym()?)?.all_intro("a", rat())
}

/// `⊢ ∀x. ¬(int.lt x x)` — int strict-order irreflexivity (proved in
/// `init::int`), exposed for the rat `lt_irrefl` port.
fn int_lt_irrefl_given() -> Thm {
    int::lt_irrefl()
}

/// `⊢ ∀d:int.pos. rat.topos (rat.rep d) = d` — the `int.pos` carrier
/// round-trip (`Thm::spec_abs_rep` on the `int_pos` newtype), the unconditional
/// `abs ∘ rep = id` law. Used to collapse a re-wrapped positive denominator
/// back to its `int.pos` value (the `.cov` `topos_rep` given).
fn topos_rep_given() -> Result<Thm> {
    let d = Term::free("d", int_pos_ty());
    Thm::spec_abs_rep(int_pos_spec(), Vec::new(), d.clone())?.all_intro("d", int_pos_ty())
}

/// Rewrite the *reduced* representative projections `fst(rep_pair a)` /
/// `snd(rep_pair a)` in a term back to their **named** `rat.num a` / `rat.den a`
/// forms (β-expansion), so every seam given speaks the same surface the `.cov`
/// proofs write. Returns `⊢ t = t_named`.
fn name_projections(t: &Term, a: &Term) -> Result<Thm> {
    name_projections_over(t, std::slice::from_ref(a))
}

/// [`name_projections`] over several representative variables at once (for the
/// ternary `*_assoc` / `distrib` compute givens, which mention `a`, `b`, `c`).
fn name_projections_over(t: &Term, vars: &[Term]) -> Result<Thm> {
    let mut eqs = Vec::new();
    for v in vars {
        eqs.push(Thm::beta_conv(num_app(v))?.sym()?); // rfst v = num_op v
        eqs.push(Thm::beta_conv(den_app(v))?.sym()?); // rden v = den_op v
    }
    rewrite_seq(t, &eqs)
}

/// Re-fold the raw `mkfs N D` RHS of a `*_via_components`-style theorem
/// `⊢ a <op> e = mkfs N D` to the named `rat.MK N D` (with `N`/`D`'s
/// representative projections renamed to `rat.num a`/`rat.den a`), then
/// ∀-close over `a`. The literal `0`/`1`/`one_pos` sub-terms stay inside the
/// given; the `.cov` proof simplifies them with the int givens (matched by
/// `rw`-unification, never spelled).
fn compute_given(lhs: Thm, a: &Term) -> Result<Thm> {
    let (n, d) = mk_components(&dest_eq(&lhs)?.1)?;
    // mkfs N D = rat.MK N D, then rename the reduced projections inside.
    let fold = mk_unfold(&n, &d)?.sym()?; // mkfs N D = rat.MK N D
    let mk_named = fold.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone();
    let rename = name_projections(&mk_named, a)?; // rat.MK N D = rat.MK N' D'
    lhs.trans(fold)?.trans(rename)?.all_intro("a", rat())
}

/// `⊢ ∀a. a * 1 = rat.MK (num a · 1) (topos(rep(den a) · rep one_pos))`.
fn mul_one_compute() -> Result<Thm> {
    let a = rvar("a");
    compute_given(mul_via_components(&recon_mk(&a)?, &Thm::refl(rat_one())?)?, &a)
}
/// `⊢ ∀a. a + 0 = rat.MK (num a · rep one_pos + 0 · rep(den a))
///                       (topos(rep(den a) · rep one_pos))`.
fn add_zero_compute() -> Result<Thm> {
    let a = rvar("a");
    compute_given(add_via_components(&recon_mk(&a)?, &Thm::refl(rat_zero())?)?, &a)
}
/// `⊢ ∀a. a * 0 = rat.MK (num a · 0) (topos(rep(den a) · rep one_pos))`.
fn mul_zero_compute() -> Result<Thm> {
    let a = rvar("a");
    compute_given(mul_via_components(&recon_mk(&a)?, &Thm::refl(rat_zero())?)?, &a)
}
/// `⊢ ∀a. a + (-a) = rat.MK (num a · rep(den a) + (int.neg(num a)) · rep(den a))
///                          (topos(rep(den a) · rep(den a)))`.
fn add_neg_compute() -> Result<Thm> {
    let a = rvar("a");
    let neg_a = neg_via_components(&a)?; // -a = MK(int.neg(num a))(den a) [raw mkfs]
    compute_given(add_via_components(&recon_mk(&a)?, &neg_a)?, &a)
}

/// Re-fold + name a ternary `⊢ <expr over a,b,c> = mkfs N D` to the named
/// `rat.MK N' D'` form (projections of `a`/`b`/`c` named), ∀-closing `a b c`.
fn compute_given3(lhs: Thm) -> Result<Thm> {
    let (a, b, c) = (rvar("a"), rvar("b"), rvar("c"));
    let (n, d) = mk_components(&dest_eq(&lhs)?.1)?;
    let fold = mk_unfold(&n, &d)?.sym()?; // mkfs N D = rat.MK N D
    let mk_named = fold.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone();
    let rename = name_projections_over(&mk_named, &[a, b, c])?;
    lhs.trans(fold)?
        .trans(rename)?
        .all_intro("c", rat())?
        .all_intro("b", rat())?
        .all_intro("a", rat())
}

/// `⊢ ∀a b c. (a*b)*c = rat.MK ((num a·num b)·num c)
///                              (topos(rep(topos(rep(den a)·rep(den b)))·rep(den c)))`.
fn mul_assoc_lhs_compute() -> Result<Thm> {
    let (a, b, c) = (rvar("a"), rvar("b"), rvar("c"));
    let (ra, rb, rc) = (recon_mk(&a)?, recon_mk(&b)?, recon_mk(&c)?);
    let ab = mul_via_components(&ra, &rb)?;
    compute_given3(mul_via_components(&ab, &rc)?)
}
/// `⊢ ∀a b c. a*(b*c) = rat.MK (num a·(num b·num c))
///                              (topos(rep(den a)·rep(topos(rep(den b)·rep(den c)))))`.
fn mul_assoc_rhs_compute() -> Result<Thm> {
    let (a, b, c) = (rvar("a"), rvar("b"), rvar("c"));
    let (ra, rb, rc) = (recon_mk(&a)?, recon_mk(&b)?, recon_mk(&c)?);
    let bc = mul_via_components(&rb, &rc)?;
    compute_given3(mul_via_components(&ra, &bc)?)
}

/// `⊢ ∀a b c. (a+b)+c = rat.MK <lhsN> <lhsD>` (additive LHS in MK form).
fn add_assoc_lhs_compute() -> Result<Thm> {
    let (a, b, c) = (rvar("a"), rvar("b"), rvar("c"));
    let (ra, rb, rc) = (recon_mk(&a)?, recon_mk(&b)?, recon_mk(&c)?);
    let ab = add_via_components(&ra, &rb)?;
    compute_given3(add_via_components(&ab, &rc)?)
}
/// `⊢ ∀a b c. a+(b+c) = rat.MK <rhsN> <rhsD>` (additive RHS in MK form).
fn add_assoc_rhs_compute() -> Result<Thm> {
    let (a, b, c) = (rvar("a"), rvar("b"), rvar("c"));
    let (ra, rb, rc) = (recon_mk(&a)?, recon_mk(&b)?, recon_mk(&c)?);
    let bc = add_via_components(&rb, &rc)?;
    compute_given3(add_via_components(&ra, &bc)?)
}

/// Name + ∀-close a bridge `⊢ mkfs lN lD = mkfs rN rD` (reduced projections of
/// `a`/`b`/`c`) to `⊢ ∀a b c. rat.MK lN' lD' = rat.MK rN' rD'`.
fn bridge_given3(bridge: Thm) -> Result<Thm> {
    let (a, b, c) = (rvar("a"), rvar("b"), rvar("c"));
    let (lmk, rmk) = dest_eq(&bridge)?;
    let (ln, ld) = mk_components(&lmk)?;
    let (rn, rd) = mk_components(&rmk)?;
    // mkfs … = rat.MK …  on both sides, then name the projections.
    let lfold = mk_unfold(&ln, &ld)?.sym()?; // mkfs lN lD = rat.MK lN lD
    let rfold = mk_unfold(&rn, &rd)?.sym()?;
    let named_l = name_projections_over(
        &lfold.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone(),
        &[a.clone(), b.clone(), c.clone()],
    )?;
    let named_r = name_projections_over(
        &rfold.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone(),
        &[a.clone(), b.clone(), c.clone()],
    )?;
    // rat.MK lN' lD' = mkfs lN lD = mkfs rN rD = rat.MK rN' rD'.
    named_l
        .sym()?
        .trans(lfold.sym()?)?
        .trans(bridge)?
        .trans(rfold)?
        .trans(named_r)?
        .all_intro("c", rat())?
        .all_intro("b", rat())?
        .all_intro("a", rat())
}

/// `⊢ ∀a b c. a*(b+c) = rat.MK <lf> <ld>` (distributivity LHS in MK form).
fn distrib_lhs_compute() -> Result<Thm> {
    let (a, b, c) = (rvar("a"), rvar("b"), rvar("c"));
    let (ra, rb, rc) = (recon_mk(&a)?, recon_mk(&b)?, recon_mk(&c)?);
    let bc = add_via_components(&rb, &rc)?;
    compute_given3(mul_via_components(&ra, &bc)?)
}
/// `⊢ ∀a b c. a*b + a*c = rat.MK <rf> <rd>` (distributivity RHS in MK form).
fn distrib_rhs_compute() -> Result<Thm> {
    let (a, b, c) = (rvar("a"), rvar("b"), rvar("c"));
    let (ra, rb, rc) = (recon_mk(&a)?, recon_mk(&b)?, recon_mk(&c)?);
    let ab = mul_via_components(&ra, &rb)?;
    let ac = mul_via_components(&ra, &rc)?;
    compute_given3(add_via_components(&ab, &ac)?)
}

/// `⊢ ∀a b c. rat.MK <add_assoc lhsN> <lhsD> = rat.MK <rhsN> <rhsD>` — the
/// additive-associativity bridge (the int three-monomial numerator alignment +
/// the `int.pos` denominator round-trips), extracted from `add_assoc_impl`.
fn add_assoc_bridge() -> Result<Thm> {
    bridge_given3(add_assoc_bridge_raw()?)
}

/// `⊢ ∀a b c. rat.MK <mul lhsN> <lhsD> = rat.MK <rhsN> <rhsD>` — the
/// distributivity bridge (the common-factor cross-multiplication lifted by
/// `class_intro`), extracted from `distrib_impl`.
fn distrib_bridge() -> Result<Thm> {
    bridge_given3(distrib_bridge_raw()?)
}

/// The `ratprim` seam environment imported by `rat.cov`.
pub fn rat_env() -> crate::script::Env {
    use crate::script::{ConstDef, Env};
    let mut e = Env::empty();

    // rat operators
    e.define_const("rat.add", ConstDef::Op(rat_add()));
    e.define_const("rat.mul", ConstDef::Op(rat_mul()));
    e.define_const("rat.neg", ConstDef::Op(rat_neg()));
    e.define_const("rat.sub", ConstDef::Op(rat_sub()));
    e.define_const("rat.lt", ConstDef::Op(rat_lt()));
    e.define_const("rat.le", ConstDef::Op(rat_le()));
    e.define_const("rat.zero", ConstDef::Op(rat_zero()));
    e.define_const("rat.one", ConstDef::Op(rat_one()));
    // component layer
    e.define_const("rat.MK", ConstDef::Op(mk_op()));
    e.define_const("rat.num", ConstDef::Op(num_op()));
    e.define_const("rat.den", ConstDef::Op(den_op()));
    e.define_const("rat.rep", ConstDef::Op(rep_op()));
    e.define_const("rat.topos", ConstDef::Op(topos_op()));
    // int ops the components live in
    e.define_const("int.add", ConstDef::Op(int::int_add()));
    e.define_const("int.mul", ConstDef::Op(int::int_mul()));
    e.define_const("int.neg", ConstDef::Op(int::int_neg()));
    e.define_const("int.lt", ConstDef::Op(int::int_lt()));
    // int literal constants the unit/zero proofs spell explicitly.
    e.define_const("int.zero", ConstDef::Op(izero()));
    e.define_const("int.one", ConstDef::Op(Term::int_lit(1i128)));
    // the canonical positive denominator `1 : int.pos` (the `rat.zero`/`rat.one`
    // denominator) — the `mul_zero`/`add_neg` class-equality steps name it.
    e.define_const("rat.one_pos", ConstDef::Op(one_pos()));

    // quotient seam givens
    e.define_lemma("recon", recon_given().expect("rat recon given"));
    e.define_lemma("add_mk", add_mk_given().expect("rat add_mk given"));
    e.define_lemma("mul_mk", mul_mk_given().expect("rat mul_mk given"));
    e.define_lemma("neg_mk", neg_mk_given().expect("rat neg_mk given"));
    e.define_lemma("zero_mk", zero_given().expect("rat zero given"));
    e.define_lemma("one_mk", one_given().expect("rat one given"));
    e.define_lemma("class_eq", class_eq_given().expect("rat class_eq given"));
    e.define_lemma("pos_prod_rt", pos_prod_rt_given());
    e.define_lemma("one_pos_rt", one_pos_rt_given());
    e.define_lemma("zero_times", zero_times_given().expect("rat zero_times given"));
    e.define_lemma("int_distrib_r", int_distrib_r_given().expect("rat int_distrib_r given"));
    e.define_lemma("lt_self", lt_self_given().expect("rat lt_self given"));
    e.define_lemma("int_lt_irrefl", int_lt_irrefl_given());
    e.define_lemma("topos_rep", topos_rep_given().expect("rat topos_rep given"));
    e.define_lemma("mul_one_compute", mul_one_compute().expect("rat mul_one_compute"));
    e.define_lemma("add_zero_compute", add_zero_compute().expect("rat add_zero_compute"));
    e.define_lemma("mul_zero_compute", mul_zero_compute().expect("rat mul_zero_compute"));
    e.define_lemma("add_neg_compute", add_neg_compute().expect("rat add_neg_compute"));
    e.define_lemma("mul_assoc_lhs", mul_assoc_lhs_compute().expect("rat mul_assoc_lhs"));
    e.define_lemma("mul_assoc_rhs", mul_assoc_rhs_compute().expect("rat mul_assoc_rhs"));
    e.define_lemma("add_assoc_lhs", add_assoc_lhs_compute().expect("rat add_assoc_lhs"));
    e.define_lemma("add_assoc_rhs", add_assoc_rhs_compute().expect("rat add_assoc_rhs"));
    e.define_lemma("add_assoc_bridge", add_assoc_bridge().expect("rat add_assoc_bridge"));
    e.define_lemma("distrib_lhs", distrib_lhs_compute().expect("rat distrib_lhs"));
    e.define_lemma("distrib_rhs", distrib_rhs_compute().expect("rat distrib_rhs"));
    e.define_lemma("distrib_bridge", distrib_bridge().expect("rat distrib_bridge"));

    // int ring givens (proved in init::int) — the `.cov` numerator/denominator
    // algebra runs over these.
    e.define_lemma("int_add_comm", int::add_comm());
    e.define_lemma("int_add_assoc", int::add_assoc());
    e.define_lemma("int_add_zero", int::add_zero());
    e.define_lemma("int_add_neg", int::add_neg());
    e.define_lemma("int_mul_comm", int::mul_comm());
    e.define_lemma("int_mul_assoc", int::mul_assoc());
    e.define_lemma("int_mul_one", int::mul_one());
    e.define_lemma("int_mul_zero", int::mul_zero());
    e.define_lemma("int_distrib", int::distrib());

    e
}

// ============================================================================
// Commutative-ring axioms (and the field inverse)
// ============================================================================
//
// `add_comm` / `mul_comm` are **proved** (on the nose, see above). The
// remaining axioms keep the audit-trail style of `init::int`: each is a
// `Thm::assume` carrying its statement as a self-hyp. They are HOL theorems
// of the quotient, derivable from the `int` ordered-ring theory; discharging
// them does not change this public surface. See `SKELETONS.md`.

fn rvar(name: &str) -> Term {
    Term::free(name, rat())
}
#[cfg(test)]
fn radd(a: Term, b: Term) -> Term {
    Term::app(Term::app(rat_add(), a), b)
}
fn rmul(a: Term, b: Term) -> Term {
    Term::app(Term::app(rat_mul(), a), b)
}
fn forall_rat(vars: &[&str], body: Term) -> Term {
    let mut t = body;
    for name in vars.iter().rev() {
        t = t.forall(name, rat()).expect("forall_rat: bind variable");
    }
    t
}

cached_thm! {
    /// `⊢ ∀a b. a + b = b + a` — **proved**. `ratAdd` is componentwise on
    /// representatives (`(a/b)+(c/d) = (a·d+c·b)/(b·d)`), so commutativity
    /// holds *on the nose*: the numerator `a·d+c·b` commutes to `c·b+a·d`
    /// by `int::add_comm`, the denominator `b·d` to `d·b` by
    /// `int::mul_comm`, and equal representative pairs give equal classes
    /// (`lift_to_class`). No quotient lifting, no `int` cancellation.
    pub fn add_comm() -> Thm {
        add_comm_impl().expect("rat::add_comm derivation")
    }
}
fn add_comm_impl() -> Result<Thm> {
    let (a, b) = (rvar("a"), rvar("b"));
    let dl = binary_beta(rat_add(), a.clone(), b.clone())?; // ⊢ a+b = mkRat P
    let dr = binary_beta(rat_add(), b.clone(), a.clone())?; // ⊢ b+a = mkRat Q

    let (pa, pb) = (rep_pair(a.clone()), rep_pair(b.clone()));
    // Numerator: (num pa·den pb) + (num pb·den pa)  commutes.
    let num_eq = int::add_comm()
        .all_elim(imul(num(&pa), den(&pb)))?
        .all_elim(imul(num(&pb), den(&pa)))?;
    // Denominator: (den pa·den pb)  commutes, under the `int.pos` re-wrap.
    let den_eq = int::mul_comm()
        .all_elim(den(&pa))?
        .all_elim(den(&pb))?
        .cong_arg(to_pos_fn())?;
    let mkeq = lift_to_class(pair_cong(num_eq, den_eq)?)?; // ⊢ mkRat P = mkRat Q

    dl.trans(mkeq)?
        .trans(dr.sym()?)?
        .all_intro("b", rat())?
        .all_intro("a", rat())
}

cached_thm! {
    /// `⊢ ∀a b c. (a + b) + c = a + (b + c)` — **proved**. In component form
    /// both sides are `MK(N, to_pos(D))`; the numerators `N` are equal as
    /// `int` polynomials (`distrib_r` to split, `mul_assoc`/`mul_comm` to
    /// align the three monomials `fa·(db·dc)`, `fb·(da·dc)`, `fc·(da·db)`,
    /// `add_assoc` to re-bracket the sum) and the denominators by `mul_assoc`
    /// under `to_pos` (nested `to_pos` via [`pos_prod_rt`]).
    pub fn add_assoc() -> Thm {
        add_assoc_impl().expect("rat::add_assoc")
    }
}
fn add_assoc_impl() -> Result<Thm> {
    let (a, b, c) = (rvar("a"), rvar("b"), rvar("c"));
    let (ra, rb, rc) = (recon_mk(&a)?, recon_mk(&b)?, recon_mk(&c)?);
    let lhs = add_via_components(&add_via_components(&ra, &rb)?, &rc)?;
    let rhs = add_via_components(&ra, &add_via_components(&rb, &rc)?)?;
    let bridge = add_assoc_bridge_raw()?;
    lhs.trans(bridge)?
        .trans(rhs.sym()?)?
        .all_intro("c", rat())?
        .all_intro("b", rat())?
        .all_intro("a", rat())
}

/// The additive-associativity bridge `⊢ mkfs lhsN lhsD = mkfs rhsN rhsD` over
/// the free `a, b, c` (the int three-monomial numerator alignment + the
/// `int.pos` denominator round-trips). Shared by [`add_assoc_impl`] and the
/// `rat.cov` `add_assoc_bridge` seam given.
fn add_assoc_bridge_raw() -> Result<Thm> {
    let (a, b, c) = (rvar("a"), rvar("b"), rvar("c"));
    let (ra, rb, rc) = (recon_mk(&a)?, recon_mk(&b)?, recon_mk(&c)?);
    let ab = add_via_components(&ra, &rb)?;
    let lhs = add_via_components(&ab, &rc)?;
    let bc = add_via_components(&rb, &rc)?;
    let rhs = add_via_components(&ra, &bc)?;

    let (fa, fb, fc) = (rfst(&a), rfst(&b), rfst(&c));
    let (da, db, dc) = (rden(&a), rden(&b), rden(&c));
    let (rda, rdb, rdc) = (
        den(&rep_pair(a.clone())),
        den(&rep_pair(b.clone())),
        den(&rep_pair(c.clone())),
    );
    let comm = |u: &Term, v: &Term| int::mul_comm().all_elim(u.clone())?.all_elim(v.clone());
    let massoc = |u: &Term, v: &Term, w: &Term| {
        int::mul_assoc()
            .all_elim(u.clone())?
            .all_elim(v.clone())?
            .all_elim(w.clone())
    };

    // Round-trip the nested denominators in the extracted numerators.
    let ppab = pos_prod_rt().all_elim(da.clone())?.all_elim(db.clone())?;
    let ppbc = pos_prod_rt().all_elim(db.clone())?.all_elim(dc.clone())?;
    let lhs_f = mk_components(&dest_eq(&lhs)?.1)?.0;
    let rhs_f = mk_components(&dest_eq(&rhs)?.1)?.0;
    let lf_rt = rewrite_seq(&lhs_f, std::slice::from_ref(&ppab))?; // lhs_f = lhs_f'
    let rf_rt = rewrite_seq(&rhs_f, std::slice::from_ref(&ppbc))?; // rhs_f = rhs_f'

    // The three monomials (both sides normalise to N1 + (N2' + N3')).
    let (m1, m2) = (imul(fa.clone(), rdb.clone()), imul(fb.clone(), rda.clone()));
    let cap_m1 = imul(imul(fa.clone(), rdb.clone()), rdc.clone());
    let cap_m2 = imul(imul(fb.clone(), rda.clone()), rdc.clone());
    let cap_m3 = imul(fc.clone(), imul(rda.clone(), rdb.clone()));
    let n1 = imul(fa.clone(), imul(rdb.clone(), rdc.clone()));

    let s_a = idistrib_r(&m1, &m2, &rdc)?; // (fa·rdb + fb·rda)·rdc = M1 + M2
    let lhs_step = iadd_cong(s_a, Thm::refl(cap_m3.clone())?)?; // lhs_f' = (M1+M2)+M3
    let reassoc = int::add_assoc()
        .all_elim(cap_m1.clone())?
        .all_elim(cap_m2.clone())?
        .all_elim(cap_m3.clone())?; // (M1+M2)+M3 = M1+(M2+M3)

    let e_m1 = massoc(&fa, &rdb, &rdc)?; // M1 = fa·(rdb·rdc) = N1
    let e_m2 = massoc(&fb, &rda, &rdc)?; // M2 = fb·(rda·rdc)
    let e_n2 = massoc(&fb, &rdc, &rda)?.trans(imul_l_cong(&fb, comm(&rdc, &rda)?)?)?; // N2 = fb·(rdc·rda) = fb·(rda·rdc)
    let e_n3 = massoc(&fc, &rdb, &rda)?.trans(imul_l_cong(&fc, comm(&rdb, &rda)?)?)?; // N3 = fc·(rdb·rda) = fc·(rda·rdb)
    let mid = iadd_cong(e_m2.trans(e_n2.sym()?)?, e_n3.sym()?)?; // M2+M3 = N2+N3
    let mmm_nnn = iadd_cong(e_m1, mid)?; // M1+(M2+M3) = N1+(N2+N3)

    let s_b = idistrib_r(
        &imul(fb.clone(), rdc.clone()),
        &imul(fc.clone(), rdb.clone()),
        &rda,
    )?; // (fb·rdc+fc·rdb)·rda = N2+N3
    let rhs_step = iadd_cong(Thm::refl(n1)?, s_b)?; // rhs_f' = N1+(N2+N3)

    let fp_eq = lhs_step
        .trans(reassoc)?
        .trans(mmm_nnn)?
        .trans(rhs_step.sym()?)?; // lhs_f' = rhs_f'
    let f_eq = lf_rt.trans(fp_eq)?.trans(rf_rt.sym()?)?; // lhs_f = rhs_f

    // Denominator: same shape as mul_assoc.
    let dl = mk_components(&dest_eq(&lhs)?.1)?.1;
    let assoc_d = massoc(&rda, &rdb, &rdc)?.cong_arg(to_pos_fn())?;
    let assoc_rhs = assoc_d
        .concl()
        .as_eq()
        .ok_or(Error::NotAnEquation)?
        .1
        .clone();
    let d_eq = rewrite_seq(&dl, std::slice::from_ref(&ppab))?
        .trans(assoc_d)?
        .trans(rewrite_seq(&assoc_rhs, &[ppbc.sym()?])?)?;

    mkfs_cong(f_eq, d_eq)
}

cached_thm! {
    /// `⊢ ∀a. a + 0 = a` — **proved**. `0 = MK(0, one_pos)`, so
    /// `a + 0 = MK(fa·rep one_pos + 0·rep da, to_pos(rep da · rep one_pos))`;
    /// the numerator collapses to `fa` (`one_pos_rt` + `int::mul_one` /
    /// `mul_zero` / `add_zero`) and the denominator to `da` (as in `mul_one`).
    pub fn add_zero() -> Thm {
        add_zero_impl().expect("rat::add_zero")
    }
}
fn add_zero_impl() -> Result<Thm> {
    let a = rvar("a");
    let ra = recon_mk(&a)?; // a = MK(fa, da)
    let r0 = Thm::refl(rat_zero())?; // rat_zero = MK(0, one_pos)
    let lhs = add_via_components(&ra, &r0)?;
    let (fa, da) = (rfst(&a), rden(&a));
    let rda = den(&rep_pair(a.clone())); // rep da
    let i0 = Term::int_lit(0i128);

    // Numerator: fa·rep one_pos + 0·rep da = fa.
    let t1 = imul_l_cong(&fa, one_pos_rt())? // fa·rep one_pos = fa·1
        .trans(int::mul_one().all_elim(fa.clone())?)?; // = fa
    let t2 = int::mul_comm()
        .all_elim(i0.clone())?
        .all_elim(rda.clone())? // 0·rep da = rep da·0
        .trans(int::mul_zero().all_elim(rda.clone())?)?; // = 0
    let f_eq = iadd_cong(t1, t2)?.trans(int::add_zero().all_elim(fa)?)?; // = fa

    // Denominator: to_pos(rep da · rep one_pos) = da (same as mul_one).
    let dl = mk_components(&dest_eq(&lhs)?.1)?.1;
    let d_eq = rewrite_seq(&dl, &[one_pos_rt()])?
        .trans(int::mul_one().all_elim(rda)?.cong_arg(to_pos_fn())?)?
        .trans(Thm::spec_abs_rep(int_pos_spec(), Vec::new(), da)?)?;

    let bridge = mkfs_cong(f_eq, d_eq)?;
    lhs.trans(bridge)?.trans(ra.sym()?)?.all_intro("a", rat())
}

cached_thm! {
    /// `⊢ ∀a. a + (-a) = 0` — **proved** (additive inverse). `-a = MK(-fa,
    /// da)` (β), so `a + (-a) = MK(fa·rep da + (-fa)·rep da, …)`; the
    /// numerator is `(fa + -fa)·rep da = 0` (`idistrib_r` + `int::add_neg`),
    /// and `MK(0, to_pos(rep da · rep da)) = 0` by `class_intro` (as in
    /// `mul_zero`).
    pub fn add_neg() -> Thm {
        add_neg_impl().expect("rat::add_neg")
    }
}
fn add_neg_impl() -> Result<Thm> {
    let a = rvar("a");
    let ra = recon_mk(&a)?; // a = MK(fa, da)
    let neg_a = neg_via_components(&a)?; // -a = MK(int_neg fa, da)
    let lhs = add_via_components(&ra, &neg_a)?; // a + (-a) = MK(fa·rda + (-fa)·rda, to_pos(rda·rda))
    let fa = rfst(&a);
    let rda = den(&rep_pair(a.clone())); // rep da
    let nfa = Term::app(int::int_neg(), fa.clone());
    let i0 = Term::int_lit(0i128);

    // Numerator: fa·rda + (-fa)·rda = (fa + -fa)·rda = 0·rda = 0.
    let f_eq = idistrib_r(&fa, &nfa, &rda)?
        .sym()? // fa·rda + (-fa)·rda = (fa + -fa)·rda
        .trans(mul_r(int::add_neg().all_elim(fa)?, &rda)?)? // = 0·rda
        .trans(
            int::mul_comm()
                .all_elim(i0.clone())?
                .all_elim(rda.clone())?
                .trans(int::mul_zero().all_elim(rda.clone())?)?,
        )?; // = rda·0 = 0

    let dl = mk_components(&dest_eq(&lhs)?.1)?.1; // to_pos(rda · rda) : int.pos
    let step = lhs.trans(mkfs_cong(f_eq, Thm::refl(dl.clone())?)?)?; // a+(-a) = MK(0, dl)

    // 0/dl ~ 0/1: cross-mult 0·rep(one_pos) = 0·rep(dl) (both 0).
    let rep = Term::spec_rep(int_pos_spec(), Vec::new());
    let zero_times = |d: Term| -> Result<Thm> {
        int::mul_comm()
            .all_elim(i0.clone())?
            .all_elim(Term::app(rep.clone(), d.clone()))?
            .trans(int::mul_zero().all_elim(Term::app(rep.clone(), d))?)
    };
    let g = zero_times(one_pos())?.trans(zero_times(dl.clone())?.sym()?)?;
    let rel = rel_of_pairs(&i0, &dl, &i0, &one_pos(), g)?;
    let cls = crate::init::quotient::class_intro(
        &rat_spec(),
        &[],
        &ip_pair(),
        &rat_rel_symm(),
        &rat_rel_trans(),
        rel,
    )?;

    step.trans(cls)?.all_intro("a", rat())
}

cached_thm! {
    /// `⊢ ∀a b. a * b = b * a` — **proved**, like [`add_comm`]. `ratMul`
    /// is `(a/b)·(c/d) = (a·c)/(b·d)`; the numerator `a·c` commutes to
    /// `c·a` and the denominator `b·d` to `d·b`, both by `int::mul_comm`,
    /// and equal representatives lift to equal classes.
    pub fn mul_comm() -> Thm {
        mul_comm_impl().expect("rat::mul_comm derivation")
    }
}
fn mul_comm_impl() -> Result<Thm> {
    let (a, b) = (rvar("a"), rvar("b"));
    let dl = binary_beta(rat_mul(), a.clone(), b.clone())?; // ⊢ a*b = mkRat P
    let dr = binary_beta(rat_mul(), b.clone(), a.clone())?; // ⊢ b*a = mkRat Q

    let (pa, pb) = (rep_pair(a.clone()), rep_pair(b.clone()));
    // Numerator num pa·num pb and denominator den pa·den pb each commute.
    let num_eq = int::mul_comm().all_elim(num(&pa))?.all_elim(num(&pb))?;
    let den_eq = int::mul_comm()
        .all_elim(den(&pa))?
        .all_elim(den(&pb))?
        .cong_arg(to_pos_fn())?;
    let mkeq = lift_to_class(pair_cong(num_eq, den_eq)?)?; // ⊢ mkRat P = mkRat Q

    dl.trans(mkeq)?
        .trans(dr.sym()?)?
        .all_intro("b", rat())?
        .all_intro("a", rat())
}

cached_thm! {
    /// `⊢ ∀a b c. (a * b) * c = a * (b * c)` — **proved**. Reconstruct each
    /// rational in component form (`MK(f, d)`), push `ratMul` through to
    /// `MK` of the componentwise int product / `int.pos` denominator, then
    /// close: numerators by `int::mul_assoc`, denominators by `int::mul_assoc`
    /// under `to_pos` (the nested `to_pos` round-trips via [`pos_prod_rt`]).
    pub fn mul_assoc() -> Thm {
        mul_assoc_impl().expect("rat::mul_assoc")
    }
}
fn mul_assoc_impl() -> Result<Thm> {
    let (a, b, c) = (rvar("a"), rvar("b"), rvar("c"));
    let (ra, rb, rc) = (recon_mk(&a)?, recon_mk(&b)?, recon_mk(&c)?);

    // (a·b)·c and a·(b·c) in MK component form.
    let ab = mul_via_components(&ra, &rb)?;
    let lhs = mul_via_components(&ab, &rc)?;
    let bc = mul_via_components(&rb, &rc)?;
    let rhs = mul_via_components(&ra, &bc)?;

    // Components fa : int, da : int.pos; rda = rep da : int.
    let (fa, fb, fc) = (rfst(&a), rfst(&b), rfst(&c));
    let (da, db, dc) = (rden(&a), rden(&b), rden(&c));
    let (rda, rdb, rdc) = (
        den(&rep_pair(a.clone())),
        den(&rep_pair(b.clone())),
        den(&rep_pair(c.clone())),
    );

    // Numerator: (fa·fb)·fc = fa·(fb·fc).
    let f_eq = int::mul_assoc().all_elim(fa)?.all_elim(fb)?.all_elim(fc)?;

    // Denominator (extracted from the two sides, so the shapes line up).
    let dl = mk_components(&dest_eq(&lhs)?.1)?.1; // to_pos(rep(to_pos(rda·rdb))·rdc)
    let ppab = pos_prod_rt().all_elim(da.clone())?.all_elim(db.clone())?; // rep(to_pos(rda·rdb)) = rda·rdb
    let ppbc = pos_prod_rt().all_elim(db)?.all_elim(dc)?; // rep(to_pos(rdb·rdc)) = rdb·rdc
    let assoc_d = int::mul_assoc()
        .all_elim(rda.clone())?
        .all_elim(rdb.clone())?
        .all_elim(rdc.clone())?
        .cong_arg(to_pos_fn())?; // to_pos((rda·rdb)·rdc) = to_pos(rda·(rdb·rdc))
    let assoc_rhs = assoc_d
        .concl()
        .as_eq()
        .ok_or(Error::NotAnEquation)?
        .1
        .clone();
    let d_eq = rewrite_seq(&dl, &[ppab])? // dl = to_pos((rda·rdb)·rdc)
        .trans(assoc_d)? // = to_pos(rda·(rdb·rdc))
        .trans(rewrite_seq(&assoc_rhs, &[ppbc.sym()?])?)?; // = to_pos(rda·rep(to_pos(rdb·rdc)))

    let bridge = mkfs_cong(f_eq, d_eq)?;
    lhs.trans(bridge)?
        .trans(rhs.sym()?)?
        .all_intro("c", rat())?
        .all_intro("b", rat())?
        .all_intro("a", rat())
}

cached_thm! {
    /// `⊢ ∀a. a * 1 = a` — **proved**. `1 = MK(1, one_pos)`, so
    /// `a · 1 = MK(fa·1, to_pos(rep da · rep one_pos)) = MK(fa, da) = a`:
    /// numerator by `int::mul_one`, denominator by `one_pos_rt` + `int::mul_one`
    /// + the unconditional `spec_abs_rep` round-trip.
    pub fn mul_one() -> Thm {
        mul_one_impl().expect("rat::mul_one")
    }
}
fn mul_one_impl() -> Result<Thm> {
    let a = rvar("a");
    let ra = recon_mk(&a)?; // a = MK(fa, da)
    let r1 = Thm::refl(rat_one())?; // rat_one = MK(1, one_pos)
    let lhs = mul_via_components(&ra, &r1)?; // a·1 = MK(fa·1, to_pos(rep da · rep one_pos))
    let (fa, da) = (rfst(&a), rden(&a));
    let rda = den(&rep_pair(a.clone())); // rep da

    let f_eq = int::mul_one().all_elim(fa)?; // fa·1 = fa
    let dl = mk_components(&dest_eq(&lhs)?.1)?.1; // to_pos(rep da · rep one_pos)
    let d_eq = rewrite_seq(&dl, &[one_pos_rt()])? // = to_pos(rep da · 1)
        .trans(int::mul_one().all_elim(rda)?.cong_arg(to_pos_fn())?)? // = to_pos(rep da)
        .trans(Thm::spec_abs_rep(int_pos_spec(), Vec::new(), da)?)?; // = da

    let bridge = mkfs_cong(f_eq, d_eq)?;
    lhs.trans(bridge)?.trans(ra.sym()?)?.all_intro("a", rat())
}

cached_thm! {
    /// `⊢ ∀a. a * 0 = 0` — **proved**. `a · 0 = MK(fa·0, …) = MK(0, da)`
    /// (numerator by `int::mul_zero`, denominator to `da` as in `mul_one`),
    /// then `MK(0, da) = MK(0, one_pos) = 0` by `class_intro` on the
    /// cross-multiplication `0·rep(one_pos) = 0·rep(da)` (both `0`).
    pub fn mul_zero() -> Thm {
        mul_zero_impl().expect("rat::mul_zero")
    }
}
fn mul_zero_impl() -> Result<Thm> {
    let a = rvar("a");
    let ra = recon_mk(&a)?; // a = MK(fa, da)
    let r0 = Thm::refl(rat_zero())?; // rat_zero = MK(0, one_pos)
    let lhs = mul_via_components(&ra, &r0)?; // a·0 = MK(fa·0, to_pos(rep da · rep one_pos))
    let (fa, da) = (rfst(&a), rden(&a));
    let rda = den(&rep_pair(a.clone())); // rep da
    let i0 = Term::int_lit(0i128);
    let rop = Term::app(Term::spec_rep(int_pos_spec(), Vec::new()), one_pos()); // rep(one_pos)

    let f_eq = int::mul_zero().all_elim(fa)?; // fa·0 = 0
    let dl = mk_components(&dest_eq(&lhs)?.1)?.1;
    let d_eq = rewrite_seq(&dl, &[one_pos_rt()])?
        .trans(
            int::mul_one()
                .all_elim(rda.clone())?
                .cong_arg(to_pos_fn())?,
        )?
        .trans(Thm::spec_abs_rep(int_pos_spec(), Vec::new(), da.clone())?)?;
    let step = lhs.trans(mkfs_cong(f_eq, d_eq)?)?; // a·0 = MK(0, da) = mk_rat(ip 0 da)

    // 0/da ~ 0/1: cross-mult 0·rep(one_pos) = 0·rep(da) (both 0).
    let lz = int::mul_comm()
        .all_elim(i0.clone())?
        .all_elim(rop.clone())?
        .trans(int::mul_zero().all_elim(rop)?)?; // 0·rep(one_pos) = 0
    let rz = int::mul_comm()
        .all_elim(i0.clone())?
        .all_elim(rda.clone())?
        .trans(int::mul_zero().all_elim(rda)?)?; // 0·rep(da) = 0
    let g = lz.trans(rz.sym()?)?; // 0·rep(one_pos) = 0·rep(da)
    let rel = rel_of_pairs(&i0, &da, &i0, &one_pos(), g)?; // rat_rel (ip 0 da)(ip 0 one_pos)
    let cls = crate::init::quotient::class_intro(
        &rat_spec(),
        &[],
        &ip_pair(),
        &rat_rel_symm(),
        &rat_rel_trans(),
        rel,
    )?; // mk_rat(ip 0 da) = mk_rat(ip 0 one_pos) = rat_zero

    step.trans(cls)?.all_intro("a", rat())
}

cached_thm! {
    /// `⊢ ∀a b c. a * (b + c) = a * b + a * c` — **proved** (left
    /// distributivity). Unlike the other ring axioms this is *not*
    /// componentwise: `a·(b+c) = N/D` while `a·b + a·c = (rda·N)/(rda·D)` —
    /// the same rational scaled by the common factor `rda`. The
    /// cross-multiplication `N·(rda·D) = (rda·N)·D` then collapses to comm/
    /// assoc, lifted by `class_intro`.
    pub fn distrib() -> Thm {
        distrib_impl().expect("rat::distrib")
    }
}
fn distrib_impl() -> Result<Thm> {
    let (a, b, c) = (rvar("a"), rvar("b"), rvar("c"));
    let (ra, rb, rc) = (recon_mk(&a)?, recon_mk(&b)?, recon_mk(&c)?);
    let lhs_thm = mul_via_components(&ra, &add_via_components(&rb, &rc)?)?;
    let rhs_thm = add_via_components(
        &mul_via_components(&ra, &rb)?,
        &mul_via_components(&ra, &rc)?,
    )?;
    let bridge = distrib_bridge_raw()?;
    lhs_thm
        .trans(bridge)?
        .trans(rhs_thm.sym()?)?
        .all_intro("c", rat())?
        .all_intro("b", rat())?
        .all_intro("a", rat())
}

/// The distributivity bridge `⊢ mkfs lf ld = mkfs rf rd` over the free
/// `a, b, c` (the common-factor cross-multiplication `N_L·D_R = N_R·D_L`
/// lifted by `class_intro`). Shared by [`distrib_impl`] and the `rat.cov`
/// `distrib_bridge` seam given.
fn distrib_bridge_raw() -> Result<Thm> {
    let (a, b, c) = (rvar("a"), rvar("b"), rvar("c"));
    let (ra, rb, rc) = (recon_mk(&a)?, recon_mk(&b)?, recon_mk(&c)?);
    let bc = add_via_components(&rb, &rc)?;
    let lhs_thm = mul_via_components(&ra, &bc)?; // a·(b+c) = MK(lf, ld)
    let ab = mul_via_components(&ra, &rb)?;
    let ac = mul_via_components(&ra, &rc)?;
    let rhs_thm = add_via_components(&ab, &ac)?; // a·b + a·c = MK(rf, rd)

    let (lf, ld) = mk_components(&dest_eq(&lhs_thm)?.1)?; // N_L (clean), LHS denom (nested)
    let (rf, rd) = mk_components(&dest_eq(&rhs_thm)?.1)?; // RHS num (nested), RHS denom (nested)

    let (fa, fb, fc) = (rfst(&a), rfst(&b), rfst(&c));
    let (da, db, dc) = (rden(&a), rden(&b), rden(&c)); // int.pos components
    let (rda, rdb, rdc) = (
        den(&rep_pair(a.clone())),
        den(&rep_pair(b.clone())),
        den(&rep_pair(c.clone())),
    );
    // int.pos denominators of the intermediate ops.
    let dbc = mk_components(&dest_eq(&bc)?.1)?.1;
    let dab = mk_components(&dest_eq(&ab)?.1)?.1;
    let dac = mk_components(&dest_eq(&ac)?.1)?.1;

    let comm = |u: &Term, v: &Term| int::mul_comm().all_elim(u.clone())?.all_elim(v.clone());
    let massoc = |u: &Term, v: &Term, w: &Term| {
        int::mul_assoc()
            .all_elim(u.clone())?
            .all_elim(v.clone())?
            .all_elim(w.clone())
    };
    let pp = |x: &Term, y: &Term| pos_prod_rt().all_elim(x.clone())?.all_elim(y.clone());

    let n_l = lf.clone(); // fa·(fb·rdc + fc·rdb)
    let d_l = imul(rda.clone(), imul(rdb.clone(), rdc.clone()));

    // rep(ld) = D_L ; rep(rd) = D_R ; rf = N_R (round-trips of the nested denoms).
    let rep_ld = pp(&da, &dbc)?.trans(imul_l_cong(&rda, pp(&db, &dc)?)?)?;
    let rep_rd = pp(&dab, &dac)?.trans(imul_cong(pp(&da, &db)?, pp(&da, &dc)?)?)?;
    let rf_eq = iadd_cong(
        imul_l_cong(&imul(fa.clone(), fb.clone()), pp(&da, &dc)?)?,
        imul_l_cong(&imul(fa.clone(), fc.clone()), pp(&da, &db)?)?,
    )?; // rf = N_R

    // D_R = rda·D_L.
    let dr_fact = imul_interchange(&rda, &rdb, &rda, &rdc)?.trans(massoc(
        &rda,
        &rda,
        &imul(rdb.clone(), rdc.clone()),
    )?)?;
    // rda·N_L = N_R.
    let nbc = iadd(imul(fb.clone(), rdc.clone()), imul(fc.clone(), rdb.clone()));
    let term1 = imul_interchange(&fa, &fb, &rda, &rdc)?
        .trans(mul_r(comm(&fa, &rda)?, &imul(fb.clone(), rdc.clone()))?)?; // (fa·fb)·(rda·rdc) = (rda·fa)·(fb·rdc)
    let term2 = imul_interchange(&fa, &fc, &rda, &rdb)?
        .trans(mul_r(comm(&fa, &rda)?, &imul(fc.clone(), rdb.clone()))?)?;
    let nr_fact = massoc(&rda, &fa, &nbc)?
        .sym()? // rda·(fa·nbc) = (rda·fa)·nbc
        .trans(
            int::distrib()
                .all_elim(imul(rda.clone(), fa.clone()))?
                .all_elim(imul(fb.clone(), rdc.clone()))?
                .all_elim(imul(fc.clone(), rdb.clone()))?,
        )? // = (rda·fa)·(fb·rdc) + (rda·fa)·(fc·rdb)
        .trans(iadd_cong(term1.sym()?, term2.sym()?)?)?; // = N_R

    // Cross-multiplication N_L·D_R = N_R·D_L, by the common factor rda.
    let g_clean = imul_l_cong(&n_l, dr_fact)? // N_L·D_R = N_L·(rda·D_L)
        .trans(massoc(&n_l, &rda, &d_l)?.sym()?)? // = (N_L·rda)·D_L
        .trans(mul_r(comm(&n_l, &rda)?, &d_l)?)? // = (rda·N_L)·D_L
        .trans(mul_r(nr_fact, &d_l)?)?; // = N_R·D_L

    // Re-introduce the raw (nested) numerator / denominators for rel_of_pairs.
    let g = g_clean
        .lhs_conv(|t| t.rw_all(&rep_rd.clone().sym()?))? // D_R ↦ rep(rd)
        .rhs_conv(|t| rewrite_seq(t, &[rf_eq.sym()?, rep_ld.sym()?]))?; // N_R ↦ rf, D_L ↦ rep(ld)

    let rel = rel_of_pairs(&lf, &ld, &rf, &rd, g)?;
    let _ = (lhs_thm, rhs_thm); // their MK forms feed `distrib_impl`'s caller.
    crate::init::quotient::class_intro(
        &rat_spec(),
        &[],
        &ip_pair(),
        &rat_rel_symm(),
        &rat_rel_trans(),
        rel,
    )
}

/// `⊢ ∀a. ¬(a = 0) ⟹ ∃b. a * b = 1` — the field axiom (multiplicative
/// inverse). This is what makes `rat` a *field* rather than just a ring,
/// and underwrites division (and so the midpoint form of density).
pub fn mul_inv() -> Thm {
    let a = rvar("a");
    let b = rvar("b");
    let has_inv = rmul(a.clone(), b)
        .equals(rat_one())
        .expect("mul_inv: a * b = 1")
        .exists("b", rat())
        .expect("mul_inv: ∃b");
    let neq = a
        .clone()
        .equals(rat_zero())
        .expect("mul_inv: a = 0")
        .not()
        .expect("mul_inv: ≠");
    let body = neq.imp(has_inv).expect("mul_inv");
    axiom(forall_rat(&["a"], body))
}

// ============================================================================
// Strict order — defined via cross-multiplication; linear-order axioms
// postulated
// ============================================================================

/// `a < b` on `int`.
fn ilt(a: Term, b: Term) -> Term {
    Term::app(Term::app(int::int_lt(), a), b)
}

/// `ratLt : rat → rat → bool` ≡ `(a/b) < (c/d) ⟺ a·d < c·b` (valid
/// because denominators are strictly positive). Defined here at the
/// representative level — `defs/rat.rs` ships only the declaration-only
/// `ratLe`; `<` is the strict companion the density statement is phrased
/// in.
pub fn rat_lt() -> Term {
    let (x, y) = (Term::free("x", rat()), Term::free("y", rat()));
    let (px, py) = (rep_pair(x.clone()), rep_pair(y.clone()));
    let body = ilt(imul(num(&px), den(&py)), imul(num(&py), den(&px)));
    Term::abs(
        rat(),
        subst::close(&Term::abs(rat(), subst::close(&body, "y")), "x"),
    )
}

/// `a < b` on `rat`.
fn rlt(a: Term, b: Term) -> Term {
    Term::app(Term::app(rat_lt(), a), b)
}
/// `a ≤ b` on `rat` (the declared kernel `ratLe`).
fn rle(a: Term, b: Term) -> Term {
    Term::app(Term::app(rat_le(), a), b)
}

cached_thm! {
    /// `⊢ ∀a. ¬(a < a)` — irreflexivity, **proved on the nose** from
    /// `int::lt_irrefl`: `ratLt a a` reduces to `int_lt X X` with
    /// `X = num(rep a) · den(rep a)`, so the rational `<` inherits the
    /// integer's irreflexivity at `X`.
    pub fn lt_irrefl() -> Thm {
        lt_irrefl_impl().expect("rat::lt_irrefl")
    }
}
fn lt_irrefl_impl() -> Result<Thm> {
    let a = rvar("a");
    let red = rlt(a.clone(), a.clone()).reduce()?; // ratLt a a = int_lt X X
    let ltxx = red.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone();
    let x = ltxx
        .as_app()
        .ok_or(Error::NotAnEquation)?
        .0
        .as_app()
        .ok_or(Error::NotAnEquation)?
        .1
        .clone(); // X = num(rep a) · den(rep a)
    int::lt_irrefl()
        .all_elim(x)? // ¬(int_lt X X)
        .rewrite(&red.sym()?)? // ¬(ratLt a a)
        .all_intro("a", rat())
}

cached_thm! {
    /// `⊢ ∀a b c. a < b ⟹ b < c ⟹ a < c` — **proved** by lifting to the
    /// `int` cross-multiplication comparisons. With `fa·db < fb·da` and
    /// `fb·dc < fc·db` (`db`,`da`,`dc` the positive denominators), scale the
    /// first by `dc`, the second by `da`, reshuffle (`prove_imul_eq`) so both
    /// read `(…)·db`, chain by `int::lt_trans`, then cancel `db`
    /// (`int::lt_mul_pos_iff`) to land on `fa·dc < fc·da`.
    pub fn lt_trans() -> Thm {
        lt_trans_impl().expect("rat::lt_trans")
    }
}
fn lt_trans_impl() -> Result<Thm> {
    let (a, b, c) = (rvar("a"), rvar("b"), rvar("c"));
    let (ra, rb, rc) = (recon_mk(&a)?, recon_mk(&b)?, recon_mk(&c)?);
    // int numerator / (positive) denominator components.
    let (fa, da) = (rfst(&a), den(&rep_pair(a.clone())));
    let (fb, db) = (rfst(&b), den(&rep_pair(b.clone())));
    let (fc, dc) = (rfst(&c), den(&rep_pair(c.clone())));

    // ratLt a b = int.lt (fa·db)(fb·da), etc.
    let dab = lt_via_components(&ra, &rb)?;
    let dbc = lt_via_components(&rb, &rc)?;
    let dac = lt_via_components(&ra, &rc)?;

    let (hab, hbc) = (rlt(a.clone(), b.clone()), rlt(b.clone(), c.clone()));
    let h1 = dab.eq_mp(Thm::assume(hab.clone())?)?; // fa·db < fb·da
    let h2 = dbc.eq_mp(Thm::assume(hbc.clone())?)?; // fb·dc < fc·db

    // positivity of the three denominators.
    let pos_da = int::int_pos_pos().all_elim(rden(&a))?; // 0 < da
    let pos_db = int::int_pos_pos().all_elim(rden(&b))?; // 0 < db
    let pos_dc = int::int_pos_pos().all_elim(rden(&c))?; // 0 < dc

    // Scale h1 by dc>0: (fa·db)·dc < (fb·da)·dc.
    let s1 = int::lt_mul_pos()
        .all_elim(imul(fa.clone(), db.clone()))?
        .all_elim(imul(fb.clone(), da.clone()))?
        .all_elim(dc.clone())?
        .imp_elim(pos_dc.clone())?
        .imp_elim(h1)?;
    // Scale h2 by da>0: (fb·dc)·da < (fc·db)·da.
    let s2 = int::lt_mul_pos()
        .all_elim(imul(fb.clone(), dc.clone()))?
        .all_elim(imul(fc.clone(), db.clone()))?
        .all_elim(da.clone())?
        .imp_elim(pos_da.clone())?
        .imp_elim(h2)?;

    // Reshuffle both into `(…)·db` form.
    //   (fa·db)·dc = (fa·dc)·db ;  (fb·da)·dc = (fb·dc)·da
    let r1l = int::prove_imul_eq(&imul(imul(fa.clone(), db.clone()), dc.clone()), &imul(imul(fa.clone(), dc.clone()), db.clone()))?;
    let r1r = int::prove_imul_eq(&imul(imul(fb.clone(), da.clone()), dc.clone()), &imul(imul(fb.clone(), dc.clone()), da.clone()))?;
    let s1n = s1.rewrite(&r1l)?.rewrite(&r1r)?; // (fa·dc)·db < (fb·dc)·da
    //   (fc·db)·da = (fc·da)·db
    let r2r = int::prove_imul_eq(&imul(imul(fc.clone(), db.clone()), da.clone()), &imul(imul(fc.clone(), da.clone()), db.clone()))?;
    let s2n = s2.rewrite(&r2r)?; // (fb·dc)·da < (fc·da)·db

    // Chain: (fa·dc)·db < (fc·da)·db.
    let chained = int::lt_trans()
        .all_elim(imul(imul(fa.clone(), dc.clone()), db.clone()))?
        .all_elim(imul(imul(fb.clone(), dc.clone()), da.clone()))?
        .all_elim(imul(imul(fc.clone(), da.clone()), db.clone()))?
        .imp_elim(s1n)?
        .imp_elim(s2n)?; // (fa·dc)·db < (fc·da)·db

    // Cancel db>0: fa·dc < fc·da.
    let cancelled = int::lt_mul_pos_iff()
        .all_elim(imul(fa.clone(), dc.clone()))?
        .all_elim(imul(fc.clone(), da.clone()))?
        .all_elim(db.clone())?
        .imp_elim(pos_db)?
        .eq_mp(chained)?; // fa·dc < fc·da

    dac.sym()?
        .eq_mp(cancelled)? // ratLt a c
        .imp_intro(&hbc)?
        .imp_intro(&hab)?
        .all_intro("c", rat())?
        .all_intro("b", rat())?
        .all_intro("a", rat())
}

cached_thm! {
    /// `⊢ ∀a b. a < b ∨ a = b ∨ b < a` — **proved**. `int::lt_trichotomy` on
    /// the cross-products `(fa·db, fb·da)` gives the three cases; map `<`/`>`
    /// back through [`lt_via_components`] and the middle `=` case through the
    /// quotient (`rel_of_pairs` + `class_intro` lifts `fa·db = fb·da` to
    /// `a = b`).
    pub fn lt_trichotomy() -> Thm {
        lt_trichotomy_impl().expect("rat::lt_trichotomy")
    }
}
fn lt_trichotomy_impl() -> Result<Thm> {
    let (a, b) = (rvar("a"), rvar("b"));
    let (ra, rb) = (recon_mk(&a)?, recon_mk(&b)?);
    let (fa, da_pos) = (rfst(&a), rden(&a)); // fa : int, da_pos : int.pos
    let (fb, db_pos) = (rfst(&b), rden(&b));
    let (da, db) = (den(&rep_pair(a.clone())), den(&rep_pair(b.clone()))); // rep da_pos, rep db_pos

    let x = imul(fa.clone(), db.clone()); // fa·db
    let y = imul(fb.clone(), da.clone()); // fb·da

    // int trichotomy on (x, y): (x<y) ∨ (x=y) ∨ (y<x).
    let tri = int::lt_trichotomy().all_elim(x.clone())?.all_elim(y.clone())?;

    let dab = lt_via_components(&ra, &rb)?; // ratLt a b = int.lt x y
    let dba = lt_via_components(&rb, &ra)?; // ratLt b a = int.lt y x

    // target conclusion shape.
    let eq_ab = a.clone().equals(b.clone())?;
    let goal = rlt(a.clone(), b.clone()).or(eq_ab.clone().or(rlt(b.clone(), a.clone()))?)?;

    // disjunct 1: x<y ⟹ a<b ⟹ goal.
    let xlty = lt_via_int(&x, &y);
    let br1 = dab
        .sym()?
        .eq_mp(Thm::assume(xlty.clone())?)? // {x<y} ⊢ ratLt a b
        .or_intro_l(eq_ab.clone().or(rlt(b.clone(), a.clone()))?)?
        .imp_intro(&xlty)?;
    // disjunct 3: y<x ⟹ b<a ⟹ goal.
    let yltx = lt_via_int(&y, &x);
    let br3 = {
        let ba = dba.sym()?.eq_mp(Thm::assume(yltx.clone())?)?; // ratLt b a
        ba.or_intro_r(eq_ab.clone())? // (a=b) ∨ (b<a)
            .or_intro_r(rlt(a.clone(), b.clone()))? // a<b ∨ ((a=b) ∨ (b<a))
            .imp_intro(&yltx)?
    };
    // disjunct 2: x=y ⟹ a=b ⟹ goal.
    let xeqy = x.clone().equals(y.clone())?;
    let br2 = {
        // x=y is `fa·db = fb·da`; lift to `rat_rel (ip fa da_pos)(ip fb db_pos)`.
        let g = Thm::assume(xeqy.clone())?;
        let rel = rel_of_pairs(&fa, &da_pos, &fb, &db_pos, g)?; // rat_rel (ip fa da_pos)(ip fb db_pos)
        let cls = crate::init::quotient::class_intro(
            &rat_spec(),
            &[],
            &ip_pair(),
            &rat_rel_symm(),
            &rat_rel_trans(),
            rel,
        )?; // mk_rat(ip fa da_pos) = mk_rat(ip fb db_pos)
        // a = mk_rat(ip fa da_pos) = mk_rat(ip fb db_pos) = b.
        let a_eq_b = ra.clone().trans(cls)?.trans(rb.clone().sym()?)?; // {x=y} ⊢ a=b
        a_eq_b
            .or_intro_l(rlt(b.clone(), a.clone()))? // (a=b) ∨ (b<a)
            .or_intro_r(rlt(a.clone(), b.clone()))? // a<b ∨ …
            .imp_intro(&xeqy)?
    };

    // Combine via the int trichotomy ∨-elim.
    let tail = tri
        .concl()
        .as_app()
        .ok_or_else(|| Error::ConnectiveRule("lt_trichotomy: ∨ shape".into()))?
        .1
        .clone(); // (x=y) ∨ (y<x)
    let tail_thm = Thm::assume(tail.clone())?
        .or_elim(br2, br3)?
        .imp_intro(&tail)?;
    tri.or_elim(br1, tail_thm)? // ⊢ goal
        .all_intro("b", rat())?
        .all_intro("a", rat())
}

/// `int.lt a b` term-builder (for trichotomy disjunct shapes).
fn lt_via_int(a: &Term, b: &Term) -> Term {
    Term::app(Term::app(int::int_lt(), a.clone()), b.clone())
}

/// `⊢ ∀a b. (a ≤ b) = (a < b ∨ a = b)` — `≤` in terms of `<`.
pub fn le_def() -> Thm {
    let (a, b) = (rvar("a"), rvar("b"));
    let rhs = rlt(a.clone(), b.clone())
        .or(a.clone().equals(b.clone()).expect("le_def: a = b"))
        .expect("le_def rhs");
    let eq = rle(a, b).equals(rhs).expect("le_def");
    axiom(forall_rat(&["a", "b"], eq))
}

// ============================================================================
// Order toolkit — derived `≤` facts (and the one base strictness postulate)
// ============================================================================
//
// `le_refl` / `lt_imp_le` / `le_trans` are **derived** from `le_def` and the
// strict-order postulates (`lt_irrefl` / `lt_trans`). The single new
// postulate is `zero_lt_one` (`0 < 1`) — the base strictness fact reduction
// cannot reach (`ratLt` picks representatives via ε). `not_one_le_zero`
// (`¬(1 ≤ 0)`) then follows. These are what the `real` Dedekind-cut proofs
// (`init::real`) consume: cut upward-closure is `le_trans`, non-emptiness is
// `le_refl`, and `0 ≠ 1` for reals turns on `not_one_le_zero`.

cached_thm! {
    /// `⊢ 0 < 1` — **proved** by lifting through the quotient: `0 = MK 0 1`,
    /// `1 = MK 1 1`, so `ratLt 0 1 = int.lt (0·rep 1)(1·rep 1)`
    /// ([`lt_via_components`]); resolve `rep one_pos = 1` ([`one_pos_rt`]) and
    /// the literal products to land on the `int` fact `0 < 1`.
    pub fn zero_lt_one() -> Thm {
        zero_lt_one_impl().expect("rat::zero_lt_one")
    }
}
fn zero_lt_one_impl() -> Result<Thm> {
    // rat_zero = MK 0 one_pos, rat_one = MK 1 one_pos — definitionally `mk_rat`
    // of the explicit pairs, so the MK reconstructions are reflexivity.
    let r0 = Thm::refl(rat_zero())?; // 0 = MK 0 one_pos
    let r1 = Thm::refl(rat_one())?; // 1 = MK 1 one_pos
    let de = lt_via_components(&r0, &r1)?; // ratLt 0 1 = int.lt (0·rep one_pos)(1·rep one_pos)
    // Resolve `rep one_pos = 1`, then fully evaluate the literal comparison to
    // `T`, and read off `ratLt 0 1`.
    let rep1 = one_pos_rt(); // rep one_pos = 1
    de.rhs_conv(|t| t.rw_all(&rep1))? // ratLt 0 1 = int.lt (0·1)(1·1)
        .rhs_conv(|t| t.reduce())? // ratLt 0 1 = T
        .eqt_elim() // ⊢ ratLt 0 1
}

cached_thm! {
    /// `⊢ ∀a. a ≤ a` — reflexivity of `≤`, from `le_def` + `=`-reflexivity.
    pub fn le_refl() -> Thm {
        le_refl_impl().expect("le_refl")
    }
}
fn le_refl_impl() -> Result<Thm> {
    let a = rvar("a");
    let ld = le_def().all_elim(a.clone())?.all_elim(a.clone())?; // (a≤a) = (a<a ∨ a=a)
    let disj = Thm::refl(a.clone())?.or_intro_r(rlt(a.clone(), a.clone()))?; // ⊢ a<a ∨ a=a
    ld.sym()?.eq_mp(disj)?.all_intro("a", rat())
}

cached_thm! {
    /// `⊢ ∀a b. a < b ⟹ a ≤ b` — strict implies non-strict.
    pub fn lt_imp_le() -> Thm {
        lt_imp_le_impl().expect("lt_imp_le")
    }
}
fn lt_imp_le_impl() -> Result<Thm> {
    let (a, b) = (rvar("a"), rvar("b"));
    let lt = rlt(a.clone(), b.clone());
    let ld = le_def().all_elim(a.clone())?.all_elim(b.clone())?; // (a≤b)=(a<b ∨ a=b)
    let disj = Thm::assume(lt.clone())?.or_intro_l(a.clone().equals(b.clone())?)?; // {a<b} ⊢ a<b ∨ a=b
    ld.sym()?
        .eq_mp(disj)?
        .imp_intro(&lt)?
        .all_intro("b", rat())?
        .all_intro("a", rat())
}

cached_thm! {
    /// `⊢ ∀a b c. a ≤ b ⟹ b ≤ c ⟹ a ≤ c` — transitivity of `≤`, by case
    /// analysis on `le_def` (each `≤` is `<` or `=`) using `lt_trans` and
    /// equality congruence.
    pub fn le_trans() -> Thm {
        le_trans_impl().expect("le_trans")
    }
}
fn le_trans_impl() -> Result<Thm> {
    let (a, b, c) = (rvar("a"), rvar("b"), rvar("c"));
    let (hab, hbc) = (rle(a.clone(), b.clone()), rle(b.clone(), c.clone()));

    // Goal disjunction `a<c ∨ a=c`, and the closer `(a<c ∨ a=c) ⟹ a≤c`.
    let ld_ac = le_def().all_elim(a.clone())?.all_elim(c.clone())?; // (a≤c)=(a<c ∨ a=c)
    let close_goal = |disj: Thm| -> Result<Thm> { ld_ac.clone().sym()?.eq_mp(disj) };

    // From the two `≤` hyps, the two disjunctions.
    let d_ab = le_def()
        .all_elim(a.clone())?
        .all_elim(b.clone())?
        .eq_mp(Thm::assume(hab.clone())?)?; // {a≤b} ⊢ a<b ∨ a=b
    let d_bc = le_def()
        .all_elim(b.clone())?
        .all_elim(c.clone())?
        .eq_mp(Thm::assume(hbc.clone())?)?; // {b≤c} ⊢ b<c ∨ b=c

    // The four leaf derivations of `a≤c`, each as `<branch hyp> ⊢ a≤c`.
    // a<b, b<c ⟹ a<c.
    let lt_lt = |ab: Thm, bc: Thm| -> Result<Thm> {
        let ac = lt_trans()
            .all_elim(a.clone())?
            .all_elim(b.clone())?
            .all_elim(c.clone())?
            .imp_elim(ab)?
            .imp_elim(bc)?; // a<c
        close_goal(ac.or_intro_l(a.clone().equals(c.clone())?)?)
    };
    // a<b, b=c ⟹ a<c   (rewrite the `b` in `a<b` to `c`).
    let lt_eq = |ab: Thm, bc_eq: Thm| -> Result<Thm> {
        let cong = bc_eq.cong_arg(Term::app(rat_lt(), a.clone()))?; // (a<b)=(a<c)
        let ac = cong.eq_mp(ab)?; // a<c
        close_goal(ac.or_intro_l(a.clone().equals(c.clone())?)?)
    };
    // a=b, b<c ⟹ a<c   (rewrite the `b` in `b<c` to `a`).
    let eq_lt = |ab_eq: Thm, bc: Thm| -> Result<Thm> {
        let cong = ab_eq.cong_arg(rat_lt())?.cong_fn(c.clone())?; // (a<c)=(b<c)
        let ac = cong.sym()?.eq_mp(bc)?; // a<c
        close_goal(ac.or_intro_l(a.clone().equals(c.clone())?)?)
    };
    // a=b, b=c ⟹ a=c.
    let eq_eq = |ab_eq: Thm, bc_eq: Thm| -> Result<Thm> {
        let ac = ab_eq.trans(bc_eq)?; // a=c
        close_goal(ac.or_intro_r(rlt(a.clone(), c.clone()))?)
    };

    // Inner case split on `b<c ∨ b=c`, given a fixed left branch builder.
    let ab_lt = rlt(a.clone(), b.clone());
    let ab_eq = a.clone().equals(b.clone())?;
    let bc_lt = rlt(b.clone(), c.clone());
    let bc_eq = b.clone().equals(c.clone())?;

    // Left of the outer split: assume a<b, case-split d_bc.
    let outer_left = {
        let ab = Thm::assume(ab_lt.clone())?;
        let br_lt = lt_lt(ab.clone(), Thm::assume(bc_lt.clone())?)?.imp_intro(&bc_lt)?;
        let br_eq = lt_eq(ab, Thm::assume(bc_eq.clone())?)?.imp_intro(&bc_eq)?;
        d_bc.clone().or_elim(br_lt, br_eq)?.imp_intro(&ab_lt)? // {a≤b,b≤c} ⊢ a<b ⟹ a≤c
    };
    // Right of the outer split: assume a=b, case-split d_bc.
    let outer_right = {
        let ab = Thm::assume(ab_eq.clone())?;
        let br_lt = eq_lt(ab.clone(), Thm::assume(bc_lt.clone())?)?.imp_intro(&bc_lt)?;
        let br_eq = eq_eq(ab, Thm::assume(bc_eq.clone())?)?.imp_intro(&bc_eq)?;
        d_bc.or_elim(br_lt, br_eq)?.imp_intro(&ab_eq)? // {a≤b,b≤c} ⊢ a=b ⟹ a≤c
    };

    d_ab.or_elim(outer_left, outer_right)? // {a≤b,b≤c} ⊢ a≤c
        .imp_intro(&hbc)?
        .imp_intro(&hab)?
        .all_intro("c", rat())?
        .all_intro("b", rat())?
        .all_intro("a", rat())
}

cached_thm! {
    /// `⊢ ¬(1 ≤ 0)` — from `0 < 1` (`zero_lt_one`), `lt_trans` and
    /// `lt_irrefl`. The distinguishing fact behind `real` `0 ≠ 1`.
    pub fn not_one_le_zero() -> Thm {
        not_one_le_zero_impl().expect("not_one_le_zero")
    }
}
fn not_one_le_zero_impl() -> Result<Thm> {
    let (zero, one) = (rat_zero(), rat_one());
    let one_le_zero = rle(one.clone(), zero.clone());
    // (1≤0) = (1<0 ∨ 1=0); under the assumption, the disjunction.
    let ld = le_def().all_elim(one.clone())?.all_elim(zero.clone())?;
    let disj = ld.eq_mp(Thm::assume(one_le_zero.clone())?)?; // {1≤0} ⊢ 1<0 ∨ 1=0

    let lt_10 = rlt(one.clone(), zero.clone());
    let eq_10 = one.clone().equals(zero.clone())?;

    // 1<0 branch: 0<1 and 1<0 give 0<0, contradicting irreflexivity.
    let br_lt = {
        let chain = lt_trans()
            .all_elim(zero.clone())?
            .all_elim(one.clone())?
            .all_elim(zero.clone())?
            .imp_elim(zero_lt_one())?
            .imp_elim(Thm::assume(lt_10.clone())?)?; // 0<0
        lt_irrefl()
            .all_elim(zero.clone())?
            .not_elim(chain)?
            .imp_intro(&lt_10)?
    };
    // 1=0 branch: rewrite 0<1 by 1=0 to 0<0, same contradiction.
    let br_eq = {
        let cong = Thm::assume(eq_10.clone())?.cong_arg(Term::app(rat_lt(), zero.clone()))?; // (0<1)=(0<0)
        let zero_lt_zero = cong.eq_mp(zero_lt_one())?; // 0<0
        lt_irrefl()
            .all_elim(zero.clone())?
            .not_elim(zero_lt_zero)?
            .imp_intro(&eq_10)?
    };

    disj.or_elim(br_lt, br_eq)? // {1≤0, 0<1} ⊢ F
        .imp_intro(&one_le_zero)?
        .not_intro()
}

// ============================================================================
// Linear-order facts — also DERIVED from the order postulates
// ============================================================================
//
// `lt_asymm` / `lt_imp_ne` / `le_antisym` / `le_total` round out `rat` as a
// linear order. Like `le_refl`/`le_trans` above, they are **derived** from
// the strict-order postulates (`lt_irrefl`/`lt_trans`/`lt_trichotomy`) +
// `le_def` and add no new postulate of their own. (The `rat` ordered-field
// *ring* axioms remain postulated — discharging them goes through the `int`
// *multiplicative* theory, which is not yet proved; these order facts need
// only the strict-order postulates and so are available now.)

cached_thm! {
    /// `⊢ ∀a b. a < b ⟹ ¬(b < a)` — strict order is asymmetric: `a < b` and
    /// `b < a` would give `a < a` by `lt_trans`, contradicting `lt_irrefl`.
    pub fn lt_asymm() -> Thm {
        lt_asymm_impl().expect("lt_asymm")
    }
}
fn lt_asymm_impl() -> Result<Thm> {
    let (a, b) = (rvar("a"), rvar("b"));
    let (ab, ba) = (rlt(a.clone(), b.clone()), rlt(b.clone(), a.clone()));
    let aa = lt_trans()
        .all_elim(a.clone())?
        .all_elim(b.clone())?
        .all_elim(a.clone())?
        .imp_elim(Thm::assume(ab.clone())?)?
        .imp_elim(Thm::assume(ba.clone())?)?; // {a<b, b<a} ⊢ a<a
    let f = lt_irrefl().all_elim(a.clone())?.not_elim(aa)?; // {a<b, b<a} ⊢ F
    f.imp_intro(&ba)?
        .not_intro()? // {a<b} ⊢ ¬(b<a)
        .imp_intro(&ab)?
        .all_intro("b", rat())?
        .all_intro("a", rat())
}

cached_thm! {
    /// `⊢ ∀a b. a < b ⟹ ¬(a = b)` — a strict inequality rules out equality:
    /// `a = b` rewrites `a < b` to `a < a`, contradicting `lt_irrefl`.
    pub fn lt_imp_ne() -> Thm {
        lt_imp_ne_impl().expect("lt_imp_ne")
    }
}
fn lt_imp_ne_impl() -> Result<Thm> {
    let (a, b) = (rvar("a"), rvar("b"));
    let ab = rlt(a.clone(), b.clone());
    let eq = a.clone().equals(b.clone())?;
    // (a<a) = (a<b) by congruence under `(<) a` using `a = b`; flip and apply.
    let cong = Thm::assume(eq.clone())?.cong_arg(Term::app(rat_lt(), a.clone()))?;
    let aa = cong.sym()?.eq_mp(Thm::assume(ab.clone())?)?; // {a<b, a=b} ⊢ a<a
    let f = lt_irrefl().all_elim(a.clone())?.not_elim(aa)?;
    f.imp_intro(&eq)?
        .not_intro()? // {a<b} ⊢ ¬(a=b)
        .imp_intro(&ab)?
        .all_intro("b", rat())?
        .all_intro("a", rat())
}

cached_thm! {
    /// `⊢ ∀a b. a ≤ b ⟹ b ≤ a ⟹ a = b` — antisymmetry, by case analysis on
    /// `le_def` (each `≤` is `<` or `=`): the `<`/`<` case contradicts
    /// `lt_asymm` (ex falso), the others give `a = b` directly.
    pub fn le_antisym() -> Thm {
        le_antisym_impl().expect("le_antisym")
    }
}
fn le_antisym_impl() -> Result<Thm> {
    let (a, b) = (rvar("a"), rvar("b"));
    let (hab, hba) = (rle(a.clone(), b.clone()), rle(b.clone(), a.clone()));
    let goal = a.clone().equals(b.clone())?; // a = b
    let d_ab = le_def()
        .all_elim(a.clone())?
        .all_elim(b.clone())?
        .eq_mp(Thm::assume(hab.clone())?)?; // {a≤b} ⊢ a<b ∨ a=b
    let d_ba = le_def()
        .all_elim(b.clone())?
        .all_elim(a.clone())?
        .eq_mp(Thm::assume(hba.clone())?)?; // {b≤a} ⊢ b<a ∨ b=a

    let ab_lt = rlt(a.clone(), b.clone());
    let ab_eq = a.clone().equals(b.clone())?;
    let ba_lt = rlt(b.clone(), a.clone());
    let ba_eq = b.clone().equals(a.clone())?;

    // a<b branch: split d_ba.
    let br_ab_lt = {
        // b<a: a<b and b<a contradict `lt_asymm`, so a=b ex falso.
        let sub_lt = {
            let not_ba = lt_asymm()
                .all_elim(a.clone())?
                .all_elim(b.clone())?
                .imp_elim(Thm::assume(ab_lt.clone())?)?; // {a<b} ⊢ ¬(b<a)
            let f = not_ba.not_elim(Thm::assume(ba_lt.clone())?)?; // {a<b, b<a} ⊢ F
            f.false_elim(goal.clone())?.imp_intro(&ba_lt)? // {a<b} ⊢ b<a ⟹ a=b
        };
        // b=a: a=b by symmetry.
        let sub_eq = Thm::assume(ba_eq.clone())?.sym()?.imp_intro(&ba_eq)?; // ⊢ b=a ⟹ a=b
        d_ba.or_elim(sub_lt, sub_eq)?.imp_intro(&ab_lt)? // {a≤b, b≤a} ⊢ a<b ⟹ a=b
    };
    // a=b branch: immediate.
    let br_ab_eq = Thm::assume(ab_eq.clone())?.imp_intro(&ab_eq)?; // ⊢ a=b ⟹ a=b

    d_ab.or_elim(br_ab_lt, br_ab_eq)? // {a≤b, b≤a} ⊢ a=b
        .imp_intro(&hba)?
        .imp_intro(&hab)?
        .all_intro("b", rat())?
        .all_intro("a", rat())
}

cached_thm! {
    /// `⊢ ∀a b. a ≤ b ∨ b ≤ a` — totality, from `lt_trichotomy` + `le_def`
    /// (`a<b` and `a=b` each give `a≤b`; `b<a` gives `b≤a`).
    pub fn le_total() -> Thm {
        le_total_impl().expect("le_total")
    }
}
fn le_total_impl() -> Result<Thm> {
    let (a, b) = (rvar("a"), rvar("b"));
    let (le_ab, le_ba) = (rle(a.clone(), b.clone()), rle(b.clone(), a.clone()));

    let ab_lt = rlt(a.clone(), b.clone());
    let ab_eq = a.clone().equals(b.clone())?;
    let ba_lt = rlt(b.clone(), a.clone());
    let inner_hyp = ab_eq.clone().or(ba_lt.clone())?; // a=b ∨ b<a (trichotomy's tail)

    let tri = lt_trichotomy().all_elim(a.clone())?.all_elim(b.clone())?; // ⊢ a<b ∨ (a=b ∨ b<a)

    // a<b ⟹ goal  (a<b gives a≤b).
    let br_lt = {
        let le = lt_imp_le()
            .all_elim(a.clone())?
            .all_elim(b.clone())?
            .imp_elim(Thm::assume(ab_lt.clone())?)?; // {a<b} ⊢ a≤b
        le.or_intro_l(le_ba.clone())?.imp_intro(&ab_lt)? // ⊢ a<b ⟹ goal
    };
    // a=b ⟹ goal  (a=b gives a≤b via le_def).
    let br_eq = {
        let ld = le_def().all_elim(a.clone())?.all_elim(b.clone())?; // (a≤b)=(a<b ∨ a=b)
        let disj = Thm::assume(ab_eq.clone())?.or_intro_r(ab_lt.clone())?; // {a=b} ⊢ a<b ∨ a=b
        let le = ld.sym()?.eq_mp(disj)?; // {a=b} ⊢ a≤b
        le.or_intro_l(le_ba.clone())?.imp_intro(&ab_eq)? // ⊢ a=b ⟹ goal
    };
    // b<a ⟹ goal  (b<a gives b≤a).
    let br_ba = {
        let le = lt_imp_le()
            .all_elim(b.clone())?
            .all_elim(a.clone())?
            .imp_elim(Thm::assume(ba_lt.clone())?)?; // {b<a} ⊢ b≤a
        le.or_intro_r(le_ab.clone())?.imp_intro(&ba_lt)? // ⊢ b<a ⟹ goal
    };
    let inner = Thm::assume(inner_hyp.clone())?
        .or_elim(br_eq, br_ba)? // {a=b ∨ b<a} ⊢ goal
        .imp_intro(&inner_hyp)?; // ⊢ (a=b ∨ b<a) ⟹ goal
    tri.or_elim(br_lt, inner)? // ⊢ goal
        .all_intro("b", rat())?
        .all_intro("a", rat())
}

// ============================================================================
// Density — DERIVED from the two mediant inequalities
// ============================================================================
//
// The witness between `x < y` is the **mediant** `(a+c)/(b+d)` of
// representatives `x = a/b`, `y = c/d` — strictly between `x` and `y`
// exactly when `x < y`, and (unlike the midpoint `(x+y)/2`) needing no
// division to construct. The two mediant inequalities are the postulated
// leaves; `dense` itself is a genuine derivation from them.

/// `ratMediant : rat → rat → rat` ≡ `(a/b) ⊕ (c/d) = (a+c)/(b+d)`.
pub fn mediant() -> Term {
    binary_rat(|px, py| ip(iadd(num(px), num(py)), to_pos(iadd(den(px), den(py)))))
}
/// `mediant a b` applied.
fn med(a: Term, b: Term) -> Term {
    Term::app(Term::app(mediant(), a), b)
}

/// `⊢ ∀x y. x < y ⟹ x < mediant x y` — the mediant exceeds the smaller.
///
/// **Postulated** (audit hyp). Unfolds to the `int` order fact
/// `a·d < c·b ⟹ a·(b+d) < (a+c)·b` lifted through the quotient — blocked
/// on the `int` ordered-ring theory (`SKELETONS.md`).
pub fn mediant_gt() -> Thm {
    let (x, y) = (rvar("x"), rvar("y"));
    let concl = rlt(x.clone(), med(x.clone(), y.clone()));
    let body = rlt(x, y).imp(concl).expect("mediant_gt");
    axiom(forall_rat(&["x", "y"], body))
}

/// `⊢ ∀x y. x < y ⟹ mediant x y < y` — the mediant is below the larger.
///
/// **Postulated** (audit hyp) — the mirror of [`mediant_gt`].
pub fn mediant_lt() -> Thm {
    let (x, y) = (rvar("x"), rvar("y"));
    let concl = rlt(med(x.clone(), y.clone()), y.clone());
    let body = rlt(x, y).imp(concl).expect("mediant_lt");
    axiom(forall_rat(&["x", "y"], body))
}

cached_thm! {
    /// `⊢ ∀x y. x < y ⟹ ∃z. x < z ∧ z < y` — **the rationals are dense.**
    ///
    /// A genuine derivation: the mediant `z = mediant x y` is the witness,
    /// `mediant_gt` / `mediant_lt` give the two strict inequalities, and
    /// `∃`-introduction + `∧`-introduction package them. The only
    /// postulated leaves are the two mediant inequalities; once they are
    /// discharged this theorem is hypothesis-free.
    pub fn dense() -> Thm {
        dense_impl().expect("dense derivation")
    }
}
fn dense_impl() -> Result<Thm> {
    let (x, y) = (rvar("x"), rvar("y"));
    let m = med(x.clone(), y.clone());
    let hyp = rlt(x.clone(), y.clone());
    let h = Thm::assume(hyp.clone())?;

    // {x<y} ⊢ x < m   and   {x<y} ⊢ m < y.
    let gt = mediant_gt()
        .all_elim(x.clone())?
        .all_elim(y.clone())?
        .imp_elim(h.clone())?;
    let lt = mediant_lt()
        .all_elim(x.clone())?
        .all_elim(y.clone())?
        .imp_elim(h)?;
    let conj = gt.and_intro(lt)?; // {x<y} ⊢ x < m ∧ m < y

    // ∃z. x < z ∧ z < y, with witness `m`.
    let z = rvar("z");
    let pred_body = rlt(x.clone(), z.clone()).and(rlt(z.clone(), y.clone()))?;
    let pred = Term::abs(rat(), subst::close(&pred_body, "z"));
    let pf = Thm::beta_conv(Term::app(pred.clone(), m.clone()))?
        .sym()?
        .eq_mp(conj)?; // {x<y} ⊢ pred m
    let ex = logic::exists_intro(pred, m, pf)?; // {x<y} ⊢ ∃z. x<z ∧ z<y

    ex.imp_intro(&hyp)?
        .all_intro("y", rat())?
        .all_intro("x", rat())
}

crate::cov_theory! {
    /// rat commutative-ring laws ported to `rat.cov`, over `core` + the
    /// `ratprim` quotient seam env. Mirrors how int's ring would port one
    /// level down; the heavy quotient machinery stays in `ratprim` givens.
    pub mod cov from "rat.cov" {
        import "core" = crate::script::Env::core();
        import "ratprim" = crate::init::rat::rat_env();
        "add_comm"  => pub fn add_comm_cov;
        "mul_comm"  => pub fn mul_comm_cov;
        "lt_irrefl" => pub fn lt_irrefl_cov;
        "mul_one"   => pub fn mul_one_cov;
        "add_zero"  => pub fn add_zero_cov;
        "mul_zero"  => pub fn mul_zero_cov;
        "add_neg"   => pub fn add_neg_cov;
        "mul_assoc" => pub fn mul_assoc_cov;
        "add_assoc" => pub fn add_assoc_cov;
        "distrib"   => pub fn distrib_cov;
    }
}

#[cfg(test)]
mod cov_tests {
    use super::*;

    /// Each `.cov`-proved rat law must reach the *same* conclusion as its
    /// Rust counterpart in this module — the kernel re-derives it from the
    /// `ratprim` seam givens.
    #[test]
    fn cov_matches_rust() {
        assert_eq!(cov::add_comm_cov().concl(), super::add_comm().concl());
        assert_eq!(cov::mul_comm_cov().concl(), super::mul_comm().concl());
        assert_eq!(cov::lt_irrefl_cov().concl(), super::lt_irrefl().concl());
        assert_eq!(cov::mul_one_cov().concl(), super::mul_one().concl());
        assert_eq!(cov::add_zero_cov().concl(), super::add_zero().concl());
        assert_eq!(cov::mul_zero_cov().concl(), super::mul_zero().concl());
        assert_eq!(cov::add_neg_cov().concl(), super::add_neg().concl());
        assert_eq!(cov::mul_assoc_cov().concl(), super::mul_assoc().concl());
        assert_eq!(cov::add_assoc_cov().concl(), super::add_assoc().concl());
        assert_eq!(cov::distrib_cov().concl(), super::distrib().concl());
    }

}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rat_ty_matches_the_catalogue() {
        // The re-exported `rat` type is the `defs/rat.rs` one, and not bool.
        assert_eq!(rat(), covalence_core::defs::rat_ty());
        assert!(!rat().is_bool());
    }

    #[test]
    fn seam_givens_build() {
        // Every seam given builds with a bool conclusion and rests only on the
        // self-flagged int stubs (`int_mul_rcancel` / `int_pos_nonzero` /
        // `pos_prod_rt` / `one_pos_rt`), all of which are bool hypotheses.
        for g in [
            recon_given().unwrap(),
            add_mk_given().unwrap(),
            mul_mk_given().unwrap(),
            neg_mk_given().unwrap(),
            zero_given().unwrap(),
            one_given().unwrap(),
            class_eq_given().unwrap(),
            lt_self_given().unwrap(),
            topos_rep_given().unwrap(),
            mul_one_compute().unwrap(),
            add_zero_compute().unwrap(),
            mul_zero_compute().unwrap(),
            add_neg_compute().unwrap(),
            zero_times_given().unwrap(),
            int_distrib_r_given().unwrap(),
            mul_assoc_lhs_compute().unwrap(),
            mul_assoc_rhs_compute().unwrap(),
            add_assoc_lhs_compute().unwrap(),
            add_assoc_rhs_compute().unwrap(),
            add_assoc_bridge().unwrap(),
            distrib_lhs_compute().unwrap(),
            distrib_rhs_compute().unwrap(),
            distrib_bridge().unwrap(),
        ] {
            assert!(g.concl().type_of().unwrap().is_bool());
            assert!(g.hyps().iter().all(|h| h.type_of().unwrap().is_bool()));
        }
    }

    #[test]
    fn rat_env_builds() {
        let _ = rat_env();
    }


    #[test]
    fn recon_given_named_form() {
        // recon's RHS is `rat.MK (rat.num a)(rat.den a)` in *unreduced* named-op
        // form (a redex per projection), so `.cov` can feed it to add_mk/etc.
        let g = recon_given().unwrap();
        let a = rvar("a");
        let inst = g.all_elim(a.clone()).unwrap();
        let (l, r) = inst.concl().as_eq().unwrap();
        assert_eq!(l, &a);
        assert_eq!(r, &mk_app(&num_app(&a), &den_app(&a)));
    }

    #[test]
    fn rat_rel_is_a_binary_relation_on_pairs() {
        // rat_rel : (int×int.pos) → (int×int.pos) → bool.
        let expected = Type::fun(ip_pair(), Type::fun(ip_pair(), Type::bool()));
        assert_eq!(rat_rel().type_of().unwrap(), expected);
    }

    #[test]
    fn rel_app_reduces_to_a_cross_multiplication() {
        // rat_rel (a,1) (c,1)  β-reduces to  a·den(c,1) = c·den(a,1).
        let p = ip(Term::int_lit(2i128), one_pos());
        let q = ip(Term::int_lit(3i128), one_pos());
        let reduced = rel_app(&p, &q).reduce().unwrap();
        // The reduct is a bool equation between two int products.
        let rhs = reduced.concl().as_eq().unwrap().1;
        assert!(rhs.as_eq().is_some(), "reduct is `_ · _ = _ · _`");
    }

    #[test]
    fn mk_rat_is_a_rational() {
        let p = ip(Term::int_lit(5i128), one_pos());
        assert_eq!(mk_rat(&p).type_of().unwrap(), rat());
    }

    #[test]
    fn rat_rel_refl_and_symm_are_genuine() {
        // refl / symm are proved outright (no hypotheses).
        for t in [rat_rel_refl(), rat_rel_symm()] {
            assert!(t.hyps().is_empty(), "rat_rel refl/symm are proved");
            assert!(t.concl().type_of().unwrap().is_bool());
        }
        let (p, q) = (Term::free("p", ip_pair()), Term::free("q", ip_pair()));
        assert_eq!(
            rat_rel_refl().all_elim(p.clone()).unwrap().concl(),
            &rel_app(&p, &p)
        );
        let symm = rat_rel_symm()
            .all_elim(p.clone())
            .unwrap()
            .all_elim(q.clone())
            .unwrap();
        assert_eq!(symm.concl(), &rel_app(&p, &q).imp(rel_app(&q, &p)).unwrap());
    }

    #[test]
    fn rat_rel_trans_is_genuine() {
        // trans is now a fully genuine (hypothesis-free) theorem: the `int`
        // facts it cancels with (`int_mul_rcancel` / `int_pos_nonzero`) are
        // themselves proved in `init::int`, so no postulate leaks through.
        let t = rat_rel_trans();
        assert!(t.concl().type_of().unwrap().is_bool());
        assert!(
            t.hyps().is_empty(),
            "rat_rel_trans is hypothesis-free now that the int facts are proved"
        );
        // Shape: ∀p q r. rat_rel p q ⟹ rat_rel q r ⟹ rat_rel p r.
        let (p, q, r) = (
            Term::free("p", ip_pair()),
            Term::free("q", ip_pair()),
            Term::free("r", ip_pair()),
        );
        let inst = t
            .clone()
            .all_elim(p.clone())
            .and_then(|t| t.all_elim(q.clone()))
            .and_then(|t| t.all_elim(r.clone()))
            .unwrap();
        let expected = rel_app(&p, &q)
            .imp(rel_app(&q, &r).imp(rel_app(&p, &r)).unwrap())
            .unwrap();
        assert_eq!(inst.concl(), &expected);
    }

    #[test]
    fn class_intro_lifts_rat_rel_to_a_class_equation() {
        // With symm proved and trans postulated, the forward quotient law
        // lifts a `~`-fact to a rat-class equation over the real spec.
        use crate::init::quotient;
        let (p, q) = (Term::free("p", ip_pair()), Term::free("q", ip_pair()));
        let ab = Thm::assume(rel_app(&p, &q)).unwrap();
        let lifted = quotient::class_intro(
            &rat_spec(),
            &[],
            &ip_pair(),
            &rat_rel_symm(),
            &rat_rel_trans(),
            ab,
        )
        .expect("class_intro on rat_rel");
        let (l, r) = lifted.concl().as_eq().expect("lifted to a class equation");
        assert_eq!(l, &mk_rat(&p));
        assert_eq!(r, &mk_rat(&q));
        assert!(lifted.hyps().iter().any(|h| h == &rel_app(&p, &q)));
    }

    #[test]
    fn maps_have_the_expected_types() {
        assert_eq!(of_int().type_of().unwrap(), Type::fun(Type::int(), rat()));
        assert_eq!(of_nat().type_of().unwrap(), Type::fun(Type::nat(), rat()));
    }

    #[test]
    fn operations_have_the_expected_types() {
        let r = rat();
        let bin = Type::fun(r.clone(), Type::fun(r.clone(), r.clone()));
        let un = Type::fun(r.clone(), r.clone());
        assert_eq!(rat_add().type_of().unwrap(), bin);
        assert_eq!(rat_sub().type_of().unwrap(), bin);
        assert_eq!(rat_mul().type_of().unwrap(), bin);
        assert_eq!(rat_div().type_of().unwrap(), bin);
        assert_eq!(rat_neg().type_of().unwrap(), un);
        assert_eq!(rat_inv().type_of().unwrap(), un);
        assert_eq!(rat_zero().type_of().unwrap(), r);
        assert_eq!(rat_one().type_of().unwrap(), rat());
    }

    #[test]
    fn ring_axioms_are_well_typed_and_self_flagged() {
        // The still-postulated ring/field axioms (add_comm / mul_comm /
        // mul_assoc are now proved — see `commutativity_is_genuine` /
        // `mul_assoc_is_genuine`).
        let all = [mul_inv()];
        for ax in all {
            assert!(ax.concl().type_of().unwrap().is_bool());
            assert!(
                ax.hyps().iter().any(|h| h == ax.concl()),
                "a postulated rat axiom carries itself as a hypothesis"
            );
        }
    }

    #[test]
    fn commutativity_is_genuine() {
        // add_comm / mul_comm are proved (no hypotheses), on the nose from
        // the proved `int` commutativity facts through the quotient.
        let (a, b) = (rvar("a"), rvar("b"));
        for (thm, op) in [(add_comm(), rat_add() as Term), (mul_comm(), rat_mul())] {
            assert!(
                thm.hyps().is_empty(),
                "rat commutativity is proved, not postulated"
            );
            let inst = thm
                .all_elim(a.clone())
                .unwrap()
                .all_elim(b.clone())
                .unwrap();
            let bin = |x: Term, y: Term| Term::app(Term::app(op.clone(), x), y);
            let expected = bin(a.clone(), b.clone())
                .equals(bin(b.clone(), a.clone()))
                .unwrap();
            assert_eq!(inst.concl(), &expected);
        }
    }

    #[test]
    fn add_comm_specialises() {
        // ∀a b. a+b = b+a  ⟹  of_int 1 + of_int 2 = of_int 2 + of_int 1.
        let one = Term::app(of_int(), Term::int_lit(1i128));
        let two = Term::app(of_int(), Term::int_lit(2i128));
        let inst = add_comm()
            .all_elim(one.clone())
            .and_then(|t| t.all_elim(two.clone()))
            .expect("specialise add_comm");
        let expected = radd(one.clone(), two.clone())
            .equals(radd(two, one))
            .unwrap();
        assert_eq!(inst.concl(), &expected);
    }

    #[test]
    fn order_axioms_are_well_typed_and_self_flagged() {
        // `le_def` is the last still-postulated order axiom (it *defines* the
        // declaration-only kernel `ratLe`); `lt_irrefl`/`zero_lt_one`/
        // `lt_trans`/`lt_trichotomy` are all proved now (see their genuine
        // tests).
        for ax in [le_def()] {
            assert!(ax.concl().type_of().unwrap().is_bool());
            assert!(ax.hyps().iter().any(|h| h == ax.concl()));
        }
    }

    #[test]
    fn mul_assoc_is_genuine() {
        // (a·b)·c = a·(b·c), genuine modulo the int/int.pos round-trip stubs.
        let thm = mul_assoc();
        let (a, b, c) = (rvar("a"), rvar("b"), rvar("c"));
        let inst = thm
            .clone()
            .all_elim(a.clone())
            .and_then(|t| t.all_elim(b.clone()))
            .and_then(|t| t.all_elim(c.clone()))
            .unwrap();
        let expected = rmul(rmul(a.clone(), b.clone()), c.clone())
            .equals(rmul(a, rmul(b, c)))
            .unwrap();
        assert_eq!(inst.concl(), &expected);
        assert!(thm.hyps().iter().all(|h| h.type_of().unwrap().is_bool()));
        assert!(!thm.hyps().iter().any(|h| h == thm.concl()));
    }

    #[test]
    fn mul_one_is_genuine() {
        let thm = mul_one();
        let a = rvar("a");
        let inst = thm.clone().all_elim(a.clone()).unwrap();
        assert_eq!(inst.concl(), &rmul(a.clone(), rat_one()).equals(a).unwrap());
        assert!(thm.hyps().iter().all(|h| h.type_of().unwrap().is_bool()));
        assert!(!thm.hyps().iter().any(|h| h == thm.concl()));
    }

    #[test]
    fn add_zero_is_genuine() {
        let thm = add_zero();
        let a = rvar("a");
        let inst = thm.clone().all_elim(a.clone()).unwrap();
        assert_eq!(
            inst.concl(),
            &radd(a.clone(), rat_zero()).equals(a).unwrap()
        );
        assert!(thm.hyps().iter().all(|h| h.type_of().unwrap().is_bool()));
        assert!(!thm.hyps().iter().any(|h| h == thm.concl()));
    }

    #[test]
    fn mul_zero_is_genuine() {
        let thm = mul_zero();
        let a = rvar("a");
        let inst = thm.clone().all_elim(a.clone()).unwrap();
        assert_eq!(
            inst.concl(),
            &rmul(a, rat_zero()).equals(rat_zero()).unwrap()
        );
        assert!(thm.hyps().iter().all(|h| h.type_of().unwrap().is_bool()));
        assert!(!thm.hyps().iter().any(|h| h == thm.concl()));
    }

    #[test]
    fn add_neg_is_genuine() {
        let thm = add_neg();
        let a = rvar("a");
        let inst = thm.clone().all_elim(a.clone()).unwrap();
        let neg_a = Term::app(rat_neg(), a.clone());
        assert_eq!(inst.concl(), &radd(a, neg_a).equals(rat_zero()).unwrap());
        assert!(thm.hyps().iter().all(|h| h.type_of().unwrap().is_bool()));
        assert!(!thm.hyps().iter().any(|h| h == thm.concl()));
    }

    #[test]
    fn add_assoc_is_genuine() {
        let thm = add_assoc();
        let (a, b, c) = (rvar("a"), rvar("b"), rvar("c"));
        let inst = thm
            .clone()
            .all_elim(a.clone())
            .and_then(|t| t.all_elim(b.clone()))
            .and_then(|t| t.all_elim(c.clone()))
            .unwrap();
        let expected = radd(radd(a.clone(), b.clone()), c.clone())
            .equals(radd(a, radd(b, c)))
            .unwrap();
        assert_eq!(inst.concl(), &expected);
        assert!(thm.hyps().iter().all(|h| h.type_of().unwrap().is_bool()));
        assert!(!thm.hyps().iter().any(|h| h == thm.concl()));
    }

    #[test]
    fn distrib_is_genuine() {
        let thm = distrib();
        let (a, b, c) = (rvar("a"), rvar("b"), rvar("c"));
        let inst = thm
            .clone()
            .all_elim(a.clone())
            .and_then(|t| t.all_elim(b.clone()))
            .and_then(|t| t.all_elim(c.clone()))
            .unwrap();
        let expected = rmul(a.clone(), radd(b.clone(), c.clone()))
            .equals(radd(rmul(a.clone(), b), rmul(a, c)))
            .unwrap();
        assert_eq!(inst.concl(), &expected);
        assert!(thm.hyps().iter().all(|h| h.type_of().unwrap().is_bool()));
        assert!(!thm.hyps().iter().any(|h| h == thm.concl()));
    }

    #[test]
    fn lt_irrefl_is_genuine() {
        let thm = lt_irrefl();
        assert!(
            thm.hyps().is_empty(),
            "rat::lt_irrefl is proved, not postulated"
        );
        let a = rvar("a");
        let inst = thm.all_elim(a.clone()).unwrap();
        assert_eq!(inst.concl(), &rlt(a.clone(), a.clone()).not().unwrap());
    }

    #[test]
    fn zero_lt_one_is_genuine() {
        let t = zero_lt_one();
        assert!(t.hyps().is_empty(), "rat::zero_lt_one is proved");
        assert_eq!(t.concl(), &rlt(rat_zero(), rat_one()));
    }

    #[test]
    fn lt_trichotomy_is_genuine() {
        let (a, b) = (rvar("a"), rvar("b"));
        let t = lt_trichotomy();
        assert!(t.hyps().is_empty(), "rat::lt_trichotomy is proved");
        let inst = t.all_elim(a.clone()).unwrap().all_elim(b.clone()).unwrap();
        let expected = rlt(a.clone(), b.clone())
            .or(a
                .clone()
                .equals(b.clone())
                .unwrap()
                .or(rlt(b.clone(), a.clone()))
                .unwrap())
            .unwrap();
        assert_eq!(inst.concl(), &expected);
    }

    #[test]
    fn lt_trans_is_genuine() {
        let (a, b, c) = (rvar("a"), rvar("b"), rvar("c"));
        let t = lt_trans();
        assert!(t.hyps().is_empty(), "rat::lt_trans is proved");
        let inst = t
            .all_elim(a.clone())
            .unwrap()
            .all_elim(b.clone())
            .unwrap()
            .all_elim(c.clone())
            .unwrap();
        let expected = rlt(a.clone(), b.clone())
            .imp(rlt(b, c.clone()).imp(rlt(a, c)).unwrap())
            .unwrap();
        assert_eq!(inst.concl(), &expected);
    }

    #[test]
    fn order_toolkit_derivations_are_well_typed() {
        // le_refl / lt_imp_le / le_trans / not_one_le_zero are derived: they
        // carry only postulate hypotheses (no stray assumptions), are
        // bool-typed, and have the expected shapes.
        let a = rvar("a");
        let refl = le_refl().all_elim(a.clone()).unwrap();
        assert_eq!(refl.concl(), &rle(a.clone(), a.clone()));

        // not_one_le_zero : ¬(1 ≤ 0), resting on the zero_lt_one postulate.
        let n = not_one_le_zero();
        assert_eq!(n.concl(), &rle(rat_one(), rat_zero()).not().unwrap());
        assert!(n.hyps().iter().all(|h| h.type_of().unwrap().is_bool()));

        // le_trans specialises to a concrete double implication.
        let (x, y, z) = (rvar("x"), rvar("y"), rvar("z"));
        let lt = le_trans()
            .all_elim(x.clone())
            .and_then(|t| t.all_elim(y.clone()))
            .and_then(|t| t.all_elim(z.clone()))
            .unwrap();
        let expected = rle(x.clone(), y.clone())
            .imp(rle(y, z.clone()).imp(rle(x, z)).unwrap())
            .unwrap();
        assert_eq!(lt.concl(), &expected);
    }

    #[test]
    fn linear_order_facts_have_expected_shapes() {
        // lt_asymm / lt_imp_ne / le_antisym / le_total — derived, carrying
        // only (bool) postulate hypotheses, with the expected shapes.
        let (a, b) = (rvar("a"), rvar("b"));
        for t in [lt_asymm(), lt_imp_ne(), le_antisym(), le_total()] {
            assert!(t.concl().type_of().unwrap().is_bool());
            assert!(t.hyps().iter().all(|h| h.type_of().unwrap().is_bool()));
        }

        let inst2 = |t: Thm| t.all_elim(a.clone()).unwrap().all_elim(b.clone()).unwrap();

        // ∀a b. a < b ⟹ ¬(b < a).
        let asym = inst2(lt_asymm());
        let exp_asym = rlt(a.clone(), b.clone())
            .imp(rlt(b.clone(), a.clone()).not().unwrap())
            .unwrap();
        assert_eq!(asym.concl(), &exp_asym);

        // ∀a b. a < b ⟹ ¬(a = b).
        let ne = inst2(lt_imp_ne());
        let exp_ne = rlt(a.clone(), b.clone())
            .imp(a.clone().equals(b.clone()).unwrap().not().unwrap())
            .unwrap();
        assert_eq!(ne.concl(), &exp_ne);

        // ∀a b. a ≤ b ⟹ b ≤ a ⟹ a = b.
        let anti = inst2(le_antisym());
        let exp_anti = rle(a.clone(), b.clone())
            .imp(
                rle(b.clone(), a.clone())
                    .imp(a.clone().equals(b.clone()).unwrap())
                    .unwrap(),
            )
            .unwrap();
        assert_eq!(anti.concl(), &exp_anti);

        // ∀a b. a ≤ b ∨ b ≤ a.
        let tot = inst2(le_total());
        let exp_tot = rle(a.clone(), b.clone())
            .or(rle(b.clone(), a.clone()))
            .unwrap();
        assert_eq!(tot.concl(), &exp_tot);
    }

    #[test]
    fn rat_lt_and_mediant_have_expected_types() {
        let r = rat();
        assert_eq!(
            rat_lt().type_of().unwrap(),
            Type::fun(r.clone(), Type::fun(r.clone(), Type::bool()))
        );
        assert_eq!(
            mediant().type_of().unwrap(),
            Type::fun(r.clone(), Type::fun(r.clone(), r))
        );
    }

    #[test]
    fn dense_is_derived_from_the_mediant_postulates() {
        let thm = dense();
        // The statement: ∀x y. x < y ⟹ ∃z. x < z ∧ z < y.
        let (x, y) = (rvar("x"), rvar("y"));
        let inst = thm
            .clone()
            .all_elim(x.clone())
            .and_then(|t| t.all_elim(y.clone()))
            .unwrap();
        // The consequent of the (instantiated) implication is an ∃.
        let (ante, conseq) = {
            let c = inst.concl();
            // c = (x < y) ⟹ ∃z. …
            let (head, conseq) = c.as_app().unwrap();
            let (_imp, ante) = head.as_app().unwrap();
            (ante.clone(), conseq.clone())
        };
        assert_eq!(ante, rlt(x, y));
        // The consequent is `exists[rat] pred`.
        let head = conseq.as_app().expect("consequent is an application").0;
        assert_eq!(head, &covalence_core::defs::exists(rat()));

        // dense is genuine *modulo* exactly the two mediant postulates: it
        // carries them (and nothing else) as hypotheses.
        let hyps = thm.hyps();
        assert_eq!(hyps.len(), 2, "only the two mediant postulates remain");
        for h in hyps {
            assert!(h.type_of().unwrap().is_bool());
        }
    }

    #[test]
    fn of_nat_factors_through_of_int() {
        // ∀n. of_nat n = of_int (nat.toInt n); specialise to a concrete n.
        let n = Term::free("k", Type::nat());
        let inst = of_nat_via_int().all_elim(n.clone()).unwrap();
        let lhs = Term::app(of_nat(), n.clone());
        let rhs = Term::app(of_int(), Term::app(nat::nat_to_int(), n));
        // of_nat_via_int is a β-fact: genuine, hypothesis-free.
        assert!(of_nat_via_int().hyps().is_empty());
        let (l, r) = inst.concl().as_eq().unwrap();
        assert_eq!(l, &lhs);
        assert_eq!(r, &rhs);
    }
}



