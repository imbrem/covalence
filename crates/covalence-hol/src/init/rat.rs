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
//!   [`rat_add`], [`rat_neg`], [`rat_mul`]) and the strict order
//!   ([`rat_lt`]) are defined at the representative level; the ordered-
//!   field axioms over them are **postulated** (same audit-trail style as
//!   `init::int`), pending the quotient derivations.
//! - **Density.** [`dense`] — `∀x y. x < y ⟹ ∃z. x < z ∧ z < y` — is
//!   **derived** from the two mediant-inequality postulates via the
//!   mediant `(a+c)/(b+d)`, the witness that needs no division.

use covalence_core::defs::{fst, int_pos_spec, int_pos_ty, prod, snd};
use covalence_core::{Result, Term, Thm, Type, subst};

use crate::init::ext::TermExt;
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
    let (p, q) = (Term::free("p", pair_ty.clone()), Term::free("q", pair_ty.clone()));
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
    Term::app(Term::spec_abs(int_pos_spec(), Vec::new()), Term::int_lit(1i128))
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

/// Universally close `body` over the named representative-pair variables,
/// outermost first.
fn forall_pair(vars: &[&str], body: Term) -> Term {
    let mut t = body;
    for name in vars.iter().rev() {
        t = t.forall(name, ip_pair()).expect("forall_pair: bind variable");
    }
    t
}

// ============================================================================
// `rat_rel` is an equivalence
// ============================================================================
//
// `refl` / `symm` are pure `int`-equation manipulations of the cross-
// multiplication body and are **proved** outright. `trans` is the one
// piece that needs `int` *multiplicative cancellation by a positive*
// denominator (from `a·d = c·b` and `c·f = e·d`, cancel `d` to reach
// `a·f = e·b`); that `int` fact is not yet discharged, so `trans` is a
// postulate (`SKELETONS.md`).

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
    /// transitivity.
    ///
    /// **Postulated** (audit hyp). The derivation: from `num p · den q =
    /// num q · den p` and `num q · den r = num r · den q`, multiply the
    /// first by `den r` and the second by `den p`, commute/associate so
    /// the common `num q · den q · den r` factor matches, giving
    /// `(num p · den r) · den q = (num r · den p) · den q`, then cancel
    /// `den q` (strictly positive, hence nonzero) — the `int`
    /// multiplicative cancellation that is not yet a proved `int` fact.
    pub fn rat_rel_trans() -> Thm {
        let (p, q, r) = (
            Term::free("p", ip_pair()),
            Term::free("q", ip_pair()),
            Term::free("r", ip_pair()),
        );
        let pr = rel_app(&p, &r);
        let body = rel_app(&p, &q)
            .imp(rel_app(&q, &r).imp(pr).expect("rat_rel_trans inner"))
            .expect("rat_rel_trans");
        axiom(forall_pair(&["p", "q", "r"], body))
    }
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

/// `mkRat (build px py)` for a binary op: `px = repPair x`, `py = repPair y`.
fn binary_rat(build: impl Fn(&Term, &Term) -> Term) -> Term {
    let (x, y) = (Term::free("x", rat()), Term::free("y", rat()));
    let body = mk_rat(&build(&rep_pair(x.clone()), &rep_pair(y.clone())));
    Term::abs(rat(), subst::close(&Term::abs(rat(), subst::close(&body, "y")), "x"))
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
    binary_rat(|px, py| {
        ip(imul(num(px), num(py)), to_pos(imul(den(px), den(py))))
    })
}

/// `ratNeg : rat → rat` ≡ `-(a/b) = (-a)/b` (denominator unchanged).
pub fn rat_neg() -> Term {
    let x = Term::free("x", rat());
    let px = rep_pair(x.clone());
    let neg_num = Term::app(int::int_neg(), num(&px));
    let body = mk_rat(&ip(neg_num, den_pos(&px)));
    Term::abs(rat(), subst::close(&body, "x"))
}

// ============================================================================
// Commutative-ring axioms (and the field inverse) — postulated
// ============================================================================
//
// Same audit-trail style as `init::int`: each is a `Thm::assume` carrying
// its statement as a self-hyp. They are HOL theorems of the quotient,
// derivable from the `int` ordered-ring theory; discharging them does not
// change this public surface. See `SKELETONS.md`.

fn rvar(name: &str) -> Term {
    Term::free(name, rat())
}
fn radd(a: Term, b: Term) -> Term {
    Term::app(Term::app(rat_add(), a), b)
}
fn rmul(a: Term, b: Term) -> Term {
    Term::app(Term::app(rat_mul(), a), b)
}
fn rneg(a: Term) -> Term {
    Term::app(rat_neg(), a)
}
fn forall_rat(vars: &[&str], body: Term) -> Term {
    let mut t = body;
    for name in vars.iter().rev() {
        t = t.forall(name, rat()).expect("forall_rat: bind variable");
    }
    t
}

/// `⊢ ∀a b. a + b = b + a`.
pub fn add_comm() -> Thm {
    let (a, b) = (rvar("a"), rvar("b"));
    let eq = radd(a.clone(), b.clone()).equals(radd(b, a)).expect("add_comm");
    axiom(forall_rat(&["a", "b"], eq))
}

/// `⊢ ∀a b c. (a + b) + c = a + (b + c)`.
pub fn add_assoc() -> Thm {
    let (a, b, c) = (rvar("a"), rvar("b"), rvar("c"));
    let lhs = radd(radd(a.clone(), b.clone()), c.clone());
    let rhs = radd(a, radd(b, c));
    axiom(forall_rat(&["a", "b", "c"], lhs.equals(rhs).expect("add_assoc")))
}

/// `⊢ ∀a. a + 0 = a`.
pub fn add_zero() -> Thm {
    let a = rvar("a");
    let eq = radd(a.clone(), rat_zero()).equals(a).expect("add_zero");
    axiom(forall_rat(&["a"], eq))
}

/// `⊢ ∀a. a + (-a) = 0` — additive inverse.
pub fn add_neg() -> Thm {
    let a = rvar("a");
    let eq = radd(a.clone(), rneg(a)).equals(rat_zero()).expect("add_neg");
    axiom(forall_rat(&["a"], eq))
}

/// `⊢ ∀a b. a * b = b * a`.
pub fn mul_comm() -> Thm {
    let (a, b) = (rvar("a"), rvar("b"));
    let eq = rmul(a.clone(), b.clone()).equals(rmul(b, a)).expect("mul_comm");
    axiom(forall_rat(&["a", "b"], eq))
}

/// `⊢ ∀a b c. (a * b) * c = a * (b * c)`.
pub fn mul_assoc() -> Thm {
    let (a, b, c) = (rvar("a"), rvar("b"), rvar("c"));
    let lhs = rmul(rmul(a.clone(), b.clone()), c.clone());
    let rhs = rmul(a, rmul(b, c));
    axiom(forall_rat(&["a", "b", "c"], lhs.equals(rhs).expect("mul_assoc")))
}

/// `⊢ ∀a. a * 1 = a`.
pub fn mul_one() -> Thm {
    let a = rvar("a");
    let eq = rmul(a.clone(), rat_one()).equals(a).expect("mul_one");
    axiom(forall_rat(&["a"], eq))
}

/// `⊢ ∀a. a * 0 = 0`.
pub fn mul_zero() -> Thm {
    let a = rvar("a");
    let eq = rmul(a, rat_zero()).equals(rat_zero()).expect("mul_zero");
    axiom(forall_rat(&["a"], eq))
}

/// `⊢ ∀a b c. a * (b + c) = a * b + a * c` — left distributivity.
pub fn distrib() -> Thm {
    let (a, b, c) = (rvar("a"), rvar("b"), rvar("c"));
    let lhs = rmul(a.clone(), radd(b.clone(), c.clone()));
    let rhs = radd(rmul(a.clone(), b), rmul(a, c));
    axiom(forall_rat(&["a", "b", "c"], lhs.equals(rhs).expect("distrib")))
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
    let neq = a.clone().equals(rat_zero()).expect("mul_inv: a = 0").not().expect("mul_inv: ≠");
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
    Term::abs(rat(), subst::close(&Term::abs(rat(), subst::close(&body, "y")), "x"))
}

/// `a < b` on `rat`.
fn rlt(a: Term, b: Term) -> Term {
    Term::app(Term::app(rat_lt(), a), b)
}
/// `a ≤ b` on `rat` (the declared kernel `ratLe`).
fn rle(a: Term, b: Term) -> Term {
    Term::app(Term::app(rat_le(), a), b)
}

/// `⊢ ∀a. ¬(a < a)` — irreflexivity.
pub fn lt_irrefl() -> Thm {
    let a = rvar("a");
    axiom(forall_rat(&["a"], rlt(a.clone(), a).not().expect("lt_irrefl")))
}

/// `⊢ ∀a b c. a < b ⟹ b < c ⟹ a < c` — transitivity.
pub fn lt_trans() -> Thm {
    let (a, b, c) = (rvar("a"), rvar("b"), rvar("c"));
    let inner = rlt(b.clone(), c.clone())
        .imp(rlt(a.clone(), c))
        .expect("lt_trans inner");
    let body = rlt(a, b).imp(inner).expect("lt_trans");
    axiom(forall_rat(&["a", "b", "c"], body))
}

/// `⊢ ∀a b. a < b ∨ a = b ∨ b < a` — trichotomy (totality).
pub fn lt_trichotomy() -> Thm {
    let (a, b) = (rvar("a"), rvar("b"));
    let eq = a.clone().equals(b.clone()).expect("trichotomy: a = b");
    let tail = eq.or(rlt(b.clone(), a.clone())).expect("trichotomy tail");
    let body = rlt(a, b).or(tail).expect("trichotomy");
    axiom(forall_rat(&["a", "b"], body))
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
    binary_rat(|px, py| {
        ip(iadd(num(px), num(py)), to_pos(iadd(den(px), den(py))))
    })
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
    fn rat_rel_is_a_binary_relation_on_pairs() {
        // rat_rel : (int×int.pos) → (int×int.pos) → bool.
        let expected = Type::fun(
            ip_pair(),
            Type::fun(ip_pair(), Type::bool()),
        );
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
        assert_eq!(rat_rel_refl().all_elim(p.clone()).unwrap().concl(), &rel_app(&p, &p));
        let symm = rat_rel_symm()
            .all_elim(p.clone())
            .unwrap()
            .all_elim(q.clone())
            .unwrap();
        assert_eq!(symm.concl(), &rel_app(&p, &q).imp(rel_app(&q, &p)).unwrap());
    }

    #[test]
    fn rat_rel_trans_is_a_self_flagged_postulate() {
        let t = rat_rel_trans();
        assert!(t.concl().type_of().unwrap().is_bool());
        assert!(
            t.hyps().iter().any(|h| h == t.concl()),
            "the postulate carries itself as a hypothesis"
        );
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
        assert_eq!(rat_add().type_of().unwrap(), bin);
        assert_eq!(rat_mul().type_of().unwrap(), bin);
        assert_eq!(rat_neg().type_of().unwrap(), Type::fun(r.clone(), r.clone()));
        assert_eq!(rat_zero().type_of().unwrap(), r);
        assert_eq!(rat_one().type_of().unwrap(), rat());
    }

    #[test]
    fn ring_axioms_are_well_typed_and_self_flagged() {
        let all = [
            add_comm(),
            add_assoc(),
            add_zero(),
            add_neg(),
            mul_comm(),
            mul_assoc(),
            mul_one(),
            mul_zero(),
            distrib(),
            mul_inv(),
        ];
        for ax in all {
            assert!(ax.concl().type_of().unwrap().is_bool());
            assert!(
                ax.hyps().iter().any(|h| h == ax.concl()),
                "a postulated rat axiom carries itself as a hypothesis"
            );
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
        for ax in [lt_irrefl(), lt_trans(), lt_trichotomy(), le_def()] {
            assert!(ax.concl().type_of().unwrap().is_bool());
            assert!(ax.hyps().iter().any(|h| h == ax.concl()));
        }
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
