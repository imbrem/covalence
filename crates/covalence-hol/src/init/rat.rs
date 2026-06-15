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
    let rhs = applied.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone();
    applied.trans(Thm::beta_conv(rhs)?) // ⊢ op a b = body_a[y:=b]
}

/// From `⊢ n1 = n2` and `⊢ d1 = d2` build `⊢ pair n1 d1 = pair n2 d2` at
/// `int × int.pos` — congruence of the representative pair in both slots.
fn pair_cong(num_eq: Thm, den_eq: Thm) -> Result<Thm> {
    let pair_op = covalence_core::defs::pair(Type::int(), int_pos_ty());
    let d1 = den_eq.concl().as_eq().ok_or(Error::NotAnEquation)?.0.clone();
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

/// `⊢ 0 < 1` — the base strictness fact (postulated; `ratLt` is stuck at
/// the ε-chosen representatives, so this is not reducible).
pub fn zero_lt_one() -> Thm {
    axiom(rlt(rat_zero(), rat_one()))
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
    let disj = Thm::assume(lt.clone())?
        .or_intro_l(a.clone().equals(b.clone())?)?; // {a<b} ⊢ a<b ∨ a=b
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

    disj
        .or_elim(br_lt, br_eq)? // {1≤0, 0<1} ⊢ F
        .imp_intro(&one_le_zero)?
        .not_intro()
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
        // The still-postulated ring/field axioms (add_comm / mul_comm are
        // now proved — see `commutativity_is_genuine`).
        let all = [
            add_assoc(),
            add_zero(),
            add_neg(),
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
    fn commutativity_is_genuine() {
        // add_comm / mul_comm are proved (no hypotheses), on the nose from
        // the proved `int` commutativity facts through the quotient.
        let (a, b) = (rvar("a"), rvar("b"));
        for (thm, op) in [
            (add_comm(), rat_add() as Term),
            (mul_comm(), rat_mul()),
        ] {
            assert!(thm.hyps().is_empty(), "rat commutativity is proved, not postulated");
            let inst = thm.all_elim(a.clone()).unwrap().all_elim(b.clone()).unwrap();
            let bin = |x: Term, y: Term| Term::app(Term::app(op.clone(), x), y);
            let expected = bin(a.clone(), b.clone()).equals(bin(b.clone(), a.clone())).unwrap();
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
        for ax in [lt_irrefl(), lt_trans(), lt_trichotomy(), le_def()] {
            assert!(ax.concl().type_of().unwrap().is_bool());
            assert!(ax.hyps().iter().any(|h| h == ax.concl()));
        }
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
