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
//! Remaining to discharge the postulates below: (1) the **β
//! reconciliation** — `class_intro`'s `classOf a = λx. rel a x` vs
//! `defs/int.rs`'s β-reduced `mk_int`; and (2) **unfolding each `int` op**
//! to its representative-pair body (δ + the quotient coercions) so the
//! axiom reduces to a `nat` fact lifted through `class_intro`. The
//! converse law (`mkClass a = mkClass b ⟹ rel a b`, for dis-equations /
//! order) is the other quotient piece; see `SKELETONS.md`.

use covalence_core::defs::{fst, prod, snd};
use covalence_core::{Error, Result, Term, Thm, Type, subst};

use crate::init::ext::{TermExt, ThmExt};
use crate::init::nat;

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
    pub fn int_rel_refl() -> Thm {
        int_rel_refl_impl().expect("int_rel_refl")
    }
}
fn int_rel_refl_impl() -> Result<Thm> {
    let p = Term::free("p", nn());
    let reduced = Thm::refl(nat::add(fst_nn(&p), snd_nn(&p)))?;
    expand_rel(reduced, &rel_app(&p, &p))?.all_intro("p", nn())
}

cached_thm! {
    /// `⊢ ∀p q. int_rel p q ⟹ int_rel q p` — symmetry (`sym` of the
    /// defining `nat` equation).
    pub fn int_rel_symm() -> Thm {
        int_rel_symm_impl().expect("int_rel_symm")
    }
}
fn int_rel_symm_impl() -> Result<Thm> {
    let (p, q) = (Term::free("p", nn()), Term::free("q", nn()));
    let hyp = rel_app(&p, &q);
    let flipped = reduce_rel(Thm::assume(hyp.clone())?)?.sym()?; // ⊢ fst q+snd p = fst p+snd q
    expand_rel(flipped, &rel_app(&q, &p))?
        .imp_intro(&hyp)?
        .all_intro("q", nn())?
        .all_intro("p", nn())
}

cached_thm! {
    /// `⊢ ∀p q r. int_rel p q ⟹ int_rel q r ⟹ int_rel p r` —
    /// transitivity, by adding the two defining equations and cancelling
    /// the common `nat` summand (`add_interchange` + `add_cancel`).
    pub fn int_rel_trans() -> Thm {
        int_rel_trans_impl().expect("int_rel_trans")
    }
}
fn int_rel_trans_impl() -> Result<Thm> {
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
fn rep_pair(a: &Term) -> Term {
    let rep = Term::spec_rep(covalence_core::defs::int_ty_spec(), Vec::<Type>::new());
    let rep_a = Term::app(rep, a.clone());
    let p = Term::free("p", nn());
    let pred = Term::abs(nn(), subst::close(&Term::app(rep_a, p), "p"));
    Term::app(Term::select_op(nn()), pred)
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
// Commutative ring
// ============================================================================

cached_thm! {
    /// `⊢ ∀a b. a + b = b + a` — **proved**. `int.add` is componentwise
    /// `nat` addition on representatives, which is commutative *on the nose*
    /// (`Pa = fst(rep a)+fst(rep b) = fst(rep b)+fst(rep a) = Qa` by
    /// `nat::add_comm`, likewise `Pb = Qb`), so no quotient lifting is
    /// needed: unfold both sides and rewrite the representative components.
    pub fn add_comm() -> Thm {
        add_comm_impl().expect("int::add_comm derivation")
    }
}
fn add_comm_impl() -> Result<Thm> {
    let (a, b) = (var("a"), var("b"));
    let dl = add_defining_eq(&a, &b)?; // int.add a b = abs(classOf(pair Pa Pb))
    let dr = add_defining_eq(&b, &a)?; // int.add b a = abs(classOf(pair Qa Qb))

    // Pa = Qa (commute first components); Pb = Qb (second components).
    let (rpa, rpb) = (rep_pair(&a), rep_pair(&b));
    let eq_a = nat::add_comm().all_elim(fst_nn(&rpa))?.all_elim(fst_nn(&rpb))?;
    let eq_b = nat::add_comm().all_elim(snd_nn(&rpa))?.all_elim(snd_nn(&rpb))?;

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

/// `⊢ ∀a b c. (a + b) + c = a + (b + c)`.
pub fn add_assoc() -> Thm {
    let (a, b, c) = (var("a"), var("b"), var("c"));
    let lhs = add(add(a.clone(), b.clone()), c.clone());
    let rhs = add(a, add(b, c));
    let eq = lhs.equals(rhs).expect("add_assoc");
    axiom(forall_int(&["a", "b", "c"], eq))
}

/// `⊢ ∀a. a + 0 = a`.
pub fn add_zero() -> Thm {
    let a = var("a");
    let eq = add(a.clone(), lit(0)).equals(a).expect("add_zero: a + 0 = a");
    axiom(forall_int(&["a"], eq))
}

/// `⊢ ∀a. a + (-a) = 0` — additive inverse.
pub fn add_neg() -> Thm {
    let a = var("a");
    let eq = add(a.clone(), neg(a))
        .equals(lit(0))
        .expect("add_neg: a + (-a) = 0");
    axiom(forall_int(&["a"], eq))
}

cached_thm! {
    /// `⊢ ∀a b. a * b = b * a` — **proved**. Like [`add_comm`], `int.mul`
    /// is built from `nat::mul` on representatives, so commutativity is *on
    /// the nose*: the first component `fa·fb + sa·sb` commutes to
    /// `fb·fa + sb·sa` by `nat::mul_comm`, and the second `fa·sb + sa·fb`
    /// to `fb·sa + sb·fa` by `nat::mul_comm` (each product) plus one
    /// `nat::add_comm` (to swap the two summands). Unfold + rewrite.
    pub fn mul_comm() -> Thm {
        mul_comm_impl().expect("int::mul_comm derivation")
    }
}
fn mul_comm_impl() -> Result<Thm> {
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
    let eq = mul(a.clone(), lit(1)).equals(a).expect("mul_one: a * 1 = a");
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

/// `⊢ ∀a b. a - b = a + (-b)` — subtraction by negation.
pub fn sub_def() -> Thm {
    let (a, b) = (var("a"), var("b"));
    let sub = Term::app(Term::app(int_sub(), a.clone()), b.clone());
    let eq = sub.equals(add(a, neg(b))).expect("sub_def: a - b = a + (-b)");
    axiom(forall_int(&["a", "b"], eq))
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
            add_assoc(),
            add_zero(),
            add_neg(),
            mul_assoc(),
            mul_one(),
            mul_zero(),
            distrib(),
            sub_def(),
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
    fn add_comm_is_a_genuine_theorem() {
        let thm = add_comm();
        assert!(thm.hyps().is_empty(), "int::add_comm is proved, not postulated");
        // ∀a b. a + b = b + a, specialised.
        let (a, b) = (var("a"), var("b"));
        let inst = thm.all_elim(a.clone()).unwrap().all_elim(b.clone()).unwrap();
        let expected = add(a.clone(), b.clone()).equals(add(b, a)).unwrap();
        assert_eq!(inst.concl(), &expected);
    }

    #[test]
    fn mul_comm_is_a_genuine_theorem() {
        let thm = mul_comm();
        assert!(thm.hyps().is_empty(), "int::mul_comm is proved, not postulated");
        let (a, b) = (var("a"), var("b"));
        let inst = thm.all_elim(a.clone()).unwrap().all_elim(b.clone()).unwrap();
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
        assert_eq!(int_rel_refl().all_elim(p.clone()).unwrap().concl(), &rel_app(&p, &p));
        // symm specialises to `int_rel p q ⟹ int_rel q p`.
        let symm = int_rel_symm().all_elim(p.clone()).unwrap().all_elim(q.clone()).unwrap();
        assert_eq!(symm.concl(), &rel_app(&p, &q).imp(rel_app(&q, &p)).unwrap());
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
        let lifted = quotient::class_intro(
            &spec,
            &[],
            &nn(),
            &int_rel_symm(),
            &int_rel_trans(),
            ab,
        )
        .expect("class_intro on int_rel");
        assert!(lifted.concl().as_eq().is_some(), "lifted to a class equation");
        assert!(lifted.hyps().iter().any(|h| h == &rel_app(&p, &q)));
    }
}
