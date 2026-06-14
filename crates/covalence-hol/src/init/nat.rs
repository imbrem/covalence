//! `nat` theorems: the `defs/nat.rs` catalogue re-exported, plus the
//! proved Peano properties of HOL `nat` — mirroring how [`init::logic`]
//! pairs the connective definitions with their proved facts.
//!
//! [`init::logic`]: crate::init::logic
//!
//! This module is the home of the *theorems*; the **shallow embedding**
//! of Peano arithmetic into HOL (the [`Peano`] trait impl) lives in
//! [`crate::peano::shallow`] and reads its axioms from here.
//!
//! ## The single postulate, and everything derived from it
//!
//! - **Genuine** (hypothesis-free): [`succ_inj`] / [`zero_ne_succ`]
//!   (kernel freeness primitives generalised with `all_intro`).
//! - **[`rec_holds`]** — `natRec` satisfies its recursion equations.
//!   This is the **one** remaining `nat` postulate (`Thm::assume`,
//!   flagged in `SKELETONS.md`). The plan (option **B**) is to prove it
//!   via the recursion theorem (`∃r. P_rec r` + `spec_ax` + induction).
//! - **Derived from [`rec_holds`] alone**: the four recursion equations
//!   [`add_base`] / [`add_step`] / [`mul_base`] / [`mul_step`], by
//!   δ-unfolding `nat.add` / `nat.mul` / `iter` down to `natRec` and
//!   applying [`rec_holds`]; and on top of those, the **additive theory**
//!   [`add_zero`] / [`add_succ_r`] / [`add_comm`] / [`add_assoc`], proved
//!   by `nat`-induction (the [`induct`] helper). Each therefore carries
//!   exactly *one* hypothesis — [`rec_holds`]'s conclusion. **The moment
//!   `rec_holds` becomes a hypothesis-free proof, all of these become
//!   genuine theorems automatically, with no change here.**
//!
//! These additive facts are the `nat` half of what the `int` quotient
//! lift ([`init::int`](crate::init::int)) needs.

use covalence_core::{Result, Term, Thm, Type, defs, subst};
use covalence_types::Nat;

use crate::init::ext::{TermExt, ThmExt};

// Re-export the `defs/nat.rs` term catalogue (the operations; the
// `*_spec` handles stay in `covalence_core::defs`).
pub use covalence_core::defs::{
    iter, nat_add, nat_div, nat_le, nat_lt, nat_mod, nat_mul, nat_pow, nat_pred, nat_rec, nat_sub,
    nat_succ, nat_to_int,
};

// ============================================================================
// Small term helpers (private — the public surface is theorems)
// ============================================================================

fn nat() -> Type {
    Type::nat()
}

pub(crate) fn zero() -> Term {
    Term::nat_lit(Nat::zero())
}

pub(crate) fn succ(n: Term) -> Term {
    Term::app(nat_succ(), n)
}

pub(crate) fn add(a: Term, b: Term) -> Term {
    Term::app(Term::app(nat_add(), a), b)
}

pub(crate) fn mul(a: Term, b: Term) -> Term {
    Term::app(Term::app(nat_mul(), a), b)
}

fn var(name: &str) -> Term {
    Term::free(name, nat())
}

/// `nat → nat → nat`, the type of a `natRec` step over `nat`.
fn step_ty() -> Type {
    Type::fun(nat(), Type::fun(nat(), nat()))
}

/// `natRec[nat] a b c`.
fn rec3(a: Term, b: Term, c: Term) -> Term {
    Term::app(Term::app(Term::app(nat_rec(nat()), a), b), c)
}

/// The RHS of an equational theorem (panics if not `⊢ _ = _`).
fn rhs(thm: &Thm) -> Term {
    thm.concl()
        .as_eq()
        .expect("init::nat: expected an equation")
        .1
        .clone()
}

// ============================================================================
// Freeness — genuine, from the kernel primitives
// ============================================================================

/// `⊢ ∀m n. (S m = S n) ⟹ (m = n)` — successor injectivity.
pub fn succ_inj() -> Thm {
    Thm::succ_inj(var("m"), var("n"))
        .and_then(|t| t.all_intro("n", nat()))
        .and_then(|t| t.all_intro("m", nat()))
        .expect("succ_inj: kernel freeness rule")
}

/// `⊢ ∀n. ¬(0 = S n)` — zero is not a successor.
pub fn zero_ne_succ() -> Thm {
    Thm::zero_ne_succ(var("n"))
        .and_then(|t| t.all_intro("n", nat()))
        .expect("zero_ne_succ: kernel freeness rule")
}

// ============================================================================
// The recursion equation — the single postulate (pending the recursion theorem)
// ============================================================================

/// `⊢ ∀z f. (natRec z f 0 = z) ∧ (∀n. natRec z f (S n) = f n (natRec z f n))`
/// at `α = nat` — `natRec` satisfies its recursion equations.
///
/// **Postulated** for now (the only `nat` postulate). Proving it via the
/// recursion theorem discharges everything below automatically — see the
/// [module docs](self).
pub fn rec_holds() -> Thm {
    let z = var("z");
    let f = Term::free("f", step_ty());
    let n = var("n");

    // natRec z f 0 = z
    let base = rec3(z.clone(), f.clone(), zero())
        .equals(z.clone())
        .expect("rec_holds: base eq");
    // ∀n. natRec z f (S n) = f n (natRec z f n)
    let step_lhs = rec3(z.clone(), f.clone(), succ(n.clone()));
    let step_rhs = Term::app(Term::app(f.clone(), n.clone()), rec3(z.clone(), f.clone(), n));
    let step = step_lhs
        .equals(step_rhs)
        .and_then(|e| e.forall("n", nat()))
        .expect("rec_holds: step");
    let body = base.and(step).expect("rec_holds: ∧");
    let all = body
        .forall("f", step_ty())
        .and_then(|t| t.forall("z", nat()))
        .expect("rec_holds: ∀z f");

    Thm::assume(all).expect("rec_holds: assume")
}

/// `⊢ natRec z f 0 = z` — the base equation at a concrete `z`, `f`.
fn rec_zero(z: Term, f: Term) -> Result<Thm> {
    rec_holds().all_elim(z)?.all_elim(f)?.and_elim_l()
}

/// `⊢ natRec z f (S n) = f n (natRec z f n)` — the step equation.
fn rec_succ(z: Term, f: Term, n: Term) -> Result<Thm> {
    rec_holds()
        .all_elim(z)?
        .all_elim(f)?
        .and_elim_r()?
        .all_elim(n)
}

/// `⊢ t = t'`, where `t'` is `t` with the let-style specs `nat.add` /
/// `nat.mul` / `iter` δ-unfolded and β-reduced to weak-normal form
/// (typically a `natRec` application). Reduction is weak, so `natRec`
/// step-functions and folded sub-applications under binders are
/// preserved — exactly what the recursion equations expect.
fn eval(t: Term) -> Result<Thm> {
    let mut acc = Thm::refl(t)?;
    loop {
        let cur = rhs(&acc);
        // δ-unfold the let-specs on the spine, then βι-reduce.
        let mut conv = Thm::refl(cur.clone())?;
        for spec in [defs::nat_add_spec(), defs::nat_mul_spec(), defs::iter_spec()] {
            let d = rhs(&conv).delta_all(spec.symbol())?;
            conv = conv.trans(d)?;
        }
        let red = rhs(&conv).reduce()?;
        conv = conv.trans(red)?;
        let next = rhs(&conv);
        acc = acc.trans(conv)?;
        if next == cur {
            return Ok(acc);
        }
    }
}

// ============================================================================
// Recursion equations for + / * — DERIVED from `rec_holds`
// ============================================================================

/// `⊢ ∀m. 0 + m = m`. Depends only on [`rec_holds`].
pub fn add_base() -> Thm {
    add_base_impl().expect("add_base derivation")
}
fn add_base_impl() -> Result<Thm> {
    let m = var("m");
    let f = Term::abs(nat(), nat_succ()); // λ_:nat. succ
    let conv = eval(add(zero(), m.clone()))?; // ⊢ 0 + m = natRec m (λ_.succ) 0
    let rz = rec_zero(m.clone(), f)?; //          ⊢ natRec m (λ_.succ) 0 = m
    conv.trans(rz)?.all_intro("m", nat())
}

/// `⊢ ∀n m. S n + m = S (n + m)`. Depends only on [`rec_holds`].
pub fn add_step() -> Thm {
    add_step_impl().expect("add_step derivation")
}
fn add_step_impl() -> Result<Thm> {
    let n = var("n");
    let m = var("m");
    let f = Term::abs(nat(), nat_succ()); // λ_:nat. succ

    // S n + m = natRec m (λ_.succ) (S n) = (λ_.succ) n (natRec m (λ_.succ) n)
    let conv1 = eval(add(succ(n.clone()), m.clone()))?;
    let rs = rec_succ(m.clone(), f, n.clone())?;
    let red = rhs(&rs).reduce()?; // = succ (natRec m (λ_.succ) n)
    // natRec m (λ_.succ) n = n + m  (fold), then push under `succ`.
    let fold = eval(add(n.clone(), m.clone()))?.sym()?;
    let cong = fold.cong_arg(nat_succ())?; // ⊢ succ(natRec…) = succ(n + m)

    let eq = conv1.trans(rs)?.trans(red)?.trans(cong)?; // ⊢ S n + m = S (n + m)
    eq.all_intro("m", nat())?.all_intro("n", nat())
}

/// `λ_:nat. λx:nat. m + x` — the `natRec` step function `nat.mul` uses.
fn mul_step_fn(m: Term) -> Term {
    let inner = Term::abs(nat(), subst::close(&add(m, var("x")), "x")); // λx. m + x
    Term::abs(nat(), inner) // λ_. (λx. m + x)
}

/// `⊢ ∀m. 0 * m = 0`. Depends only on [`rec_holds`].
pub fn mul_base() -> Thm {
    mul_base_impl().expect("mul_base derivation")
}
fn mul_base_impl() -> Result<Thm> {
    let m = var("m");
    let f = mul_step_fn(m.clone());
    let conv = eval(mul(zero(), m))?; // ⊢ 0 * m = natRec 0 f 0
    let rz = rec_zero(zero(), f)?; //      ⊢ natRec 0 f 0 = 0
    conv.trans(rz)?.all_intro("m", nat())
}

/// `⊢ ∀n m. S n * m = m + n * m`. Depends only on [`rec_holds`].
pub fn mul_step() -> Thm {
    mul_step_impl().expect("mul_step derivation")
}
fn mul_step_impl() -> Result<Thm> {
    let n = var("n");
    let m = var("m");
    let f = mul_step_fn(m.clone());

    // S n * m = natRec 0 f (S n) = f n (natRec 0 f n)
    let conv1 = eval(mul(succ(n.clone()), m.clone()))?;
    let rs = rec_succ(zero(), f, n.clone())?;
    let red = rhs(&rs).reduce()?; // = m + (natRec 0 f n)
    // natRec 0 f n = n * m  (fold), then push under `(m +)`.
    let fold = eval(mul(n.clone(), m.clone()))?.sym()?;
    let cong = fold.cong_arg(Term::app(nat_add(), m.clone()))?; // ⊢ m + natRec… = m + n*m

    let eq = conv1.trans(rs)?.trans(red)?.trans(cong)?; // ⊢ S n * m = m + n * m
    eq.all_intro("m", nat())?.all_intro("n", nat())
}

// ============================================================================
// Additive theory — proved by induction from the recursion equations
// ============================================================================
//
// These carry the single `rec_holds` hypothesis (inherited through
// `add_base` / `add_step`), so they become genuine theorems the moment
// `rec_holds` is discharged — exactly like the recursion equations above.

/// `⊢ f arg` from a proof of its β-reduct — wrap a fact into the "applied"
/// form `nat_induct` wants.
fn beta_expand(f: &Term, arg: Term, body: Thm) -> Result<Thm> {
    Thm::beta_conv(Term::app(f.clone(), arg))?.sym()?.eq_mp(body)
}

/// `⊢ body[arg]` from `⊢ f arg` — β-reduce a redex conclusion.
fn beta_reduce_thm(thm: Thm) -> Result<Thm> {
    Thm::beta_conv(thm.concl().clone())?.eq_mp(thm)
}

/// Prove `⊢ ∀n. body` by `nat`-induction. `motive` is `λn. body`; `base`
/// proves the β-reduct `body[0/n]`; `step` proves `body[n] ⟹ body[S n]`
/// for the free variable `n`. Wraps both into [`Thm::nat_induct`]'s applied
/// form and β-normalises the result for a readable conclusion.
fn induct(motive: &Term, base: Thm, step: Thm) -> Result<Thm> {
    let n = var("n");
    let base = beta_expand(motive, zero(), base)?; // ⊢ motive 0
    let pn = Term::app(motive.clone(), n.clone());
    let body_n = beta_reduce_thm(Thm::assume(pn.clone())?)?; // {motive n} ⊢ body[n]
    let body_sn = step.imp_elim(body_n)?; //                    {motive n} ⊢ body[S n]
    let p_sn = beta_expand(motive, succ(n.clone()), body_sn)?; // {motive n} ⊢ motive (S n)
    let step = p_sn.imp_intro(&pn)?; //                          ⊢ motive n ⟹ motive (S n)
    let applied = Thm::nat_induct(base, step)?; //               ⊢ ∀n. motive n
    crate::init::eq::beta_nf(applied.concl().clone()).eq_mp(applied)
}

/// `⊢ ∀a. a + 0 = a` — right unit of `+` (the recursion equation gives the
/// *left* unit `0 + a = a`; this is the induction-on-`a` mirror).
pub fn add_zero() -> Thm {
    add_zero_impl().expect("add_zero derivation")
}
fn add_zero_impl() -> Result<Thm> {
    let n = var("n");
    let body = add(n.clone(), zero()).equals(n.clone())?; // n + 0 = n
    let motive = Term::abs(nat(), subst::close(&body, "n"));

    // base: 0 + 0 = 0.
    let base = add_base().all_elim(zero())?;

    // step: (n + 0 = n) ⟹ (S n + 0 = S n).
    let ih_concl = add(n.clone(), zero()).equals(n.clone())?;
    let ih = Thm::assume(ih_concl.clone())?; // {n+0=n} ⊢ n + 0 = n
    let s = add_step().all_elim(n.clone())?.all_elim(zero())?; // ⊢ S n + 0 = S(n + 0)
    let cong = ih.cong_arg(nat_succ())?; //                       {n+0=n} ⊢ S(n+0) = S n
    let step = s.trans(cong)?.imp_intro(&ih_concl)?; //  ⊢ (n+0=n) ⟹ (S n + 0 = S n)

    induct(&motive, base, step)
}

/// `⊢ x + c = y + c` from `⊢ x = y` — congruence on `+`'s left argument.
fn cong_add_l(eq: Thm, c: Term) -> Result<Thm> {
    eq.cong_arg(nat_add())?.cong_fn(c)
}

/// `⊢ ∀a b. a + S b = S (a + b)` — the successor-on-the-right equation
/// (mirror of [`add_step`], which moves a successor on the *left*).
pub fn add_succ_r() -> Thm {
    add_succ_r_impl().expect("add_succ_r derivation")
}
fn add_succ_r_impl() -> Result<Thm> {
    // body[n] ≔ ∀b. n + S b = S (n + b)
    let body_at = |t: &Term| -> Result<Term> {
        let b = var("b");
        add(t.clone(), succ(b.clone()))
            .equals(succ(add(t.clone(), b)))?
            .forall("b", nat())
    };
    let motive = Term::abs(nat(), subst::close(&body_at(&var("n"))?, "n"));

    // base: ∀b. 0 + S b = S (0 + b).
    let base = {
        let b = var("b");
        let e1 = add_base().all_elim(succ(b.clone()))?; // 0 + Sb = Sb
        let e2 = add_base().all_elim(b.clone())?.cong_arg(nat_succ())?.sym()?; // Sb = S(0+b)
        e1.trans(e2)?.all_intro("b", nat())?
    };

    // step: body[n] ⟹ body[S n].
    let n = var("n");
    let ihc = body_at(&n)?;
    let inner = {
        let b = var("b");
        let ih_b = Thm::assume(ihc.clone())?.all_elim(b.clone())?; // n + Sb = S(n+b)
        let s1 = add_step().all_elim(n.clone())?.all_elim(succ(b.clone()))?; // Sn+Sb = S(n+Sb)
        let s2 = ih_b.cong_arg(nat_succ())?; //                                S(n+Sb) = S(S(n+b))
        let s3 = add_step()
            .all_elim(n.clone())?
            .all_elim(b.clone())?
            .cong_arg(nat_succ())?
            .sym()?; //                                                       S(S(n+b)) = S(Sn+b)
        s1.trans(s2)?.trans(s3)?.all_intro("b", nat())?
    };
    let step = inner.imp_intro(&ihc)?;
    induct(&motive, base, step)
}

/// `⊢ ∀a b. a + b = b + a` — commutativity of `+`.
pub fn add_comm() -> Thm {
    add_comm_impl().expect("add_comm derivation")
}
fn add_comm_impl() -> Result<Thm> {
    // body[n] ≔ ∀b. n + b = b + n
    let body_at = |t: &Term| -> Result<Term> {
        let b = var("b");
        add(t.clone(), b.clone())
            .equals(add(b, t.clone()))?
            .forall("b", nat())
    };
    let motive = Term::abs(nat(), subst::close(&body_at(&var("n"))?, "n"));

    // base: ∀b. 0 + b = b + 0.
    let base = {
        let b = var("b");
        let e1 = add_base().all_elim(b.clone())?; // 0 + b = b
        let e2 = add_zero().all_elim(b.clone())?.sym()?; // b = b + 0
        e1.trans(e2)?.all_intro("b", nat())?
    };

    // step: body[n] ⟹ body[S n].
    let n = var("n");
    let ihc = body_at(&n)?;
    let inner = {
        let b = var("b");
        let ih_b = Thm::assume(ihc.clone())?.all_elim(b.clone())?; // n + b = b + n
        let s1 = add_step().all_elim(n.clone())?.all_elim(b.clone())?; // Sn+b = S(n+b)
        let s2 = ih_b.cong_arg(nat_succ())?; //                          S(n+b) = S(b+n)
        let s3 = add_succ_r().all_elim(b.clone())?.all_elim(n.clone())?.sym()?; // S(b+n) = b+Sn
        s1.trans(s2)?.trans(s3)?.all_intro("b", nat())?
    };
    let step = inner.imp_intro(&ihc)?;
    induct(&motive, base, step)
}

/// `⊢ ∀a b c. (a + b) + c = a + (b + c)` — associativity of `+`.
pub fn add_assoc() -> Thm {
    add_assoc_impl().expect("add_assoc derivation")
}
fn add_assoc_impl() -> Result<Thm> {
    // body[n] ≔ ∀b c. (n + b) + c = n + (b + c)
    let body_at = |t: &Term| -> Result<Term> {
        let (b, c) = (var("b"), var("c"));
        let lhs = add(add(t.clone(), b.clone()), c.clone());
        let rhs = add(t.clone(), add(b, c));
        lhs.equals(rhs)?.forall("c", nat())?.forall("b", nat())
    };
    let motive = Term::abs(nat(), subst::close(&body_at(&var("n"))?, "n"));

    // base: ∀b c. (0 + b) + c = 0 + (b + c).
    let base = {
        let (b, c) = (var("b"), var("c"));
        // (0 + b) + c = b + c
        let lhs = cong_add_l(add_base().all_elim(b.clone())?, c.clone())?;
        // 0 + (b + c) = b + c
        let rhs = add_base().all_elim(add(b.clone(), c.clone()))?;
        lhs.trans(rhs.sym()?)? // (0+b)+c = 0+(b+c)
            .all_intro("c", nat())?
            .all_intro("b", nat())?
    };

    // step: body[n] ⟹ body[S n].
    let n = var("n");
    let ihc = body_at(&n)?;
    let inner = {
        let (b, c) = (var("b"), var("c"));
        let ih_bc = Thm::assume(ihc.clone())?
            .all_elim(b.clone())?
            .all_elim(c.clone())?; // (n+b)+c = n+(b+c)
        // (Sn + b) + c = (S(n+b)) + c
        let s1 = cong_add_l(add_step().all_elim(n.clone())?.all_elim(b.clone())?, c.clone())?;
        // (S(n+b)) + c = S((n+b)+c)
        let s2 = add_step().all_elim(add(n.clone(), b.clone()))?.all_elim(c.clone())?;
        // S((n+b)+c) = S(n+(b+c))
        let s3 = ih_bc.cong_arg(nat_succ())?;
        // S(n+(b+c)) = Sn + (b+c)
        let s4 = add_step()
            .all_elim(n.clone())?
            .all_elim(add(b.clone(), c.clone()))?
            .sym()?;
        s1.trans(s2)?.trans(s3)?.trans(s4)?
            .all_intro("c", nat())?
            .all_intro("b", nat())?
    };
    let step = inner.imp_intro(&ihc)?;
    induct(&motive, base, step)
}

/// `⊢ ∀a b c. (a + c = b + c) ⟹ (a = b)` — right cancellation of `+`.
/// Proved by induction on the cancelled summand, using successor
/// injectivity ([`succ_inj`]) at the step. This is the `nat` lemma the
/// `int` quotient relation's transitivity rests on.
pub fn add_cancel() -> Thm {
    add_cancel_impl().expect("add_cancel derivation")
}
fn add_cancel_impl() -> Result<Thm> {
    let (a, b) = (var("a"), var("b"));
    // body[n] ≔ (a + n = b + n) ⟹ (a = b)
    let body_at = |t: &Term| -> Result<Term> {
        add(a.clone(), t.clone())
            .equals(add(b.clone(), t.clone()))?
            .imp(a.clone().equals(b.clone())?)
    };
    let motive = Term::abs(nat(), subst::close(&body_at(&var("n"))?, "n"));

    // base: (a + 0 = b + 0) ⟹ (a = b) — strip the `+ 0`s and chain.
    let base = {
        let prem = add(a.clone(), zero()).equals(add(b.clone(), zero()))?;
        let az = add_zero().all_elim(a.clone())?; // a + 0 = a
        let bz = add_zero().all_elim(b.clone())?; // b + 0 = b
        az.sym()?
            .trans(Thm::assume(prem.clone())?)?
            .trans(bz)? // {a+0=b+0} ⊢ a = b
            .imp_intro(&prem)?
    };

    // step: body[n] ⟹ body[S n].
    let n = var("n");
    let ihc = body_at(&n)?;
    let inner = {
        let prem = add(a.clone(), succ(n.clone())).equals(add(b.clone(), succ(n.clone())))?;
        // a + S n = S(a + n),  b + S n = S(b + n).
        let asr = add_succ_r().all_elim(a.clone())?.all_elim(n.clone())?;
        let bsr = add_succ_r().all_elim(b.clone())?.all_elim(n.clone())?;
        // {a+Sn=b+Sn} ⊢ S(a+n) = S(b+n).
        let ssucc = asr.sym()?.trans(Thm::assume(prem.clone())?)?.trans(bsr)?;
        // succ injectivity: S(a+n) = S(b+n) ⟹ a+n = b+n.
        let acn = succ_inj()
            .all_elim(add(a.clone(), n.clone()))?
            .all_elim(add(b.clone(), n.clone()))?
            .imp_elim(ssucc)?; // {a+Sn=b+Sn} ⊢ a+n = b+n
        // Apply the induction hypothesis.
        Thm::assume(ihc.clone())?
            .imp_elim(acn)? // {body n, a+Sn=b+Sn} ⊢ a = b
            .imp_intro(&prem)? // {body n} ⊢ (a+Sn=b+Sn) ⟹ (a=b)
    };
    let step = inner.imp_intro(&ihc)?;
    induct(&motive, base, step)?
        .all_intro("b", nat())?
        .all_intro("a", nat())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn freeness_theorems_are_genuine() {
        assert!(succ_inj().hyps().is_empty(), "succ_inj is proved");
        assert!(zero_ne_succ().hyps().is_empty(), "zero_ne_succ is proved");
    }

    #[test]
    fn add_zero_proves_right_unit() {
        // ⊢ ∀n. n + 0 = n, specialising to 5 + 0 = 5.
        let thm = add_zero();
        let five = Term::nat_lit(Nat::from_inner(5u32.into()));
        let inst = thm.clone().all_elim(five.clone()).unwrap();
        assert_eq!(inst.concl(), &add(five.clone(), zero()).equals(five).unwrap());
        // and it rests only on rec_holds, like the recursion equations.
        let rh = rec_holds().concl().clone();
        assert!(thm.hyps().iter().all(|h| h == &rh));
    }

    #[test]
    fn additive_theory_proves_the_ring_facts() {
        let lit = |n: u32| Term::nat_lit(Nat::from_inner(n.into()));
        // add_succ_r: 2 + S 3 = S (2 + 3)
        let sr = add_succ_r().all_elim(lit(2)).unwrap().all_elim(lit(3)).unwrap();
        assert_eq!(
            sr.concl(),
            &add(lit(2), succ(lit(3))).equals(succ(add(lit(2), lit(3)))).unwrap()
        );
        // add_comm: 2 + 3 = 3 + 2
        let comm = add_comm().all_elim(lit(2)).unwrap().all_elim(lit(3)).unwrap();
        assert_eq!(comm.concl(), &add(lit(2), lit(3)).equals(add(lit(3), lit(2))).unwrap());
        // add_assoc: (1 + 2) + 3 = 1 + (2 + 3)
        let assoc = add_assoc()
            .all_elim(lit(1)).unwrap()
            .all_elim(lit(2)).unwrap()
            .all_elim(lit(3)).unwrap();
        let l = add(add(lit(1), lit(2)), lit(3));
        let r = add(lit(1), add(lit(2), lit(3)));
        assert_eq!(assoc.concl(), &l.equals(r).unwrap());
        // all rest only on rec_holds.
        let rh = rec_holds().concl().clone();
        for t in [add_succ_r(), add_comm(), add_assoc()] {
            assert!(t.hyps().iter().all(|h| h == &rh), "depends only on rec_holds");
        }
    }

    #[test]
    fn add_cancel_cancels_a_common_summand() {
        // ∀a b c. (a+c = b+c) ⟹ (a=b); instantiate to a concrete implication.
        let (a, b, c) = (var("a"), var("b"), var("c"));
        let thm = add_cancel()
            .all_elim(a.clone()).unwrap()
            .all_elim(b.clone()).unwrap()
            .all_elim(c.clone()).unwrap();
        let prem = add(a.clone(), c.clone()).equals(add(b.clone(), c)).unwrap();
        let concl = a.equals(b).unwrap();
        assert_eq!(thm.concl(), &prem.imp(concl).unwrap());
        // depends only on rec_holds (succ_inj is genuine).
        let rh = rec_holds().concl().clone();
        assert!(add_cancel().hyps().iter().all(|h| h == &rh));
    }

    /// Every derived recursion equation depends on **exactly** the one
    /// `rec_holds` postulate — nothing else. So discharging `rec_holds`
    /// discharges them all.
    #[test]
    fn arithmetic_facts_depend_only_on_rec_holds() {
        let postulate = rec_holds().concl().clone();
        for fact in [add_base(), add_step(), mul_base(), mul_step()] {
            assert!(fact.concl().type_of().unwrap().is_bool());
            assert_eq!(
                fact.hyps().iter().collect::<Vec<_>>(),
                vec![&postulate],
                "a derived nat fact must rest on rec_holds alone"
            );
        }
    }

    #[test]
    fn add_base_has_the_expected_statement() {
        // ∀m. 0 + m = m  ⟹(spec k)  0 + k = k.
        let inst = add_base().all_elim(var("k")).expect("specialize add_base");
        let expected = add(zero(), var("k")).equals(var("k")).unwrap();
        assert_eq!(inst.concl(), &expected);
    }

    #[test]
    fn add_step_has_the_expected_statement() {
        // ∀n m. S n + m = S (n + m), specialised at n,m := j,k.
        let inst = add_step()
            .all_elim(var("j"))
            .and_then(|t| t.all_elim(var("k")))
            .unwrap();
        let expected = add(succ(var("j")), var("k"))
            .equals(succ(add(var("j"), var("k"))))
            .unwrap();
        assert_eq!(inst.concl(), &expected);
    }

    #[test]
    fn mul_base_and_step_have_expected_statements() {
        let mb = mul_base().all_elim(var("k")).unwrap();
        assert_eq!(
            mb.concl(),
            &mul(zero(), var("k")).equals(zero()).unwrap()
        );

        let ms = mul_step()
            .all_elim(var("j"))
            .and_then(|t| t.all_elim(var("k")))
            .unwrap();
        let expected = mul(succ(var("j")), var("k"))
            .equals(add(var("k"), mul(var("j"), var("k"))))
            .unwrap();
        assert_eq!(ms.concl(), &expected);
    }
}
