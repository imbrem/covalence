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
//! ## Everything is proved — no postulates
//!
//! - **Freeness**: [`succ_inj`] / [`zero_ne_succ`] (kernel freeness
//!   primitives generalised with `all_intro`).
//! - **[`rec_holds`]** — `natRec` satisfies its recursion equations.
//!   Now a **genuine theorem**: the recursion theorem
//!   ([`crate::init::recursion`]) builds a recursor by Hilbert choice
//!   over its graph and `spec_ax` transfers the equations to `natRec`.
//! - **Derived from [`rec_holds`]**: the four recursion equations
//!   [`add_base`] / [`add_step`] / [`mul_base`] / [`mul_step`], by
//!   δ-unfolding `nat.add` / `nat.mul` / `iter` down to `natRec` and
//!   applying [`rec_holds`]; and on top of those, the **additive theory**
//!   [`add_zero`] / [`add_succ_r`] / [`add_comm`] / [`add_assoc`] /
//!   [`add_cancel`] (via [`succ_inj`]) and the multiplicative right-zero
//!   [`mul_zero`], proved by `nat`-induction (the [`induct`] helper). Since
//!   `rec_holds` is hypothesis-free, all of these are genuine theorems — and
//!   the whole shallow Peano embedding with them.
//!
//! These are the `nat` half of what the `int` quotient lift
//! ([`init::int`](crate::init::int)) needs — `add_cancel` in particular is
//! what `int_rel`'s transitivity rests on.

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

cached_thm! {
    /// `⊢ ∀m n. (S m = S n) ⟹ (m = n)` — successor injectivity.
    pub fn succ_inj() -> Thm {
        Thm::succ_inj(var("m"), var("n"))
            .and_then(|t| t.all_intro("n", nat()))
            .and_then(|t| t.all_intro("m", nat()))
            .expect("succ_inj: kernel freeness rule")
    }
}

cached_thm! {
    /// `⊢ ∀n. ¬(0 = S n)` — zero is not a successor.
    pub fn zero_ne_succ() -> Thm {
        Thm::zero_ne_succ(var("n"))
            .and_then(|t| t.all_intro("n", nat()))
            .expect("zero_ne_succ: kernel freeness rule")
    }
}

// ============================================================================
// The recursion equation — now a genuine theorem
// ============================================================================

cached_thm! {
    /// `⊢ ∀z f. (natRec z f 0 = z) ∧ (∀n. natRec z f (S n) = f n (natRec z f n))`
    /// at `α = nat` — `natRec` satisfies its recursion equations.
    ///
    /// **Fully proved**, no hypotheses: the recursion theorem
    /// ([`crate::init::recursion`]) constructs a recursor by Hilbert choice
    /// over its graph, and `spec_ax(natRec, ·)` transfers the equations to
    /// `natRec`. Cached — the proof is a sizeable construction, run once.
    pub fn rec_holds() -> Thm {
        crate::init::recursion::rec_holds_proof().expect("recursion theorem proves rec_holds")
    }
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
        for spec in [
            defs::nat_add_spec(),
            defs::nat_mul_spec(),
            defs::nat_sub_spec(),
            defs::iter_spec(),
        ] {
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

cached_thm! {
    /// `⊢ ∀m. 0 + m = m`. Depends only on [`rec_holds`].
    pub fn add_base() -> Thm {
        add_base_impl().expect("add_base derivation")
    }
}
fn add_base_impl() -> Result<Thm> {
    let m = var("m");
    let f = Term::abs(nat(), nat_succ()); // λ_:nat. succ
    let conv = eval(add(zero(), m.clone()))?; // ⊢ 0 + m = natRec m (λ_.succ) 0
    let rz = rec_zero(m.clone(), f)?; //          ⊢ natRec m (λ_.succ) 0 = m
    conv.trans(rz)?.all_intro("m", nat())
}

cached_thm! {
    /// `⊢ ∀n m. S n + m = S (n + m)`. Depends only on [`rec_holds`].
    pub fn add_step() -> Thm {
        add_step_impl().expect("add_step derivation")
    }
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

cached_thm! {
    /// `⊢ ∀m. 0 * m = 0`. Depends only on [`rec_holds`].
    pub fn mul_base() -> Thm {
        mul_base_impl().expect("mul_base derivation")
    }
}
fn mul_base_impl() -> Result<Thm> {
    let m = var("m");
    let f = mul_step_fn(m.clone());
    let conv = eval(mul(zero(), m))?; // ⊢ 0 * m = natRec 0 f 0
    let rz = rec_zero(zero(), f)?; //      ⊢ natRec 0 f 0 = 0
    conv.trans(rz)?.all_intro("m", nat())
}

cached_thm! {
    /// `⊢ ∀n m. S n * m = m + n * m`. Depends only on [`rec_holds`].
    pub fn mul_step() -> Thm {
        mul_step_impl().expect("mul_step derivation")
    }
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
    induct_on("n", motive, base, step)
}

/// As [`induct`], but with the induction variable named `ivar` instead
/// of the default `n` — needed when inducting on one variable while
/// another (here often `n`) stays free in the motive.
fn induct_on(ivar: &str, motive: &Term, base: Thm, step: Thm) -> Result<Thm> {
    let n = var(ivar);
    let base = beta_expand(motive, zero(), base)?; // ⊢ motive 0
    let pn = Term::app(motive.clone(), n.clone());
    let body_n = beta_reduce_thm(Thm::assume(pn.clone())?)?; // {motive n} ⊢ body[n]
    let body_sn = step.imp_elim(body_n)?; //                    {motive n} ⊢ body[S n]
    let p_sn = beta_expand(motive, succ(n.clone()), body_sn)?; // {motive n} ⊢ motive (S n)
    let step = p_sn.imp_intro(&pn)?; //                          ⊢ motive n ⟹ motive (S n)
    let applied = Thm::nat_induct(base, step)?; //               ⊢ ∀n. motive n
    crate::init::eq::beta_nf(applied.concl().clone()).eq_mp(applied)
}

cached_thm! {
    /// `⊢ ∀a. a + 0 = a` — right unit of `+` (the recursion equation gives
    /// the *left* unit `0 + a = a`; this is the induction-on-`a` mirror).
    pub fn add_zero() -> Thm {
        add_zero_impl().expect("add_zero derivation")
    }
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

cached_thm! {
    /// `⊢ ∀a b. a + S b = S (a + b)` — the successor-on-the-right equation
    /// (mirror of [`add_step`], which moves a successor on the *left*).
    pub fn add_succ_r() -> Thm {
        add_succ_r_impl().expect("add_succ_r derivation")
    }
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

cached_thm! {
    /// `⊢ ∀a b. a + b = b + a` — commutativity of `+`.
    pub fn add_comm() -> Thm {
        add_comm_impl().expect("add_comm derivation")
    }
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

cached_thm! {
    /// `⊢ ∀a b c. (a + b) + c = a + (b + c)` — associativity of `+`.
    pub fn add_assoc() -> Thm {
        add_assoc_impl().expect("add_assoc derivation")
    }
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

cached_thm! {
    /// `⊢ ∀a b c. (a + c = b + c) ⟹ (a = b)` — right cancellation of `+`.
    /// Proved by induction on the cancelled summand, using successor
    /// injectivity ([`succ_inj`]) at the step. This is the `nat` lemma the
    /// `int` quotient relation's transitivity rests on.
    pub fn add_cancel() -> Thm {
        add_cancel_impl().expect("add_cancel derivation")
    }
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

cached_thm! {
    /// `⊢ ∀a. a * 0 = 0` — right zero of `*` (the recursion equation gives
    /// the *left* zero `0 * a = 0`; this is the induction-on-`a` mirror).
    pub fn mul_zero() -> Thm {
        mul_zero_impl().expect("mul_zero derivation")
    }
}
fn mul_zero_impl() -> Result<Thm> {
    let n = var("n");
    let body = mul(n.clone(), zero()).equals(zero())?; // n * 0 = 0
    let motive = Term::abs(nat(), subst::close(&body, "n"));

    // base: 0 * 0 = 0.
    let base = mul_base().all_elim(zero())?;

    // step: (n * 0 = 0) ⟹ (S n * 0 = 0).
    let ihc = mul(n.clone(), zero()).equals(zero())?;
    let e1 = mul_step().all_elim(n.clone())?.all_elim(zero())?; // S n * 0 = 0 + n * 0
    let e2 = Thm::assume(ihc.clone())?.cong_arg(Term::app(nat_add(), zero()))?; // 0 + n*0 = 0 + 0
    let e3 = add_base().all_elim(zero())?; // 0 + 0 = 0
    let step = e1.trans(e2)?.trans(e3)?.imp_intro(&ihc)?;

    induct(&motive, base, step)
}

// ============================================================================
// pred / sub equations — derived from `rec_holds`
// ============================================================================

pub(crate) fn pred(n: Term) -> Term {
    Term::app(nat_pred(), n)
}

pub(crate) fn sub(a: Term, b: Term) -> Term {
    Term::app(Term::app(nat_sub(), a), b)
}

/// `λk _. k` — the `natRec` step function in `nat.pred`'s body.
fn pred_g() -> Term {
    let inner = Term::abs(nat(), var("k")); // λ_:nat. k
    Term::abs(nat(), subst::close(&inner, "k")) // λk:nat. λ_:nat. k
}

/// `⊢ pred t = natRec 0 (λk _. k) t` — δ-unfold `nat.pred` + β.
fn pred_to_rec(t: Term) -> Result<Thm> {
    let unf = pred(t).delta_all(defs::nat_pred_spec().symbol())?;
    let red = rhs(&unf).reduce()?;
    unf.trans(red)
}

cached_thm! {
    /// `⊢ pred 0 = 0`.
    pub fn pred_zero() -> Thm {
        pred_zero_impl().expect("pred_zero")
    }
}
fn pred_zero_impl() -> Result<Thm> {
    pred_to_rec(zero())?.trans(rec_zero(zero(), pred_g())?)
}

cached_thm! {
    /// `⊢ ∀n. pred (S n) = n`.
    pub fn pred_succ() -> Thm {
        pred_succ_impl().expect("pred_succ")
    }
}
fn pred_succ_impl() -> Result<Thm> {
    let n = var("n");
    let g = pred_g();
    let conv = pred_to_rec(succ(n.clone()))?; // pred(Sn) = natRec 0 g (Sn)
    let rs = rec_succ(zero(), g, n.clone())?; //            = g n (natRec 0 g n)
    let red = rhs(&rs).reduce()?; //                        = n
    conv.trans(rs)?.trans(red)?.all_intro("n", nat())
}

cached_thm! {
    /// `⊢ ∀n. n - 0 = n` — subtraction's base equation.
    pub fn sub_zero() -> Thm {
        sub_zero_impl().expect("sub_zero")
    }
}
fn sub_zero_impl() -> Result<Thm> {
    let n = var("n");
    let f = Term::abs(nat(), nat_pred()); // λ_:nat. pred
    let conv = eval(sub(n.clone(), zero()))?; // n - 0 = natRec n (λ_.pred) 0
    let rz = rec_zero(n.clone(), f)?; //              = n
    conv.trans(rz)?.all_intro("n", nat())
}

cached_thm! {
    /// `⊢ ∀n m. n - S m = pred (n - m)` — subtraction's step equation.
    pub fn sub_succ() -> Thm {
        sub_succ_impl().expect("sub_succ")
    }
}
fn sub_succ_impl() -> Result<Thm> {
    let n = var("n");
    let m = var("m");
    let f = Term::abs(nat(), nat_pred());

    let conv1 = eval(sub(n.clone(), succ(m.clone())))?; // n - Sm = natRec n (λ_.pred)(Sm)
    let rs = rec_succ(n.clone(), f, m.clone())?; //                = (λ_.pred) m (natRec n (λ_.pred) m)
    let red = rhs(&rs).reduce()?; //                              = pred (natRec n (λ_.pred) m)
    let fold = eval(sub(n.clone(), m.clone()))?.sym()?; // natRec n (λ_.pred) m = n - m
    let cong = fold.cong_arg(nat_pred())?; //              pred(natRec…) = pred(n - m)

    conv1
        .trans(rs)?
        .trans(red)?
        .trans(cong)?
        .all_intro("m", nat())?
        .all_intro("n", nat())
}

cached_thm! {
    /// `⊢ ∀m. 0 - m = 0` — zero is a left zero of saturating subtraction.
    pub fn zero_sub() -> Thm {
        zero_sub_impl().expect("zero_sub")
    }
}
fn zero_sub_impl() -> Result<Thm> {
    let m = var("m");
    let body = sub(zero(), m.clone()).equals(zero())?; // 0 - m = 0
    let motive = Term::abs(nat(), subst::close(&body, "m"));

    // base: 0 - 0 = 0.
    let base = sub_zero().all_elim(zero())?;

    // step: (0 - m = 0) ⟹ (0 - S m = 0).
    let ihc = sub(zero(), m.clone()).equals(zero())?;
    let s1 = sub_succ().all_elim(zero())?.all_elim(m.clone())?; // 0 - Sm = pred(0 - m)
    let s2 = Thm::assume(ihc.clone())?.cong_arg(nat_pred())?; //   pred(0-m) = pred 0
    let s3 = pred_zero(); //                                        pred 0 = 0
    let step = s1.trans(s2)?.trans(s3)?.imp_intro(&ihc)?;

    induct_on("m", &motive, base, step)
}

cached_thm! {
    /// `⊢ ∀n m. S n - S m = n - m` — successors cancel across subtraction.
    pub fn sub_succ_succ() -> Thm {
        sub_succ_succ_impl().expect("sub_succ_succ")
    }
}
fn sub_succ_succ_impl() -> Result<Thm> {
    let n = var("n");
    // body[m] ≔ S n - S m = n - m   (induction on m, with n free)
    let body_at = |t: &Term| -> Result<Term> {
        sub(succ(n.clone()), succ(t.clone())).equals(sub(n.clone(), t.clone()))
    };
    let motive = Term::abs(nat(), subst::close(&body_at(&var("m"))?, "m"));

    // base: S n - S 0 = n - 0.   (both sides reduce to n)
    let base = {
        let s1 = sub_succ().all_elim(succ(n.clone()))?.all_elim(zero())?; // Sn - S0 = pred(Sn - 0)
        let s2 = sub_zero().all_elim(succ(n.clone()))?.cong_arg(nat_pred())?; // pred(Sn-0) = pred(Sn)
        let s3 = pred_succ().all_elim(n.clone())?; //                          pred(Sn) = n
        let s4 = sub_zero().all_elim(n.clone())?.sym()?; //                    n = n - 0
        s1.trans(s2)?.trans(s3)?.trans(s4)?
    };

    // step: body[m] ⟹ body[S m].
    let m = var("m");
    let ihc = body_at(&m)?;
    let inner = {
        let ih = Thm::assume(ihc.clone())?; // S n - S m = n - m
        let s1 = sub_succ()
            .all_elim(succ(n.clone()))?
            .all_elim(succ(m.clone()))?; // Sn - S(Sm) = pred(Sn - Sm)
        let s2 = ih.cong_arg(nat_pred())?; //  pred(Sn - Sm) = pred(n - m)
        let s3 = sub_succ().all_elim(n.clone())?.all_elim(m.clone())?.sym()?; // pred(n-m) = n - Sm
        s1.trans(s2)?.trans(s3)?
    };
    let step = inner.imp_intro(&ihc)?;
    induct_on("m", &motive, base, step)?.all_intro("n", nat())
}

// ============================================================================
// nat.le / nat.lt — order theory
//
// `nat.le` / `nat.lt` are def-style *selector predicates*: each is some
// `cmp : nat → nat → bool` satisfying the four clauses
//   cmp 0 0,  cmp 0 (S m),  ¬cmp (S n) 0,  cmp (S n)(S m) = cmp n m
// (with `lt` differing at `0 0`). To get those clauses as theorems we
// exhibit a *witness* satisfying them — `λn m. n - m = 0` for `le`,
// `λn m. S n - m = 0` for `lt`, both decided by saturating subtraction —
// and transfer the predicate to the spec with `Thm::spec_ax`.
// ============================================================================

fn le_t(a: Term, b: Term) -> Term {
    Term::app(Term::app(nat_le(), a), b)
}

fn lt_t(a: Term, b: Term) -> Term {
    Term::app(Term::app(nat_lt(), a), b)
}

/// `⊢ P = F` from `⊢ ¬P` (the `F` mirror of `ThmExt::eqt_intro`).
fn eqf_intro(not_p: Thm) -> Result<Thm> {
    let p = not_p
        .concl()
        .as_app()
        .ok_or_else(|| covalence_core::Error::ConnectiveRule("eqf_intro: not a ¬".into()))?
        .1
        .clone();
    let pf = not_p.not_elim(Thm::assume(p.clone())?)?; // {P} ⊢ F
    let fp = Thm::assume(Term::bool_lit(false))?.false_elim(p)?; // {F} ⊢ P
    pf.deduct_antisym(fp)?.sym() // ⊢ P = F
}

/// `⊢ ¬(S n = 0)`.
fn succ_ne_zero(n: Term) -> Result<Thm> {
    let zns = zero_ne_succ().all_elim(n.clone())?; // ⊢ ¬(0 = S n)
    let sn0 = succ(n).equals(zero())?;
    let symd = Thm::assume(sn0.clone())?.sym()?; // {Sn=0} ⊢ 0 = Sn
    let f = zns.not_elim(symd)?; // {Sn=0} ⊢ F
    f.imp_intro(&sn0)?.not_intro() // ⊢ ¬(Sn=0)
}

/// `⊢ (x = c) = (y = c)` from `⊢ x = y` (rewrite an equation's LHS).
fn cong_eq_l(eq: Thm, c: Term) -> Result<Thm> {
    let ty = c.type_of()?;
    Thm::refl(Term::eq_op(ty))?
        .cong_app(eq)?
        .cong_app(Thm::refl(c)?)
}

/// The witness `λn m. (a(n,m) - m... )` — a comparator decided by
/// saturating subtraction. `le`: `λn m. n - m = 0`; `lt`: shift the left
/// argument by a successor first.
fn sub_witness(shift_left: bool) -> Result<Term> {
    let n = var("n");
    let m = var("m");
    let left = if shift_left { succ(n.clone()) } else { n.clone() };
    let body = sub(left, m).equals(zero())?; // (left - m = 0) : bool
    let lam_m = Term::abs(nat(), subst::close(&body, "m"));
    Ok(Term::abs(nat(), subst::close(&lam_m, "n")))
}

/// `⊢ BODY[spec]` — the four selector clauses about `spec` itself,
/// transferred from a witness `w` whose four clauses are supplied (in the
/// predicate's right-associated order, with `w` applications un-β-reduced).
fn transfer_selector(spec: Term, w: Term, clauses: [Thm; 4]) -> Result<Thm> {
    let [c1, c2, c3, c4] = clauses;
    let body_w = c1.and_intro(c2.and_intro(c3.and_intro(c4)?)?)?; // ⊢ BODY[w]
    let imp = Thm::spec_ax(spec, w)?; // ⊢ p w ⟹ p spec
    let pw = imp
        .concl()
        .as_app()
        .and_then(|(f, _)| f.as_app())
        .map(|(_, ante)| ante.clone())
        .ok_or_else(|| covalence_core::Error::ConnectiveRule("transfer: bad spec_ax shape".into()))?;
    let pw_proof = Thm::beta_conv(pw)?.sym()?.eq_mp(body_w)?; // ⊢ p w
    let p_spec = imp.imp_elim(pw_proof)?; // ⊢ p spec
    Thm::beta_conv(p_spec.concl().clone())?.eq_mp(p_spec) // ⊢ BODY[spec]
}

cached_thm! {
    /// `⊢ (0 ≤ 0) ∧ (∀m. 0 ≤ S m) ∧ (∀n. ¬(S n ≤ 0)) ∧
    ///    (∀n m. (S n ≤ S m) = (n ≤ m))` — `nat.le`'s defining clauses,
    /// stated as the selector predicate (with `= T`/`= F` boolean forms).
    pub fn le_body() -> Thm {
        le_body_impl().expect("le_body: witness transfer")
    }
}
fn le_body_impl() -> Result<Thm> {
    let w = sub_witness(false)?; // λn m. n - m = 0
    let wap = |a: Term, b: Term| Term::app(Term::app(w.clone(), a), b);
    let bnf = crate::init::eq::beta_nf;

    // c1: w 0 0 = T          (0 - 0 = 0)
    let c1 = {
        let z = sub_zero().all_elim(zero())?; // 0 - 0 = 0
        bnf(wap(zero(), zero())).trans(z.eqt_intro()?)?
    };
    // c2: ∀m. w 0 (S m) = T  (0 - S m = 0)
    let c2 = {
        let m = var("m");
        let z = zero_sub().all_elim(succ(m.clone()))?; // 0 - S m = 0
        bnf(wap(zero(), succ(m.clone())))
            .trans(z.eqt_intro()?)?
            .all_intro("m", nat())?
    };
    // c3: ∀n. w (S n) 0 = F  (S n - 0 = 0  is false)
    let c3 = {
        let n = var("n");
        let s0 = sub_zero().all_elim(succ(n.clone()))?; // S n - 0 = S n
        let to_succ = cong_eq_l(s0, zero())?; // (S n - 0 = 0) = (S n = 0)
        let is_f = to_succ.trans(eqf_intro(succ_ne_zero(n.clone())?)?)?; // = F
        bnf(wap(succ(n.clone()), zero()))
            .trans(is_f)?
            .all_intro("n", nat())?
    };
    // c4: ∀n m. w (S n)(S m) = w n m
    let c4 = {
        let n = var("n");
        let m = var("m");
        let ss = sub_succ_succ().all_elim(n.clone())?.all_elim(m.clone())?; // Sn-Sm = n-m
        let mid = cong_eq_l(ss, zero())?; // (Sn-Sm=0) = (n-m=0)
        bnf(wap(succ(n.clone()), succ(m.clone())))
            .trans(mid)?
            .trans(bnf(wap(n.clone(), m.clone())).sym()?)?
            .all_intro("m", nat())?
            .all_intro("n", nat())?
    };

    transfer_selector(nat_le(), w, [c1, c2, c3, c4])
}

cached_thm! {
    /// `⊢ ¬(0 < 0) ∧ (∀m. 0 < S m) ∧ (∀n. ¬(S n < 0)) ∧
    ///    (∀n m. (S n < S m) = (n < m))` — `nat.lt`'s defining clauses.
    pub fn lt_body() -> Thm {
        lt_body_impl().expect("lt_body: witness transfer")
    }
}
fn lt_body_impl() -> Result<Thm> {
    let w = sub_witness(true)?; // λn m. S n - m = 0
    let wap = |a: Term, b: Term| Term::app(Term::app(w.clone(), a), b);
    let bnf = crate::init::eq::beta_nf;

    // c1: w 0 0 = F   (S 0 - 0 = 0 is false)
    let c1 = {
        let s0 = sub_zero().all_elim(succ(zero()))?; // S 0 - 0 = S 0
        let to_succ = cong_eq_l(s0, zero())?; // (S0 - 0 = 0) = (S0 = 0)
        let is_f = to_succ.trans(eqf_intro(succ_ne_zero(zero())?)?)?;
        bnf(wap(zero(), zero())).trans(is_f)?
    };
    // c2: ∀m. w 0 (S m) = T   (S 0 - S m = 0  ⇝  0 - m = 0)
    let c2 = {
        let m = var("m");
        let ss = sub_succ_succ().all_elim(zero())?.all_elim(m.clone())?; // S0 - Sm = 0 - m
        let step = cong_eq_l(ss, zero())?; // (S0-Sm=0) = (0-m=0)
        let z = zero_sub().all_elim(m.clone())?; // 0 - m = 0
        bnf(wap(zero(), succ(m.clone())))
            .trans(step)?
            .trans(z.eqt_intro()?)?
            .all_intro("m", nat())?
    };
    // c3: ∀n. w (S n) 0 = F   (S(S n) - 0 = 0 is false)
    let c3 = {
        let n = var("n");
        let s0 = sub_zero().all_elim(succ(succ(n.clone())))?; // S(Sn) - 0 = S(Sn)
        let to_succ = cong_eq_l(s0, zero())?;
        let is_f = to_succ.trans(eqf_intro(succ_ne_zero(succ(n.clone()))?)?)?;
        bnf(wap(succ(n.clone()), zero()))
            .trans(is_f)?
            .all_intro("n", nat())?
    };
    // c4: ∀n m. w (S n)(S m) = w n m   (S(Sn) - Sm = Sn - m)
    let c4 = {
        let n = var("n");
        let m = var("m");
        let ss = sub_succ_succ()
            .all_elim(succ(n.clone()))?
            .all_elim(m.clone())?; // S(Sn) - Sm = Sn - m
        let mid = cong_eq_l(ss, zero())?;
        bnf(wap(succ(n.clone()), succ(m.clone())))
            .trans(mid)?
            .trans(bnf(wap(n.clone(), m.clone())).sym()?)?
            .all_intro("m", nat())?
            .all_intro("n", nat())?
    };

    transfer_selector(nat_lt(), w, [c1, c2, c3, c4])
}

// ---- selector-clause accessors (the conjuncts of le_body / lt_body) ----

fn le_c1() -> Thm {
    le_body().and_elim_l().expect("le c1")
}
fn le_c2() -> Thm {
    le_body()
        .and_elim_r()
        .and_then(|t| t.and_elim_l())
        .expect("le c2")
}
fn le_c3() -> Thm {
    le_body()
        .and_elim_r()
        .and_then(|t| t.and_elim_r())
        .and_then(|t| t.and_elim_l())
        .expect("le c3")
}
fn le_c4() -> Thm {
    le_body()
        .and_elim_r()
        .and_then(|t| t.and_elim_r())
        .and_then(|t| t.and_elim_r())
        .expect("le c4")
}
fn lt_c1() -> Thm {
    lt_body().and_elim_l().expect("lt c1")
}
fn lt_c2() -> Thm {
    lt_body()
        .and_elim_r()
        .and_then(|t| t.and_elim_l())
        .expect("lt c2")
}
fn lt_c3() -> Thm {
    lt_body()
        .and_elim_r()
        .and_then(|t| t.and_elim_r())
        .and_then(|t| t.and_elim_l())
        .expect("lt c3")
}
fn lt_c4() -> Thm {
    lt_body()
        .and_elim_r()
        .and_then(|t| t.and_elim_r())
        .and_then(|t| t.and_elim_r())
        .expect("lt c4")
}

/// `⊢ ¬P` from `⊢ P = F` (the `F` mirror of `ThmExt::eqt_elim`).
fn eqf_elim(p_eq_f: Thm) -> Result<Thm> {
    let p = p_eq_f
        .concl()
        .as_eq()
        .ok_or_else(|| covalence_core::Error::ConnectiveRule("eqf_elim: not an equation".into()))?
        .0
        .clone();
    p_eq_f
        .eq_mp(Thm::assume(p.clone())?)? // {P} ⊢ F
        .imp_intro(&p)?
        .not_intro()
}

cached_thm! {
    /// `⊢ ∀n m. (S n ≤ S m) = (n ≤ m)` — `≤` cancels matching successors.
    pub fn le_succ_succ() -> Thm {
        le_c4()
    }
}

cached_thm! {
    /// `⊢ ∀n m. (S n < S m) = (n < m)` — `<` cancels matching successors.
    pub fn lt_succ_succ() -> Thm {
        lt_c4()
    }
}

cached_thm! {
    /// `⊢ ∀m. 0 ≤ m` — `0` is the least element.
    pub fn le_zero() -> Thm {
        le_zero_impl().expect("le_zero")
    }
}
fn le_zero_impl() -> Result<Thm> {
    // (0 ≤ m) = T by induction on m; then strip the `= T`.
    let m = var("m");
    let body = le_t(zero(), m.clone()).equals(Term::bool_lit(true))?;
    let motive = Term::abs(nat(), subst::close(&body, "m"));
    let base = le_c1(); // (0 ≤ 0) = T
    let ihc = body.clone();
    let step = le_c2().all_elim(m.clone())?.imp_intro(&ihc)?; // RHS (0≤Sm)=T holds outright
    let all_eq = induct_on("m", &motive, base, step)?; // ∀m. (0≤m)=T
    all_eq
        .all_elim(var("m"))?
        .eqt_elim()?
        .all_intro("m", nat())
}

cached_thm! {
    /// `⊢ ∀m. 0 < S m` — every successor is positive.
    pub fn zero_lt_succ() -> Thm {
        zero_lt_succ_impl().expect("zero_lt_succ")
    }
}
fn zero_lt_succ_impl() -> Result<Thm> {
    let m = var("m");
    lt_c2()
        .all_elim(m.clone())? // (0 < S m) = T
        .eqt_elim()?
        .all_intro("m", nat())
}

cached_thm! {
    /// `⊢ ∀n. n ≤ n` — reflexivity of `≤`.
    pub fn le_refl() -> Thm {
        le_refl_impl().expect("le_refl")
    }
}
fn le_refl_impl() -> Result<Thm> {
    let n = var("n");
    let body = le_t(n.clone(), n.clone());
    let motive = Term::abs(nat(), subst::close(&body, "n"));
    let base = le_c1().eqt_elim()?; // 0 ≤ 0
    let ihc = body.clone();
    let c4 = le_c4().all_elim(n.clone())?.all_elim(n.clone())?; // (Sn≤Sn)=(n≤n)
    let snsn = c4.sym()?.eq_mp(Thm::assume(ihc.clone())?)?; // {n≤n} ⊢ Sn≤Sn
    let step = snsn.imp_intro(&ihc)?;
    induct(&motive, base, step)
}

cached_thm! {
    /// `⊢ ∀n. ¬(n < n)` — irreflexivity of `<`.
    pub fn lt_irrefl() -> Thm {
        lt_irrefl_impl().expect("lt_irrefl")
    }
}
fn lt_irrefl_impl() -> Result<Thm> {
    // (n < n) = F by induction on n; then ¬(n < n).
    let n = var("n");
    let body = lt_t(n.clone(), n.clone()).equals(Term::bool_lit(false))?;
    let motive = Term::abs(nat(), subst::close(&body, "n"));
    let base = lt_c1(); // (0 < 0) = F
    let ihc = body.clone();
    let c4 = lt_c4().all_elim(n.clone())?.all_elim(n.clone())?; // (Sn<Sn)=(n<n)
    let step = c4.trans(Thm::assume(ihc.clone())?)?.imp_intro(&ihc)?; // (Sn<Sn)=F
    let all_eq = induct(&motive, base, step)?; // ∀n. (n<n)=F
    eqf_elim(all_eq.all_elim(var("n"))?)?.all_intro("n", nat())
}

cached_thm! {
    /// `⊢ ∀n. ¬(S n ≤ 0)` — nothing positive is `≤ 0`.
    pub fn not_succ_le_zero() -> Thm {
        not_succ_le_zero_impl().expect("not_succ_le_zero")
    }
}
fn not_succ_le_zero_impl() -> Result<Thm> {
    let n = var("n");
    eqf_elim(le_c3().all_elim(n.clone())?)?.all_intro("n", nat())
}

cached_thm! {
    /// `⊢ ∀n. ¬(n < 0)` — nothing is `< 0`.
    pub fn not_lt_zero() -> Thm {
        not_lt_zero_impl().expect("not_lt_zero")
    }
}
fn not_lt_zero_impl() -> Result<Thm> {
    // (n < 0) = F by induction on n.
    let n = var("n");
    let body = lt_t(n.clone(), zero()).equals(Term::bool_lit(false))?;
    let motive = Term::abs(nat(), subst::close(&body, "n"));
    let base = lt_c1(); // (0 < 0) = F
    let ihc = body.clone();
    let step = lt_c3().all_elim(n.clone())?.imp_intro(&ihc)?; // (Sn<0)=F outright
    let all_eq = induct(&motive, base, step)?;
    eqf_elim(all_eq.all_elim(var("n"))?)?.all_intro("n", nat())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn order_basic_facts_are_proved() {
        // 0 ≤ k, k ≤ k, 0 < S k, ¬(S k ≤ 0), ¬(k < k), ¬(k < 0).
        let k = var("k");
        assert_eq!(le_zero().all_elim(k.clone()).unwrap().concl(), &le_t(zero(), k.clone()));
        assert_eq!(le_refl().all_elim(k.clone()).unwrap().concl(), &le_t(k.clone(), k.clone()));
        assert_eq!(
            zero_lt_succ().all_elim(k.clone()).unwrap().concl(),
            &lt_t(zero(), succ(k.clone()))
        );
        for t in [le_zero(), le_refl(), zero_lt_succ(), lt_irrefl(), not_succ_le_zero(), not_lt_zero(), le_succ_succ(), lt_succ_succ()] {
            assert!(t.hyps().is_empty(), "order facts are hypothesis-free");
        }
    }

    #[test]
    fn freeness_theorems_are_genuine() {
        assert!(succ_inj().hyps().is_empty(), "succ_inj is proved");
        assert!(zero_ne_succ().hyps().is_empty(), "zero_ne_succ is proved");
    }

    #[test]
    fn le_lt_selector_clauses_transfer_to_the_specs() {
        // The witness transfer yields BODY[nat_le] / BODY[nat_lt],
        // hypothesis-free. Spot-check by pulling out clause 4 (the
        // recursive one) and clause 1.
        for body in [le_body(), lt_body()] {
            assert!(body.hyps().is_empty(), "selector clauses are proved");
            assert!(body.concl().type_of().unwrap().is_bool());
        }
        // le clause 1: ⊢ (0 ≤ 0) = T
        let le_c1 = le_body().and_elim_l().unwrap();
        assert_eq!(le_c1.concl(), &le_t(zero(), zero()).equals(Term::bool_lit(true)).unwrap());
        // lt clause 4: ⊢ ∀n m. (S n < S m) = (n < m)
        let lt_c4 = lt_body().and_elim_r().unwrap().and_elim_r().unwrap().and_elim_r().unwrap();
        let inst = lt_c4.all_elim(var("n")).unwrap().all_elim(var("m")).unwrap();
        assert_eq!(
            inst.concl(),
            &lt_t(succ(var("n")), succ(var("m"))).equals(lt_t(var("n"), var("m"))).unwrap()
        );
    }

    #[test]
    fn pred_and_sub_equations_are_proved() {
        // pred (S 4) = 4
        let ps = pred_succ().all_elim(var("n")).unwrap();
        assert_eq!(ps.concl(), &pred(succ(var("n"))).equals(var("n")).unwrap());
        assert!(pred_zero().hyps().is_empty());
        // n - 0 = n ; n - S m = pred (n - m)
        let sz = sub_zero().all_elim(var("n")).unwrap();
        assert_eq!(sz.concl(), &sub(var("n"), zero()).equals(var("n")).unwrap());
        // 0 - m = 0
        let zs = zero_sub().all_elim(var("k")).unwrap();
        assert_eq!(zs.concl(), &sub(zero(), var("k")).equals(zero()).unwrap());
        // S n - S m = n - m
        let ss = sub_succ_succ()
            .all_elim(var("n")).unwrap()
            .all_elim(var("m")).unwrap();
        assert_eq!(
            ss.concl(),
            &sub(succ(var("n")), succ(var("m"))).equals(sub(var("n"), var("m"))).unwrap()
        );
        for t in [pred_zero(), pred_succ(), sub_zero(), sub_succ(), zero_sub(), sub_succ_succ()] {
            assert!(t.hyps().is_empty(), "sub/pred theory is hypothesis-free");
        }
    }

    #[test]
    fn add_zero_proves_right_unit() {
        // ⊢ ∀n. n + 0 = n, specialising to 5 + 0 = 5.
        let thm = add_zero();
        let five = Term::nat_lit(Nat::from_inner(5u32.into()));
        let inst = thm.clone().all_elim(five.clone()).unwrap();
        assert_eq!(inst.concl(), &add(five.clone(), zero()).equals(five).unwrap());
        // rec_holds is proved, so this is hypothesis-free.
        assert!(thm.hyps().is_empty());
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
        // rec_holds is proved, so all of these are hypothesis-free.
        for t in [add_succ_r(), add_comm(), add_assoc()] {
            assert!(t.hyps().is_empty(), "fully proved");
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
        // rec_holds is proved (succ_inj is genuine), so this is hypothesis-free.
        assert!(add_cancel().hyps().is_empty());
    }

    #[test]
    fn mul_zero_proves_right_zero() {
        // ⊢ ∀a. a * 0 = 0, specialising to 7 * 0 = 0.
        let seven = Term::nat_lit(Nat::from_inner(7u32.into()));
        let inst = mul_zero().all_elim(seven.clone()).unwrap();
        assert_eq!(inst.concl(), &mul(seven, zero()).equals(zero()).unwrap());
        // rec_holds is proved, so this is hypothesis-free.
        assert!(mul_zero().hyps().is_empty());
    }

    /// `rec_holds` is now a genuine theorem, so every fact derived from
    /// it — the four `add`/`mul` recursion equations — is hypothesis-free
    /// too.
    #[test]
    fn arithmetic_facts_are_fully_proved() {
        assert!(rec_holds().hyps().is_empty(), "rec_holds is proved");
        for fact in [add_base(), add_step(), mul_base(), mul_step()] {
            assert!(fact.concl().type_of().unwrap().is_bool());
            assert!(
                fact.hyps().is_empty(),
                "a derived nat fact must be hypothesis-free"
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
