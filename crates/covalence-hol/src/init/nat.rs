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
//!   [`add_cancel`] (via [`succ_inj`]) and the multiplicative theory
//!   [`mul_zero`] / [`mul_succ_r`] / [`mul_comm`], proved by `nat`-induction
//!   (the [`induct`] helper). Since
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

/// `⊢ (x₁ + y₁) = (x₂ + y₂)` from `⊢ x₁ = x₂` and `⊢ y₁ = y₂`.
pub(crate) fn cong_add(xs: Thm, ys: Thm) -> Result<Thm> {
    xs.cong_arg(nat_add())?.cong_app(ys)
}

cached_thm! {
    /// `⊢ ∀a b c d. (a + b) + (c + d) = (a + d) + (b + c)` — the additive
    /// rearrangement the Grothendieck `int` relation's transitivity needs
    /// (it pairs the "outer" summands `a, d` and the "inner" summands
    /// `b, c`). Both sides equal `a + ((b + c) + d)`.
    pub fn add_interchange() -> Thm {
        add_interchange_impl().expect("add_interchange derivation")
    }
}
fn add_interchange_impl() -> Result<Thm> {
    let (a, b, c, d) = (var("a"), var("b"), var("c"), var("d"));
    let add_a = Term::app(nat_add(), a.clone());

    // (a+b)+(c+d) = a+((b+c)+d).
    let s1 = add_assoc()
        .all_elim(a.clone())?
        .all_elim(b.clone())?
        .all_elim(add(c.clone(), d.clone()))?; // (a+b)+(c+d) = a+(b+(c+d))
    let s2 = add_assoc()
        .all_elim(b.clone())?
        .all_elim(c.clone())?
        .all_elim(d.clone())?
        .sym()? // b+(c+d) = (b+c)+d
        .cong_arg(add_a.clone())?; // a+(b+(c+d)) = a+((b+c)+d)
    let lhs_to_mid = s1.trans(s2)?;

    // (a+d)+(b+c) = a+((b+c)+d).
    let t1 = add_assoc()
        .all_elim(a.clone())?
        .all_elim(d.clone())?
        .all_elim(add(b.clone(), c.clone()))?; // (a+d)+(b+c) = a+(d+(b+c))
    let t2 = add_comm()
        .all_elim(d.clone())?
        .all_elim(add(b.clone(), c.clone()))? // d+(b+c) = (b+c)+d
        .cong_arg(add_a)?; // a+(d+(b+c)) = a+((b+c)+d)
    let rhs_to_mid = t1.trans(t2)?;

    lhs_to_mid
        .trans(rhs_to_mid.sym()?)? // (a+b)+(c+d) = (a+d)+(b+c)
        .all_intro("d", nat())?
        .all_intro("c", nat())?
        .all_intro("b", nat())?
        .all_intro("a", nat())
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

cached_thm! {
    /// `⊢ ∀a b. a * S b = a + a * b` — successor-on-the-right for `*`
    /// (`mul_step` moves a successor on the *left*).
    pub fn mul_succ_r() -> Thm {
        mul_succ_r_impl().expect("mul_succ_r derivation")
    }
}
fn mul_succ_r_impl() -> Result<Thm> {
    // body[n] ≔ ∀b. n * S b = n + n * b
    let body_at = |t: &Term| -> Result<Term> {
        let b = var("b");
        mul(t.clone(), succ(b.clone()))
            .equals(add(t.clone(), mul(t.clone(), b)))?
            .forall("b", nat())
    };
    let motive = Term::abs(nat(), subst::close(&body_at(&var("n"))?, "n"));

    // base: ∀b. 0 * S b = 0 + 0 * b   (both sides reduce to 0).
    let base = {
        let b = var("b");
        let e1 = mul_base().all_elim(succ(b.clone()))?; // 0 * Sb = 0
        let rhs0 = mul_base()
            .all_elim(b.clone())?
            .cong_arg(Term::app(nat_add(), zero()))? // 0 + 0*b = 0 + 0
            .trans(add_base().all_elim(zero())?)?; // = 0
        e1.trans(rhs0.sym()?)?.all_intro("b", nat())?
    };

    // step: body[n] ⟹ body[S n].
    let n = var("n");
    let ihc = body_at(&n)?;
    let inner = {
        let b = var("b");
        let nb = mul(n.clone(), b.clone());
        // Sn * Sb = Sb + n*Sb = Sb + (n + n*b).
        let l = mul_step()
            .all_elim(n.clone())?
            .all_elim(succ(b.clone()))? // Sn*Sb = Sb + n*Sb
            .trans(
                Thm::assume(ihc.clone())?
                    .all_elim(b.clone())? // n*Sb = n + n*b
                    .cong_arg(Term::app(nat_add(), succ(b.clone())))?, // Sb + n*Sb = Sb + (n+nb)
            )?;
        // Sn + Sn*b = Sn + (b + n*b).
        let r = mul_step()
            .all_elim(n.clone())?
            .all_elim(b.clone())? // Sn*b = b + n*b
            .cong_arg(Term::app(nat_add(), succ(n.clone())))?; // Sn + Sn*b = Sn + (b+nb)
        // Sb + (n+nb) = Sn + (b+nb), via succ + b+(n+nb)=n+(b+nb).
        let inner_eq = add_assoc()
            .all_elim(b.clone())?
            .all_elim(n.clone())?
            .all_elim(nb.clone())?
            .sym()? // b+(n+nb) = (b+n)+nb
            .trans(cong_add_l(
                add_comm().all_elim(b.clone())?.all_elim(n.clone())?,
                nb.clone(),
            )?)? // = (n+b)+nb
            .trans(add_assoc().all_elim(n.clone())?.all_elim(b.clone())?.all_elim(nb.clone())?)?; // = n+(b+nb)
        let middle = add_step()
            .all_elim(b.clone())?
            .all_elim(add(n.clone(), nb.clone()))? // Sb+(n+nb) = S(b+(n+nb))
            .trans(inner_eq.cong_arg(nat_succ())?)? // = S(n+(b+nb))
            .trans(
                add_step()
                    .all_elim(n.clone())?
                    .all_elim(add(b.clone(), nb.clone()))?
                    .sym()?, // = Sn+(b+nb)
            )?;
        l.trans(middle)?.trans(r.sym()?)?.all_intro("b", nat())?
    };
    let step = inner.imp_intro(&ihc)?;
    induct(&motive, base, step)
}

cached_thm! {
    /// `⊢ ∀a b. a * b = b * a` — commutativity of `*` (uses [`mul_succ_r`]).
    pub fn mul_comm() -> Thm {
        mul_comm_impl().expect("mul_comm derivation")
    }
}
fn mul_comm_impl() -> Result<Thm> {
    // body[n] ≔ ∀b. n * b = b * n
    let body_at = |t: &Term| -> Result<Term> {
        let b = var("b");
        mul(t.clone(), b.clone())
            .equals(mul(b, t.clone()))?
            .forall("b", nat())
    };
    let motive = Term::abs(nat(), subst::close(&body_at(&var("n"))?, "n"));

    // base: ∀b. 0 * b = b * 0  (both 0).
    let base = {
        let b = var("b");
        mul_base()
            .all_elim(b.clone())? // 0*b = 0
            .trans(mul_zero().all_elim(b.clone())?.sym()?)? // = b*0
            .all_intro("b", nat())?
    };

    // step: body[n] ⟹ body[S n].
    let n = var("n");
    let ihc = body_at(&n)?;
    let inner = {
        let b = var("b");
        // Sn*b = b + n*b = b + b*n = b*Sn.
        mul_step()
            .all_elim(n.clone())?
            .all_elim(b.clone())? // Sn*b = b + n*b
            .trans(
                Thm::assume(ihc.clone())?
                    .all_elim(b.clone())? // n*b = b*n
                    .cong_arg(Term::app(nat_add(), b.clone()))?, // b + n*b = b + b*n
            )?
            .trans(mul_succ_r().all_elim(b.clone())?.all_elim(n.clone())?.sym()?)? // b + b*n = b*Sn
            .all_intro("b", nat())?
    };
    let step = inner.imp_intro(&ihc)?;
    induct(&motive, base, step)
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
    fn multiplicative_theory_proves_the_facts() {
        let (a, b) = (var("a"), var("b"));
        // mul_succ_r: a * S b = a + a*b
        let sr = mul_succ_r().all_elim(a.clone()).unwrap().all_elim(b.clone()).unwrap();
        assert_eq!(
            sr.concl(),
            &mul(a.clone(), succ(b.clone())).equals(add(a.clone(), mul(a.clone(), b.clone()))).unwrap()
        );
        // mul_comm: a * b = b * a
        let comm = mul_comm().all_elim(a.clone()).unwrap().all_elim(b.clone()).unwrap();
        assert_eq!(comm.concl(), &mul(a.clone(), b.clone()).equals(mul(b, a)).unwrap());
        // genuine (no hyps).
        assert!(mul_succ_r().hyps().is_empty() && mul_comm().hyps().is_empty());
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
