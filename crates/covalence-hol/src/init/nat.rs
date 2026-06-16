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
//!
//! ## Subtraction and order
//!
//! - **`pred` / `sub`**: [`pred_zero`] / [`pred_succ`] (now that `nat.pred`
//!   carries a `natRec` body), then [`sub_zero`] / [`sub_succ`] /
//!   [`zero_sub`] / [`sub_succ_succ`] from the recursion equations.
//! - **`nat.le` / `nat.lt`** are def-style *selector predicates*, so their
//!   defining clauses ([`le_body`] / [`lt_body`]) are transferred from a
//!   saturating-subtraction witness (`n ≤ m ⟺ n - m = 0`,
//!   `n < m ⟺ S n - m = 0`) via `Thm::spec_ax`. On top: successor
//!   cancellation ([`le_succ_succ`] / [`lt_succ_succ`]), the zero facts
//!   ([`le_zero`] / [`zero_lt_succ`] / [`not_succ_le_zero`] /
//!   [`not_lt_zero`]), reflexivity/irreflexivity ([`le_refl`] /
//!   [`lt_irrefl`]), totality ([`le_total`]), antisymmetry ([`le_antisym`]),
//!   transitivity ([`le_trans`]), and the strict/non-strict bridge
//!   [`lt_iff_succ_le`]. Transitivity goes through the additive lemmas
//!   [`le_add_r`] (`a ≤ a + k`) and [`le_add_sub`]
//!   (`a ≤ b ⟹ a + (b - a) = b`), making `≤` a full linear order.

use covalence_core::{Result, Term, Thm, Type, defs, subst};
use covalence_types::Nat;

use crate::init::eq::{beta_expand, beta_nf_concl, beta_reduce};
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

// ============================================================================
// Ported proofs — `nat.cov` over `core` + the `natrec` env
// ============================================================================

/// The `natrec` environment imported by `nat.cov`: the nat freeness rules
/// and the recursion theorem, provided as **given** lemmas. They are proved
/// in Rust above (`succ_inj` / `zero_ne_succ` / `rec_holds`) — importing
/// them lets `nat.cov` build on them without re-deriving the deep kernel
/// machinery (they can be ported themselves later).
pub fn natrec_env() -> crate::script::Env {
    let mut e = crate::script::Env::empty();
    e.lemmas.insert("nat.succ_inj".into(), succ_inj());
    e.lemmas.insert("nat.zero_ne_succ".into(), zero_ne_succ());
    e.lemmas.insert("nat.rec_holds".into(), rec_holds());
    // the `+` / `*` recursion equations (also proved in Rust for now)
    e.lemmas.insert("nat.zero_add".into(), add_base());
    e.lemmas.insert("nat.succ_add".into(), add_step());
    e.lemmas.insert("nat.zero_mul".into(), mul_base());
    e.lemmas.insert("nat.succ_mul".into(), mul_step());
    e
}

crate::cov_theory! {
    /// nat lemmas ported to `nat.cov`, over `core` + the `natrec` env.
    pub mod cov from "nat.cov" {
        import "core" = crate::script::Env::core();
        import "natrec" = crate::init::nat::natrec_env();
        "nat.succ_ne_zero" => pub fn succ_ne_zero;
        "nat.succ_cong_ne" => pub fn succ_cong_ne;
        "nat.rec_zero"     => pub fn natrec_zero_eq;
        "nat.rec_succ"     => pub fn natrec_succ_eq;
        "nat.eq_refl"      => pub fn nat_eq_refl;
        "nat.add_zero"     => pub fn add_zero_cov;
        "nat.add_succ"     => pub fn add_succ_r_cov;
        "nat.add_comm"     => pub fn add_comm_cov;
    }
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
// Recursion-equation helpers — the high-level prover API for `natRec`
// ============================================================================
//
// Every `nat` operation defined by `natRec` (`+`, `*`, `-`, …) has the same
// pair of recursion equations, and each is proved by the same dance:
//
//   * the **base** equation `op … 0 = z` — `eval` reduces the LHS to
//     `natRec z f 0`, then [`rec_zero`] rewrites that to `z`;
//   * the **step** equation `op … (S k) = ctx (op … k)` — `eval` reduces the
//     LHS to `natRec z f (S k)`, [`rec_succ`] + β to `ctx (natRec z f k)`,
//     and the inner `natRec z f k` is folded back to the recursive call
//     `op … k` under the context `ctx`.
//
// [`rec_base_eq`] / [`rec_step_eq`] capture that dance once so each
// operation's recursion equations become a single readable call.

/// `⊢ lhs = z` — a `natRec` **base** equation. `lhs` must `eval` to
/// `natRec z f 0` (e.g. `0 + m`, `0 * m`, `n - 0`).
fn rec_base_eq(lhs: Term, z: Term, f: Term) -> Result<Thm> {
    eval(lhs)?.trans(rec_zero(z, f)?)
}

/// `⊢ lhs = ctx (rec_call)` — a `natRec` **step** equation. `lhs` must
/// `eval` to `natRec z f (S k)`; after [`rec_succ`] + β the result is
/// `ctx (natRec z f k)`, and `rec_call` (which must `eval` to
/// `natRec z f k`) is folded in under the function term `ctx`.
fn rec_step_eq(lhs: Term, z: Term, f: Term, k: Term, rec_call: Term, ctx: Term) -> Result<Thm> {
    let conv1 = eval(lhs)?; // lhs = natRec z f (S k)
    let rs = rec_succ(z, f, k)?; // = f k (natRec z f k)
    let red = rhs(&rs).reduce()?; // = ctx (natRec z f k)
    let fold = eval(rec_call)?.sym()?; // natRec z f k = rec_call
    let cong = fold.cong_arg(ctx)?; // ctx (natRec z f k) = ctx (rec_call)
    conv1.trans(rs)?.trans(red)?.trans(cong)
}

// ============================================================================
// Recursion equations for + / * — DERIVED from `rec_holds`
// ============================================================================

cached_thm! {
    /// `⊢ ∀m. 0 + m = m`. Depends only on [`rec_holds`].
    pub fn add_base() -> Result<Thm> {
        let m = var("m");
        let f = Term::abs(nat(), nat_succ()); // λ_:nat. succ
        rec_base_eq(add(zero(), m), var("m"), f)?.all_intro("m", nat())
    }
}

cached_thm! {
    /// `⊢ ∀n m. S n + m = S (n + m)`. Depends only on [`rec_holds`].
    pub fn add_step() -> Result<Thm> {
        let (n, m) = (var("n"), var("m"));
        let f = Term::abs(nat(), nat_succ()); // λ_:nat. succ
        rec_step_eq(
            add(succ(n.clone()), m.clone()),
            m.clone(),
            f,
            n.clone(),
            add(n, m),
            nat_succ(), // push the recursive call under `succ`
        )?
        .all_intro("m", nat())?
        .all_intro("n", nat())
    }
}

/// `λ_:nat. λx:nat. m + x` — the `natRec` step function `nat.mul` uses.
fn mul_step_fn(m: Term) -> Term {
    let inner = Term::abs(nat(), subst::close(&add(m, var("x")), "x")); // λx. m + x
    Term::abs(nat(), inner) // λ_. (λx. m + x)
}

cached_thm! {
    /// `⊢ ∀m. 0 * m = 0`. Depends only on [`rec_holds`].
    pub fn mul_base() -> Result<Thm> {
        let m = var("m");
        let f = mul_step_fn(m.clone());
        rec_base_eq(mul(zero(), m), zero(), f)?.all_intro("m", nat())
    }
}

cached_thm! {
    /// `⊢ ∀n m. S n * m = m + n * m`. Depends only on [`rec_holds`].
    pub fn mul_step() -> Result<Thm> {
        let (n, m) = (var("n"), var("m"));
        let f = mul_step_fn(m.clone());
        rec_step_eq(
            mul(succ(n.clone()), m.clone()),
            zero(),
            f,
            n.clone(),
            mul(n, m.clone()),
            Term::app(nat_add(), m), // push the recursive call under `(m +)`
        )?
        .all_intro("m", nat())?
        .all_intro("n", nat())
    }
}

// ============================================================================
// Additive theory — proved by induction from the recursion equations
// ============================================================================
//
// These carry the single `rec_holds` hypothesis (inherited through
// `add_base` / `add_step`), so they become genuine theorems the moment
// `rec_holds` is discharged — exactly like the recursion equations above.

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
    let body_n = beta_reduce(Thm::assume(pn.clone())?)?; // {motive n} ⊢ body[n]
    let body_sn = step.imp_elim(body_n)?; //               {motive n} ⊢ body[S n]
    let p_sn = beta_expand(motive, succ(n.clone()), body_sn)?; // {motive n} ⊢ motive (S n)
    let step = p_sn.imp_intro(&pn)?; //                          ⊢ motive n ⟹ motive (S n)
    beta_nf_concl(Thm::nat_induct(base, step)?) //              ⊢ ∀n. body
}

cached_thm! {
    /// `⊢ ∀a. a + 0 = a` — right unit of `+` (the recursion equation gives
    /// the *left* unit `0 + a = a`; this is the induction-on-`a` mirror).
    pub fn add_zero() -> Result<Thm> {
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
    pub fn add_interchange() -> Result<Thm> {
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
}

cached_thm! {
    /// `⊢ ∀a b. a + S b = S (a + b)` — the successor-on-the-right equation
    /// (mirror of [`add_step`], which moves a successor on the *left*).
    pub fn add_succ_r() -> Result<Thm> {
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
}

cached_thm! {
    /// `⊢ ∀a b. a + b = b + a` — commutativity of `+`.
    pub fn add_comm() -> Result<Thm> {
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
}

cached_thm! {
    /// `⊢ ∀a b c. (a + b) + c = a + (b + c)` — associativity of `+`.
    pub fn add_assoc() -> Result<Thm> {
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
}

cached_thm! {
    /// `⊢ ∀a b c. (a + c = b + c) ⟹ (a = b)` — right cancellation of `+`.
    /// Proved by induction on the cancelled summand, using successor
    /// injectivity ([`succ_inj`]) at the step. This is the `nat` lemma the
    /// `int` quotient relation's transitivity rests on.
    pub fn add_cancel() -> Result<Thm> {
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
}

cached_thm! {
    /// `⊢ ∀a. a * 0 = 0` — right zero of `*` (the recursion equation gives
    /// the *left* zero `0 * a = 0`; this is the induction-on-`a` mirror).
    pub fn mul_zero() -> Result<Thm> {
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
}

cached_thm! {
    /// `⊢ ∀a b. a * S b = a + a * b` — successor-on-the-right for `*`
    /// (`mul_step` moves a successor on the *left*).
    pub fn mul_succ_r() -> Result<Thm> {
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
    pub fn pred_zero() -> Result<Thm> {
        pred_to_rec(zero())?.trans(rec_zero(zero(), pred_g())?)
    }
}

cached_thm! {
    /// `⊢ ∀n. pred (S n) = n`.
    pub fn pred_succ() -> Result<Thm> {
        let n = var("n");
        let g = pred_g();
        let conv = pred_to_rec(succ(n.clone()))?; // pred(Sn) = natRec 0 g (Sn)
        let rs = rec_succ(zero(), g, n.clone())?; //            = g n (natRec 0 g n)
        let red = rhs(&rs).reduce()?; //                        = n
        conv.trans(rs)?.trans(red)?.all_intro("n", nat())
    }
}

cached_thm! {
    /// `⊢ ∀n. n - 0 = n` — subtraction's base equation.
    pub fn sub_zero() -> Result<Thm> {
        let n = var("n");
        let f = Term::abs(nat(), nat_pred()); // λ_:nat. pred
        rec_base_eq(sub(n.clone(), zero()), n, f)?.all_intro("n", nat())
    }
}

cached_thm! {
    /// `⊢ ∀n m. n - S m = pred (n - m)` — subtraction's step equation.
    pub fn sub_succ() -> Result<Thm> {
        let (n, m) = (var("n"), var("m"));
        let f = Term::abs(nat(), nat_pred()); // λ_:nat. pred
        rec_step_eq(
            sub(n.clone(), succ(m.clone())),
            n.clone(),
            f,
            m.clone(),
            sub(n, m),
            nat_pred(), // push the recursive call under `pred`
        )?
        .all_intro("m", nat())?
        .all_intro("n", nat())
    }
}

cached_thm! {
    /// `⊢ ∀m. 0 - m = 0` — zero is a left zero of saturating subtraction.
    pub fn zero_sub() -> Result<Thm> {
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
}

cached_thm! {
    /// `⊢ ∀n m. S n - S m = n - m` — successors cancel across subtraction.
    pub fn sub_succ_succ() -> Result<Thm> {
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
    let left = if shift_left {
        succ(n.clone())
    } else {
        n.clone()
    };
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
        .ok_or_else(|| {
            covalence_core::Error::ConnectiveRule("transfer: bad spec_ax shape".into())
        })?;
    let pw_proof = Thm::beta_conv(pw)?.sym()?.eq_mp(body_w)?; // ⊢ p w
    let p_spec = imp.imp_elim(pw_proof)?; // ⊢ p spec
    Thm::beta_conv(p_spec.concl().clone())?.eq_mp(p_spec) // ⊢ BODY[spec]
}

cached_thm! {
    /// `⊢ (0 ≤ 0) ∧ (∀m. 0 ≤ S m) ∧ (∀n. ¬(S n ≤ 0)) ∧
    ///    (∀n m. (S n ≤ S m) = (n ≤ m))` — `nat.le`'s defining clauses,
    /// stated as the selector predicate (with `= T`/`= F` boolean forms).
    pub fn le_body() -> Result<Thm> {
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
}

cached_thm! {
    /// `⊢ ¬(0 < 0) ∧ (∀m. 0 < S m) ∧ (∀n. ¬(S n < 0)) ∧
    ///    (∀n m. (S n < S m) = (n < m))` — `nat.lt`'s defining clauses.
    pub fn lt_body() -> Result<Thm> {
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
    pub fn le_zero() -> Result<Thm> {
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
}

cached_thm! {
    /// `⊢ ∀m. 0 < S m` — every successor is positive.
    pub fn zero_lt_succ() -> Result<Thm> {
        let m = var("m");
        lt_c2()
            .all_elim(m.clone())? // (0 < S m) = T
            .eqt_elim()?
            .all_intro("m", nat())
    }
}

cached_thm! {
    /// `⊢ ∀n. n ≤ n` — reflexivity of `≤`.
    pub fn le_refl() -> Result<Thm> {
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
}

cached_thm! {
    /// `⊢ ∀a b. a * b = b * a` — commutativity of `*` (uses [`mul_succ_r`]).
    pub fn mul_comm() -> Result<Thm> {
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
}

cached_thm! {
    /// `⊢ ∀n. ¬(n < n)` — irreflexivity of `<`.
    pub fn lt_irrefl() -> Result<Thm> {
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
}

cached_thm! {
    /// `⊢ ∀n. ¬(S n ≤ 0)` — nothing positive is `≤ 0`.
    pub fn not_succ_le_zero() -> Result<Thm> {
        let n = var("n");
        eqf_elim(le_c3().all_elim(n.clone())?)?.all_intro("n", nat())
    }
}

cached_thm! {
    /// `⊢ ∀n. ¬(n < 0)` — nothing is `< 0`.
    pub fn not_lt_zero() -> Result<Thm> {
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
}

// ---- double-induction order properties ----

/// Prove `⊢ ∀a b. body(a,b)` by induction on `a`. `base` proves
/// `⊢ ∀b. body(0,b)`; `step` receives the induction hypothesis
/// `⊢ ∀b. body(a,b)` (free `a`) and must return `⊢ ∀b. body(S a, b)`
/// (typically by an inner induction on `b`).
fn induct_forall2(
    body_at: impl Fn(&Term, &Term) -> Result<Term>,
    base: Thm,
    step: impl FnOnce(Thm) -> Result<Thm>,
) -> Result<Thm> {
    let a = var("a");
    let b = var("b");
    let motive = {
        let body = body_at(&a, &b)?.forall("b", nat())?;
        Term::abs(nat(), subst::close(&body, "a"))
    };
    let ih_concl = body_at(&a, &b)?.forall("b", nat())?;
    let step_thm = step(Thm::assume(ih_concl.clone())?)?.imp_intro(&ih_concl)?;
    induct_on("a", &motive, base, step_thm)
}

cached_thm! {
    /// `⊢ ∀a b. (a ≤ b) ∨ (b ≤ a)` — `≤` is total.
    pub fn le_total() -> Result<Thm> {
        let disj = |a: &Term, b: &Term| le_t(a.clone(), b.clone()).or(le_t(b.clone(), a.clone()));

        // base a = 0: ∀b. (0 ≤ b) ∨ (b ≤ 0)   — left disjunct via le_zero.
        let base = {
            let b = var("b");
            le_zero()
                .all_elim(b.clone())?
                .or_intro_l(le_t(b.clone(), zero()))?
                .all_intro("b", nat())?
        };

        let step = |ih_a: Thm| -> Result<Thm> {
            let a = var("a");
            let b = var("b");
            // inner motive_b(b) = (S a ≤ b) ∨ (b ≤ S a)
            let motive_b = {
                let body = disj(&succ(a.clone()), &b)?;
                Term::abs(nat(), subst::close(&body, "b"))
            };
            // inner base b = 0: right disjunct (0 ≤ S a).
            let inner_base = le_zero()
                .all_elim(succ(a.clone()))?
                .or_intro_r(le_t(succ(a.clone()), zero()))?;
            // inner step: from IH_a @ b decide (S a ≤ S b) ∨ (S b ≤ S a).
            let inner_ihc = disj(&succ(a.clone()), &b)?;
            let goal_l = le_t(succ(a.clone()), succ(b.clone()));
            let goal_r = le_t(succ(b.clone()), succ(a.clone()));
            let c4ab = le_c4().all_elim(a.clone())?.all_elim(b.clone())?; // (Sa≤Sb)=(a≤b)
            let c4ba = le_c4().all_elim(b.clone())?.all_elim(a.clone())?; // (Sb≤Sa)=(b≤a)
            let left = c4ab
                .sym()?
                .eq_mp(Thm::assume(le_t(a.clone(), b.clone()))?)? // Sa≤Sb
                .or_intro_l(goal_r.clone())?
                .imp_intro(&le_t(a.clone(), b.clone()))?;
            let right = c4ba
                .sym()?
                .eq_mp(Thm::assume(le_t(b.clone(), a.clone()))?)? // Sb≤Sa
                .or_intro_r(goal_l.clone())?
                .imp_intro(&le_t(b.clone(), a.clone()))?;
            let inner_step = ih_a
                .all_elim(b.clone())? // (a≤b)∨(b≤a)
                .or_elim(left, right)?
                .imp_intro(&inner_ihc)?;
            induct_on("b", &motive_b, inner_base, inner_step)
        };

        induct_forall2(|a, b| disj(a, b), base, step)
    }
}

/// `⊢ ∀b. (b ≤ 0) ⟹ (b = 0)` — `0` is the least element strictly.
fn le_zero_iff() -> Result<Thm> {
    let b = var("b");
    let body = le_t(b.clone(), zero()).imp(b.clone().equals(zero())?)?;
    let motive = Term::abs(nat(), subst::close(&body, "b"));
    // base: (0 ≤ 0) ⟹ (0 = 0).
    let base = Thm::refl(zero())?.imp_intro(&le_t(zero(), zero()))?;
    // step: (S b ≤ 0) ⟹ (S b = 0) — antecedent is false.
    let sb_le_0 = le_t(succ(b.clone()), zero());
    let inner = not_succ_le_zero()
        .all_elim(b.clone())?
        .not_elim(Thm::assume(sb_le_0.clone())?)? // {Sb≤0} ⊢ F
        .false_elim(succ(b.clone()).equals(zero())?)? // {Sb≤0} ⊢ Sb=0
        .imp_intro(&sb_le_0)?;
    let ihc = body.clone();
    induct_on("b", &motive, base, inner.imp_intro(&ihc)?)
}

/// `(a ≤ b) ⟹ (b ≤ a) ⟹ (a = b)` — the antisymmetry body at `a`, `b`.
fn antisym_body(a: &Term, b: &Term) -> Result<Term> {
    le_t(a.clone(), b.clone()).imp(le_t(b.clone(), a.clone()).imp(a.clone().equals(b.clone())?)?)
}

cached_thm! {
    /// `⊢ ∀a b. (a ≤ b) ⟹ (b ≤ a) ⟹ (a = b)` — antisymmetry of `≤`.
    pub fn le_antisym() -> Result<Thm> {
        // base a = 0: ∀b. (0≤b) ⟹ (b≤0) ⟹ (0=b).
        let base = {
            let b = var("b");
            let b_le_0 = le_t(b.clone(), zero());
            let inner = le_zero_iff()?
                .all_elim(b.clone())?
                .imp_elim(Thm::assume(b_le_0.clone())?)? // {b≤0} ⊢ b=0
                .sym()? // {b≤0} ⊢ 0=b
                .imp_intro(&b_le_0)?;
            inner
                .imp_intro(&le_t(zero(), b.clone()))?
                .all_intro("b", nat())?
        };

        let step = |ih_a: Thm| -> Result<Thm> {
            let a = var("a");
            let b = var("b");
            let motive_b = {
                let body = antisym_body(&succ(a.clone()), &b)?;
                Term::abs(nat(), subst::close(&body, "b"))
            };
            // inner base b = 0: (Sa≤0) ⟹ (0≤Sa) ⟹ (Sa=0) — antecedent false.
            let inner_base = {
                let sa_le_0 = le_t(succ(a.clone()), zero());
                not_succ_le_zero()
                    .all_elim(a.clone())?
                    .not_elim(Thm::assume(sa_le_0.clone())?)? // {Sa≤0} ⊢ F
                    .false_elim(
                        le_t(zero(), succ(a.clone()))
                            .imp(succ(a.clone()).equals(zero())?)?,
                    )? // {Sa≤0} ⊢ (0≤Sa)⟹(Sa=0)
                    .imp_intro(&sa_le_0)?
            };
            // inner step b = S b': use IH_a @ b' on the cancelled successors.
            let inner_ihc = antisym_body(&succ(a.clone()), &b)?;
            let sa_le_sb = le_t(succ(a.clone()), succ(b.clone()));
            let sb_le_sa = le_t(succ(b.clone()), succ(a.clone()));
            let c4ab = le_c4().all_elim(a.clone())?.all_elim(b.clone())?; // (Sa≤Sb)=(a≤b)
            let c4ba = le_c4().all_elim(b.clone())?.all_elim(a.clone())?; // (Sb≤Sa)=(b≤a)
            let ab = c4ab.eq_mp(Thm::assume(sa_le_sb.clone())?)?; // {Sa≤Sb} ⊢ a≤b
            let ba = c4ba.eq_mp(Thm::assume(sb_le_sa.clone())?)?; // {Sb≤Sa} ⊢ b≤a
            let inner_step = ih_a
                .all_elim(b.clone())?
                .imp_elim(ab)?
                .imp_elim(ba)? // {…} ⊢ a=b
                .cong_arg(nat_succ())? // Sa=Sb
                .imp_intro(&sb_le_sa)?
                .imp_intro(&sa_le_sb)? // ⊢ motive_b(S b)
                .imp_intro(&inner_ihc)?; // ⊢ motive_b(b) ⟹ motive_b(S b)
            induct_on("b", &motive_b, inner_base, inner_step)
        };

        induct_forall2(antisym_body, base, step)
    }
}

/// `(a < b) = (S a ≤ b)` — the `<`/`≤` bridge body at `a`, `b`.
fn lt_succ_le_body(a: &Term, b: &Term) -> Result<Term> {
    lt_t(a.clone(), b.clone()).equals(le_t(succ(a.clone()), b.clone()))
}

cached_thm! {
    /// `⊢ ∀a b. (a < b) = (S a ≤ b)` — strict `<` is `≤` shifted by one
    /// (both are decided by `S a - b = 0`).
    pub fn lt_iff_succ_le() -> Result<Thm> {
        // base a = 0: ∀b. (0 < b) = (S 0 ≤ b)  — inner induction on b.
        let base = {
            let b = var("b");
            let motive_b = Term::abs(nat(), subst::close(&lt_succ_le_body(&zero(), &b)?, "b"));
            // b = 0: both sides are F.
            let ib = lt_c1().trans(le_c3().all_elim(zero())?.sym()?)?;
            // b = S b': both sides are T.
            let ihc = lt_succ_le_body(&zero(), &b)?;
            let lhs_t = lt_c2().all_elim(b.clone())?; // (0 < S b) = T
            let rhs_t = le_c4()
                .all_elim(zero())?
                .all_elim(b.clone())? // (S 0 ≤ S b) = (0 ≤ b)
                .trans(le_zero().all_elim(b.clone())?.eqt_intro()?)?; // = T
            let is = lhs_t.trans(rhs_t.sym()?)?.imp_intro(&ihc)?;
            induct_on("b", &motive_b, ib, is)?
        };

        let step = |ih_a: Thm| -> Result<Thm> {
            let a = var("a");
            let b = var("b");
            let motive_b = Term::abs(nat(), subst::close(&lt_succ_le_body(&succ(a.clone()), &b)?, "b"));
            // b = 0: both sides F.
            let ib = lt_c3()
                .all_elim(a.clone())? // (S a < 0) = F
                .trans(le_c3().all_elim(succ(a.clone()))?.sym()?)?; // = (S(S a) ≤ 0)
            // b = S b': cancel a successor on both sides, then IH_a @ b'.
            let ihc = lt_succ_le_body(&succ(a.clone()), &b)?;
            let lhs_eq = lt_c4().all_elim(a.clone())?.all_elim(b.clone())?; // (Sa<Sb)=(a<b)
            let rhs_eq = le_c4().all_elim(succ(a.clone()))?.all_elim(b.clone())?; // (S(Sa)≤Sb)=(Sa≤b)
            let is = lhs_eq
                .trans(ih_a.all_elim(b.clone())?)? // (Sa<Sb)=(Sa≤b)
                .trans(rhs_eq.sym()?)? // =(S(Sa)≤Sb)
                .imp_intro(&ihc)?;
            induct_on("b", &motive_b, ib, is)
        };

        induct_forall2(lt_succ_le_body, base, step)
    }
}

// ============================================================================
// Multiplicative theory, continued — the rest of the `nat` commutative-semiring
// laws (`mul_succ_r` / `mul_comm` above). Read by the `nat` semiring embedding
// in `crate::semiring`. Genuine once `rec_holds` is discharged (which it is).
// ============================================================================

/// `⊢ x * c = y * c` from `⊢ x = y` — congruence on `*`'s left argument.
fn cong_mul_l(eq: Thm, c: Term) -> Result<Thm> {
    eq.cong_arg(nat_mul())?.cong_fn(c)
}

/// Specialise a `∀a b c d. …` theorem at four `nat` witnesses.
fn elim4(thm: Thm, a: &Term, b: &Term, c: &Term, d: &Term) -> Result<Thm> {
    thm.all_elim(a.clone())?
        .all_elim(b.clone())?
        .all_elim(c.clone())?
        .all_elim(d.clone())
}

cached_thm! {
    /// `⊢ ∀a. a * 1 = a` — the `nat` literal `1` is a right unit of `*`
    /// (`1` is folded to `S 0`, then [`mul_succ_r`] + [`mul_zero`] +
    /// [`add_zero`] collapse `a * S 0`).
    pub fn mul_one() -> Result<Thm> {
        let a = var("a");
        let one = Term::nat_lit(1u32);
        let one_is_s0 = succ(zero()).reduce()?.sym()?; // ⊢ 1 = S 0
        let c0 = one_is_s0.cong_arg(Term::app(nat_mul(), a.clone()))?; // a*1 = a*(S 0)
        let c1 = mul_succ_r().all_elim(a.clone())?.all_elim(zero())?; // a*(S 0) = a + a*0
        let c2 = mul_zero()
            .all_elim(a.clone())?
            .cong_arg(Term::app(nat_add(), a.clone()))?; // a + a*0 = a + 0
        let c3 = add_zero().all_elim(a.clone())?; // a + 0 = a
        let _ = one; // documents the `1` representation; the proof uses `S 0`.
        c0.trans(c1)?.trans(c2)?.trans(c3)?.all_intro("a", nat())
    }
}

cached_thm! {
    /// `⊢ ∀a b c. a * (b + c) = a * b + a * c` — left distributivity of `*`
    /// over `+` (induction on `a`; the step rearranges four summands via
    /// [`add_interchange`]).
    pub fn distrib() -> Result<Thm> {
        // body[n] ≔ ∀b c. n*(b+c) = n*b + n*c
        let body_at = |t: &Term| -> Result<Term> {
            let (b, c) = (var("b"), var("c"));
            mul(t.clone(), add(b.clone(), c.clone()))
                .equals(add(mul(t.clone(), b.clone()), mul(t.clone(), c)))?
                .forall("c", nat())?
                .forall("b", nat())
        };
        let motive = Term::abs(nat(), subst::close(&body_at(&var("n"))?, "n"));

        // base: 0*(b+c) = 0*b + 0*c  (both 0).
        let base = {
            let (b, c) = (var("b"), var("c"));
            let l = mul_base().all_elim(add(b.clone(), c.clone()))?; // 0*(b+c) = 0
            let rb = mul_base().all_elim(b.clone())?; // 0*b = 0
            let rc = mul_base().all_elim(c.clone())?; // 0*c = 0
            let r = cong_add(rb, rc)?.trans(add_base().all_elim(zero())?)?; // 0*b+0*c = 0
            l.trans(r.sym()?)?
                .all_intro("c", nat())?
                .all_intro("b", nat())?
        };

        // step: body[n] ⟹ body[S n].
        let n = var("n");
        let ihc = body_at(&n)?;
        let inner = {
            let (b, c) = (var("b"), var("c"));
            let ih = Thm::assume(ihc.clone())?
                .all_elim(b.clone())?
                .all_elim(c.clone())?; // n*(b+c) = n*b + n*c
            // LHS: S n*(b+c) = (b+c) + n*(b+c)  [mul_step]  = (b+c) + (n*b+n*c)  [ih]
            let l1 = mul_step()
                .all_elim(n.clone())?
                .all_elim(add(b.clone(), c.clone()))?;
            let l2 = ih.cong_arg(Term::app(nat_add(), add(b.clone(), c.clone())))?;
            let lhs = l1.trans(l2)?; // S n*(b+c) = (b+c) + (n*b+n*c)
            // RHS: S n*b + S n*c = (b+n*b) + (c+n*c)  [mul_step both]
            let rb = mul_step().all_elim(n.clone())?.all_elim(b.clone())?; // S n*b = b+n*b
            let rc = mul_step().all_elim(n.clone())?.all_elim(c.clone())?; // S n*c = c+n*c
            let rhs = cong_add(rb, rc)?;
            // Bridge: (b+c)+(n*b+n*c) = (b+n*b)+(c+n*c) — commute the inner pair,
            // then the additive interchange swaps the middle two.
            let (nb, nc) = (mul(n.clone(), b.clone()), mul(n.clone(), c.clone()));
            let s1 = add_comm()
                .all_elim(nb.clone())?
                .all_elim(nc.clone())?
                .cong_arg(Term::app(nat_add(), add(b.clone(), c.clone())))?; // (b+c)+(nb+nc) = (b+c)+(nc+nb)
            let s2 = elim4(add_interchange(), &b, &c, &nc, &nb)?; // (b+c)+(nc+nb) = (b+nb)+(c+nc)
            let mid = s1.trans(s2)?;
            lhs.trans(mid)?
                .trans(rhs.sym()?)?
                .all_intro("c", nat())?
                .all_intro("b", nat())?
        };
        let step = inner.imp_intro(&ihc)?;
        induct(&motive, base, step)
    }
}

cached_thm! {
    /// `⊢ ∀a b c. (a + b) * c = a * c + b * c` — right distributivity, by
    /// [`mul_comm`] from the left law [`distrib`].
    pub fn distrib_r() -> Result<Thm> {
        let (a, b, c) = (var("a"), var("b"), var("c"));
        let s1 = mul_comm()
            .all_elim(add(a.clone(), b.clone()))?
            .all_elim(c.clone())?; // (a+b)*c = c*(a+b)
        let s2 = distrib()
            .all_elim(c.clone())?
            .all_elim(a.clone())?
            .all_elim(b.clone())?; // c*(a+b) = c*a + c*b
        let ca = mul_comm().all_elim(c.clone())?.all_elim(a.clone())?; // c*a = a*c
        let cb = mul_comm().all_elim(c.clone())?.all_elim(b.clone())?; // c*b = b*c
        let s3 = cong_add(ca, cb)?; // c*a + c*b = a*c + b*c
        s1.trans(s2)?
            .trans(s3)?
            .all_intro("c", nat())?
            .all_intro("b", nat())?
            .all_intro("a", nat())
    }
}

// ---- transitivity, via the additive structure of ≤ ----

cached_thm! {
    /// `⊢ ∀a k. a ≤ a + k` — adding on the right never decreases.
    pub fn le_add_r() -> Result<Thm> {
        let a = var("a");
        // motive λa. ∀k. a ≤ a + k
        let body_at = |t: &Term| -> Result<Term> {
            let k = var("k");
            le_t(t.clone(), add(t.clone(), k.clone())).forall("k", nat())
        };
        let motive = Term::abs(nat(), subst::close(&body_at(&a)?, "a"));
        // base a = 0: ∀k. 0 ≤ 0 + k.
        let base = {
            let k = var("k");
            le_zero()
                .all_elim(add(zero(), k.clone()))?
                .all_intro("k", nat())?
        };
        // step: (∀k. a ≤ a+k) ⟹ (∀k. S a ≤ S a + k).
        let ihc = body_at(&a)?;
        let k = var("k");
        let ih_k = Thm::assume(ihc.clone())?.all_elim(k.clone())?; // a ≤ a+k
        let c4 = le_c4()
            .all_elim(a.clone())?
            .all_elim(add(a.clone(), k.clone()))?; // (Sa ≤ S(a+k)) = (a ≤ a+k)
        let sa_le = c4.sym()?.eq_mp(ih_k)?; // Sa ≤ S(a+k)
        let astep = add_step().all_elim(a.clone())?.all_elim(k.clone())?; // Sa+k = S(a+k)
        // (Sa ≤ S(a+k)) = (Sa ≤ Sa+k)  by rewriting S(a+k) ↦ Sa+k.
        let congle = Thm::refl(nat_le())?
            .cong_app(Thm::refl(succ(a.clone()))?)?
            .cong_app(astep.sym()?)?;
        let step = congle
            .eq_mp(sa_le)?
            .all_intro("k", nat())?
            .imp_intro(&ihc)?;
        induct_on("a", &motive, base, step)
    }
}

/// `(a ≤ b) ⟹ a + (b - a) = b` — the order/subtraction body at `a`, `b`.
fn le_add_sub_body(a: &Term, b: &Term) -> Result<Term> {
    le_t(a.clone(), b.clone()).imp(add(a.clone(), sub(b.clone(), a.clone())).equals(b.clone())?)
}

cached_thm! {
    /// `⊢ ∀a b. (a ≤ b) ⟹ a + (b - a) = b` — `≤` lets subtraction undo
    /// addition.
    pub fn le_add_sub() -> Result<Thm> {
        // base a = 0: ∀b. (0 ≤ b) ⟹ 0 + (b - 0) = b.
        let base = {
            let b = var("b");
            add_base()
                .all_elim(sub(b.clone(), zero()))? // 0 + (b-0) = b-0
                .trans(sub_zero().all_elim(b.clone())?)? // = b
                .imp_intro(&le_t(zero(), b.clone()))?
                .all_intro("b", nat())?
        };

        let step = |ih_a: Thm| -> Result<Thm> {
            let a = var("a");
            let b = var("b");
            let motive_b = Term::abs(nat(), subst::close(&le_add_sub_body(&succ(a.clone()), &b)?, "b"));
            // inner base b = 0: (S a ≤ 0) ⟹ … — antecedent false.
            let inner_base = {
                let sa0 = le_t(succ(a.clone()), zero());
                not_succ_le_zero()
                    .all_elim(a.clone())?
                    .not_elim(Thm::assume(sa0.clone())?)?
                    .false_elim(
                        add(succ(a.clone()), sub(zero(), succ(a.clone()))).equals(zero())?,
                    )?
                    .imp_intro(&sa0)?
            };
            // inner step b = S b': cancel one successor, apply IH_a @ b'.
            let inner_ihc = le_add_sub_body(&succ(a.clone()), &b)?;
            let sasb = le_t(succ(a.clone()), succ(b.clone()));
            let ab = le_c4()
                .all_elim(a.clone())?
                .all_elim(b.clone())?
                .eq_mp(Thm::assume(sasb.clone())?)?; // {Sa≤Sb} ⊢ a≤b
            let iha = ih_a.all_elim(b.clone())?.imp_elim(ab)?; // {Sa≤Sb} ⊢ a+(b-a)=b
            let ss = sub_succ_succ().all_elim(b.clone())?.all_elim(a.clone())?; // Sb-Sa = b-a
            // Sa+(Sb-Sa) = Sa+(b-a) = S(a+(b-a)) = S b = S b'
            let eq = ss
                .cong_arg(Term::app(nat_add(), succ(a.clone())))? // Sa+(Sb-Sa) = Sa+(b-a)
                .trans(
                    add_step()
                        .all_elim(a.clone())?
                        .all_elim(sub(b.clone(), a.clone()))?, // = S(a+(b-a))
                )?
                .trans(iha.cong_arg(nat_succ())?)?; // = S b
            let inner_step = eq.imp_intro(&sasb)?.imp_intro(&inner_ihc)?;
            induct_on("b", &motive_b, inner_base, inner_step)
        };

        induct_forall2(le_add_sub_body, base, step)
    }
}

cached_thm! {
    /// `⊢ ∀a b c. (a ≤ b) ⟹ (b ≤ c) ⟹ (a ≤ c)` — transitivity of `≤`.
    ///
    /// `a ≤ b` and `b ≤ c` give `a + (b-a) = b` and `b + (c-b) = c`
    /// ([`le_add_sub`]), so `a + ((b-a) + (c-b)) = c` by associativity,
    /// and [`le_add_r`] turns that into `a ≤ c`.
    pub fn le_trans() -> Result<Thm> {
        let (a, b, c) = (var("a"), var("b"), var("c"));
        let hab = le_t(a.clone(), b.clone());
        let hbc = le_t(b.clone(), c.clone());
        let (p, q) = (sub(b.clone(), a.clone()), sub(c.clone(), b.clone())); // b-a, c-b

        let e1 = le_add_sub()
            .all_elim(a.clone())?
            .all_elim(b.clone())?
            .imp_elim(Thm::assume(hab.clone())?)?; // {a≤b} ⊢ a+(b-a) = b
        let e2 = le_add_sub()
            .all_elim(b.clone())?
            .all_elim(c.clone())?
            .imp_elim(Thm::assume(hbc.clone())?)?; // {b≤c} ⊢ b+(c-b) = c

        // a + (p+q) = (a+p)+q = b+q = c
        let a_pq_eq_c = add_assoc()
            .all_elim(a.clone())?
            .all_elim(p.clone())?
            .all_elim(q.clone())? // (a+p)+q = a+(p+q)
            .sym()?
            .trans(cong_add_l(e1, q.clone())?)? // = b+q
            .trans(e2)?; // = c

        // a ≤ a+(p+q), then rewrite a+(p+q) ↦ c.
        let lar = le_add_r()
            .all_elim(a.clone())?
            .all_elim(add(p.clone(), q.clone()))?; // a ≤ a+(p+q)
        let a_le_c = Thm::refl(nat_le())?
            .cong_app(Thm::refl(a.clone())?)?
            .cong_app(a_pq_eq_c)? // (a ≤ a+(p+q)) = (a ≤ c)
            .eq_mp(lar)?;

        a_le_c
            .imp_intro(&hbc)?
            .imp_intro(&hab)?
            .all_intro("c", nat())?
            .all_intro("b", nat())?
            .all_intro("a", nat())
    }
}

cached_thm! {
    /// `⊢ ∀a b c. (a * b) * c = a * (b * c)` — associativity of `*`
    /// (induction on `a`, using [`distrib_r`] at the step).
    pub fn mul_assoc() -> Result<Thm> {
        // body[n] ≔ ∀b c. (n*b)*c = n*(b*c)
        let body_at = |t: &Term| -> Result<Term> {
            let (b, c) = (var("b"), var("c"));
            mul(mul(t.clone(), b.clone()), c.clone())
                .equals(mul(t.clone(), mul(b.clone(), c)))?
                .forall("c", nat())?
                .forall("b", nat())
        };
        let motive = Term::abs(nat(), subst::close(&body_at(&var("n"))?, "n"));

        // base: (0*b)*c = 0*(b*c)  (both 0).
        let base = {
            let (b, c) = (var("b"), var("c"));
            let l1 = cong_mul_l(mul_base().all_elim(b.clone())?, c.clone())?; // (0*b)*c = 0*c
            let l2 = mul_base().all_elim(c.clone())?; // 0*c = 0
            let r = mul_base().all_elim(mul(b.clone(), c.clone()))?.sym()?; // 0 = 0*(b*c)
            l1.trans(l2)?
                .trans(r)?
                .all_intro("c", nat())?
                .all_intro("b", nat())?
        };

        // step: body[n] ⟹ body[S n].
        let n = var("n");
        let ihc = body_at(&n)?;
        let inner = {
            let (b, c) = (var("b"), var("c"));
            let ih = Thm::assume(ihc.clone())?
                .all_elim(b.clone())?
                .all_elim(c.clone())?; // (n*b)*c = n*(b*c)
            // LHS: (S n*b)*c = (b + n*b)*c  [mul_step]  = b*c + (n*b)*c  [distrib_r]
            //               = b*c + n*(b*c)  [ih]
            let l1 = cong_mul_l(
                mul_step().all_elim(n.clone())?.all_elim(b.clone())?,
                c.clone(),
            )?;
            let l2 = distrib_r()
                .all_elim(b.clone())?
                .all_elim(mul(n.clone(), b.clone()))?
                .all_elim(c.clone())?;
            let l3 = ih.cong_arg(Term::app(nat_add(), mul(b.clone(), c.clone())))?;
            // RHS: S n*(b*c) = (b*c) + n*(b*c)  [mul_step]
            let r1 = mul_step()
                .all_elim(n.clone())?
                .all_elim(mul(b.clone(), c.clone()))?;
            l1.trans(l2)?
                .trans(l3)?
                .trans(r1.sym()?)?
                .all_intro("c", nat())?
                .all_intro("b", nat())?
        };
        let step = inner.imp_intro(&ihc)?;
        induct(&motive, base, step)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn le_trans_holds() {
        // ⊢ ∀a b c. a≤b ⟹ b≤c ⟹ a≤c.
        let (a, b, c) = (var("a"), var("b"), var("c"));
        let inst = le_trans()
            .all_elim(a.clone())
            .unwrap()
            .all_elim(b.clone())
            .unwrap()
            .all_elim(c.clone())
            .unwrap();
        let want = le_t(a.clone(), b.clone())
            .imp(le_t(b.clone(), c.clone()).imp(le_t(a, c)).unwrap())
            .unwrap();
        assert_eq!(inst.concl(), &want);
        for t in [le_add_r(), le_add_sub(), le_trans()] {
            assert!(t.hyps().is_empty(), "transitivity chain is hypothesis-free");
        }
    }

    #[test]
    fn lt_iff_succ_le_holds() {
        // ⊢ ∀a b. (a < b) = (S a ≤ b); instantiate and sanity-check shape.
        let inst = lt_iff_succ_le()
            .all_elim(var("a"))
            .unwrap()
            .all_elim(var("b"))
            .unwrap();
        assert_eq!(
            inst.concl(),
            &lt_succ_le_body(&var("a"), &var("b")).unwrap()
        );
        assert!(lt_iff_succ_le().hyps().is_empty());
    }

    #[test]
    fn le_antisym_holds() {
        // ⊢ ∀a b. a≤b ⟹ b≤a ⟹ a=b, instantiated.
        let inst = le_antisym()
            .all_elim(var("a"))
            .unwrap()
            .all_elim(var("b"))
            .unwrap();
        assert_eq!(inst.concl(), &antisym_body(&var("a"), &var("b")).unwrap());
        assert!(le_antisym().hyps().is_empty());
    }

    #[test]
    fn le_total_holds() {
        // ⊢ ∀a b. a≤b ∨ b≤a, instantiated.
        let inst = le_total()
            .all_elim(var("a"))
            .unwrap()
            .all_elim(var("b"))
            .unwrap();
        let expected = le_t(var("a"), var("b"))
            .or(le_t(var("b"), var("a")))
            .unwrap();
        assert_eq!(inst.concl(), &expected);
        assert!(le_total().hyps().is_empty());
    }

    #[test]
    fn order_basic_facts_are_proved() {
        // 0 ≤ k, k ≤ k, 0 < S k, ¬(S k ≤ 0), ¬(k < k), ¬(k < 0).
        let k = var("k");
        assert_eq!(
            le_zero().all_elim(k.clone()).unwrap().concl(),
            &le_t(zero(), k.clone())
        );
        assert_eq!(
            le_refl().all_elim(k.clone()).unwrap().concl(),
            &le_t(k.clone(), k.clone())
        );
        assert_eq!(
            zero_lt_succ().all_elim(k.clone()).unwrap().concl(),
            &lt_t(zero(), succ(k.clone()))
        );
        for t in [
            le_zero(),
            le_refl(),
            zero_lt_succ(),
            lt_irrefl(),
            not_succ_le_zero(),
            not_lt_zero(),
            le_succ_succ(),
            lt_succ_succ(),
        ] {
            assert!(t.hyps().is_empty(), "order facts are hypothesis-free");
        }
    }

    #[test]
    fn freeness_theorems_are_genuine() {
        assert!(succ_inj().hyps().is_empty(), "succ_inj is proved");
        assert!(zero_ne_succ().hyps().is_empty(), "zero_ne_succ is proved");
    }

    #[test]
    fn multiplicative_theory_proves_the_facts() {
        let (a, b) = (var("a"), var("b"));
        // mul_succ_r: a * S b = a + a*b
        let sr = mul_succ_r()
            .all_elim(a.clone())
            .unwrap()
            .all_elim(b.clone())
            .unwrap();
        assert_eq!(
            sr.concl(),
            &mul(a.clone(), succ(b.clone()))
                .equals(add(a.clone(), mul(a.clone(), b.clone())))
                .unwrap()
        );
        // mul_comm: a * b = b * a
        let comm = mul_comm()
            .all_elim(a.clone())
            .unwrap()
            .all_elim(b.clone())
            .unwrap();
        assert_eq!(
            comm.concl(),
            &mul(a.clone(), b.clone()).equals(mul(b, a)).unwrap()
        );
        // genuine (no hyps).
        assert!(mul_succ_r().hyps().is_empty() && mul_comm().hyps().is_empty());
    }

    #[test]
    fn commutative_semiring_laws_are_genuine_and_well_stated() {
        // The remaining commutative-semiring laws (read by the `nat` semiring
        // embedding): mul_one / distrib / distrib_r / mul_assoc.
        let (a, b, c) = (var("a"), var("b"), var("c"));

        // mul_one: ∀a. a * 1 = a
        let one = mul_one().all_elim(a.clone()).unwrap();
        assert_eq!(
            one.concl(),
            &mul(a.clone(), Term::nat_lit(1u32))
                .equals(a.clone())
                .unwrap()
        );

        // distrib: ∀a b c. a * (b + c) = a * b + a * c
        let d = distrib()
            .all_elim(a.clone())
            .unwrap()
            .all_elim(b.clone())
            .unwrap()
            .all_elim(c.clone())
            .unwrap();
        assert_eq!(
            d.concl(),
            &mul(a.clone(), add(b.clone(), c.clone()))
                .equals(add(mul(a.clone(), b.clone()), mul(a.clone(), c.clone())))
                .unwrap()
        );

        // distrib_r: ∀a b c. (a + b) * c = a * c + b * c
        let dr = distrib_r()
            .all_elim(a.clone())
            .unwrap()
            .all_elim(b.clone())
            .unwrap()
            .all_elim(c.clone())
            .unwrap();
        assert_eq!(
            dr.concl(),
            &mul(add(a.clone(), b.clone()), c.clone())
                .equals(add(mul(a.clone(), c.clone()), mul(b.clone(), c.clone())))
                .unwrap()
        );

        // mul_assoc: ∀a b c. (a * b) * c = a * (b * c)
        let assoc = mul_assoc()
            .all_elim(a.clone())
            .unwrap()
            .all_elim(b.clone())
            .unwrap()
            .all_elim(c.clone())
            .unwrap();
        assert_eq!(
            assoc.concl(),
            &mul(mul(a.clone(), b.clone()), c.clone())
                .equals(mul(a.clone(), mul(b.clone(), c.clone())))
                .unwrap()
        );

        for t in [mul_one(), distrib(), distrib_r(), mul_assoc()] {
            assert!(t.hyps().is_empty(), "a nat semiring law must be genuine");
            assert!(t.concl().type_of().unwrap().is_bool());
        }
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
        assert_eq!(
            le_c1.concl(),
            &le_t(zero(), zero()).equals(Term::bool_lit(true)).unwrap()
        );
        // lt clause 4: ⊢ ∀n m. (S n < S m) = (n < m)
        let lt_c4 = lt_body()
            .and_elim_r()
            .unwrap()
            .and_elim_r()
            .unwrap()
            .and_elim_r()
            .unwrap();
        let inst = lt_c4
            .all_elim(var("n"))
            .unwrap()
            .all_elim(var("m"))
            .unwrap();
        assert_eq!(
            inst.concl(),
            &lt_t(succ(var("n")), succ(var("m")))
                .equals(lt_t(var("n"), var("m")))
                .unwrap()
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
            .all_elim(var("n"))
            .unwrap()
            .all_elim(var("m"))
            .unwrap();
        assert_eq!(
            ss.concl(),
            &sub(succ(var("n")), succ(var("m")))
                .equals(sub(var("n"), var("m")))
                .unwrap()
        );
        for t in [
            pred_zero(),
            pred_succ(),
            sub_zero(),
            sub_succ(),
            zero_sub(),
            sub_succ_succ(),
        ] {
            assert!(t.hyps().is_empty(), "sub/pred theory is hypothesis-free");
        }
    }

    #[test]
    fn add_zero_proves_right_unit() {
        // ⊢ ∀n. n + 0 = n, specialising to 5 + 0 = 5.
        let thm = add_zero();
        let five = Term::nat_lit(Nat::from_inner(5u32.into()));
        let inst = thm.clone().all_elim(five.clone()).unwrap();
        assert_eq!(
            inst.concl(),
            &add(five.clone(), zero()).equals(five).unwrap()
        );
        // rec_holds is proved, so this is hypothesis-free.
        assert!(thm.hyps().is_empty());
    }

    #[test]
    fn additive_theory_proves_the_ring_facts() {
        let lit = |n: u32| Term::nat_lit(Nat::from_inner(n.into()));
        // add_succ_r: 2 + S 3 = S (2 + 3)
        let sr = add_succ_r()
            .all_elim(lit(2))
            .unwrap()
            .all_elim(lit(3))
            .unwrap();
        assert_eq!(
            sr.concl(),
            &add(lit(2), succ(lit(3)))
                .equals(succ(add(lit(2), lit(3))))
                .unwrap()
        );
        // add_comm: 2 + 3 = 3 + 2
        let comm = add_comm()
            .all_elim(lit(2))
            .unwrap()
            .all_elim(lit(3))
            .unwrap();
        assert_eq!(
            comm.concl(),
            &add(lit(2), lit(3)).equals(add(lit(3), lit(2))).unwrap()
        );
        // add_assoc: (1 + 2) + 3 = 1 + (2 + 3)
        let assoc = add_assoc()
            .all_elim(lit(1))
            .unwrap()
            .all_elim(lit(2))
            .unwrap()
            .all_elim(lit(3))
            .unwrap();
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
            .all_elim(a.clone())
            .unwrap()
            .all_elim(b.clone())
            .unwrap()
            .all_elim(c.clone())
            .unwrap();
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
        assert_eq!(mb.concl(), &mul(zero(), var("k")).equals(zero()).unwrap());

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

#[cfg(test)]
mod cov_tests {
    use super::cov;

    #[test]
    fn nat_cov_loads_and_proves() {
        // Force the `nat.cov` theory: all five lemmas must replay (the
        // `induct` tactic + the natrec equations + the freeness corollaries).
        assert!(cov::succ_ne_zero().hyps().is_empty());
        assert!(cov::succ_cong_ne().hyps().is_empty());
        assert!(cov::natrec_zero_eq().hyps().is_empty());
        assert!(cov::natrec_succ_eq().hyps().is_empty());
        assert!(cov::nat_eq_refl().hyps().is_empty());
        assert!(cov::add_zero_cov().hyps().is_empty());
        assert!(cov::add_succ_r_cov().hyps().is_empty());
        // `add.comm` ported via #by/induct/rw must equal the Rust proof.
        assert_eq!(cov::add_comm_cov().concl(), super::add_comm().concl());
    }
}
