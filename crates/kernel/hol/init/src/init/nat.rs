//! `nat` theorems: the `defs/nat.rs` catalogue re-exported, plus the
//! proved Peano properties of HOL `nat` — mirroring how [`init::logic`]
//! pairs the connective definitions with their proved facts.
//!
//! [`init::logic`]: crate::init::logic
//!
//! This module is the home of the *theorems*; the **shallow embedding**
//! of Peano arithmetic into HOL (the [`Peano`](crate::peano::Peano) trait impl) lives in
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
//!   (the `induct` helper). Since
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

use covalence_core::{Error, Result, Term, Type, subst};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::defs;
use covalence_hol_eval::derived::DerivedRules;
use covalence_types::Nat;

use crate::init::eq::{beta_expand, beta_nf_concl, beta_reduce};
use crate::init::ext::{TermExt, ThmExt};

// Re-export the `defs/nat.rs` term catalogue (the operations; the
// `*_spec` handles stay in `covalence_hol_eval::defs`).
pub use covalence_hol_eval::defs::{
    iter, nat_add, nat_div, nat_le, nat_lt, nat_mod, nat_mul, nat_pow, nat_pred, nat_rec, nat_shl,
    nat_shr, nat_sub, nat_succ, nat_to_int,
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
            .expect("succ.inj: kernel freeness rule")
    }
}

cached_thm! {
    /// `⊢ ∀n. ¬(0 = S n)` — zero is not a successor.
    pub fn zero_ne_succ() -> Thm {
        Thm::zero_ne_succ(var("n"))
            .and_then(|t| t.all_intro("n", nat()))
            .expect("zero.ne_succ: kernel freeness rule")
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
        crate::init::recursion::rec_holds_proof().expect("recursion theorem proves rec.holds")
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
    e.define_lemma("succ.inj", succ_inj());
    e.define_lemma("zero.ne_succ", zero_ne_succ());
    e.define_lemma("rec.holds", rec_holds());
    // the `+` / `*` recursion equations (also proved in Rust for now)
    e.define_lemma("zero.add", add_base());
    e.define_lemma("succ.add", add_step());
    e.define_lemma("zero.mul", mul_base());
    e.define_lemma("succ.mul", mul_step());
    // pred / saturating-subtraction recursion equations
    e.define_lemma("pred.zero", pred_zero());
    e.define_lemma("pred.succ", pred_succ());
    e.define_lemma("sub.zero", sub_zero());
    e.define_lemma("sub.succ", sub_succ());
    // pow / shl / shr recursion equations (proved in Rust above, like + / *).
    e.define_lemma("pow.zero", pow_zero());
    e.define_lemma("pow.succ", pow_succ());
    e.define_lemma("shl.zero", shl_zero());
    e.define_lemma("shl.succ", shl_succ());
    e.define_lemma("shr.zero", shr_zero());
    e.define_lemma("shr.succ", shr_succ());
    // the `≤` / `<` defining clauses (`= T`/`= F` boolean forms), as the
    // 4-way conjunctions; nat.cov projects them with `and-elim`.
    e.define_lemma("le.body", le_body());
    e.define_lemma("lt.body", lt_body());
    e
}

crate::cov_theory! {
    /// nat lemmas ported to `nat.cov`, over `core` + the `natrec` env.
    pub mod cov from "nat.cov" {
        import "core" = crate::script::Env::core();
        import "natrec" = crate::init::nat::natrec_env();
        import "logic" = crate::init::logic::cov::env();
        "succ.ne_zero" => pub fn succ_ne_zero;
        "succ.cong_ne" => pub fn succ_cong_ne;
        "rec.zero"     => pub fn natrec_zero_eq;
        "rec.succ"     => pub fn natrec_succ_eq;
        "eq.refl"      => pub fn nat_eq_refl;
        "add.zero"     => pub fn add_zero_cov;
        "add.succ"     => pub fn add_succ_r_cov;
        "add.comm"     => pub fn add_comm_cov;
        "add.assoc"    => pub fn add_assoc_cov;
        "add.cancel"   => pub fn add_cancel_cov;
        "mul.comm"     => pub fn mul_comm_cov;
        "mul.one"      => pub fn mul_one_cov;
        "distrib"      => pub fn distrib_cov;
        "mul.assoc"    => pub fn mul_assoc_cov;
        "le.succ_self" => pub fn le_succ_self_cov;
        "le.total"     => pub fn le_total_cov;
        "lt.iff_succ_le" => pub fn lt_iff_succ_le_cov;
        "le.add_r"     => pub fn le_add_r_cov;
        "le.zero_iff"  => pub fn le_zero_iff_cov;
        "le.antisym"   => pub fn le_antisym_cov;
        "le.add_sub"   => pub fn le_add_sub_cov;
        "le.trans"     => pub fn le_trans_cov;
        "lt.imp_le"    => pub fn lt_imp_le_cov;
        "lt.trans"     => pub fn lt_trans_cov;
        "le.add_cancel_r" => pub fn le_add_cancel_r_cov;
        "lt.add_mono_r"   => pub fn lt_add_mono_r_cov;
        "le.iff_lt_or_eq" => pub fn le_iff_lt_or_eq_cov;
        "lt.trichotomy"   => pub fn lt_trichotomy_cov;
        "add.lt_add"   => pub fn add_lt_add_cov;
        "lt.cross"     => pub fn lt_cross_cov;
        "le.cross"     => pub fn le_cross_cov;
        "pow.add"      => pub fn pow_add_cov;
        "shl.eq_mul_pow" => pub fn shl_eq_mul_pow_cov;
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
    beta_nf_concl(crate::init::ext::nat_induct(base, step)?) //              ⊢ ∀n. body
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
// in `crate::algebra::semiring`. Genuine once `rec_holds` is discharged (which it is).
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

// ============================================================================
// Strict order `<` — the facts the `int` ordered-ring axioms lift through the
// Grothendieck quotient: `lt` transitivity, `≤`/`<` add-cancellation and
// add-monotonicity, the `≤ = < ∨ =` bridge, and trichotomy.
// ============================================================================

/// `⊢ n + 1 = S n` — fold the `1` literal into a successor.
pub fn add_one_succ(n: &Term) -> Result<Thm> {
    let one_is_s0 = succ(zero()).reduce()?.sym()?; // 1 = S 0
    one_is_s0
        .cong_arg(Term::app(nat_add(), n.clone()))? // n+1 = n+S0
        .trans(add_succ_r().all_elim(n.clone())?.all_elim(zero())?)? // = S(n+0)
        .trans(add_zero().all_elim(n.clone())?.cong_arg(nat_succ())?) // = S n
}

cached_thm! {
    /// `⊢ ∀n. n ≤ S n`.
    pub fn le_succ_self() -> Result<Thm> {
        let n = var("n");
        let one = Term::nat_lit(1u32);
        le_add_r()
            .all_elim(n.clone())?
            .all_elim(one)? // n ≤ n+1
            .rewrite(&add_one_succ(&n)?)? // n ≤ S n
            .all_intro("n", nat())
    }
}

cached_thm! {
    /// `⊢ ∀a b. (a < b) ⟹ (a ≤ b)`.
    pub fn lt_imp_le() -> Result<Thm> {
        let (a, b) = (var("a"), var("b"));
        let hab = lt_t(a.clone(), b.clone());
        // a<b ⟹ Sa≤b ; a≤Sa ; le_trans a Sa b.
        let sa_le_b = lt_iff_succ_le()
            .all_elim(a.clone())?
            .all_elim(b.clone())?
            .eq_mp(Thm::assume(hab.clone())?)?; // {a<b} ⊢ Sa ≤ b
        let a_le_sa = le_succ_self().all_elim(a.clone())?; // a ≤ Sa
        let a_le_b = le_trans()
            .all_elim(a.clone())?
            .all_elim(succ(a.clone()))?
            .all_elim(b.clone())?
            .imp_elim(a_le_sa)?
            .imp_elim(sa_le_b)?; // {a<b} ⊢ a ≤ b
        a_le_b
            .imp_intro(&hab)?
            .all_intro("b", nat())?
            .all_intro("a", nat())
    }
}

cached_thm! {
    /// `⊢ ∀a b c. (a + c ≤ b + c) = (a ≤ b)` — adding a common summand is an
    /// order equivalence (induction on `c`, peeling successors).
    pub fn le_add_cancel_r() -> Result<Thm> {
        let (a, b) = (var("a"), var("b"));
        let body_at = |t: &Term| -> Result<Term> {
            le_t(add(a.clone(), t.clone()), add(b.clone(), t.clone()))
                .equals(le_t(a.clone(), b.clone()))
        };
        let motive = Term::abs(nat(), subst::close(&body_at(&var("c"))?, "c"));
        // base c=0: (a+0 ≤ b+0) = (a ≤ b).
        let base = Thm::refl(nat_le())?
            .cong_app(add_zero().all_elim(a.clone())?)?
            .cong_app(add_zero().all_elim(b.clone())?)?;
        // step: body[c] ⟹ body[S c].
        let c = var("c");
        let ihc = body_at(&c)?;
        let inner = {
            let asr = add_succ_r().all_elim(a.clone())?.all_elim(c.clone())?; // a+Sc = S(a+c)
            let bsr = add_succ_r().all_elim(b.clone())?.all_elim(c.clone())?; // b+Sc = S(b+c)
            let e1 = Thm::refl(nat_le())?.cong_app(asr)?.cong_app(bsr)?; // (a+Sc≤b+Sc) = (S(a+c)≤S(b+c))
            let e2 = le_succ_succ()
                .all_elim(add(a.clone(), c.clone()))?
                .all_elim(add(b.clone(), c.clone()))?; // = (a+c≤b+c)
            e1.trans(e2)?.trans(Thm::assume(ihc.clone())?)?.imp_intro(&ihc)?
        };
        induct_on("c", &motive, base, inner)?
            .all_intro("b", nat())?
            .all_intro("a", nat())
    }
}

cached_thm! {
    /// `⊢ ∀a b c. (a + c < b + c) = (a < b)` — `<` add-monotonicity.
    pub fn lt_add_mono_r() -> Result<Thm> {
        let (a, b, c) = (var("a"), var("b"), var("c"));
        // (a+c<b+c) = (S(a+c)≤b+c) = (Sa+c≤b+c) = (Sa≤b) = (a<b).
        let e1 = lt_iff_succ_le()
            .all_elim(add(a.clone(), c.clone()))?
            .all_elim(add(b.clone(), c.clone()))?;
        let astep = add_step().all_elim(a.clone())?.all_elim(c.clone())?; // Sa+c = S(a+c)
        let e2 = Thm::refl(nat_le())?
            .cong_app(astep.sym()?)?
            .cong_fn(add(b.clone(), c.clone()))?; // (S(a+c)≤b+c) = (Sa+c≤b+c)
        let e3 = le_add_cancel_r()
            .all_elim(succ(a.clone()))?
            .all_elim(b.clone())?
            .all_elim(c.clone())?; // = (Sa≤b)
        let e4 = lt_iff_succ_le()
            .all_elim(a.clone())?
            .all_elim(b.clone())?
            .sym()?; // (Sa≤b) = (a<b)
        e1.trans(e2)?
            .trans(e3)?
            .trans(e4)?
            .all_intro("c", nat())?
            .all_intro("b", nat())?
            .all_intro("a", nat())
    }
}

cached_thm! {
    /// `⊢ ∀a b c. (a < b) ⟹ (b < c) ⟹ (a < c)` — transitivity of `<`.
    pub fn lt_trans() -> Result<Thm> {
        let (a, b, c) = (var("a"), var("b"), var("c"));
        let (hab, hbc) = (lt_t(a.clone(), b.clone()), lt_t(b.clone(), c.clone()));
        let sa_le_b = lt_iff_succ_le()
            .all_elim(a.clone())?
            .all_elim(b.clone())?
            .eq_mp(Thm::assume(hab.clone())?)?; // {a<b} ⊢ Sa ≤ b
        let b_le_c = lt_imp_le()
            .all_elim(b.clone())?
            .all_elim(c.clone())?
            .imp_elim(Thm::assume(hbc.clone())?)?; // {b<c} ⊢ b ≤ c
        let sa_le_c = le_trans()
            .all_elim(succ(a.clone()))?
            .all_elim(b.clone())?
            .all_elim(c.clone())?
            .imp_elim(sa_le_b)?
            .imp_elim(b_le_c)?; // Sa ≤ c
        lt_iff_succ_le()
            .all_elim(a.clone())?
            .all_elim(c.clone())?
            .sym()?
            .eq_mp(sa_le_c)? // a < c
            .imp_intro(&hbc)?
            .imp_intro(&hab)?
            .all_intro("c", nat())?
            .all_intro("b", nat())?
            .all_intro("a", nat())
    }
}

cached_thm! {
    /// `⊢ ∀a b c d. (a < b) ⟹ (c < d) ⟹ (a + c < b + d)` — add two strict
    /// inequalities (`lt_add_mono_r` on each side, bridged by `lt_trans`).
    pub fn add_lt_add() -> Result<Thm> {
        let (a, b, c, d) = (var("a"), var("b"), var("c"), var("d"));
        let (hab, hcd) = (lt_t(a.clone(), b.clone()), lt_t(c.clone(), d.clone()));
        // a+c < b+c.
        let ac_lt_bc = lt_add_mono_r()
            .all_elim(a.clone())?
            .all_elim(b.clone())?
            .all_elim(c.clone())?
            .sym()?
            .eq_mp(Thm::assume(hab.clone())?)?;
        // c+b < d+b, then commute to b+c < b+d.
        let bc_lt_bd = lt_add_mono_r()
            .all_elim(c.clone())?
            .all_elim(d.clone())?
            .all_elim(b.clone())?
            .sym()?
            .eq_mp(Thm::assume(hcd.clone())?)? // c+b < d+b
            .rewrite(&add_comm().all_elim(c.clone())?.all_elim(b.clone())?)? // b+c < d+b
            .rewrite(&add_comm().all_elim(d.clone())?.all_elim(b.clone())?)?; // b+c < b+d
        lt_trans()
            .all_elim(add(a.clone(), c.clone()))?
            .all_elim(add(b.clone(), c.clone()))?
            .all_elim(add(b.clone(), d.clone()))?
            .imp_elim(ac_lt_bc)?
            .imp_elim(bc_lt_bd)?
            .imp_intro(&hcd)?
            .imp_intro(&hab)?
            .all_intro("d", nat())?
            .all_intro("c", nat())?
            .all_intro("b", nat())?
            .all_intro("a", nat())
    }
}

cached_thm! {
    /// `⊢ ∀p q r s. (p + s = r + q) ⟹ (nat.lt p q = nat.lt r s)` — a strict
    /// comparison depends only on the cross-sum, so equal cross-sums give
    /// equal comparisons (the well-definedness the `int`/Grothendieck order
    /// rests on). Both sides equal `(r+q) < (q+s)` after `lt_add_mono_r`.
    pub fn lt_cross() -> Result<Thm> {
        let (p, q, r, s) = (var("p"), var("q"), var("r"), var("s"));
        let hyp = add(p.clone(), s.clone()).equals(add(r.clone(), q.clone()))?; // p+s = r+q
        // (p<q) = (p+s<q+s) = (r+q<q+s).
        let e1 = lt_add_mono_r()
            .all_elim(p.clone())?
            .all_elim(q.clone())?
            .all_elim(s.clone())?
            .sym()?
            .rewrite(&Thm::assume(hyp.clone())?)?; // (p<q) = (r+q < q+s)
        // (r<s) = (r+q<s+q) = (r+q<q+s).
        let e2 = lt_add_mono_r()
            .all_elim(r.clone())?
            .all_elim(s.clone())?
            .all_elim(q.clone())?
            .sym()?
            .rewrite(&add_comm().all_elim(s.clone())?.all_elim(q.clone())?)?; // (r<s) = (r+q < q+s)
        e1.trans(e2.sym()?)?
            .imp_intro(&hyp)?
            .all_intro("s", nat())?
            .all_intro("r", nat())?
            .all_intro("q", nat())?
            .all_intro("p", nat())
    }
}

cached_thm! {
    /// `⊢ ∀p q r s. (p + s = r + q) ⟹ (nat.le p q = nat.le r s)` — the `≤`
    /// mirror of [`lt_cross`] (via `le_add_cancel_r`).
    pub fn le_cross() -> Result<Thm> {
        let (p, q, r, s) = (var("p"), var("q"), var("r"), var("s"));
        let hyp = add(p.clone(), s.clone()).equals(add(r.clone(), q.clone()))?;
        let e1 = le_add_cancel_r()
            .all_elim(p.clone())?
            .all_elim(q.clone())?
            .all_elim(s.clone())?
            .sym()?
            .rewrite(&Thm::assume(hyp.clone())?)?; // (p≤q) = (r+q ≤ q+s)
        let e2 = le_add_cancel_r()
            .all_elim(r.clone())?
            .all_elim(s.clone())?
            .all_elim(q.clone())?
            .sym()?
            .rewrite(&add_comm().all_elim(s.clone())?.all_elim(q.clone())?)?; // (r≤s) = (r+q ≤ q+s)
        e1.trans(e2.sym()?)?
            .imp_intro(&hyp)?
            .all_intro("s", nat())?
            .all_intro("r", nat())?
            .all_intro("q", nat())?
            .all_intro("p", nat())
    }
}

/// Prove `⊢ ∀n. body` by case analysis (no induction hypothesis): `base`
/// proves `body[0]`, `cases_step` proves `∀n. body[S n]`.
fn nat_cases(motive: &Term, base: Thm, cases_step: Thm) -> Result<Thm> {
    let n = var("n");
    let body_n = rhs(&Thm::beta_conv(Term::app(motive.clone(), n.clone()))?); // body[n]
    let step = cases_step.all_elim(n)?.imp_intro(&body_n)?; // body[n] ⟹ body[S n]
    induct(motive, base, step)
}

cached_thm! {
    /// `⊢ ∀a b. (a ≤ b) = ((a < b) ∨ (a = b))` — the `≤`/`<` decomposition.
    pub fn le_iff_lt_or_eq() -> Result<Thm> {
        let (a, b) = (var("a"), var("b"));
        let eq_ab = a.clone().equals(b.clone())?;
        let disj = lt_t(a.clone(), b.clone()).or(eq_ab.clone())?;
        let le_ab = le_t(a.clone(), b.clone());

        // Forward: {a ≤ b} ⊢ disj — by cases on d = b - a using a + d = b.
        let fwd = {
            // motive_d ≔ λd. (a + d = b) ⟹ disj.
            let body_at = |t: &Term| -> Result<Term> {
                add(a.clone(), t.clone()).equals(b.clone())?.imp(disj.clone())
            };
            let motive = Term::abs(nat(), subst::close(&body_at(&var("d"))?, "d"));
            // base d=0: a+0=b ⟹ disj (a=b, right).
            let base = {
                let prem = add(a.clone(), zero()).equals(b.clone())?;
                add_zero()
                    .all_elim(a.clone())?
                    .sym()?
                    .trans(Thm::assume(prem.clone())?)? // {a+0=b} ⊢ a = b
                    .or_intro_r(lt_t(a.clone(), b.clone()))? // ⊢ disj
                    .imp_intro(&prem)?
            };
            // cases_step: ∀k. a+Sk=b ⟹ disj (a<b, left).
            let cases_step = {
                let k = var("k");
                let prem = add(a.clone(), succ(k.clone())).equals(b.clone())?;
                let s_ak_eq_b = add_succ_r()
                    .all_elim(a.clone())?
                    .all_elim(k.clone())?
                    .sym()?
                    .trans(Thm::assume(prem.clone())?)?; // {a+Sk=b} ⊢ S(a+k) = b
                let sa_le_sak = le_succ_succ()
                    .all_elim(a.clone())?
                    .all_elim(add(a.clone(), k.clone()))?
                    .sym()?
                    .eq_mp(le_add_r().all_elim(a.clone())?.all_elim(k.clone())?)?; // Sa ≤ S(a+k)
                lt_iff_succ_le()
                    .all_elim(a.clone())?
                    .all_elim(b.clone())?
                    .sym()?
                    .eq_mp(sa_le_sak.rewrite(&s_ak_eq_b)?)? // {a+Sk=b} ⊢ a < b
                    .or_intro_l(eq_ab.clone())? // ⊢ disj
                    .imp_intro(&prem)?
                    .all_intro("k", nat())?
            };
            let by_d = nat_cases(&motive, base, cases_step)?; // ∀d. a+d=b ⟹ disj
            let ad_eq_b = le_add_sub()
                .all_elim(a.clone())?
                .all_elim(b.clone())?
                .imp_elim(Thm::assume(le_ab.clone())?)?; // {a≤b} ⊢ a+(b-a)=b
            by_d.all_elim(sub(b.clone(), a.clone()))?.imp_elim(ad_eq_b)? // {a≤b} ⊢ disj
        };

        // Backward: {disj} ⊢ a ≤ b.
        let bwd = {
            let left = lt_imp_le().all_elim(a.clone())?.all_elim(b.clone())?; // (a<b)⟹(a≤b)
            let right = {
                let aeqb = Thm::assume(eq_ab.clone())?;
                Thm::refl(nat_le())?
                    .cong_fn(a.clone())?
                    .cong_app(aeqb)? // (a≤a) = (a≤b)
                    .eq_mp(le_refl().all_elim(a.clone())?)? // {a=b} ⊢ a≤b
                    .imp_intro(&eq_ab)?
            };
            Thm::assume(disj.clone())?.or_elim(left, right)?
        };

        bwd.deduct_antisym(fwd)? // ⊢ (a≤b) = disj
            .all_intro("b", nat())?
            .all_intro("a", nat())
    }
}

cached_thm! {
    /// `⊢ ∀a b. (a < b) ∨ ((a = b) ∨ (b < a))` — trichotomy of `<`.
    pub fn lt_trichotomy() -> Result<Thm> {
        let (a, b) = (var("a"), var("b"));
        let (lab, lba) = (lt_t(a.clone(), b.clone()), lt_t(b.clone(), a.clone()));
        let (eab, eba) = (a.clone().equals(b.clone())?, b.clone().equals(a.clone())?);
        let tail = eab.clone().or(lba.clone())?; // (a=b) ∨ (b<a)
        // goal ≔ a<b ∨ ((a=b) ∨ (b<a)) — assembled by the or-intros below.

        // a ≤ b branch.
        let left = {
            let lub = le_iff_lt_or_eq()
                .all_elim(a.clone())?
                .all_elim(b.clone())?
                .eq_mp(Thm::assume(le_t(a.clone(), b.clone()))?)?; // {a≤b} ⊢ a<b ∨ a=b
            let l1 = Thm::assume(lab.clone())?
                .or_intro_l(tail.clone())?
                .imp_intro(&lab)?; // (a<b)⟹goal
            let r1 = Thm::assume(eab.clone())?
                .or_intro_l(lba.clone())?
                .or_intro_r(lab.clone())?
                .imp_intro(&eab)?; // (a=b)⟹goal
            lub.or_elim(l1, r1)?.imp_intro(&le_t(a.clone(), b.clone()))?
        };
        // b ≤ a branch.
        let right = {
            let lub = le_iff_lt_or_eq()
                .all_elim(b.clone())?
                .all_elim(a.clone())?
                .eq_mp(Thm::assume(le_t(b.clone(), a.clone()))?)?; // {b≤a} ⊢ b<a ∨ b=a
            let l2 = Thm::assume(lba.clone())?
                .or_intro_r(eab.clone())?
                .or_intro_r(lab.clone())?
                .imp_intro(&lba)?; // (b<a)⟹goal
            let r2 = Thm::assume(eba.clone())?
                .sym()?
                .or_intro_l(lba.clone())?
                .or_intro_r(lab.clone())?
                .imp_intro(&eba)?; // (b=a)⟹goal
            lub.or_elim(l2, r2)?.imp_intro(&le_t(b.clone(), a.clone()))?
        };

        le_total()
            .all_elim(a.clone())?
            .all_elim(b.clone())?
            .or_elim(left, right)?
            .all_intro("b", nat())?
            .all_intro("a", nat())
    }
}

// ============================================================================
// Additive normaliser — prove `t = t'` for any two `+`-trees over the same
// multiset of leaves (associate to the right, then bubble into order). The
// reusable workhorse for the Grothendieck rearrangements.
// ============================================================================

/// `nat.add a b` → `(a, b)`; `None` for any other (leaf) term.
fn as_add(t: &Term) -> Option<(Term, Term)> {
    let (f, b) = t.as_app()?;
    let (op, a) = f.as_app()?;
    (*op == nat_add()).then(|| (a.clone(), b.clone()))
}

/// `⊢ left + x = left + y` from `eq : ⊢ x = y`.
fn cong_add_r(left: &Term, eq: Thm) -> Result<Thm> {
    eq.cong_arg(Term::app(nat_add(), left.clone()))
}

/// `⊢ t = t'` re-associating `t` fully to the right (leaf order preserved).
fn right_nest(t: &Term) -> Result<Thm> {
    if let Some((a, b)) = as_add(t) {
        let ea = right_nest(&a)?; // a = rn_a
        let eb = right_nest(&b)?; // b = rn_b
        let (rn_a, rn_b) = (rhs(&ea), rhs(&eb));
        cong_add(ea, eb)?.trans(assoc_append(&rn_a, &rn_b)?)
    } else {
        Thm::refl(t.clone())
    }
}

/// `⊢ (rn_a + rn_b) = right-nested(leaves rn_a ++ rn_b)` for right-nested
/// `rn_a` — repeated associativity.
fn assoc_append(rn_a: &Term, rn_b: &Term) -> Result<Thm> {
    if let Some((x0, rest_a)) = as_add(rn_a) {
        let assoc = add_assoc()
            .all_elim(x0.clone())?
            .all_elim(rest_a.clone())?
            .all_elim(rn_b.clone())?; // (x0+rest)+rn_b = x0+(rest+rn_b)
        assoc.trans(cong_add_r(&x0, assoc_append(&rest_a, rn_b)?)?)
    } else {
        Thm::refl(add(rn_a.clone(), rn_b.clone()))
    }
}

/// `⊢ a0 + (x + r) = x + (a0 + r)` — swap the first two of a right-nested sum.
fn swap_front2(a0: &Term, x: &Term, r: &Term) -> Result<Thm> {
    add_assoc()
        .all_elim(a0.clone())?
        .all_elim(x.clone())?
        .all_elim(r.clone())?
        .sym()? // a0+(x+r) = (a0+x)+r
        .trans(cong_add_l(
            add_comm().all_elim(a0.clone())?.all_elim(x.clone())?,
            r.clone(),
        )?)? // = (x+a0)+r
        .trans(
            add_assoc()
                .all_elim(x.clone())?
                .all_elim(a0.clone())?
                .all_elim(r.clone())?,
        ) // = x+(a0+r)
}

/// `⊢ a = x + a'` — bring an occurrence of `x` to the front of a right-nested
/// sum `a` (with `a'` the remaining leaves). Requires `x` to occur in `a` and
/// `a` to have at least two leaves.
fn bring_front(a: &Term, x: &Term) -> Result<Thm> {
    let (a0, a_rest) =
        as_add(a).ok_or_else(|| Error::ConnectiveRule("bring_front: leaf".into()))?;
    if a0 == *x {
        return Thm::refl(a.clone()); // a = x + a_rest
    }
    if as_add(&a_rest).is_none() {
        // a_rest is the single remaining leaf — it is `x`.  a0 + x = x + a0.
        return add_comm().all_elim(a0)?.all_elim(a_rest);
    }
    let br = bring_front(&a_rest, x)?; // a_rest = x + a_rest'
    let a_rest_p = as_add(&rhs(&br))
        .ok_or_else(|| Error::ConnectiveRule("bring_front: shape".into()))?
        .1;
    cong_add_r(&a0, br)?.trans(swap_front2(&a0, x, &a_rest_p)?)
}

/// `⊢ a = b` for right-nested `a`, `b` over the same leaf multiset.
fn permute_eq(a: &Term, b: &Term) -> Result<Thm> {
    if a == b {
        return Thm::refl(a.clone());
    }
    let (b0, b_rest) = as_add(b).ok_or_else(|| Error::ConnectiveRule("permute_eq: leaf".into()))?;
    let bring = bring_front(a, &b0)?; // a = b0 + a_rest
    let a_rest = as_add(&rhs(&bring))
        .ok_or_else(|| Error::ConnectiveRule("permute_eq: shape".into()))?
        .1;
    bring.trans(cong_add_r(&b0, permute_eq(&a_rest, &b_rest)?)?)
}

/// **Additive normalisation.** `⊢ lhs = rhs` whenever `lhs` and `rhs` are
/// `+`-trees over the same multiset of leaves (re-associate both to the
/// right, then permute). Errors if the leaf multisets differ.
pub fn prove_add_eq(lhs: &Term, rhs_t: &Term) -> Result<Thm> {
    let el = right_nest(lhs)?; // lhs = rnL
    let er = right_nest(rhs_t)?; // rhs = rnR
    let perm = permute_eq(&rhs(&el), &rhs(&er))?; // rnL = rnR
    el.trans(perm)?.trans(er.sym()?)
}

// ============================================================================
// Strict multiplicative monotonicity — `int`'s positive-multiplier order law
// lifts through these.
// ============================================================================

cached_thm! {
    /// `⊢ ∀x p. (0 < p) ⟹ (x < x + p)`.
    pub fn lt_add_pos() -> Result<Thm> {
        let (x, p) = (var("x"), var("p"));
        let hp = lt_t(zero(), p.clone());
        let s0_le_p = lt_iff_succ_le()
            .all_elim(zero())?
            .all_elim(p.clone())?
            .eq_mp(Thm::assume(hp.clone())?)?; // S0 ≤ p
        let shifted = le_add_cancel_r()
            .all_elim(succ(zero()))?
            .all_elim(p.clone())?
            .all_elim(x.clone())?
            .sym()?
            .eq_mp(s0_le_p)?; // S0 + x ≤ p + x
        let comm_l = shifted
            .rewrite(&add_comm().all_elim(succ(zero()))?.all_elim(x.clone())?)? // x+S0 ≤ p+x
            .rewrite(&add_comm().all_elim(p.clone())?.all_elim(x.clone())?)?; // x+S0 ≤ x+p
        let xs0 = add_succ_r()
            .all_elim(x.clone())?
            .all_elim(zero())?
            .trans(add_zero().all_elim(x.clone())?.cong_arg(nat_succ())?)?; // x+S0 = S x
        let sx_le = comm_l.rewrite(&xs0)?; // S x ≤ x+p
        lt_iff_succ_le()
            .all_elim(x.clone())?
            .all_elim(add(x.clone(), p.clone()))?
            .sym()?
            .eq_mp(sx_le)? // x < x+p
            .imp_intro(&hp)?
            .all_intro("p", nat())?
            .all_intro("x", nat())
    }
}

cached_thm! {
    /// `⊢ ∀a b. (0 < a) ⟹ (0 < b) ⟹ (0 < a · b)` — a product of positives
    /// is positive (cases on `a`; the successor case uses `0 < b ≤ b + a'·b`).
    pub fn mul_pos() -> Result<Thm> {
        let b = var("b");
        let body_at = |t: &Term| -> Result<Term> {
            lt_t(zero(), t.clone())
                .imp(lt_t(zero(), b.clone()).imp(lt_t(zero(), mul(t.clone(), b.clone())))?)?
                .forall("b", nat())
        };
        let motive = Term::abs(nat(), subst::close(&body_at(&var("a"))?, "a"));
        // base a=0: 0<0 is false, so vacuous.
        let base = {
            let h00 = lt_t(zero(), zero());
            let concl = lt_t(zero(), b.clone()).imp(lt_t(zero(), mul(zero(), b.clone())))?;
            lt_irrefl()
                .all_elim(zero())?
                .not_elim(Thm::assume(h00.clone())?)? // {0<0} ⊢ F
                .false_elim(concl)?
                .imp_intro(&h00)?
                .all_intro("b", nat())?
        };
        // step a=S a'.
        let cases_step = {
            let ap = var("a'");
            let (pos_sa, pos_b) = (lt_t(zero(), succ(ap.clone())), lt_t(zero(), b.clone()));
            let sum = add(b.clone(), mul(ap.clone(), b.clone())); // b + a'·b
            let ms = mul_step().all_elim(ap.clone())?.all_elim(b.clone())?; // S a'·b = b + a'·b
            let s0_le_b = lt_iff_succ_le()
                .all_elim(zero())?
                .all_elim(b.clone())?
                .eq_mp(Thm::assume(pos_b.clone())?)?; // S0 ≤ b
            let s0_le_sum = le_trans()
                .all_elim(succ(zero()))?
                .all_elim(b.clone())?
                .all_elim(sum.clone())?
                .imp_elim(s0_le_b)?
                .imp_elim(le_add_r().all_elim(b.clone())?.all_elim(mul(ap.clone(), b.clone()))?)?; // S0 ≤ b+a'·b
            lt_iff_succ_le()
                .all_elim(zero())?
                .all_elim(sum)?
                .sym()?
                .eq_mp(s0_le_sum)? // 0 < b+a'·b
                .rewrite(&ms.sym()?)? // 0 < S a'·b
                .imp_intro(&pos_b)?
                .imp_intro(&pos_sa)?
                .all_intro("b", nat())?
                .all_intro("a'", nat())?
        };
        nat_cases(&motive, base, cases_step)
    }
}

cached_thm! {
    /// `⊢ ∀a b c. (a < b) ⟹ (0 < c) ⟹ (a · c < b · c)`.
    pub fn lt_mul_mono_r() -> Result<Thm> {
        let (a, b, c) = (var("a"), var("b"), var("c"));
        let (hab, hc) = (lt_t(a.clone(), b.clone()), lt_t(zero(), c.clone()));
        // b = a + d, d = S(b − S a), 0 < d.
        let sa_le_b = lt_iff_succ_le()
            .all_elim(a.clone())?
            .all_elim(b.clone())?
            .eq_mp(Thm::assume(hab.clone())?)?; // S a ≤ b
        let dprime = sub(b.clone(), succ(a.clone())); // b − S a
        let split = le_add_sub()
            .all_elim(succ(a.clone()))?
            .all_elim(b.clone())?
            .imp_elim(sa_le_b)?; // S a + (b−S a) = b
        let b_eq = add_succ_r()
            .all_elim(a.clone())?
            .all_elim(dprime.clone())? // a + S d' = S(a+d')
            .trans(add_step().all_elim(a.clone())?.all_elim(dprime.clone())?.sym()?)? // = S a + d'
            .trans(split)?; // a + S d' = b
        let d = succ(dprime.clone());
        let pos_dc = mul_pos()
            .all_elim(d.clone())?
            .all_elim(c.clone())?
            .imp_elim(zero_lt_succ().all_elim(dprime.clone())?)? // 0 < d
            .imp_elim(Thm::assume(hc.clone())?)?; // 0 < d·c
        let acc_eq = distrib_r()
            .all_elim(a.clone())?
            .all_elim(d.clone())?
            .all_elim(c.clone())?
            .sym()? // a·c + d·c = (a+d)·c
            .trans(Thm::refl(nat_mul())?.cong_app(b_eq)?.cong_fn(c.clone())?)?; // = b·c
        lt_add_pos()
            .all_elim(mul(a.clone(), c.clone()))?
            .all_elim(mul(d.clone(), c.clone()))?
            .imp_elim(pos_dc)? // a·c < a·c + d·c
            .rewrite(&acc_eq)? // a·c < b·c
            .imp_intro(&hc)?
            .imp_intro(&hab)?
            .all_intro("c", nat())?
            .all_intro("b", nat())?
            .all_intro("a", nat())
    }
}

// ============================================================================
// iter / pow / shl / shr — recursion equations and characterizing theorems.
//
// `iter`, `nat.pow`, `nat.shl`, `nat.shr` all iterate on their *second*
// argument and seed with the first (or a literal). Their recursion equations
// are derived from `rec_holds` the same way `+`/`*`/`-`'s are, then the
// algebraic facts (`pow_add`, `shl_eq_mul_pow`, …) follow by `nat`-induction.
// ============================================================================

pub(crate) fn pow(n: Term, m: Term) -> Term {
    Term::app(Term::app(nat_pow(), n), m)
}

pub(crate) fn shl(n: Term, m: Term) -> Term {
    Term::app(Term::app(nat_shl(), n), m)
}

pub(crate) fn shr(n: Term, m: Term) -> Term {
    Term::app(Term::app(nat_shr(), n), m)
}

// `nat.pow` *seeds* its `iter` with the literal `1` (`one`): in that closed
// position the `reduce` in `pow_to_iter` folds `succ 0` to the `Nat` literal
// `1n`, so the recursion equation matches `1n`. The `2` inside the
// `nat.shl`/`nat.shr` *step* functions sits under a binder (`λx. 2*x`), where
// `reduce` leaves it as `succ (succ 0)` (`two`) — so we match that shape there.
fn one() -> Term {
    Term::nat_lit(1u32)
}

/// `succ (succ 0)` — the shape of `2` *inside* the `shl`/`shr` step lambdas,
/// where `reduce` leaves it un-folded (it is under a binder).
fn two() -> Term {
    succ(succ(zero()))
}

/// `2n` — the `Nat` literal `reduce` produces once the step lambda is applied
/// (the multiplier in the `shl`/`shr` recursion equations).
fn two_lit() -> Term {
    Term::nat_lit(2u32)
}

/// `iter[nat] m f a` as a `Term`.
fn iter_t(m: Term, f: Term, a: Term) -> Term {
    Term::app(Term::app(Term::app(iter(nat()), m), f), a)
}

/// `λ_:nat. f` — the `natRec` step function `iter` is built from.
fn iter_step(f: Term) -> Term {
    Term::abs(nat(), f)
}

cached_thm! {
    /// `⊢ ∀(f:nat→nat)(a:nat). iter 0 f a = a` — `iter`'s base equation.
    pub fn iter_zero() -> Result<Thm> {
        let f = Term::free("f", Type::fun(nat(), nat()));
        let a = var("a");
        rec_base_eq(iter_t(zero(), f.clone(), a.clone()), a.clone(), iter_step(f.clone()))?
            .all_intro("a", nat())?
            .all_intro("f", Type::fun(nat(), nat()))
    }
}

cached_thm! {
    /// `⊢ ∀(f:nat→nat)(a:nat)(m:nat). iter (S m) f a = f (iter m f a)` —
    /// `iter`'s step equation.
    pub fn iter_succ() -> Result<Thm> {
        let f = Term::free("f", Type::fun(nat(), nat()));
        let a = var("a");
        let m = var("m");
        rec_step_eq(
            iter_t(succ(m.clone()), f.clone(), a.clone()),
            a.clone(),
            iter_step(f.clone()),
            m.clone(),
            iter_t(m.clone(), f.clone(), a.clone()),
            f.clone(), // push the recursive call under `f`
        )?
        .all_intro("m", nat())?
        .all_intro("a", nat())?
        .all_intro("f", Type::fun(nat(), nat()))
    }
}

// ---- pow ----

/// `⊢ pow n m = iter m (λx. n*x) 1` — δ-unfold `nat.pow` + β.
fn pow_to_iter(n: Term, m: Term) -> Result<Thm> {
    let unf = pow(n, m).delta_all(defs::nat_pow_spec().symbol())?;
    let red = rhs(&unf).reduce()?;
    unf.trans(red)
}

/// `λx:nat. n*x` — the `iter` step function in `nat.pow`'s body.
fn pow_step(n: Term) -> Term {
    Term::abs(nat(), subst::close(&mul(n, var("x")), "x"))
}

cached_thm! {
    /// `⊢ ∀a. a ^ 0 = 1`.
    pub fn pow_zero() -> Result<Thm> {
        let a = var("a");
        let conv = pow_to_iter(a.clone(), zero())?; // a^0 = iter 0 (λx. a*x) 1
        let iz = iter_zero()
            .all_elim(pow_step(a.clone()))?
            .all_elim(one())?; // iter 0 (λx. a*x) 1 = 1
        conv.trans(iz)?.all_intro("a", nat())
    }
}

cached_thm! {
    /// `⊢ ∀a m. a ^ (S m) = a * a ^ m`.
    pub fn pow_succ() -> Result<Thm> {
        let a = var("a");
        let m = var("m");
        let step = pow_step(a.clone());
        let conv = pow_to_iter(a.clone(), succ(m.clone()))?; // a^(Sm) = iter (Sm) step 1
        let is = iter_succ()
            .all_elim(step.clone())?
            .all_elim(one())?
            .all_elim(m.clone())?; // = step (iter m step 1)
        let red = rhs(&is).reduce()?; // = a * (iter m step 1)
        let fold = pow_to_iter(a.clone(), m.clone())?
            .sym()?
            .cong_arg(Term::app(nat_mul(), a.clone()))?; // a*(iter m step 1) = a*(a^m)
        conv.trans(is)?.trans(red)?.trans(fold)?
            .all_intro("m", nat())?
            .all_intro("a", nat())
    }
}

// ---- shl ----

/// `⊢ shl n m = iter m (λx. 2*x) n` — δ-unfold `nat.shl` + β.
fn shl_to_iter(n: Term, m: Term) -> Result<Thm> {
    let unf = shl(n, m).delta_all(defs::nat_shl_spec().symbol())?;
    let red = rhs(&unf).reduce()?;
    unf.trans(red)
}

/// `λx:nat. 2*x` — the `iter` step function in `nat.shl`'s body.
fn shl_step() -> Term {
    Term::abs(nat(), subst::close(&mul(two(), var("x")), "x"))
}

cached_thm! {
    /// `⊢ ∀a. shl a 0 = a`.
    pub fn shl_zero() -> Result<Thm> {
        let a = var("a");
        let conv = shl_to_iter(a.clone(), zero())?; // shl a 0 = iter 0 (λx. 2*x) a
        let iz = iter_zero().all_elim(shl_step())?.all_elim(a.clone())?;
        conv.trans(iz)?.all_intro("a", nat())
    }
}

cached_thm! {
    /// `⊢ ∀a m. shl a (S m) = 2 * shl a m`.
    pub fn shl_succ() -> Result<Thm> {
        let a = var("a");
        let m = var("m");
        let step = shl_step();
        let conv = shl_to_iter(a.clone(), succ(m.clone()))?;
        let is = iter_succ()
            .all_elim(step.clone())?
            .all_elim(a.clone())?
            .all_elim(m.clone())?;
        let red = rhs(&is).reduce()?; // = 2 * (iter m step a)
        let fold = shl_to_iter(a.clone(), m.clone())?
            .sym()?
            .cong_arg(Term::app(nat_mul(), two_lit()))?; // 2*(iter m step a) = 2*(shl a m)
        conv.trans(is)?.trans(red)?.trans(fold)?
            .all_intro("m", nat())?
            .all_intro("a", nat())
    }
}

// ---- shr ----

/// `⊢ shr n m = iter m (λx. div x 2) n` — δ-unfold `nat.shr` + β.
fn shr_to_iter(n: Term, m: Term) -> Result<Thm> {
    let unf = shr(n, m).delta_all(defs::nat_shr_spec().symbol())?;
    let red = rhs(&unf).reduce()?;
    unf.trans(red)
}

/// `λx:nat. div x 2` — the `iter` step function in `nat.shr`'s body.
fn shr_step() -> Term {
    let div_x_2 = Term::app(Term::app(nat_div(), var("x")), two());
    Term::abs(nat(), subst::close(&div_x_2, "x"))
}

cached_thm! {
    /// `⊢ ∀a. shr a 0 = a`.
    pub fn shr_zero() -> Result<Thm> {
        let a = var("a");
        let conv = shr_to_iter(a.clone(), zero())?;
        let iz = iter_zero().all_elim(shr_step())?.all_elim(a.clone())?;
        conv.trans(iz)?.all_intro("a", nat())
    }
}

cached_thm! {
    /// `⊢ ∀a m. shr a (S m) = div (shr a m) 2`.
    pub fn shr_succ() -> Result<Thm> {
        let a = var("a");
        let m = var("m");
        let step = shr_step();
        let conv = shr_to_iter(a.clone(), succ(m.clone()))?;
        let is = iter_succ()
            .all_elim(step.clone())?
            .all_elim(a.clone())?
            .all_elim(m.clone())?;
        let red = rhs(&is).reduce()?; // = div (iter m step a) 2
        let fold = shr_to_iter(a.clone(), m.clone())?
            .sym()?
            .cong_arg(nat_div())?
            .cong_fn(two_lit())?; // div (iter m step a) 2 = div (shr a m) 2
        conv.trans(is)?.trans(red)?.trans(fold)?
            .all_intro("m", nat())?
            .all_intro("a", nat())
    }
}

// ---- pow: the exponent-additivity law ----

cached_thm! {
    /// `⊢ ∀a m n. a ^ (m + n) = a ^ m * a ^ n` — exponents add (the
    /// homomorphism `(nat,+) → (nat,·)`). Proved by induction on `n`.
    pub fn pow_add() -> Result<Thm> {
        let a = var("a");
        let m = var("m");
        // body[n] ≔ a^(m+n) = a^m * a^n
        let body_at = |t: &Term| -> Result<Term> {
            pow(a.clone(), add(m.clone(), t.clone()))
                .equals(mul(pow(a.clone(), m.clone()), pow(a.clone(), t.clone())))
        };
        let motive = Term::abs(nat(), subst::close(&body_at(&var("n"))?, "n"));

        // base n=0: a^(m+0) = a^m = a^m * 1 = a^m * a^0.
        let base = {
            let lhs = add_zero()
                .all_elim(m.clone())?
                .cong_arg(Term::app(nat_pow(), a.clone()))?; // a^(m+0) = a^m
            let am = pow(a.clone(), m.clone());
            let rhs = mul_one()
                .all_elim(am.clone())?
                .sym()? // a^m = a^m * 1
                .trans(
                    pow_zero()
                        .all_elim(a.clone())?
                        .sym()?
                        .cong_arg(Term::app(nat_mul(), am.clone()))?, // a^m*1 = a^m*a^0
                )?;
            lhs.trans(rhs)?
        };

        // step: body[n] ⟹ body[S n].
        let n = var("n");
        let ihc = body_at(&n)?;
        let am = pow(a.clone(), m.clone());
        let an = pow(a.clone(), n.clone());
        let inner = {
            // a^(m+Sn) = a^(S(m+n)) = a*a^(m+n) = a*(a^m*a^n).
            let l = add_succ_r()
                .all_elim(m.clone())?
                .all_elim(n.clone())? // m+Sn = S(m+n)
                .cong_arg(Term::app(nat_pow(), a.clone()))? // a^(m+Sn) = a^(S(m+n))
                .trans(pow_succ().all_elim(a.clone())?.all_elim(add(m.clone(), n.clone()))?)? // = a*a^(m+n)
                .trans(
                    Thm::assume(ihc.clone())?
                        .cong_arg(Term::app(nat_mul(), a.clone()))?, // = a*(a^m*a^n)
                )?;
            // a^m * a^(Sn) = a^m*(a*a^n).
            let r = pow_succ()
                .all_elim(a.clone())?
                .all_elim(n.clone())? // a^(Sn) = a*a^n
                .cong_arg(Term::app(nat_mul(), am.clone()))?; // a^m*a^(Sn) = a^m*(a*a^n)
            // a*(a^m*a^n) = a^m*(a*a^n)  — by comm/assoc.
            let bridge = mul_assoc()
                .all_elim(a.clone())?
                .all_elim(am.clone())?
                .all_elim(an.clone())?
                .sym()? // a*(a^m*a^n) = (a*a^m)*a^n
                .trans(cong_mul_l(
                    mul_comm().all_elim(a.clone())?.all_elim(am.clone())?,
                    an.clone(),
                )?)? // = (a^m*a)*a^n
                .trans(
                    mul_assoc()
                        .all_elim(am.clone())?
                        .all_elim(a.clone())?
                        .all_elim(an.clone())?,
                )?; // = a^m*(a*a^n)
            l.trans(bridge)?.trans(r.sym()?)?
        };
        let step = inner.imp_intro(&ihc)?;
        induct_on("n", &motive, base, step)?
            .all_intro("m", nat())?
            .all_intro("a", nat())
    }
}

// ---- shl: the `shl a m = a * 2^m` characterization ----

cached_thm! {
    /// `⊢ ∀a m. shl a m = a * 2 ^ m` — a left shift by `m` multiplies by
    /// `2^m`. Proved by induction on `m` (`shl_succ` + `pow_succ`).
    pub fn shl_eq_mul_pow() -> Result<Thm> {
        let a = var("a");
        // body[m] ≔ shl a m = a * 2^m
        let body_at = |t: &Term| -> Result<Term> {
            shl(a.clone(), t.clone())
                .equals(mul(a.clone(), pow(two_lit(), t.clone())))
        };
        let motive = Term::abs(nat(), subst::close(&body_at(&var("m"))?, "m"));

        // base m=0: shl a 0 = a = a*1 = a*2^0.
        let base = {
            let l = shl_zero().all_elim(a.clone())?; // shl a 0 = a
            let r = mul_one()
                .all_elim(a.clone())?
                .sym()? // a = a*1
                .trans(
                    pow_zero()
                        .all_elim(two_lit())?
                        .sym()?
                        .cong_arg(Term::app(nat_mul(), a.clone()))?, // a*1 = a*2^0
                )?;
            l.trans(r)?
        };

        // step: body[m] ⟹ body[S m].
        let m = var("m");
        let ihc = body_at(&m)?;
        let inner = {
            // shl a (Sm) = 2*shl a m = 2*(a*2^m).
            let l = shl_succ()
                .all_elim(a.clone())?
                .all_elim(m.clone())? // shl a (Sm) = 2 * shl a m
                .trans(
                    Thm::assume(ihc.clone())?
                        .cong_arg(Term::app(nat_mul(), two_lit()))?, // = 2*(a*2^m)
                )?;
            // a*2^(Sm) = a*(2*2^m).
            let r = pow_succ()
                .all_elim(two_lit())?
                .all_elim(m.clone())? // 2^(Sm) = 2*2^m
                .cong_arg(Term::app(nat_mul(), a.clone()))?; // a*2^(Sm) = a*(2*2^m)
            // 2*(a*2^m) = a*(2*2^m) — comm/assoc.
            let pm = pow(two_lit(), m.clone());
            let bridge = mul_assoc()
                .all_elim(two_lit())?
                .all_elim(a.clone())?
                .all_elim(pm.clone())?
                .sym()? // 2*(a*2^m) = (2*a)*2^m
                .trans(cong_mul_l(
                    mul_comm().all_elim(two_lit())?.all_elim(a.clone())?,
                    pm.clone(),
                )?)? // = (a*2)*2^m
                .trans(
                    mul_assoc()
                        .all_elim(a.clone())?
                        .all_elim(two_lit())?
                        .all_elim(pm.clone())?,
                )?; // = a*(2*2^m)
            l.trans(bridge)?.trans(r.sym()?)?
        };
        let step = inner.imp_intro(&ihc)?;
        induct_on("m", &motive, base, step)?
            .all_intro("a", nat())
    }
}

// ---- div / mod ----
//
// `nat.div` is a def-style Euclidean *selector* (it picks the unique `d` with
// `m≠0 ⟹ d·m ≤ n < (d+1)·m`); transferring those bounds to `nat.div` itself
// needs a *witness* floor function — built by strong induction over the graph,
// like the `natRec` construction. That witness is deferred (see
// `init/SKELETONS.md`). What IS reachable now, hypothesis-free, is `nat.mod`'s
// *definition* (it is an ordinary `let`): `mod n m = n − (n/m)·m`.

#[allow(dead_code)] // the `div`/`mod` term-builder pair (used in tests + future div facts)
pub(crate) fn nat_div_t(n: Term, m: Term) -> Term {
    Term::app(Term::app(nat_div(), n), m)
}

pub(crate) fn nat_mod_t(n: Term, m: Term) -> Term {
    Term::app(Term::app(nat_mod(), n), m)
}

cached_thm! {
    /// `⊢ ∀n m. n mod m = n − (n / m) · m` — the Euclidean remainder is
    /// `n` minus the largest multiple of `m` below it. This is `nat.mod`'s
    /// *definition* (`nat.mod` is a `let`), δ-unfolded and β-reduced — a
    /// genuine, hypothesis-free equation that needs no `div` facts.
    pub fn mod_def() -> Result<Thm> {
        let n = var("n");
        let m = var("m");
        let unf = nat_mod_t(n.clone(), m.clone()).delta_all(defs::nat_mod_spec().symbol())?;
        let red = rhs(&unf).reduce()?;
        unf.trans(red)?
            .all_intro("m", nat())?
            .all_intro("n", nat())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn iter_recursion_equations() {
        let f = Term::free("f", Type::fun(nat(), nat()));
        let (a, m) = (var("a"), var("m"));
        // iter 0 f a = a.
        let iz = iter_zero()
            .all_elim(f.clone())
            .unwrap()
            .all_elim(a.clone())
            .unwrap();
        assert_eq!(
            iz.concl(),
            &iter_t(zero(), f.clone(), a.clone())
                .equals(a.clone())
                .unwrap()
        );
        // iter (S m) f a = f (iter m f a).
        let is = iter_succ()
            .all_elim(f.clone())
            .unwrap()
            .all_elim(a.clone())
            .unwrap()
            .all_elim(m.clone())
            .unwrap();
        let want = iter_t(succ(m.clone()), f.clone(), a.clone())
            .equals(Term::app(f.clone(), iter_t(m.clone(), f, a)))
            .unwrap();
        assert_eq!(is.concl(), &want);
        for t in [iter_zero(), iter_succ()] {
            assert!(t.hyps().is_empty());
        }
    }

    #[test]
    fn pow_recursion_equations() {
        let (a, m) = (var("a"), var("m"));
        // a^0 = 1.
        let pz = pow_zero().all_elim(a.clone()).unwrap();
        assert_eq!(pz.concl(), &pow(a.clone(), zero()).equals(one()).unwrap());
        // a^(S m) = a * a^m.
        let ps = pow_succ()
            .all_elim(a.clone())
            .unwrap()
            .all_elim(m.clone())
            .unwrap();
        let want = pow(a.clone(), succ(m.clone()))
            .equals(mul(a.clone(), pow(a, m)))
            .unwrap();
        assert_eq!(ps.concl(), &want);
        for t in [pow_zero(), pow_succ()] {
            assert!(t.hyps().is_empty());
        }
    }

    #[test]
    fn shl_recursion_equations() {
        let (a, m) = (var("a"), var("m"));
        let sz = shl_zero().all_elim(a.clone()).unwrap();
        assert_eq!(
            sz.concl(),
            &shl(a.clone(), zero()).equals(a.clone()).unwrap()
        );
        let ss = shl_succ()
            .all_elim(a.clone())
            .unwrap()
            .all_elim(m.clone())
            .unwrap();
        let want = shl(a.clone(), succ(m.clone()))
            .equals(mul(two_lit(), shl(a, m)))
            .unwrap();
        assert_eq!(ss.concl(), &want);
        for t in [shl_zero(), shl_succ()] {
            assert!(t.hyps().is_empty());
        }
    }

    #[test]
    fn shr_recursion_equations() {
        let (a, m) = (var("a"), var("m"));
        let sz = shr_zero().all_elim(a.clone()).unwrap();
        assert_eq!(
            sz.concl(),
            &shr(a.clone(), zero()).equals(a.clone()).unwrap()
        );
        let ss = shr_succ()
            .all_elim(a.clone())
            .unwrap()
            .all_elim(m.clone())
            .unwrap();
        let div2 = |t: Term| Term::app(Term::app(nat_div(), t), two_lit());
        let want = shr(a.clone(), succ(m.clone()))
            .equals(div2(shr(a, m)))
            .unwrap();
        assert_eq!(ss.concl(), &want);
        for t in [shr_zero(), shr_succ()] {
            assert!(t.hyps().is_empty());
        }
    }

    #[test]
    fn mod_definitional_equation() {
        // ⊢ ∀n m. n mod m = n − (n/m)·m.
        let (n, m) = (var("n"), var("m"));
        let md = mod_def()
            .all_elim(n.clone())
            .unwrap()
            .all_elim(m.clone())
            .unwrap();
        let want = nat_mod_t(n.clone(), m.clone())
            .equals(sub(
                n.clone(),
                mul(nat_div_t(n.clone(), m.clone()), m.clone()),
            ))
            .unwrap();
        assert_eq!(md.concl(), &want);
        assert!(mod_def().hyps().is_empty());
    }

    #[test]
    fn pow_add_and_shl_characterization() {
        let (a, m, n) = (var("a"), var("m"), var("n"));
        // a^(m+n) = a^m * a^n.
        let pa = pow_add()
            .all_elim(a.clone())
            .unwrap()
            .all_elim(m.clone())
            .unwrap()
            .all_elim(n.clone())
            .unwrap();
        let want = pow(a.clone(), add(m.clone(), n.clone()))
            .equals(mul(pow(a.clone(), m.clone()), pow(a.clone(), n.clone())))
            .unwrap();
        assert_eq!(pa.concl(), &want);
        // shl a m = a * 2^m.
        let sh = shl_eq_mul_pow()
            .all_elim(a.clone())
            .unwrap()
            .all_elim(m.clone())
            .unwrap();
        let want2 = shl(a.clone(), m.clone())
            .equals(mul(a.clone(), pow(two_lit(), m.clone())))
            .unwrap();
        assert_eq!(sh.concl(), &want2);
        for t in [pow_add(), shl_eq_mul_pow()] {
            assert!(t.hyps().is_empty(), "exponent laws are hypothesis-free");
        }
    }

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
    fn mul_monotonicity_and_normaliser() {
        let (a, b, c) = (var("a"), var("b"), var("c"));
        // mul_pos / lt_mul_mono_r genuine + well-stated.
        let mp = mul_pos()
            .all_elim(a.clone())
            .unwrap()
            .all_elim(b.clone())
            .unwrap();
        assert_eq!(
            mp.concl(),
            &lt_t(zero(), a.clone())
                .imp(
                    lt_t(zero(), b.clone())
                        .imp(lt_t(zero(), mul(a.clone(), b.clone())))
                        .unwrap()
                )
                .unwrap()
        );
        let mm = lt_mul_mono_r()
            .all_elim(a.clone())
            .unwrap()
            .all_elim(b.clone())
            .unwrap()
            .all_elim(c.clone())
            .unwrap();
        assert_eq!(
            mm.concl(),
            &lt_t(a.clone(), b.clone())
                .imp(
                    lt_t(zero(), c.clone())
                        .imp(lt_t(mul(a.clone(), c.clone()), mul(b.clone(), c.clone())))
                        .unwrap()
                )
                .unwrap()
        );
        assert!(mul_pos().hyps().is_empty() && lt_mul_mono_r().hyps().is_empty());
        // prove_add_eq: (a+b)+c = c+(b+a) (same leaves, reordered).
        let lhs = add(add(a.clone(), b.clone()), c.clone());
        let rhs_t = add(c.clone(), add(b.clone(), a.clone()));
        let pe = super::prove_add_eq(&lhs, &rhs_t).unwrap();
        assert_eq!(pe.concl(), &lhs.equals(rhs_t).unwrap());
        assert!(pe.hyps().is_empty());
    }

    #[test]
    fn strict_order_theory_is_genuine() {
        let (a, b, c) = (var("a"), var("b"), var("c"));
        // lt_trans: a<b ⟹ b<c ⟹ a<c.
        let lt = lt_trans()
            .all_elim(a.clone())
            .unwrap()
            .all_elim(b.clone())
            .unwrap()
            .all_elim(c.clone())
            .unwrap();
        assert_eq!(
            lt.concl(),
            &lt_t(a.clone(), b.clone())
                .imp(
                    lt_t(b.clone(), c.clone())
                        .imp(lt_t(a.clone(), c.clone()))
                        .unwrap()
                )
                .unwrap()
        );
        // lt_add_mono_r: (a+c<b+c) = (a<b).
        let mono = lt_add_mono_r()
            .all_elim(a.clone())
            .unwrap()
            .all_elim(b.clone())
            .unwrap()
            .all_elim(c.clone())
            .unwrap();
        assert_eq!(
            mono.concl(),
            &lt_t(add(a.clone(), c.clone()), add(b.clone(), c.clone()))
                .equals(lt_t(a.clone(), b.clone()))
                .unwrap()
        );
        // trichotomy + le_iff_lt_or_eq shapes.
        let tri = lt_trichotomy()
            .all_elim(a.clone())
            .unwrap()
            .all_elim(b.clone())
            .unwrap();
        assert!(tri.concl().type_of().unwrap().is_bool());
        for t in [
            le_succ_self(),
            lt_imp_le(),
            le_add_cancel_r(),
            lt_add_mono_r(),
            lt_trans(),
            le_iff_lt_or_eq(),
            lt_trichotomy(),
        ] {
            assert!(t.hyps().is_empty(), "nat strict-order facts are genuine");
        }
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
        assert!(succ_inj().hyps().is_empty(), "succ.inj is proved");
        assert!(zero_ne_succ().hyps().is_empty(), "zero.ne_succ is proved");
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
        assert!(rec_holds().hyps().is_empty(), "rec.holds is proved");
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
        // The ported commutative-semiring lemmas must state exactly what the
        // hand-written Rust proofs state (same checked theorem, two proofs).
        assert_eq!(cov::add_comm_cov().concl(), super::add_comm().concl());
        assert_eq!(cov::add_assoc_cov().concl(), super::add_assoc().concl());
        assert_eq!(cov::add_cancel_cov().concl(), super::add_cancel().concl());
        assert_eq!(cov::mul_comm_cov().concl(), super::mul_comm().concl());
        assert_eq!(cov::mul_one_cov().concl(), super::mul_one().concl());
        assert_eq!(cov::distrib_cov().concl(), super::distrib().concl());
        assert_eq!(cov::mul_assoc_cov().concl(), super::mul_assoc().concl());
        // Order theory ported to `nat.cov`.
        assert_eq!(
            cov::le_succ_self_cov().concl(),
            super::le_succ_self().concl()
        );
        assert_eq!(cov::le_total_cov().concl(), super::le_total().concl());
        assert_eq!(
            cov::lt_iff_succ_le_cov().concl(),
            super::lt_iff_succ_le().concl()
        );
        assert_eq!(cov::le_add_r_cov().concl(), super::le_add_r().concl());
        assert_eq!(
            cov::le_zero_iff_cov().concl(),
            super::le_zero_iff().unwrap().concl()
        );
        assert_eq!(cov::le_antisym_cov().concl(), super::le_antisym().concl());
        assert_eq!(cov::le_add_sub_cov().concl(), super::le_add_sub().concl());
        assert_eq!(cov::le_trans_cov().concl(), super::le_trans().concl());
        assert_eq!(cov::lt_imp_le_cov().concl(), super::lt_imp_le().concl());
        assert_eq!(cov::lt_trans_cov().concl(), super::lt_trans().concl());
        assert_eq!(
            cov::le_add_cancel_r_cov().concl(),
            super::le_add_cancel_r().concl()
        );
        assert_eq!(
            cov::lt_add_mono_r_cov().concl(),
            super::lt_add_mono_r().concl()
        );
        assert_eq!(
            cov::le_iff_lt_or_eq_cov().concl(),
            super::le_iff_lt_or_eq().concl()
        );
        assert_eq!(
            cov::lt_trichotomy_cov().concl(),
            super::lt_trichotomy().concl()
        );
        assert_eq!(cov::add_lt_add_cov().concl(), super::add_lt_add().concl());
        assert_eq!(cov::lt_cross_cov().concl(), super::lt_cross().concl());
        assert_eq!(cov::le_cross_cov().concl(), super::le_cross().concl());
        // Exponentiation / shift ported to `nat.cov`.
        assert_eq!(cov::pow_add_cov().concl(), super::pow_add().concl());
        assert_eq!(
            cov::shl_eq_mul_pow_cov().concl(),
            super::shl_eq_mul_pow().concl()
        );
    }

    #[test]
    fn use_nat_qualifies_lemmas() {
        // `nat.cov` now defines its lemmas UNQUALIFIED (`add_comm`, …); a
        // downstream theory recovers the `nat.` namespace with `(#use nat)`,
        // so the lemma is reachable as `nat.add_comm`.
        use crate::script::{Env, run};
        let theory = run(
            r#"
            (#import core)
            (#open core)
            (#import nat)
            (#use nat)
            (#thm comm.echo
              (#fix (a nat) (b nat))
              (#concl (= (nat.add a b) (nat.add b a)))
              (#proof (all-elim b (all-elim a (nat.add.comm)))))
            "#,
            |name| match name {
                "core" => Some(Env::core()),
                "nat" => Some(cov::env()),
                _ => None,
            },
            |_| None,
        )
        .expect("`(#use nat)` should expose `nat.add.comm`");
        assert!(theory.thms[0].thm.hyps().is_empty());
    }
}
