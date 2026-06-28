//! # Gödel coding for the λ_iter deep embedding — the pairing layer
//!
//! The λ_iter deep embedding (`init/lambda_iter.rs`) reifies every syntactic
//! object — types, expressions, contexts, derivations — as a natural-number
//! *code*, so that "induction over the structure of …" becomes
//! course-of-values induction on `nat` (the substrate proved in
//! `lambda_iter.cov` / `cv_recursion.rs`). The bridge from *structural*
//! recursion to recursion on `<` is an injective **pairing**
//! `⟨·,·⟩ : nat → nat → nat` whose projections land *strictly below* the pair —
//! so a child node's code is `< ` its parent's, exactly the decrease a
//! course-of-values definition of `WfTyCode` / `Typed` / `El` consumes.
//!
//! ## The pairing
//!
//! ```text
//!     pair a b  ≜  2^a · (2·b + 1)        (here written 2^a · S(b + b))
//! ```
//!
//! the classic 2-adic bijection `nat × nat → nat⁺`. It is the lightest pairing
//! to *verify*: because `2^a ≥ 1` and `2b+1 ≥ 1`, the product is `≥ 1` (never
//! `0`, so `0` is cleanly "not a code") and **strictly dominates both
//! components** for all `a, b`:
//!
//! * [`pair_pos`]      `⊢ ∀a b. 0 < pair a b`           (and [`pair_ne_zero`])
//! * [`pair_left_lt`]  `⊢ ∀a b. a < pair a b`           (`a < 2^a ≤ pair`)
//! * [`pair_right_lt`] `⊢ ∀a b. b < pair a b`           (`b < 2b+1 ≤ pair`)
//!
//! `pair` is a genuine shell-level [`TermSpec`] (`code.pair`), so downstream
//! proofs δ-unfold it like any `defs::*` constant.
//!
//! Authored in Rust (like `cv_recursion.rs`): the proofs reuse the `init::nat`
//! arithmetic library (`mul_pos`, `lt_add_pos`, `pow_succ`, `mul_succ_r`, the
//! order theory) directly, which is far less painful than re-deriving them
//! through the `.cov` surface.
//!
//! Deferred (see `init/SKELETONS.md`): the projections `π₁`/`π₂` + their
//! round-trip laws, injectivity, the constructor `tag` constants, and the
//! `WfTyCode`/`Typed`/`El` decoders these unlock.

use std::sync::LazyLock;

use covalence_core::defs::TermSpec;
use covalence_core::{Result, Term, Thm, Type, defs, subst};
use smol_str::SmolStr;

use crate::init::ext::{TermExt, ThmExt};
use crate::init::lambda_iter::{nat_lt_le_trans, nat_lt_pred, nat_zero_or_succ};
use crate::init::{eq, logic, nat};

// ============================================================================
// Term helpers
// ============================================================================

fn nat_ty() -> Type {
    Type::nat()
}
fn lit(n: u64) -> Term {
    Term::nat_lit(n)
}
fn nvar(s: &str) -> Term {
    Term::free(s, nat_ty())
}
fn succ(t: Term) -> Term {
    Term::app(defs::nat_succ(), t)
}
fn mul(a: Term, b: Term) -> Term {
    Term::app(Term::app(defs::nat_mul(), a), b)
}
fn add(a: Term, b: Term) -> Term {
    Term::app(Term::app(defs::nat_add(), a), b)
}
fn pow(a: Term, b: Term) -> Term {
    Term::app(Term::app(defs::nat_pow(), a), b)
}
fn lt(a: Term, b: Term) -> Term {
    Term::app(Term::app(defs::nat_lt(), a), b)
}
fn le(a: Term, b: Term) -> Term {
    Term::app(Term::app(defs::nat_le(), a), b)
}
/// `2^a` — the pairing's exponential factor.
fn pow2(a: Term) -> Term {
    pow(lit(2), a)
}

// ============================================================================
// Small numeric facts (decided by `reduce` on literals)
// ============================================================================

/// `⊢ x < y` for literals `x < y` — `reduce` folds `nat.lt` on literals to `T`.
fn lt_lit(x: u64, y: u64) -> Result<Thm> {
    lt(lit(x), lit(y)).reduce()?.eqt_elim()
}

/// `⊢ 0 < 2^0` — the shared base case (`2^0 → 1`, `0 < 1 → T`).
fn zero_lt_pow2_zero() -> Result<Thm> {
    lt(lit(0), pow2(lit(0))).reduce()?.eqt_elim()
}

// ============================================================================
// Ordinary `nat` induction (local copy of `nat::induct_on`, which is private)
// ============================================================================

/// Prove `⊢ ∀<ivar>. body` by `nat`-induction, where `motive = λ<ivar>. body`,
/// `base : ⊢ body[0]`, and `step : ⊢ body[n] ⟹ body[S n]` (`n` free).
fn induct_on(ivar: &str, motive: &Term, base: Thm, step: Thm) -> Result<Thm> {
    let n = nvar(ivar);
    let base = eq::beta_expand(motive, lit(0), base)?; // ⊢ motive 0
    let pn = Term::app(motive.clone(), n.clone());
    let body_n = eq::beta_reduce(Thm::assume(pn.clone())?)?; // {motive n} ⊢ body[n]
    let body_sn = step.imp_elim(body_n)?; //                   {motive n} ⊢ body[S n]
    let p_sn = eq::beta_expand(motive, succ(n.clone()), body_sn)?; // {motive n} ⊢ motive (S n)
    let step = p_sn.imp_intro(&pn)?; //                          ⊢ motive n ⟹ motive (S n)
    eq::beta_nf_concl(Thm::nat_induct(base, step)?)
}

// ============================================================================
// Supporting order lemmas
// ============================================================================

/// `⊢ ∀a b c. a ≤ b ⟹ b < c ⟹ a < c` — the `≤`/`<` mixed transitivity the
/// `nat` order theory leaves out (it has `lt_le_trans`, not this side).
fn le_lt_trans_thm() -> Result<Thm> {
    let (a, b, c) = (nvar("a"), nvar("b"), nvar("c"));
    let hab = Thm::assume(le(a.clone(), b.clone()))?; // a ≤ b
    let hbc = Thm::assume(lt(b.clone(), c.clone()))?; // b < c
    // b < c  ⟺  S b ≤ c
    let sb_le_c = nat::lt_iff_succ_le()
        .all_elim(b.clone())?
        .all_elim(c.clone())?
        .eq_mp(hbc)?; // S b ≤ c
    // a ≤ b  ⟺  S a ≤ S b
    let sa_le_sb = nat::le_succ_succ()
        .all_elim(a.clone())?
        .all_elim(b.clone())?
        .sym()?
        .eq_mp(hab)?; // S a ≤ S b
    let sa_le_c = nat::le_trans()
        .all_elim(succ(a.clone()))?
        .all_elim(succ(b.clone()))?
        .all_elim(c.clone())?
        .imp_elim(sa_le_sb)?
        .imp_elim(sb_le_c)?; // S a ≤ c
    let a_lt_c = nat::lt_iff_succ_le()
        .all_elim(a.clone())?
        .all_elim(c.clone())?
        .sym()?
        .eq_mp(sa_le_c)?; // a < c
    a_lt_c
        .imp_intro(&lt(b.clone(), c.clone()))?
        .imp_intro(&le(a.clone(), b.clone()))?
        .all_intro("c", nat_ty())?
        .all_intro("b", nat_ty())?
        .all_intro("a", nat_ty())
}

/// `⊢ ∀a. 0 < 2^a` — every power of two is positive (`mul_pos` on the step).
pub fn pos_pow2() -> Result<Thm> {
    let a = nvar("a");
    let body = lt(lit(0), pow2(a.clone()));
    let motive = Term::abs(nat_ty(), subst::close(&body, "a"));

    // base: 0 < 2^0  (reduce decides it: 2^0 → 1, 0 < 1 → T).
    let base = zero_lt_pow2_zero()?;

    // step: (0 < 2^a) ⟹ (0 < 2^(S a)).
    let step = {
        let ih = Thm::assume(lt(lit(0), pow2(a.clone())))?; // 0 < 2^a
        let pow_s = nat::pow_succ().all_elim(lit(2))?.all_elim(a.clone())?; // 2^(S a) = 2·2^a
        let pos = nat::mul_pos()
            .all_elim(lit(2))?
            .all_elim(pow2(a.clone()))?
            .imp_elim(lt_lit(0, 2)?)?
            .imp_elim(ih)?; // 0 < 2·2^a
        pos.rewrite(&pow_s.sym()?)? // 0 < 2^(S a)
            .imp_intro(&lt(lit(0), pow2(a.clone())))?
    };
    induct_on("a", &motive, base, step)
}

/// `⊢ ∀a. a < 2^a` — left domination's engine.
pub fn lt_pow2_self() -> Result<Thm> {
    let a = nvar("a");
    let body = lt(a.clone(), pow2(a.clone()));
    let motive = Term::abs(nat_ty(), subst::close(&body, "a"));

    // base: 0 < 2^0.
    let base = zero_lt_pow2_zero()?;

    // step: (a < 2^a) ⟹ (S a < 2^(S a)).
    let step = {
        let ih = Thm::assume(lt(a.clone(), pow2(a.clone())))?; // a < 2^a
        // S a ≤ 2^a
        let sa_le = nat::lt_iff_succ_le()
            .all_elim(a.clone())?
            .all_elim(pow2(a.clone()))?
            .eq_mp(ih)?; // S a ≤ 2^a
        // 2^a < 2·2^a   (from 1 < 2, 0 < 2^a, lt_mul_mono_r, then 1·2^a = 2^a)
        let mono = nat::lt_mul_mono_r()
            .all_elim(lit(1))?
            .all_elim(lit(2))?
            .all_elim(pow2(a.clone()))?
            .imp_elim(lt_lit(1, 2)?)?
            .imp_elim(pos_pow2()?.all_elim(a.clone())?)?; // 1·2^a < 2·2^a
        // 1·2^a = 2^a  (1·x = x·1 = x)
        let one_mul = nat::mul_comm()
            .all_elim(lit(1))?
            .all_elim(pow2(a.clone()))?
            .trans(nat::mul_one().all_elim(pow2(a.clone()))?)?; // 1·2^a = 2^a
        let dbl = mono.rewrite(&one_mul)?; // 2^a < 2·2^a
        // S a ≤ 2^a < 2·2^a  ⟹  S a < 2·2^a
        let chain = le_lt_trans_thm()?
            .all_elim(succ(a.clone()))?
            .all_elim(pow2(a.clone()))?
            .all_elim(mul(lit(2), pow2(a.clone())))?
            .imp_elim(sa_le)?
            .imp_elim(dbl)?; // S a < 2·2^a
        let pow_s = nat::pow_succ().all_elim(lit(2))?.all_elim(a.clone())?; // 2^(S a) = 2·2^a
        chain
            .rewrite(&pow_s.sym()?)? // S a < 2^(S a)
            .imp_intro(&lt(a.clone(), pow2(a.clone())))?
    };
    induct_on("a", &motive, base, step)
}

// ============================================================================
// `code.pair : nat → nat → nat`  ≜  λa b. 2^a · S(b + b)
// ============================================================================

fn pair_body() -> Term {
    let (a, b) = (nvar("a"), nvar("b"));
    let body = mul(pow2(a.clone()), succ(add(b.clone(), b.clone()))); // 2^a · S(b+b)
    let lam_b = Term::abs(nat_ty(), subst::close(&body, "b")); // λb. …
    Term::abs(nat_ty(), subst::close(&lam_b, "a")) // λa b. …
}

/// `code.pair : nat → nat → nat` ≡ `λa b. 2^a · (2·b + 1)`.
pub fn pair_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let body = pair_body();
        let ty = body
            .type_of()
            .expect("code.pair body must type-check to nat → nat → nat");
        TermSpec::new(SmolStr::new_static("code.pair"), Some(ty), Some(body))
    });
    LAZY.clone()
}

/// `code.pair`.
pub fn pair_const() -> Term {
    Term::term_spec(pair_spec(), Vec::new())
}

/// `code.pair a b`.
pub fn pair(a: Term, b: Term) -> Term {
    Term::app(Term::app(pair_const(), a), b)
}

/// `code.pair a b` (internal alias for the proofs below).
fn pair_app(a: Term, b: Term) -> Term {
    pair(a, b)
}

/// `⊢ code.pair a b = 2^a · S(b + b)` — δ-unfold + β.
fn pair_unfold(a: &Term, b: &Term) -> Result<Thm> {
    Term::app(Term::app(pair_const(), a.clone()), b.clone())
        .delta_all(pair_spec().symbol())?
        .rhs_conv(|t| Ok(eq::beta_nf(t.clone())))
}

/// `⊢ ∀a b. 0 < code.pair a b` — the product of two positives is positive.
pub fn pair_pos() -> Result<Thm> {
    let (a, b) = (nvar("a"), nvar("b"));
    let unf = pair_unfold(&a, &b)?; // pair a b = 2^a · S(b+b)
    let pos = nat::mul_pos()
        .all_elim(pow2(a.clone()))?
        .all_elim(succ(add(b.clone(), b.clone())))?
        .imp_elim(pos_pow2()?.all_elim(a.clone())?)? // 0 < 2^a
        .imp_elim(nat::zero_lt_succ().all_elim(add(b.clone(), b.clone()))?)?; // 0 < S(b+b)
    pos.rewrite(&unf.sym()?)? // 0 < pair a b
        .all_intro("b", nat_ty())?
        .all_intro("a", nat_ty())
}

/// `⊢ ∀a b. ¬(code.pair a b = 0)` — `0` is never a code.
pub fn pair_ne_zero() -> Result<Thm> {
    let (a, b) = (nvar("a"), nvar("b"));
    let pos = pair_pos()?.all_elim(a.clone())?.all_elim(b.clone())?; // 0 < pair a b
    let heq = pair_app(a.clone(), b.clone()).equals(lit(0))?; // pair a b = 0
    let lt00 = pos.rewrite(&Thm::assume(heq.clone())?)?; // {pair=0} ⊢ 0 < 0
    nat::lt_irrefl()
        .all_elim(lit(0))?
        .not_elim(lt00)? // {pair=0} ⊢ F
        .imp_intro(&heq)? // ⊢ (pair=0) ⟹ F
        .not_intro()? // ⊢ ¬(pair=0)
        .all_intro("b", nat_ty())?
        .all_intro("a", nat_ty())
}

/// `⊢ ∀a b. a < code.pair a b` — left domination (`a < 2^a ≤ pair`).
pub fn pair_left_lt() -> Result<Thm> {
    let (a, b) = (nvar("a"), nvar("b"));
    let unf = pair_unfold(&a, &b)?; // pair = 2^a · S(b+b)
    // 2^a · S(b+b) = 2^a + 2^a·(b+b)
    let msr = nat::mul_succ_r()
        .all_elim(pow2(a.clone()))?
        .all_elim(add(b.clone(), b.clone()))?;
    let pair_eq = unf.trans(msr)?; // pair = 2^a + 2^a·(b+b)
    // 2^a ≤ 2^a + 2^a·(b+b) = pair
    let le_pair = nat::le_add_r()
        .all_elim(pow2(a.clone()))?
        .all_elim(mul(pow2(a.clone()), add(b.clone(), b.clone())))?
        .rewrite(&pair_eq.sym()?)?; // 2^a ≤ pair
    let a_lt = lt_pow2_self()?.all_elim(a.clone())?; // a < 2^a
    nat_lt_le_trans()
        .all_elim(a.clone())?
        .all_elim(pow2(a.clone()))?
        .all_elim(pair_app(a.clone(), b.clone()))?
        .imp_elim(a_lt)?
        .imp_elim(le_pair)? // a < pair
        .all_intro("b", nat_ty())?
        .all_intro("a", nat_ty())
}

/// `⊢ ∀a b. b < code.pair a b` — right domination (`b < S(b+b) ≤ pair`).
pub fn pair_right_lt() -> Result<Thm> {
    let (a, b) = (nvar("a"), nvar("b"));
    let unf = pair_unfold(&a, &b)?; // pair = 2^a · S(b+b)

    // b < S(b+b):  b ≤ b+b  ⟹  S b ≤ S(b+b)  ⟹  b < S(b+b).
    let b_le = nat::le_add_r().all_elim(b.clone())?.all_elim(b.clone())?; // b ≤ b + b
    let sb_le = nat::le_succ_succ()
        .all_elim(b.clone())?
        .all_elim(add(b.clone(), b.clone()))?
        .sym()?
        .eq_mp(b_le)?; // S b ≤ S(b+b)
    let b_lt_sbb = nat::lt_iff_succ_le()
        .all_elim(b.clone())?
        .all_elim(succ(add(b.clone(), b.clone())))?
        .sym()?
        .eq_mp(sb_le)?; // b < S(b+b)

    // S(b+b) ≤ pair:  pick k with 2^a = S k (0 < 2^a), then
    // pair = S k · S(b+b) = S(b+b) + k·S(b+b) ≥ S(b+b).
    let pos_pa = pos_pow2()?.all_elim(a.clone())?; // 0 < 2^a
    let exk = nat_lt_pred()
        .all_elim(lit(0))?
        .all_elim(pow2(a.clone()))?
        .imp_elim(pos_pa)?; // ∃k. 2^a = S k
    let goal = le(
        succ(add(b.clone(), b.clone())),
        pair_app(a.clone(), b.clone()),
    ); // S(b+b) ≤ pair
    let sbb = succ(add(b.clone(), b.clone()));
    let elim_step = {
        let k = nvar("k");
        // exists_elim hands us the redex `pred k`; β-reduce to `2^a = S k`.
        let pred = exk.concl().as_app().expect("∃ is an application").1.clone();
        let hk_redex = Term::app(pred, k.clone());
        let hk = eq::beta_reduce(Thm::assume(hk_redex.clone())?)?; // ⊢ 2^a = S k
        // S k · S(b+b) = S(b+b) + k·S(b+b)
        let ms = nat::mul_step().all_elim(k.clone())?.all_elim(sbb.clone())?; // S k · S(b+b) = S(b+b) + k·S(b+b)
        // pair = 2^a · S(b+b) = S k · S(b+b) = S(b+b) + k·S(b+b)
        let pair_eq = unf
            .clone()
            .rewrite(&hk)? // pair = S k · S(b+b)
            .trans(ms)?; // pair = S(b+b) + k·S(b+b)
        nat::le_add_r()
            .all_elim(sbb.clone())?
            .all_elim(mul(k.clone(), sbb.clone()))?
            .rewrite(&pair_eq.sym()?)? // S(b+b) ≤ pair
            .imp_intro(&hk_redex)?
            .all_intro("k", nat_ty())?
    };
    let sbb_le_pair = logic::exists_elim(exk, goal, elim_step)?; // S(b+b) ≤ pair

    // b < S(b+b) ≤ pair  ⟹  b < pair.
    nat_lt_le_trans()
        .all_elim(b.clone())?
        .all_elim(sbb.clone())?
        .all_elim(pair_app(a.clone(), b.clone()))?
        .imp_elim(b_lt_sbb)?
        .imp_elim(sbb_le_pair)? // b < pair
        .all_intro("b", nat_ty())?
        .all_intro("a", nat_ty())
}

// ============================================================================
// Injectivity of `code.pair` — the 2-adic argument
//
// `pair a b = 2^a · (2b+1)`. The odd factor `2b+1` and the power `2^a` are
// recovered uniquely: the exponent is the 2-adic valuation, the odd part fixes
// `b`. The crux is `parity` (no number is both even and odd); given it, a single
// induction on `a` peels one factor of 2 per step.
// ============================================================================

/// `⊢ ∀x. 2·x = x + x`.
fn two_double() -> Result<Thm> {
    let x = nvar("x");
    let two_s1 = succ(lit(1)).reduce()?.sym()?; // 2 = S 1
    let to_s1 = two_s1.cong_arg(defs::nat_mul())?.cong_fn(x.clone())?; // 2·x = (S 1)·x
    let ms = nat::mul_step().all_elim(lit(1))?.all_elim(x.clone())?; // (S 1)·x = x + 1·x
    let one_mul = nat::mul_comm()
        .all_elim(lit(1))?
        .all_elim(x.clone())?
        .trans(nat::mul_one().all_elim(x.clone())?)?; // 1·x = x·1 = x
    to_s1.trans(ms)?.rewrite(&one_mul)?.all_intro("x", nat_ty())
}

/// `⊢ 2^0 · x = x`.
fn pow_zero_mul(x: &Term) -> Result<Thm> {
    let pz = nat::pow_zero().all_elim(lit(2))?; // 2^0 = 1
    let to_one = pz.cong_arg(defs::nat_mul())?.cong_fn(x.clone())?; // 2^0·x = 1·x
    let one_mul = nat::mul_comm()
        .all_elim(lit(1))?
        .all_elim(x.clone())?
        .trans(nat::mul_one().all_elim(x.clone())?)?; // 1·x = x
    to_one.trans(one_mul)
}

/// `⊢ 2^(S c) · m = (2^c · m) + (2^c · m)` — a successor power-of-two multiple
/// is "even" (twice the predecessor multiple).
fn pow_succ_double(c: &Term, m: &Term) -> Result<Thm> {
    let ps = nat::pow_succ().all_elim(lit(2))?.all_elim(c.clone())?; // 2^(S c) = 2·2^c
    let to = ps.cong_arg(defs::nat_mul())?.cong_fn(m.clone())?; // 2^(S c)·m = (2·2^c)·m
    let assoc = nat::mul_assoc()
        .all_elim(lit(2))?
        .all_elim(pow2(c.clone()))?
        .all_elim(m.clone())?; // (2·2^c)·m = 2·(2^c·m)
    let dbl = two_double()?.all_elim(mul(pow2(c.clone()), m.clone()))?; // 2·(2^c·m) = (2^c·m)+(2^c·m)
    to.trans(assoc)?.trans(dbl)
}

/// `⊢ ∀b d. (b + b = d + d) ⟹ b = d` — doubling is injective.
fn double_inj() -> Result<Thm> {
    let (b, d) = (nvar("b"), nvar("d"));
    let h_term = add(b.clone(), b.clone()).equals(add(d.clone(), d.clone()))?; // b+b = d+d
    let h = Thm::assume(h_term.clone())?;
    let goal = b.clone().equals(d.clone())?;

    // From `x < y` derive ⊥ (so the goal) by collapsing `x+x < y+y` to `d+d < d+d`.
    let absurd = |lt_lo: Term, lt_hi: Term, sum_lo: Term, sum_hi: Term| -> Result<Thm> {
        let hlt = Thm::assume(lt(lt_lo.clone(), lt_hi.clone()))?;
        let sums_lt = nat::add_lt_add()
            .all_elim(lt_lo.clone())?
            .all_elim(lt_hi.clone())?
            .all_elim(lt_lo.clone())?
            .all_elim(lt_hi.clone())?
            .imp_elim(hlt.clone())?
            .imp_elim(hlt.clone())?; // sum_lo < sum_hi  (lo+lo < hi+hi)
        // rewrite the live sum (`b+b`) to `d+d` via `h`, landing `d+d < d+d`.
        let collapsed = sums_lt.rewrite(&h)?; // both summands become d+d
        let _ = (sum_lo, sum_hi);
        nat::lt_irrefl()
            .all_elim(add(d.clone(), d.clone()))?
            .not_elim(collapsed)?
            .false_elim(goal.clone())?
            .imp_intro(&lt(lt_lo, lt_hi))
    };

    let tri = nat::lt_trichotomy()
        .all_elim(b.clone())?
        .all_elim(d.clone())?; // b<d ∨ (b=d ∨ d<b)
    let case_eq = Thm::assume(goal.clone())?.imp_intro(&goal)?; // (b=d) ⟹ b=d
    let case_dlt = absurd(
        d.clone(),
        b.clone(),
        add(d.clone(), d.clone()),
        add(b.clone(), b.clone()),
    )?;
    let inner = Thm::assume(goal.clone().or(lt(d.clone(), b.clone()))?)?
        .or_elim(case_eq, case_dlt)?
        .imp_intro(&goal.clone().or(lt(d.clone(), b.clone()))?)?; // (b=d ∨ d<b) ⟹ b=d
    let case_blt = absurd(
        b.clone(),
        d.clone(),
        add(b.clone(), b.clone()),
        add(d.clone(), d.clone()),
    )?;
    tri.or_elim(case_blt, inner)?
        .imp_intro(&h_term)?
        .all_intro("d", nat_ty())?
        .all_intro("b", nat_ty())
}

/// `⊢ ∀x b. ¬(S(b + b) = x + x)` — no number is both odd and even. By induction
/// on `x` with a nested case on `b`.
pub(crate) fn parity() -> Result<Thm> {
    let (x, b) = (nvar("x"), nvar("b"));
    // motive Q(x) = ∀b. ¬(S(b+b) = x+x)
    let q_body = succ(add(b.clone(), b.clone()))
        .equals(add(x.clone(), x.clone()))?
        .not()?
        .forall("b", nat_ty())?;
    let motive = Term::abs(nat_ty(), subst::close(&q_body, "x"));

    // base Q(0): ∀b. ¬(S(b+b) = 0+0).
    let base = {
        let b = nvar("b");
        let zz = nat::add_zero().all_elim(lit(0))?; // 0+0 = 0
        let assumed = succ(add(b.clone(), b.clone())).equals(add(lit(0), lit(0)))?;
        let to_zero = Thm::assume(assumed.clone())?.rewrite(&zz)?; // S(b+b) = 0
        nat::cov::succ_ne_zero()
            .all_elim(add(b.clone(), b.clone()))?
            .not_elim(to_zero)? // F
            .imp_intro(&assumed)?
            .not_intro()?
            .all_intro("b", nat_ty())?
    };

    // step: body[x] ⟹ body[S x].
    let step = {
        let (x, b) = (nvar("x"), nvar("b"));
        let body_x = succ(add(b.clone(), b.clone()))
            .equals(add(x.clone(), x.clone()))?
            .not()?
            .forall("b", nat_ty())?; // ∀b. ¬(S(b+b)=x+x)  (the IH)
        let ih = Thm::assume(body_x.clone())?;

        // (S t)+(S t) = S(S(t+t))
        let sxsx = |t: &Term| -> Result<Thm> {
            nat::add_succ_r()
                .all_elim(succ(t.clone()))?
                .all_elim(t.clone())? // (S t) + S t = S((S t)+t)
                .trans(
                    nat::add_step()
                        .all_elim(t.clone())?
                        .all_elim(t.clone())? // (S t)+t = S(t+t)
                        .cong_arg(defs::nat_succ())?,
                ) // S((S t)+t) = S(S(t+t))
        };
        let sxsx_x = sxsx(&x)?; // (S x)+(S x) = S(S(x+x))

        let assumed =
            succ(add(b.clone(), b.clone())).equals(add(succ(x.clone()), succ(x.clone())))?; // S(b+b) = (S x)+(S x)
        let a2 = Thm::assume(assumed.clone())?.rewrite(&sxsx_x)?; // S(b+b) = S(S(x+x))

        let exb = nat_zero_or_succ().all_elim(b.clone())?; // b=0 ∨ ∃k. b=S k
        let f_goal = Term::bool_lit(false);

        // case b = 0 : S 0 = S(S(x+x)) ⟹ 0 = S(x+x), absurd.
        let case_zero = {
            let hb_term = b.clone().equals(lit(0))?;
            let a2_0 = a2
                .clone()
                .rewrite(&Thm::assume(hb_term.clone())?)? // S(0+0) = S(S(x+x))
                .rewrite(&nat::add_zero().all_elim(lit(0))?)?; // S 0 = S(S(x+x))
            let inj = nat::succ_inj()
                .all_elim(lit(0))?
                .all_elim(succ(add(x.clone(), x.clone())))?
                .imp_elim(a2_0)?; // 0 = S(x+x)
            nat::cov::succ_ne_zero()
                .all_elim(add(x.clone(), x.clone()))?
                .not_elim(inj.sym()?)? // F
                .imp_intro(&hb_term)?
        };

        // case ∃b'. b = S b' : descend to the IH at b'.
        let ex_term = exb.concl().as_app().expect("∃ disjunct").1.clone(); // ∃k. b=S k
        let case_succ = {
            let bp = nvar("b'");
            let pred = ex_term.as_app().expect("∃ predicate").1.clone();
            let hbp_redex = Term::app(pred, bp.clone());
            let hbp = eq::beta_reduce(Thm::assume(hbp_redex.clone())?)?; // b = S b'
            let a2_s = a2
                .clone()
                .rewrite(&hbp)? // S((S b')+(S b')) = S(S(x+x))
                .rewrite(&sxsx(&bp)?)?; // S(S(S(b'+b'))) = S(S(x+x))
            let inj1 = nat::succ_inj()
                .all_elim(succ(succ(add(bp.clone(), bp.clone()))))?
                .all_elim(succ(add(x.clone(), x.clone())))?
                .imp_elim(a2_s)?; // S(S(b'+b')) = S(x+x)
            let inj2 = nat::succ_inj()
                .all_elim(succ(add(bp.clone(), bp.clone())))?
                .all_elim(add(x.clone(), x.clone()))?
                .imp_elim(inj1)?; // S(b'+b') = x+x
            ih.clone()
                .all_elim(bp.clone())?
                .not_elim(inj2)? // F
                .imp_intro(&hbp_redex)?
                .all_intro("b'", nat_ty())?
        };
        let right = logic::exists_elim(Thm::assume(ex_term.clone())?, f_goal, case_succ)?
            .imp_intro(&ex_term)?; // (∃b'. b=S b') ⟹ F

        exb.or_elim(case_zero, right)? // F
            .imp_intro(&assumed)?
            .not_intro()? // ¬(S(b+b) = (S x)+(S x))
            .all_intro("b", nat_ty())? // body[S x]
            .imp_intro(&body_x)? // body[x] ⟹ body[S x]
    };

    induct_on("x", &motive, base, step)
}

/// `S(t + t)` — the odd factor `2t + 1`.
fn odd(t: &Term) -> Term {
    succ(add(t.clone(), t.clone()))
}

/// `⊢ ∀a c b d. (2^a·(2b+1) = 2^c·(2d+1)) ⟹ (a = c ∧ b = d)` — the core of
/// injectivity (over the unfolded pairing). Induction on `a`: each step peels
/// one factor of 2 (`double_inj`); the odd/even clashes close by `parity`.
fn inj_core() -> Result<Thm> {
    let (a, c, b, d) = (nvar("a"), nvar("c"), nvar("b"), nvar("d"));
    // body[a] = ∀c b d. (2^a·odd(b) = 2^c·odd(d)) ⟹ (a=c ∧ b=d)
    let body_at = |a: &Term| -> Result<Term> {
        mul(pow2(a.clone()), odd(&b))
            .equals(mul(pow2(c.clone()), odd(&d)))?
            .imp(
                a.clone()
                    .equals(c.clone())?
                    .and(b.clone().equals(d.clone())?)?,
            )?
            .forall("d", nat_ty())?
            .forall("b", nat_ty())?
            .forall("c", nat_ty())
    };
    let motive = Term::abs(nat_ty(), subst::close(&body_at(&a)?, "a"));

    // Shared: the `c = S c'` even-RHS clash (LHS = `odd(b)` or `Z+Z`).
    // Build the goal/closers fresh per case to keep hypotheses clean.

    // ---- base: a = 0 ----
    let base = {
        let (c, b, d) = (nvar("c"), nvar("b"), nvar("d"));
        let goal = lit(0)
            .equals(c.clone())?
            .and(b.clone().equals(d.clone())?)?;
        let e_term = mul(pow2(lit(0)), odd(&b)).equals(mul(pow2(c.clone()), odd(&d)))?;
        // S(b+b) = 2^c·odd(d)   (LHS 2^0·odd(b) → odd(b))
        let h2 = Thm::assume(e_term.clone())?.rewrite(&pow_zero_mul(&odd(&b))?)?;
        let exc = nat_zero_or_succ().all_elim(c.clone())?;
        // c = 0
        let case_zero = {
            let hc = c.clone().equals(lit(0))?;
            let eq = h2
                .clone()
                .rewrite(&Thm::assume(hc.clone())?)? // odd(b) = 2^0·odd(d)
                .rewrite(&pow_zero_mul(&odd(&d))?)?; // S(b+b) = S(d+d)
            let bd = double_inj()?
                .all_elim(b.clone())?
                .all_elim(d.clone())?
                .imp_elim(
                    nat::succ_inj()
                        .all_elim(add(b.clone(), b.clone()))?
                        .all_elim(add(d.clone(), d.clone()))?
                        .imp_elim(eq)?,
                )?; // b = d
            Thm::assume(hc.clone())?
                .sym()? // 0 = c
                .and_intro(bd)?
                .imp_intro(&hc)?
        };
        // c = S c'
        let exc_t = exc.concl().as_app().expect("∃").1.clone();
        let case_succ = {
            let cp = nvar("c'");
            let pred = exc_t.as_app().expect("∃ pred").1.clone();
            let hcp_redex = Term::app(pred, cp.clone());
            let hcp = eq::beta_reduce(Thm::assume(hcp_redex.clone())?)?; // c = S c'
            let even = h2
                .clone()
                .rewrite(&hcp)? // odd(b) = 2^(S c')·odd(d)
                .rewrite(&pow_succ_double(&cp, &odd(&d))?)?; // S(b+b) = Y+Y
            let y = mul(pow2(cp.clone()), odd(&d));
            parity()?
                .all_elim(y)?
                .all_elim(b.clone())?
                .not_elim(even)? // F
                .false_elim(goal.clone())?
                .imp_intro(&hcp_redex)?
                .all_intro("c'", nat_ty())?
        };
        let right = logic::exists_elim(Thm::assume(exc_t.clone())?, goal.clone(), case_succ)?
            .imp_intro(&exc_t)?;
        exc.or_elim(case_zero, right)?
            .imp_intro(&e_term)?
            .all_intro("d", nat_ty())?
            .all_intro("b", nat_ty())?
            .all_intro("c", nat_ty())?
    };

    // ---- step: body[a'] ⟹ body[S a'] ----
    let step = {
        let (ap, c, b, d) = (nvar("a"), nvar("c"), nvar("b"), nvar("d"));
        let ih = Thm::assume(body_at(&ap)?)?;
        let goal = succ(ap.clone())
            .equals(c.clone())?
            .and(b.clone().equals(d.clone())?)?;
        let e_term = mul(pow2(succ(ap.clone())), odd(&b)).equals(mul(pow2(c.clone()), odd(&d)))?;
        // Z+Z = 2^c·odd(d)   (Z = 2^a'·odd(b))
        let z = mul(pow2(ap.clone()), odd(&b));
        let e2 = Thm::assume(e_term.clone())?.rewrite(&pow_succ_double(&ap, &odd(&b))?)?;
        let exc = nat_zero_or_succ().all_elim(c.clone())?;
        // c = 0 : RHS odd, LHS even — clash.
        let case_zero = {
            let hc = c.clone().equals(lit(0))?;
            let odd_rhs = e2
                .clone()
                .rewrite(&Thm::assume(hc.clone())?)? // Z+Z = 2^0·odd(d)
                .rewrite(&pow_zero_mul(&odd(&d))?)?; // Z+Z = S(d+d)
            parity()?
                .all_elim(z.clone())?
                .all_elim(d.clone())?
                .not_elim(odd_rhs.sym()?)? // F  (¬(S(d+d) = Z+Z))
                .false_elim(goal.clone())?
                .imp_intro(&hc)?
        };
        // c = S c'
        let exc_t = exc.concl().as_app().expect("∃").1.clone();
        let case_succ = {
            let cp = nvar("c'");
            let pred = exc_t.as_app().expect("∃ pred").1.clone();
            let hcp_redex = Term::app(pred, cp.clone());
            let hcp = eq::beta_reduce(Thm::assume(hcp_redex.clone())?)?; // c = S c'
            let w = mul(pow2(cp.clone()), odd(&d));
            // Z+Z = W+W
            let zwzw = e2
                .clone()
                .rewrite(&hcp)? // Z+Z = 2^(S c')·odd(d)
                .rewrite(&pow_succ_double(&cp, &odd(&d))?)?; // Z+Z = W+W
            let zw = double_inj()?
                .all_elim(z.clone())?
                .all_elim(w.clone())?
                .imp_elim(zwzw)?; // Z = W  (2^a'·odd(b) = 2^c'·odd(d))
            let ih_res = ih
                .clone()
                .all_elim(cp.clone())?
                .all_elim(b.clone())?
                .all_elim(d.clone())?
                .imp_elim(zw)?; // a'=c' ∧ b=d
            // S a' = c  from a'=c' and c=S c'.
            let sa_eq_c = ih_res
                .clone()
                .and_elim_l()? // a' = c'
                .cong_arg(defs::nat_succ())? // S a' = S c'
                .trans(hcp.sym()?)?; // S a' = c
            sa_eq_c
                .and_intro(ih_res.and_elim_r()?)? // (S a'=c) ∧ (b=d)
                .imp_intro(&hcp_redex)?
                .all_intro("c'", nat_ty())?
        };
        let right = logic::exists_elim(Thm::assume(exc_t.clone())?, goal.clone(), case_succ)?
            .imp_intro(&exc_t)?;
        exc.or_elim(case_zero, right)?
            .imp_intro(&e_term)?
            .all_intro("d", nat_ty())?
            .all_intro("b", nat_ty())?
            .all_intro("c", nat_ty())?
            .imp_intro(&body_at(&ap)?)?
    };

    induct_on("a", &motive, base, step)
}

/// `⊢ ∀a b c d. (code.pair a b = code.pair c d) ⟹ (a = c ∧ b = d)` — the pairing
/// is injective. Unfolds both sides and applies [`inj_core`].
pub fn pair_inj() -> Result<Thm> {
    let (a, b, c, d) = (nvar("a"), nvar("b"), nvar("c"), nvar("d"));
    let h_term = pair_app(a.clone(), b.clone()).equals(pair_app(c.clone(), d.clone()))?;
    let core_eq = pair_unfold(&a, &b)?
        .sym()? // 2^a·odd(b) = pair a b
        .trans(Thm::assume(h_term.clone())?)? // = pair c d
        .trans(pair_unfold(&c, &d)?)?; // = 2^c·odd(d)
    inj_core()?
        .all_elim(a.clone())?
        .all_elim(c.clone())?
        .all_elim(b.clone())?
        .all_elim(d.clone())?
        .imp_elim(core_eq)? // a=c ∧ b=d
        .imp_intro(&h_term)?
        .all_intro("d", nat_ty())?
        .all_intro("c", nat_ty())?
        .all_intro("b", nat_ty())?
        .all_intro("a", nat_ty())
}

/// `⊢ ∀a b c d. (code.pair a b = code.pair c d) ⟹ a = c`.
pub fn pair_inj_l() -> Result<Thm> {
    pair_inj_proj(true)
}
/// `⊢ ∀a b c d. (code.pair a b = code.pair c d) ⟹ b = d`.
pub fn pair_inj_r() -> Result<Thm> {
    pair_inj_proj(false)
}

fn pair_inj_proj(left: bool) -> Result<Thm> {
    let (a, b, c, d) = (nvar("a"), nvar("b"), nvar("c"), nvar("d"));
    let h_term = pair_app(a.clone(), b.clone()).equals(pair_app(c.clone(), d.clone()))?;
    let both = pair_inj()?
        .all_elim(a.clone())?
        .all_elim(b.clone())?
        .all_elim(c.clone())?
        .all_elim(d.clone())?
        .imp_elim(Thm::assume(h_term.clone())?)?; // a=c ∧ b=d
    let proj = if left {
        both.and_elim_l()?
    } else {
        both.and_elim_r()?
    };
    proj.imp_intro(&h_term)?
        .all_intro("d", nat_ty())?
        .all_intro("c", nat_ty())?
        .all_intro("b", nat_ty())?
        .all_intro("a", nat_ty())
}

// ============================================================================
// Pairing recurrences for the projection round-trips (`code_proj.rs`)
// ============================================================================

/// `⊢ ∀b. code.pair 0 b = S(b + b)` — the projection recurrence's base
/// (`2^0 = 1`, so the pair is just the odd factor, which is odd).
pub(crate) fn pair_zero_eq() -> Result<Thm> {
    let b = nvar("b");
    pair_unfold(&lit(0), &b)? // pair 0 b = 2^0·S(b+b)
        .trans(pow_zero_mul(&odd(&b))?)? // = S(b+b)
        .all_intro("b", nat_ty())
}

/// `⊢ ∀a b. code.pair (S a) b = 2·(code.pair a b)` — the projection recurrence's
/// step (`2^(S a) = 2·2^a`, so the pair is even).
pub(crate) fn pair_succ_eq() -> Result<Thm> {
    let (a, b) = (nvar("a"), nvar("b"));
    let unf_sa = pair_unfold(&succ(a.clone()), &b)?; // pair (S a) b = 2^(S a)·odd(b)
    let ps = nat::pow_succ().all_elim(lit(2))?.all_elim(a.clone())?; // 2^(S a) = 2·2^a
    let to = ps.cong_arg(defs::nat_mul())?.cong_fn(odd(&b))?; // 2^(S a)·odd(b) = (2·2^a)·odd(b)
    let assoc = nat::mul_assoc()
        .all_elim(lit(2))?
        .all_elim(pow2(a.clone()))?
        .all_elim(odd(&b))?; // (2·2^a)·odd(b) = 2·(2^a·odd(b))
    let cong = pair_unfold(&a, &b)?
        .sym()? // 2^a·odd(b) = pair a b
        .cong_arg(Term::app(defs::nat_mul(), lit(2)))?; // 2·(2^a·odd(b)) = 2·(pair a b)
    unf_sa
        .trans(to)?
        .trans(assoc)?
        .trans(cong)? // pair (S a) b = 2·(pair a b)
        .all_intro("b", nat_ty())?
        .all_intro("a", nat_ty())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Every pairing lemma replays to a closed (hypothesis-free) theorem.
    #[test]
    fn pairing_lemmas_are_closed() {
        for (name, thm) in [
            ("pos_pow2", pos_pow2()),
            ("lt_pow2_self", lt_pow2_self()),
            ("pair_pos", pair_pos()),
            ("pair_ne_zero", pair_ne_zero()),
            ("pair_left_lt", pair_left_lt()),
            ("pair_right_lt", pair_right_lt()),
            ("pair_zero_eq", pair_zero_eq()),
            ("pair_succ_eq", pair_succ_eq()),
        ] {
            let thm = thm.unwrap_or_else(|e| panic!("{name} failed to build: {e}"));
            assert!(
                thm.hyps().is_empty(),
                "{name} should be closed, got {:?}",
                thm.hyps()
            );
        }
    }

    /// The injectivity arithmetic helpers replay to closed theorems.
    #[test]
    fn injectivity_helpers_are_closed() {
        let x = nvar("x");
        for (name, thm) in [
            ("two_double", two_double()),
            ("double_inj", double_inj()),
            ("parity", parity()),
            ("pow_zero_mul", pow_zero_mul(&x)),
            ("pow_succ_double", pow_succ_double(&nvar("c"), &nvar("m"))),
            ("inj_core", inj_core()),
            ("pair_inj", pair_inj()),
            ("pair_inj_l", pair_inj_l()),
            ("pair_inj_r", pair_inj_r()),
        ] {
            let thm = thm.unwrap_or_else(|e| panic!("{name}: {e}"));
            assert!(thm.hyps().is_empty(), "{name} should be closed");
        }
    }

    /// `code.pair` δ-unfolds to its closed-form body, hypothesis-free.
    #[test]
    fn pair_unfolds() {
        let (a, b) = (nvar("a"), nvar("b"));
        let unf = pair_unfold(&a, &b).expect("unfold");
        assert!(unf.hyps().is_empty(), "unfold should be closed");
        // conclusion is `code.pair a b = 2^a · S(b+b)`.
        let rhs = mul(pow2(a.clone()), succ(add(b.clone(), b.clone())));
        assert!(
            format!("{}", unf.concl()).contains(&format!("{rhs}")),
            "unfold rhs mismatch: {}",
            unf.concl()
        );
    }
}
