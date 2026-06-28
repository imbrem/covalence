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
use crate::init::lambda_iter::{nat_lt_le_trans, nat_lt_pred};
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
        ] {
            let thm = thm.unwrap_or_else(|e| panic!("{name} failed to build: {e}"));
            assert!(
                thm.hyps().is_empty(),
                "{name} should be closed, got {:?}",
                thm.hyps()
            );
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
