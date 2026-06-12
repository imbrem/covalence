//! Peano proofs for `Type::nat()`.
//!
//! Provides bona-fide *proofs* of the classical Peano axioms, built
//! from more primitive kernel facts. Every proved theorem has empty
//! hypotheses (no `Thm::assume` audit trail).
//!
//! Surface form: each proof produces a Pure-meta-quantified theorem,
//! e.g.
//!
//! ```text
//! ⊢ ⋀m n:nat. Trueprop ((succ m = succ n) ⟹ (m = n))
//! ```
//!
//! rather than the fully-HOL-wrapped form
//! `⊢ Trueprop (∀m n:nat. ...)`. Both shapes carry the same content;
//! converting the outermost `⋀` to HOL `∀` requires
//! [`Thm::forall_reflection`] specialised at a lambda predicate, which
//! callers can do downstream when needed.

use std::sync::LazyLock;

use covalence_core::subst::close;
use covalence_core::{defs, Term, Thm, Type};
use covalence_types::Nat;

use crate::HolLightCtx;
use crate::bridge::{hol_eq_from_pure_eq, lift_imp_to_hol, pure_eq_from_hol_eq};

// ============================================================================
// Helpers
// ============================================================================

fn nat_ty() -> Type {
    Type::nat()
}

fn succ_fn() -> Term {
    defs::nat_succ()
}

fn succ(t: Term) -> Term {
    Term::app(succ_fn(), t)
}

fn pred_fn() -> Term {
    defs::nat_pred()
}

fn pred(t: Term) -> Term {
    Term::app(pred_fn(), t)
}

fn trueprop(p: Term, ctx: &HolLightCtx) -> Term {
    ctx.mk_trueprop(p).expect("trueprop: arg is bool-typed")
}

fn hol_eq(lhs: Term, rhs: Term, ctx: &HolLightCtx) -> Term {
    ctx.mk_eq(lhs, rhs).expect("hol_eq: same-typed args")
}

fn nat_lit(n: u32) -> Term {
    Term::nat_lit(Nat::from_inner(n.into()))
}

/// Given `Γ ⊢ Trueprop (¬p)`, return `Γ ⊢ Trueprop (p ⟹ F)`.
/// (Forward direction of `not_def`.)
#[allow(dead_code)]
fn unfold_not(thm: Thm, p: Term, ctx: &HolLightCtx) -> Thm {
    // not_def: ⋀p. Trueprop (¬p = (p ⟹ F))
    let not_def_at = Thm::not_def()
        .all_elim(p.clone())
        .expect("unfold_not: all_elim p");
    // : ⊢ Trueprop (¬p = (p ⟹ F))
    // Convert to Pure meta-eq: ¬p ≡ (p ⟹ F)
    let lhs = Term::app(ctx.not_op(), p.clone());
    let rhs = Term::app(Term::app(ctx.imp_op(), p), Term::bool_lit(false));
    let pure_eq = pure_eq_from_hol_eq(not_def_at, ctx.bool_type(), lhs.clone(), rhs.clone());
    // Wrap with Trueprop via cong_app:
    //   ⊢ Trueprop ≡ Trueprop, ⊢ ¬p ≡ (p ⟹ F)
    //   → ⊢ Trueprop (¬p) ≡ Trueprop (p ⟹ F)
    let trueprop_eq = Thm::refl(ctx.trueprop())
        .expect("unfold_not: refl trueprop")
        .cong_app(pure_eq)
        .expect("unfold_not: cong_app");
    trueprop_eq.eq_mp(thm).expect("unfold_not: eq_mp")
}

/// Given `Γ ⊢ Trueprop (p ⟹ F)`, return `Γ ⊢ Trueprop (¬p)`.
/// (Reverse direction of `not_def`.)
fn fold_not(thm: Thm, p: Term, ctx: &HolLightCtx) -> Thm {
    let not_def_at = Thm::not_def()
        .all_elim(p.clone())
        .expect("fold_not: all_elim p");
    let lhs = Term::app(ctx.not_op(), p.clone());
    let rhs = Term::app(Term::app(ctx.imp_op(), p), Term::bool_lit(false));
    let pure_eq = pure_eq_from_hol_eq(not_def_at, ctx.bool_type(), lhs.clone(), rhs.clone());
    let trueprop_eq = Thm::refl(ctx.trueprop())
        .expect("fold_not: refl trueprop")
        .cong_app(pure_eq)
        .expect("fold_not: cong_app");
    trueprop_eq
        .sym()
        .expect("fold_not: sym")
        .eq_mp(thm)
        .expect("fold_not: eq_mp")
}

// ============================================================================
// nat_zero_ne_one — base case for nat_zero_ne_succ
// ============================================================================

/// `⊢ Trueprop (¬(0 = 1))` — the canonical base-case distinctness
/// fact, proved by `Thm::reduce_prim` deciding `HolEq 0 1 = F` on
/// the closed literals. Cached process-wide; downstream proofs
/// like `prove_nat_zero_ne_succ` use it as the induction base.
pub fn nat_zero_ne_one() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(build_nat_zero_ne_one);
    AX.clone()
}

fn build_nat_zero_ne_one() -> Thm {
    let ctx = HolLightCtx::new();
    let bool_ty = ctx.bool_type();
    let zero_eq_one = hol_eq(nat_lit(0), nat_lit(1), &ctx);

    // 1. reduce_prim(HolEq 0 1) → ⊢ HolEq 0 1 ≡ F
    let eq_to_false = Thm::reduce_prim(zero_eq_one.clone())
        .expect("nat_zero_ne_one: reduce_prim");

    // 2. cong_app(refl Trueprop, eq_to_false) → ⊢ Trueprop (0=1) ≡ Trueprop F
    let trueprop_eq = Thm::refl(ctx.trueprop())
        .expect("nat_zero_ne_one: refl trueprop")
        .cong_app(eq_to_false)
        .expect("nat_zero_ne_one: cong_app");

    // 3. assume Trueprop (0=1)
    let antecedent = ctx
        .mk_trueprop(zero_eq_one.clone())
        .expect("nat_zero_ne_one: mk_trueprop");
    let assumed = Thm::assume(antecedent.clone()).expect("nat_zero_ne_one: assume");

    // 4. eq_mp → Γ ⊢ Trueprop F
    let derive_false = trueprop_eq
        .eq_mp(assumed)
        .expect("nat_zero_ne_one: eq_mp");

    // 5. imp_intro → ⊢ Trueprop (0=1) ⟹ Trueprop F
    let pure_imp = derive_false
        .imp_intro(&antecedent)
        .expect("nat_zero_ne_one: imp_intro");

    // 6. Lift to HOL imp: ⊢ Trueprop ((0=1) ⟹ F)
    let hol_imp_thm = lift_imp_to_hol(pure_imp, zero_eq_one.clone(), Term::bool_lit(false));

    // 7. Fold the (... ⟹ F) form back into ¬: ⊢ Trueprop (¬(0=1))
    let _ = bool_ty;
    fold_not(hol_imp_thm, zero_eq_one, &ctx)
}

// ============================================================================
// nat_zero_ne_succ
// ============================================================================

/// `⊢ ⋀n:nat. Trueprop (¬(0 = succ n))` — zero is never a successor.
///
/// Proved by [`Thm::nat_induction_pure`] with the predicate
/// `P n = ¬(0 = succ n)`:
/// - Base case `P 0 = ¬(0 = succ 0)`: reduces to `¬(0 = 1)` via
///   `Thm::reduce_prim` on `succ 0`, then to [`nat_zero_ne_one`].
/// - Step case: assume `¬(0 = succ n)`; suppose `0 = succ (succ n)`;
///   apply `pred` to both sides via `cong_app` + [`Thm::nat_pred_zero`]
///   + [`Thm::nat_pred_succ`] to derive `0 = succ n`; contradicts the
///   IH.
pub fn prove_nat_zero_ne_succ() -> Thm {
    let ctx = HolLightCtx::new();
    let nat = nat_ty();

    // P_lambda = λn:nat. ¬(0 = succ n)
    let n_in_p = Term::free("n", nat.clone());
    let p_body_free = ctx.mk_not(hol_eq(nat_lit(0), succ(n_in_p), &ctx));
    let p_lambda = Term::abs("n", nat.clone(), close(&p_body_free, "n"));

    // Helper to build `body[n_free]` for any free var name (used for
    // beta-reduced applications).
    let body_at = |n_term: Term| -> Term { ctx.mk_not(hol_eq(nat_lit(0), succ(n_term), &ctx)) };

    // ------ Base case: ⊢ Trueprop (P_lambda 0) ------
    let base = prove_base_case(&p_lambda, &body_at, &ctx);

    // ------ Step case: ⊢ ⋀n. Trueprop (P_lambda n) ⟹ Trueprop (P_lambda (succ n)) ------
    let step = prove_step_case(&p_lambda, &body_at, &ctx, &nat);

    // ------ Apply nat_induction_pure ------
    // ⊢ ⋀P. Trueprop (P 0) ⟹ (⋀n. Trueprop (P n) ⟹ Trueprop (P (succ n))) ⟹
    //              ⋀n. Trueprop (P n)
    let induction = Thm::nat_induction_pure()
        .all_elim(p_lambda.clone())
        .expect("zero_ne_succ: all_elim P");
    // mp base → (step_term ⟹ ⋀n. Trueprop (P_lambda n))
    let after_base = induction
        .imp_elim(base)
        .expect("zero_ne_succ: imp_elim base");
    // mp step → ⋀n. Trueprop (P_lambda n)
    let after_step = after_base
        .imp_elim(step)
        .expect("zero_ne_succ: imp_elim step");

    // Convert each `Trueprop (P_lambda n)` into `Trueprop (¬(0 = succ n))`
    // by beta-reducing inside the Pure ⋀.
    // after_step : ⋀n. Trueprop ((λn. body) n)
    // We `all_elim` at a fresh free n_witness, beta-reduce the body,
    // then re-`all_intro`.
    let n_witness = Term::free("n", nat.clone());
    let specialised = after_step
        .all_elim(n_witness.clone())
        .expect("zero_ne_succ: all_elim final");
    // specialised : ⊢ Trueprop ((λn. body) n_witness)

    let normalised = beta_top_under_trueprop(specialised, &p_lambda, n_witness.clone(), &ctx);
    // normalised : ⊢ Trueprop (¬(0 = succ n_witness))

    normalised
        .all_intro("n", nat)
        .expect("zero_ne_succ: all_intro final")
}

fn prove_base_case(
    p_lambda: &Term,
    body_at: &dyn Fn(Term) -> Term,
    ctx: &HolLightCtx,
) -> Thm {
    // Target: ⊢ Trueprop (P_lambda 0)

    // 1. Get `nat_zero_ne_one()` : ⊢ Trueprop (¬(0 = 1))
    let zno_thm = nat_zero_ne_one();

    // 2. Convert to ⊢ Trueprop (¬(0 = succ 0)).
    //    Idea: ¬(0 = succ 0) and ¬(0 = 1) differ only in `succ 0` vs `1`,
    //    which are equal by reduce_prim.
    let succ_0_eq_1 = Thm::reduce_prim(succ(nat_lit(0))).expect("base: reduce succ 0");
    // ⊢ succ 0 ≡ 1

    let nat = Type::nat();
    let refl_not = Thm::refl(ctx.not_op()).expect("base: refl not");
    let refl_eq_at_0 = Thm::refl(Term::app(ctx.eq_at(nat.clone()), nat_lit(0)))
        .expect("base: refl App(eq_at, 0)");
    // ⊢ App(eq_at, 0) ≡ App(eq_at, 0)
    let eq_cong = refl_eq_at_0
        .cong_app(succ_0_eq_1)
        .expect("base: cong_app eq_at_0 succ");
    // ⊢ App(App(eq_at, 0), succ 0) ≡ App(App(eq_at, 0), 1)
    let not_cong = refl_not.cong_app(eq_cong).expect("base: cong_app not");
    // ⊢ ¬(0 = succ 0) ≡ ¬(0 = 1)

    let tp_cong = Thm::refl(ctx.trueprop())
        .expect("base: refl Trueprop")
        .cong_app(not_cong)
        .expect("base: cong_app Trueprop");
    // ⊢ Trueprop (¬(0 = succ 0)) ≡ Trueprop (¬(0 = 1))

    let base_at_0 = tp_cong
        .sym()
        .expect("base: sym tp_cong")
        .eq_mp(zno_thm)
        .expect("base: eq_mp final");
    // ⊢ Trueprop (¬(0 = succ 0))   = Trueprop (body_at(0))

    // 3. Convert to ⊢ Trueprop (P_lambda 0) by reverse-beta.
    fold_beta_under_trueprop(base_at_0, p_lambda, nat_lit(0), &body_at(nat_lit(0)), ctx)
}

fn prove_step_case(
    p_lambda: &Term,
    body_at: &dyn Fn(Term) -> Term,
    ctx: &HolLightCtx,
    nat: &Type,
) -> Thm {
    // Target: ⊢ ⋀n. Trueprop (P_lambda n) ⟹ Trueprop (P_lambda (succ n))

    let n_free = Term::free("n", nat.clone());

    // Assume Trueprop (P_lambda n_free). β-reduce under Trueprop to
    //   `Trueprop (¬(0 = succ n_free))`.
    let p_n_term = Term::app(p_lambda.clone(), n_free.clone());
    let antecedent_orig = ctx
        .mk_trueprop(p_n_term)
        .expect("step: mk_trueprop antecedent");
    let assumed = Thm::assume(antecedent_orig.clone()).expect("step: assume");
    // assumed : Trueprop (P_lambda n) ⊢ Trueprop (P_lambda n)

    let ih_normalised = beta_top_under_trueprop(assumed, p_lambda, n_free.clone(), ctx);
    // ih_normalised : {Trueprop (P_lambda n)} ⊢ Trueprop (¬(0 = succ n))

    // Unfold ¬: derive Trueprop ((0 = succ n) ⟹ F) from the IH.
    let zero_eq_succ_n = hol_eq(nat_lit(0), succ(n_free.clone()), ctx);
    let ih_unfolded = unfold_not(ih_normalised, zero_eq_succ_n.clone(), ctx);
    // ih_unfolded : {...} ⊢ Trueprop ((0 = succ n) ⟹ F)

    // Lower HOL imp to Pure imp:
    //   {...} ⊢ Trueprop (0 = succ n) ⟹ Trueprop F
    let ih_lowered = crate::bridge::lower_imp_from_hol(
        ih_unfolded,
        zero_eq_succ_n.clone(),
        Term::bool_lit(false),
    );

    // Goal for the step: derive ⊢ Trueprop (P_lambda (succ n)) under
    // the IH hypothesis. β-equiv to Trueprop (¬(0 = succ (succ n))).
    // Equivalent unfolded: Trueprop ((0 = succ (succ n)) ⟹ F).

    // Assume Trueprop (0 = succ (succ n)). Then derive Trueprop F:
    //   - succ_inj-style: pred both sides; pred 0 = 0; pred (succ (succ n)) = succ n;
    //     so 0 = succ n; use IH.
    let zero_eq_succ_succ_n = hol_eq(nat_lit(0), succ(succ(n_free.clone())), ctx);
    let inner_ant = ctx
        .mk_trueprop(zero_eq_succ_succ_n.clone())
        .expect("step: mk_trueprop inner antecedent");
    let inner_assumed = Thm::assume(inner_ant.clone()).expect("step: inner assume");
    // inner_assumed : {... , Trueprop (0 = succ (succ n))} ⊢ Trueprop (0 = succ (succ n))

    // Convert to Pure meta-eq: 0 ≡ succ (succ n)
    let pure_eq_outer = pure_eq_from_hol_eq(
        inner_assumed,
        nat.clone(),
        nat_lit(0),
        succ(succ(n_free.clone())),
    );

    // Apply pred via cong_app: pred 0 ≡ pred (succ (succ n))
    let refl_pred = Thm::refl(pred_fn()).expect("step: refl pred");
    let pred_both = refl_pred
        .cong_app(pure_eq_outer)
        .expect("step: cong_app pred");
    // pred_both : {Trueprop (0 = succ (succ n))} ⊢ pred 0 ≡ pred (succ (succ n))

    // Rewrite LHS using nat_pred_zero (⊢ Trueprop (pred 0 = 0) → Pure-eq: pred 0 ≡ 0)
    let pred_zero_pure = pure_eq_from_hol_eq(
        Thm::nat_pred_zero(),
        nat.clone(),
        pred(nat_lit(0)),
        nat_lit(0),
    );
    // ⊢ pred 0 ≡ 0
    // So: 0 ≡ pred 0 (sym), trans with pred_both → 0 ≡ pred (succ (succ n))
    let lhs_rewritten = pred_zero_pure
        .sym()
        .expect("step: sym pred_zero")
        .trans(pred_both)
        .expect("step: trans 1");

    // Rewrite RHS using nat_pred_succ at (succ n): pred (succ (succ n)) ≡ succ n
    let pred_succ_at = Thm::nat_pred_succ()
        .all_elim(succ(n_free.clone()))
        .expect("step: all_elim pred_succ");
    let pred_succ_pure = pure_eq_from_hol_eq(
        pred_succ_at,
        nat.clone(),
        pred(succ(succ(n_free.clone()))),
        succ(n_free.clone()),
    );
    // ⊢ pred (succ (succ n)) ≡ succ n
    let final_pure = lhs_rewritten
        .trans(pred_succ_pure)
        .expect("step: trans 2");
    // {Trueprop (0 = succ (succ n))} ⊢ 0 ≡ succ n

    // Convert back to HOL: Trueprop (0 = succ n)
    let zero_eq_succ_n_thm = hol_eq_from_pure_eq(
        final_pure,
        nat.clone(),
        nat_lit(0),
        succ(n_free.clone()),
    );

    // Apply the IH: Trueprop (0 = succ n) ⟹ Trueprop F.
    let derive_false = ih_lowered
        .imp_elim(zero_eq_succ_n_thm)
        .expect("step: imp_elim IH");
    // {Trueprop (P_lambda n), Trueprop (0 = succ (succ n))} ⊢ Trueprop F

    // imp_intro the inner antecedent:
    let inner_imp = derive_false
        .imp_intro(&inner_ant)
        .expect("step: imp_intro inner");
    // {Trueprop (P_lambda n)} ⊢ Trueprop (0 = succ (succ n)) ⟹ Trueprop F

    // Lift Pure imp to HOL imp: Trueprop ((0 = succ (succ n)) ⟹ F)
    let hol_imp_thm = lift_imp_to_hol(
        inner_imp,
        zero_eq_succ_n_thm_lhs(zero_eq_succ_succ_n.clone()),
        Term::bool_lit(false),
    );

    // Fold the (... ⟹ F) form into ¬: Trueprop (¬(0 = succ (succ n)))
    let not_thm = fold_not(hol_imp_thm, zero_eq_succ_succ_n, ctx);
    // {Trueprop (P_lambda n)} ⊢ Trueprop (¬(0 = succ (succ n)))
    //                       = Trueprop (body_at(succ n))

    // Convert to Trueprop (P_lambda (succ n)) by reverse-beta.
    let succ_n_term = succ(n_free.clone());
    let p_at_succ_n = fold_beta_under_trueprop(
        not_thm,
        p_lambda,
        succ_n_term.clone(),
        &body_at(succ_n_term),
        ctx,
    );
    // {Trueprop (P_lambda n)} ⊢ Trueprop (P_lambda (succ n))

    // imp_intro the outer antecedent (the IH):
    let outer_imp = p_at_succ_n
        .imp_intro(&antecedent_orig)
        .expect("step: imp_intro outer");
    // ⊢ Trueprop (P_lambda n) ⟹ Trueprop (P_lambda (succ n))

    // all_intro at n_free:
    outer_imp
        .all_intro("n", nat.clone())
        .expect("step: all_intro n")
}

/// Identity helper used to make code more legible at the call site.
fn zero_eq_succ_n_thm_lhs(t: Term) -> Term {
    t
}

/// `⊢ Trueprop ((λx. body) arg)` → `⊢ Trueprop (body[arg/x])` —
/// β-reduces a single top-level redex inside a Trueprop.
fn beta_top_under_trueprop(
    thm: Thm,
    lambda: &Term,
    arg: Term,
    ctx: &HolLightCtx,
) -> Thm {
    let redex = Term::app(lambda.clone(), arg);
    let beta = Thm::beta_conv(redex).expect("beta_top: beta_conv");
    // ⊢ (λx. body) arg ≡ body[arg]
    let trueprop_eq = Thm::refl(ctx.trueprop())
        .expect("beta_top: refl Trueprop")
        .cong_app(beta)
        .expect("beta_top: cong_app");
    // ⊢ Trueprop ((λx. body) arg) ≡ Trueprop (body[arg])
    trueprop_eq.eq_mp(thm).expect("beta_top: eq_mp")
}

/// `⊢ Trueprop body[arg/x]` → `⊢ Trueprop ((λx. body) arg)` —
/// reverse β.
fn fold_beta_under_trueprop(
    thm: Thm,
    lambda: &Term,
    arg: Term,
    _body_at_arg: &Term,
    ctx: &HolLightCtx,
) -> Thm {
    let redex = Term::app(lambda.clone(), arg);
    let beta = Thm::beta_conv(redex).expect("fold_beta: beta_conv");
    let trueprop_eq = Thm::refl(ctx.trueprop())
        .expect("fold_beta: refl Trueprop")
        .cong_app(beta)
        .expect("fold_beta: cong_app");
    // ⊢ Trueprop (redex) ≡ Trueprop (body_at_arg)
    // sym + eq_mp:
    trueprop_eq
        .sym()
        .expect("fold_beta: sym")
        .eq_mp(thm)
        .expect("fold_beta: eq_mp")
}

// ============================================================================
// nat_succ_inj
// ============================================================================

/// `⊢ ⋀m n:nat. Trueprop ((succ m = succ n) ⟹ (m = n))`.
///
/// Strategy: assume `succ m = succ n`; apply `pred` to both sides via
/// `cong_app`; rewrite each side using `pred (succ k) = k`
/// ([`Thm::nat_pred_succ`]); conclude `m = n`. The result is
/// `Pure-imp`-bodied; we lift to HOL imp under one `Trueprop` via
/// `lift_imp_to_hol`, then universally close at `n` and `m` with
/// `all_intro` (Pure metas).
pub fn prove_nat_succ_inj() -> Thm {
    let ctx = HolLightCtx::new();
    let nat = nat_ty();
    let m = Term::free("m", nat.clone());
    let n = Term::free("n", nat.clone());

    // Kernel axiom `Thm::nat_pred_succ`:  ⋀n:nat. Trueprop (pred (succ n) = n)
    // → ⊢ Trueprop (pred (succ m) = m)
    let pred_m_hol = Thm::nat_pred_succ()
        .all_elim(m.clone())
        .expect("nat_succ_inj: all_elim m");
    // → ⊢ Trueprop (pred (succ n) = n)
    let pred_n_hol = Thm::nat_pred_succ()
        .all_elim(n.clone())
        .expect("nat_succ_inj: all_elim n");

    // Convert each to Pure meta-eq.
    let pred_m_pure = pure_eq_from_hol_eq(
        pred_m_hol,
        nat.clone(),
        pred(succ(m.clone())),
        m.clone(),
    );
    let pred_n_pure = pure_eq_from_hol_eq(
        pred_n_hol,
        nat.clone(),
        pred(succ(n.clone())),
        n.clone(),
    );

    // Assume the antecedent.
    let antecedent = trueprop(hol_eq(succ(m.clone()), succ(n.clone()), &ctx), &ctx);
    let assumed = Thm::assume(antecedent.clone()).expect("nat_succ_inj: assume");

    // → succ m ≡ succ n
    let succ_pure_eq = pure_eq_from_hol_eq(
        assumed,
        nat.clone(),
        succ(m.clone()),
        succ(n.clone()),
    );

    // → pred (succ m) ≡ pred (succ n) via cong_app
    let pred_succ_eq = Thm::refl(pred_fn())
        .expect("nat_succ_inj: refl pred_fn")
        .cong_app(succ_pure_eq)
        .expect("nat_succ_inj: cong_app pred");

    // → m ≡ n via trans
    let m_to_pred = pred_m_pure
        .sym()
        .expect("nat_succ_inj: sym pred_m_pure")
        .trans(pred_succ_eq)
        .expect("nat_succ_inj: trans (sym + cong)");
    let m_eq_n_pure = m_to_pred
        .trans(pred_n_pure)
        .expect("nat_succ_inj: trans (final)");

    // Lift back to Trueprop (m = n).
    let m_eq_n_hol = hol_eq_from_pure_eq(m_eq_n_pure, nat.clone(), m.clone(), n.clone());

    // Pure-level imp.
    let pure_imp = m_eq_n_hol
        .imp_intro(&antecedent)
        .expect("nat_succ_inj: imp_intro");

    // Lift Pure imp → Trueprop (A ⟹ B).
    let hol_imp_body = lift_imp_to_hol(
        pure_imp,
        hol_eq(succ(m.clone()), succ(n.clone()), &ctx),
        hol_eq(m.clone(), n.clone(), &ctx),
    );

    // Universally close.
    hol_imp_body
        .all_intro("n", nat.clone())
        .expect("nat_succ_inj: all_intro n")
        .all_intro("m", nat)
        .expect("nat_succ_inj: all_intro m")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn nat_succ_inj_has_empty_hyps() {
        let thm = prove_nat_succ_inj();
        assert!(
            thm.hyps().is_empty(),
            "proved Peano axiom should have empty hyps, got {} hyp(s)",
            thm.hyps().len()
        );
    }

    #[test]
    fn nat_succ_inj_concl_is_prop() {
        let thm = prove_nat_succ_inj();
        assert!(thm.concl().type_of().unwrap().is_bool());
    }

    #[test]
    fn nat_succ_inj_concl_is_correct_shape() {
        // Outer shape: ⋀m. ⋀n. Trueprop (succ m = succ n ⟹ m = n)
        let thm = prove_nat_succ_inj();
        let outer = thm.concl();
        // First binder: m
        let covalence_core::TermKind::All(_, ty1, _body1) = outer.kind() else {
            panic!("not ⋀m, got {outer:?}");
        };
        assert_eq!(ty1, &Type::nat());
    }

    #[test]
    fn nat_zero_ne_one_has_empty_hyps() {
        let thm = nat_zero_ne_one();
        assert!(thm.hyps().is_empty(), "got {} hyps", thm.hyps().len());
        assert!(thm.concl().type_of().unwrap().is_bool());
    }

    #[test]
    fn nat_zero_ne_one_is_cached() {
        // Two calls should produce structurally identical Thms.
        let a = nat_zero_ne_one();
        let b = nat_zero_ne_one();
        assert_eq!(a.concl(), b.concl());
    }

    #[test]
    fn nat_zero_ne_succ_has_empty_hyps() {
        let thm = prove_nat_zero_ne_succ();
        assert!(thm.hyps().is_empty(), "got {} hyps", thm.hyps().len());
        assert!(thm.concl().type_of().unwrap().is_bool());
    }

    #[test]
    fn nat_zero_ne_succ_outer_is_pure_forall_over_nat() {
        let thm = prove_nat_zero_ne_succ();
        let covalence_core::TermKind::All(_, ty, _) = thm.concl().kind() else {
            panic!("expected ⋀n. ..., got {:?}", thm.concl());
        };
        assert_eq!(ty, &Type::nat());
    }
}
