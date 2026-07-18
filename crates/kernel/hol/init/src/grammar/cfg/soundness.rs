//! **CFG soundness** (M3) — the discharge-free family least-fixpoint package.
//!
//! CFG languages are least fixpoints with no fold denotation, so the headline
//! soundness statement is a *rule-induction* package stated over an explicit
//! language-family variable `F : nat → set (list u8)`:
//!
//! ```text
//!   family_soundness:
//!   ⊢ ∀F. ClosedFam_E F ⟹ ∀n w. Derives_E n w ⟹ mem w (F n)
//! ```
//!
//! where `ClosedFam_E F` is the env's `Closed_E d` at `d := λn w. mem w (F n)`,
//! with exactly the **two outer β-redexes per `d`-occurrence** reduced — the
//! `Matches` antecedents and any denotation folds are never touched. See
//! [`closed_fam`] for the audited helper and `notes/vibes/logics/cfg-stratum-design.md`
//! §3.
//!
//! The derivation is **grammar-size-independent** (milliseconds): no clause is
//! ever discharged per-grammar — the clauses ride inside the *assumed*
//! `ClosedFam_E F`. We assume `Derives_E n w = ∀d. Closed_E d ⟹ d n w`,
//! `all_elim` at the concrete predicate `pred := λn w. mem w (F n)`, bridge the
//! resulting assumed-`Closed_E[d:=pred]` to the 2-β `ClosedFam_E` normal form
//! (β-equal, so a `beta_nf` equation + `eq_mp`), `imp_elim`, β-reduce the
//! conclusion `pred n w` to `mem w (F n)`, and re-intro. This kills the
//! per-grammar Closed-D perf wall by construction.
//!
//! Vacuity/agreement guards:
//! - **S0** ([`closed_fam_trivial`]) — the trivial family `F_triv = λn. {w | T}`
//!   satisfies `⊢ ClosedFam_E F_triv` (every conjunct is trivially true).
//! - **S3** ([`derives_in_family_regular`]) — regular-fragment agreement on a
//!   single-nonterminal Var-free env: `F_reg = λn. ⟦⌜r⌝⟧`, `ClosedFam_E F_reg`
//!   discharged by regex `soundness_at`, giving
//!   `⊢ Derives_E ⌜0⌝ w ⟹ mem w ⟦⌜r⌝⟧`.
//!
//! Residuals (S2 comprehension least-ness, S3 at scale, env transport) are
//! recorded in `grammar/cfg/source-local TODO markers`.

use covalence_core::{Result, Term, Type};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::derived::DerivedRules;

use super::GrammarEnv;
use crate::init::ext::TermExt;
use crate::metalogic::binary::{closed_conj2, derivable2};

// ============================================================================
// The `ClosedFam_E F` builder — the audited 2-outer-β normal form.
// ============================================================================

/// The predicate `pred := λn w. mem w (F n)` at `nat → set (list u8)`, the
/// `d`-instantiation the soundness family uses. `mem` and `F n` are left
/// un-reduced (no δ on `set.mem`, `F` opaque) — only the two outer applications
/// are β-contracted, downstream, in [`apply_pred_2beta`].
fn family_pred(f: &Term) -> Result<Term> {
    let wty = GrammarEnv::word_ty();
    let n = Term::free("n", Type::nat());
    let w = Term::free("w", wty.clone());
    // mem w (F n) : bool.
    let fn_ = f.clone().apply(n.clone())?; // F n : set (list u8)
    let body = mem_word(&w, &fn_);
    // λn w. mem w (F n).
    let inner = Term::abs(wty, covalence_core::subst::close(&body, "w"));
    Ok(Term::abs(
        Type::nat(),
        covalence_core::subst::close(&inner, "n"),
    ))
}

/// `set.mem[list u8] w L : bool` — word membership in a language, as a term.
fn mem_word(w: &Term, l: &Term) -> Term {
    Term::app(
        Term::app(crate::init::set::set_mem(GrammarEnv::word_ty()), w.clone()),
        l.clone(),
    )
}

/// Apply `pred = λn w. mem w (F n)` to `(n, w)` doing **exactly two outer β
/// steps** — never β-normalising inside `F`, inside `mem`, or anywhere deeper.
/// The single audited β point of the whole family package: `pred n w`
/// β-contracts (top redex twice) to `mem w (F n)`, which is precisely the
/// clause shape `ClosedFam_E` records.
fn apply_pred_2beta(pred: &Term, n: &Term, w: &Term) -> Result<Term> {
    // step 1: (λn w. body) n  →β  λw. body[n]
    let after_n = beta_top(&pred.clone().apply(n.clone())?)?;
    // step 2: (λw. body[n]) w  →β  body[n][w]
    beta_top(&after_n.apply(w.clone())?)
}

/// One top-level β-contraction of a redex `(λx. body) arg`, as a *term*
/// (`Thm::beta_conv`'s rhs). The head must be a λ.
fn beta_top(redex: &Term) -> Result<Term> {
    let eq = Thm::beta_conv(redex.clone())?;
    Ok(eq
        .concl()
        .as_eq()
        .expect("beta_conv yields an equation")
        .1
        .clone())
}

/// `ClosedFam_E F` — the env's `Closed_E d` closure conjunction at
/// `d := λn w. mem w (F n)`, with **each `d n w` occurrence reduced by exactly
/// two outer β steps** (the [`apply_pred_2beta`] discipline; `Matches`
/// antecedents and any `F`-denotation are untouched). The same conjunction
/// shape as `closed_for_var2` with `d` replaced by the concrete family
/// predicate. Its normal form is pinned by test.
pub fn closed_fam(env: &GrammarEnv, f: &Term) -> Result<Term> {
    let pred = family_pred(f)?;
    let rs = env.rule_set();
    closed_conj2(&rs, &|n, w| apply_pred_2beta(&pred, n, w))
}

// ============================================================================
// S1 — family soundness (discharge-free, grammar-size-independent).
// ============================================================================

/// **Family soundness** (S1):
///
/// ```text
///   ⊢ ∀F : nat → set (list u8). ClosedFam_E F ⟹ ∀n w. Derives_E n w ⟹ mem w (F n)
/// ```
///
/// Hypothesis-free and fast (milliseconds), *independent of grammar size*: no
/// clause is discharged — the clauses ride inside the assumed `ClosedFam_E F`.
///
/// **Proof.** With `F, n, w` free and `pred := λn w. mem w (F n)`:
/// assume `Derives_E n w = ∀d. Closed_E d ⟹ d n w`; `all_elim` at `pred` gives
/// `{Der} ⊢ Closed_E[d:=pred] ⟹ pred n w`. Assume `ClosedFam_E F` (the 2-β
/// form); it is β-equal to `Closed_E[d:=pred]` (for a *free* `F` nothing but the
/// two outer d-applications is a redex), so a `beta_nf` equation `eq_mp`s the
/// assumption into the antecedent form. `imp_elim` yields `{…} ⊢ pred n w`;
/// `beta_nf` the conclusion to `mem w (F n)`; discharge the two assumptions and
/// generalise `w`, `n`, then `F`.
pub fn family_soundness(env: &GrammarEnv) -> Result<Thm> {
    let wty = GrammarEnv::word_ty();
    let f_ty = Type::fun(Type::nat(), crate::init::set::set(wty.clone()));
    let f = Term::free("F", f_ty.clone());
    let n = Term::free("n", Type::nat());
    let w = Term::free("w", wty.clone());

    let rs = env.rule_set();
    let pred = family_pred(&f)?;

    // The assumed derivation `Derives_E n w`.
    let deriv_nw = derivable2(&rs, &n, &w)?;
    let assumed_der = Thm::assume(deriv_nw.clone())?; // {Der} ⊢ ∀d. Closed_E d ⟹ d n w

    // Instantiate `d := pred`: {Der} ⊢ Closed_E[d:=pred] ⟹ pred n w.
    // The antecedent is the *un-reduced* form (d n w ↦ (λn w. …) n w).
    let specialized = assumed_der.all_elim(pred.clone())?;
    let closed_unreduced = closed_conj2(&rs, &|nn, ww| {
        pred.clone().apply(nn.clone())?.apply(ww.clone())
    })?;

    // Assume the 2-β `ClosedFam_E F` and bridge it to the un-reduced form:
    // ⊢ ClosedFam_E F = Closed_E[d:=pred]  (β-equal; F free so no deep redex).
    let closed_fam_t = closed_fam(env, &f)?;
    let bridge = crate::init::eq::beta_nf(closed_unreduced.clone()); // ⊢ Closed_E[d:=pred] = ClosedFam_E F
    debug_assert_eq!(
        bridge
            .concl()
            .as_eq()
            .expect("beta_nf yields an equation")
            .1,
        &closed_fam_t,
        "closed_fam is not the β-normal form of Closed_E[d:=pred]"
    );
    let assumed_fam = Thm::assume(closed_fam_t.clone())?; // {Fam} ⊢ ClosedFam_E F
    let closed_pred = bridge.sym()?.eq_mp(assumed_fam)?; // {Fam} ⊢ Closed_E[d:=pred]

    // imp_elim, then β-reduce `pred n w` to `mem w (F n)`.
    let pred_nw = specialized.imp_elim(closed_pred)?; // {Der, Fam} ⊢ pred n w
    let mem_nw = crate::init::eq::beta_nf_concl(pred_nw)?; // {Der, Fam} ⊢ mem w (F n)

    // Discharge the two assumptions and generalise.
    mem_nw
        .imp_intro(&deriv_nw)? // {Fam} ⊢ Derives_E n w ⟹ mem w (F n)
        .all_intro("w", wty)?
        .all_intro("n", Type::nat())? // {Fam} ⊢ ∀n w. Derives_E n w ⟹ mem w (F n)
        .imp_intro(&closed_fam_t)? // ⊢ ClosedFam_E F ⟹ ∀n w. …
        .all_intro("F", f_ty) // ⊢ ∀F. ClosedFam_E F ⟹ ∀n w. …
}

// ============================================================================
// S0 — the trivial family witness.
// ============================================================================

/// `F_triv = λn. {w | T}` — the always-true family (via `set.mk` of the
/// constant-`T` predicate). Ignores `n`; every word is a member.
fn f_triv() -> Term {
    let wty = GrammarEnv::word_ty();
    // {w | T} = set.mk (λw. T).
    let always = Term::abs(
        wty.clone(),
        covalence_core::subst::close(&covalence_hol_eval::mk_bool(true), "w"),
    );
    let triv_set = Term::app(crate::init::set::set_mk(wty.clone()), always);
    // λn. triv_set (n : nat unused).
    Term::abs(Type::nat(), covalence_core::subst::close(&triv_set, "n"))
}

/// **S0** — `⊢ ClosedFam_E F_triv` for the trivial family `F_triv = λn. {w | T}`.
///
/// Each closure conjunct is `∀w…. A₁ ⟹ … ⟹ mem (cat …) (F_triv ⌜lhs⌝)`, and
/// `mem w (F_triv n) = mem w {w | T} = (λw. T) w = T` — trivially true. So every
/// conjunct is proved by discharging its antecedents (whatever they are) against
/// the trivial conclusion; we build each directly as `A₁ ⟹ … ⟹ T` and conjoin.
/// Hypothesis-free.
pub fn closed_fam_trivial(env: &GrammarEnv) -> Result<Thm> {
    let f = f_triv();
    let rs = env.rule_set();
    let pred = family_pred(&f)?;

    // The clause *terms* at the 2-β pred (= the conjuncts of ClosedFam_E F_triv).
    let clause_terms = (rs.clauses)(&|n, w| apply_pred_2beta(&pred, n, w))?;

    // Prove each conjunct: its conclusion is `mem (cat …) (F_triv ⌜lhs⌝)`, which
    // computes to `T`; discharge any ∀/⟹ prefix trivially.
    let mut clause_thms = Vec::with_capacity(clause_terms.len());
    for cl in &clause_terms {
        clause_thms.push(prove_trivial_clause(cl)?);
    }

    crate::metalogic::conj_thms(clause_thms)
}

/// Prove a single `ClosedFam_E F_triv` conjunct `⊢ ∀w…. A₁ ⟹ … ⟹ mem (cat …)
/// (F_triv ⌜lhs⌝)`. The conclusion `mem c (F_triv k)` β/δ-reduces to `T`, so we
/// prove `T` and re-fold it up under the antecedents and quantifiers.
///
/// Structure of `cl`: an outer run of `∀w_j : list u8`, then a run of `A_j ⟹`,
/// then the bare membership conclusion. We peel foralls (all_elim at the bound
/// vars), assume each antecedent, prove the conclusion `= T`, then imp_intro /
/// all_intro back.
fn prove_trivial_clause(cl: &Term) -> Result<Thm> {
    // Split `cl` into (∀-var types, antecedents, conclusion). Each ∀ is opened
    // at the same fresh free variable `OPEN_VAR`; since the clause binds one
    // word-∀ at a time (right-nested `∀w0. ∀w1. …`) opening the outermost, then
    // recursing, keeps a single live `OPEN_VAR` per level — but `all_intro`
    // re-closes by name, so we must open each at a *distinct* free var. We
    // instead open + immediately record the type, opening the freshly-exposed
    // body at a numbered name.
    let mut forall_tys: Vec<(String, Type)> = Vec::new();
    let mut rest = cl.clone();
    let mut depth = 0usize;
    while let Some((ty, _)) = as_forall(&rest) {
        let name = format!("{OPEN_VAR}{depth}");
        // Re-open at the numbered name (as_forall opened at OPEN_VAR).
        let (head, lam) = rest.as_app().expect("∀ is an app");
        let _ = head;
        let (_ty, inner) = lam.as_abs().expect("∀ arg is a λ");
        rest = covalence_core::subst::open(inner, &Term::free(&name, ty.clone()));
        forall_tys.push((name, ty));
        depth += 1;
    }
    let mut ants: Vec<Term> = Vec::new();
    while let Some((ant, concl)) = as_imp(&rest) {
        ants.push(ant.clone());
        rest = concl.clone();
    }
    // `rest` is now the bare conclusion `mem (cat …) (F_triv ⌜lhs⌝)`.
    let concl_is_true = mem_triv_is_true(&rest)?; // ⊢ (mem … ) = T
    let mut thm = concl_is_true.sym()?.eq_mp(crate::init::logic::truth())?; // ⊢ mem …

    // Re-fold: imp_intro each antecedent (innermost first), then all_intro each
    // ∀ (innermost bound first).
    for ant in ants.into_iter().rev() {
        thm = thm.imp_intro(&ant)?;
    }
    for (name, ty) in forall_tys.into_iter().rev() {
        thm = thm.all_intro(&name, ty)?;
    }
    Ok(thm)
}

/// `⊢ (mem c (F_triv k)) = T` — the trivial-family membership computation:
/// `mem c (F_triv k) = mem c {w|T} = (λw. T) c = T`. β-normalising the whole
/// membership term is safe here (no denotation fold — `{w|T}` is a `set.mk` of a
/// constant), and `set_mk` membership computes via [`crate::init::set::mem_mk`].
fn mem_triv_is_true(mem_term: &Term) -> Result<Thm> {
    // `mem_term = set.mem c (F_triv k)`. First β-reduce `F_triv k` to `{w|T}`
    // (one outer β), then apply `mem_mk`, then β the `(λw. T) c` redex.
    let wty = GrammarEnv::word_ty();
    // Extract c and the (F_triv k) set from the application spine.
    let (mem_c, triv_set_applied) = mem_term
        .as_app()
        .ok_or_else(|| covalence_core::Error::ConnectiveRule("S0: mem not an app".into()))?;
    let (_mem, c) = mem_c
        .as_app()
        .ok_or_else(|| covalence_core::Error::ConnectiveRule("S0: mem head not an app".into()))?;

    // (F_triv k) →β {w|T} = set.mk (λw. T).
    let triv_set = beta_top(triv_set_applied)?;
    let always = Term::abs(
        wty.clone(),
        covalence_core::subst::close(&covalence_hol_eval::mk_bool(true), "w"),
    );
    debug_assert_eq!(
        triv_set,
        Term::app(crate::init::set::set_mk(wty.clone()), always.clone()),
        "S0: F_triv k did not β-reduce to set.mk (λw. T)"
    );

    // ⊢ mem c (F_triv k) = mem c {w|T}  (congruence on the β of the set arg).
    let set_beta = Thm::beta_conv(triv_set_applied.clone())?; // ⊢ (F_triv k) = {w|T}
    let mem_head = Term::app(crate::init::set::set_mem(wty.clone()), c.clone());
    let cong = Thm::refl(mem_head)?.cong_app(set_beta)?; // ⊢ mem c (F_triv k) = mem c {w|T}

    // ⊢ mem c {w|T} = (λw. T) c   (mem_mk), then β to T.
    let mem_mk = crate::init::set::mem_mk(&wty, c, &always)?; // ⊢ mem c {w|T} = (λw. T) c
    let beta_true = Thm::beta_conv(always.apply(c.clone())?)?; // ⊢ (λw. T) c = T

    cong.trans(mem_mk)?.trans(beta_true)
}

// ============================================================================
// T3 — the "membership in every closed family" projection.
// ============================================================================

/// **T3** (the M5 north-star projection). Given a hypothesis-free derivation
/// `derivation : ⊢ Derives_E ⌜nt⌝ w`, produce
///
/// ```text
///   ⊢ ∀F. ClosedFam_E F ⟹ mem w (F ⌜nt⌝)
/// ```
///
/// i.e. `w` lies in *every* language family closed under the env's productions
/// — the least-fixpoint upper-bound statement M5 wants. Built from
/// [`family_soundness`] by `all_elim`-ing the family-soundness `∀n w` at
/// `(⌜nt⌝, w)` and feeding `derivation`; the `∀F` and its `ClosedFam_E F`
/// antecedent are threaded through untouched.
///
/// The conclusion word is read off `derivation.concl()` (it is `Derives_E ⌜nt⌝
/// w` — the tactic's rule-shaped `cat`/`cons`/`nil` word). Result is
/// hypothesis-free iff `derivation` is.
pub fn derives_in_family(env: &GrammarEnv, nt: super::NtId, derivation: &Thm) -> Result<Thm> {
    let wty = GrammarEnv::word_ty();
    let f_ty = Type::fun(Type::nat(), crate::init::set::set(wty.clone()));
    let f = Term::free("F", f_ty.clone());
    let tag = env.tag(nt);

    // Recover the derived word `w` from the derivation's conclusion.
    let w = derives_word(env, derivation)?;

    // family_soundness : ⊢ ∀F. ClosedFam_E F ⟹ ∀n w. Derives_E n w ⟹ mem w (F n).
    let fs = family_soundness(env)?;
    let closed_fam_t = closed_fam(env, &f)?;

    // Peel ∀F, assume ClosedFam_E F, specialise the inner ∀n w at (⌜nt⌝, w),
    // discharge with `derivation`, re-close under ClosedFam ⟹ and ∀F.
    let at_f = fs.all_elim(f.clone())?; // ⊢ ClosedFam_E F ⟹ ∀n w. …
    let assumed_fam = Thm::assume(closed_fam_t.clone())?; // {Fam} ⊢ ClosedFam_E F
    let inner = at_f.imp_elim(assumed_fam)?; // {Fam} ⊢ ∀n w. Derives_E n w ⟹ mem w (F n)
    let at_nw = inner.all_elim(tag.clone())?.all_elim(w.clone())?; // {Fam} ⊢ Derives_E ⌜nt⌝ w ⟹ mem w (F ⌜nt⌝)
    let mem_in_f = at_nw.imp_elim(derivation.clone())?; // {Fam} ⊢ mem w (F ⌜nt⌝)

    mem_in_f
        .imp_intro(&closed_fam_t)? // ⊢ ClosedFam_E F ⟹ mem w (F ⌜nt⌝)
        .all_intro("F", f_ty) // ⊢ ∀F. ClosedFam_E F ⟹ mem w (F ⌜nt⌝)
}

/// Recover the word `w` from a `⊢ Derives_E ⌜nt⌝ w` derivation: its conclusion
/// is `∀d. Closed_E d ⟹ d ⌜nt⌝ w`, so it must equal `env.derivable(nt, w)` for
/// the derived `w` — we extract `w` from the innermost `d ⌜nt⌝ w` application.
fn derives_word(_env: &GrammarEnv, derivation: &Thm) -> Result<Term> {
    // concl = ∀d. Closed_E d ⟹ d ⌜nt⌝ w. Strip the ∀d and the Closed ⟹, then
    // read the last argument of `d ⌜nt⌝ w`.
    let concl = derivation.concl();
    let (_ty, body) = as_forall(concl)
        .ok_or_else(|| covalence_core::Error::ConnectiveRule("T3: Derives not a ∀".into()))?;
    let (_closed, d_nt_w) = as_imp(&body)
        .ok_or_else(|| covalence_core::Error::ConnectiveRule("T3: Derives not an ⟹".into()))?;
    let (_d_nt, w) = d_nt_w
        .as_app()
        .ok_or_else(|| covalence_core::Error::ConnectiveRule("T3: d n w not an app".into()))?;
    Ok(w.clone())
}

// ============================================================================
// S3 — toy regular-fragment agreement (single-nonterminal Var-free env).
// ============================================================================

/// **S3** — regular-fragment agreement on a single-nonterminal, Var-free env
/// whose only production is `NT₀ → ⌜r⌝` for a terminal regex `r`. With
/// `F_reg = λn. ⟦⌜r⌝⟧` (the regex denotation, ignoring `n`), `ClosedFam_E
/// F_reg` reduces to the single clause `∀w. Matches ⌜r⌝ w ⟹ mem w ⟦⌜r⌝⟧`,
/// which is exactly regex [`crate::init::regex::soundness_at`]. Discharging it
/// via `family_soundness` yields
///
/// ```text
///   ⊢ Derives_E ⌜0⌝ w ⟹ mem w ⟦⌜r⌝⟧
/// ```
///
/// `alpha` is the regex alphabet (`u8`); `regex_term` is the reified `⌜r⌝ :
/// regex u8` of the env's single terminal production. Returns the implication
/// with `w` free, pinned at `'r := set (list u8)` (the denotation instance).
///
/// Discharge is **per-env** — it can't reuse regex's polymorphic `Closed-D`
/// cache across different envs, so it scales linearly with env size and stays a
/// tiny-env-only tool (see `grammar/cfg/source-local TODO markers`, "S3 at scale").
pub fn derives_in_family_regular(
    env: &GrammarEnv,
    nt: super::NtId,
    alpha: &Type,
    regex_term: &Term,
) -> Result<Thm> {
    let wty = GrammarEnv::word_ty();
    let denote = crate::init::regex::denote(alpha, regex_term.clone())?; // ⟦r⟧ : set (list u8)
    // F_reg = λn. ⟦r⟧ (constant in n).
    let f_reg = Term::abs(Type::nat(), covalence_core::subst::close(&denote, "n"));

    // The regex machinery leaves the fold-result type `'r` free everywhere; the
    // denotation forces `'r := set (list u8)` in the `Matches` antecedent, so the
    // whole S3 chain is pinned at that instance (design note: "stay schematic
    // everywhere, pin only at the regex-soundness projection"). `F_reg`,
    // `denote`, `w` are `'r`-free; only the `Matches` clauses carry `'r`.
    let _ = alpha;
    let r_inst = crate::init::set::set(wty.clone()); // set (list u8)

    // Discharge ClosedFam_E F_reg (pinned `'r`). Its single conjunct is
    // `∀w. Matches ⌜r⌝ w ⟹ mem w ⟦r⟧` — regex soundness after β-folding
    // `mem w (F_reg ⌜nt⌝) = mem w ⟦r⟧`.
    let closed_fam_reg = closed_fam_regular(env, nt, alpha, regex_term, &f_reg)?;

    // family_soundness, pinned at `'r := set (list u8)` so its `ClosedFam`
    // antecedent matches the discharged (pinned) form.
    let fs = family_soundness(env)?.inst_tfree("r", r_inst)?;
    let inner = fs.all_elim(f_reg.clone())?.imp_elim(closed_fam_reg)?; // ⊢ ∀n w. Derives_E n w ⟹ mem w (F_reg n)
    let w = Term::free("w", wty.clone());
    let tag = env.tag(nt);
    let at_nw = inner.all_elim(tag)?.all_elim(w.clone())?; // ⊢ Derives_E ⌜nt⌝ w ⟹ mem w (F_reg ⌜nt⌝)

    // Rewrite `mem w (F_reg ⌜nt⌝)` to `mem w ⟦r⟧` (β `F_reg ⌜nt⌝ = ⟦r⟧`).
    beta_reduce_family_mem(&at_nw, &w, &f_reg, &denote)
}

/// Discharge `⊢ ClosedFam_E F_reg` for the single-production regular env: the
/// lone conjunct `∀w. Matches ⌜r⌝ w ⟹ mem w (F_reg ⌜0⌝)` is regex
/// `soundness_at` after β-folding `mem w (F_reg ⌜0⌝) = mem w ⟦r⟧`.
fn closed_fam_regular(
    env: &GrammarEnv,
    nt: super::NtId,
    alpha: &Type,
    regex_term: &Term,
    f_reg: &Term,
) -> Result<Thm> {
    let wty = GrammarEnv::word_ty();
    // The 2-β conjuncts of ClosedFam_E F_reg (there is exactly one).
    let pred = family_pred(f_reg)?;
    let rs = env.rule_set();
    let clause_terms = (rs.clauses)(&|n, w| apply_pred_2beta(&pred, n, w))?;
    if clause_terms.len() != 1 {
        return Err(covalence_core::Error::ConnectiveRule(
            "S3: regular env must have exactly one production".into(),
        ));
    }
    let clause = &clause_terms[0]; // ∀w. Matches ⌜r⌝ w ⟹ mem w (F_reg ⌜nt⌝)

    // regex soundness_at at a fresh `w`: ⊢ Matches ⌜r⌝ w ⟹ mem w ⟦r⟧.
    let w = Term::free("w", wty.clone());
    let sound = crate::init::regex::soundness_at(alpha, regex_term, &w)?;

    // Rewrite the conclusion `mem w ⟦r⟧` up to `mem w (F_reg ⌜nt⌝)` (β-expand),
    // matching the 2-β clause shape, then ∀-close over w.
    let tag = env.tag(nt);
    let f_at = f_reg.clone().apply(tag)?; // F_reg ⌜nt⌝ (redex)
    let f_beta = Thm::beta_conv(f_at.clone())?; // ⊢ F_reg ⌜nt⌝ = ⟦r⟧
    // ⊢ mem w ⟦r⟧ = mem w (F_reg ⌜nt⌝).
    let mem_head = Term::app(crate::init::set::set_mem(wty.clone()), w.clone());
    let mem_eq = Thm::refl(mem_head)?.cong_app(f_beta.sym()?)?;
    // rewrite the implication's conclusion.
    let rewritten = rewrite_imp_concl(sound, &mem_eq)?; // ⊢ Matches ⌜r⌝ w ⟹ mem w (F_reg ⌜nt⌝)
    let closed = rewritten.all_intro("w", wty)?;
    // The rule-set clause carries a free fold-result `'r`; regex `soundness_at`
    // pins it to `set (list u8)`. Compare against the pinned clause.
    let r_inst = crate::init::set::set(GrammarEnv::word_ty());
    let clause_pinned = covalence_core::subst::subst_tfree_in_term(clause, "r", &r_inst);
    debug_assert_eq!(
        closed.concl(),
        &clause_pinned,
        "S3: closed_fam clause mismatch"
    );
    Ok(closed)
}

/// From `Γ ⊢ A ⟹ B` and `⊢ B = B'`, derive `Γ ⊢ A ⟹ B'`.
fn rewrite_imp_concl(imp: Thm, b_eq: &Thm) -> Result<Thm> {
    let (a, _b) = as_imp(imp.concl())
        .ok_or_else(|| covalence_core::Error::ConnectiveRule("rewrite_imp_concl: not ⟹".into()))?;
    let a = a.clone();
    let assumed_a = Thm::assume(a.clone())?;
    let b = imp.imp_elim(assumed_a)?; // {A} ⊢ B
    let b_prime = b_eq.clone().eq_mp(b)?; // {A} ⊢ B'
    b_prime.imp_intro(&a)
}

/// From `⊢ Derives_E ⌜nt⌝ w ⟹ mem w (F_reg ⌜nt⌝)`, rewrite the conclusion's
/// `mem w (F_reg ⌜nt⌝)` to `mem w ⟦r⟧` by β-contracting the `F_reg ⌜nt⌝` redex.
fn beta_reduce_family_mem(imp: &Thm, w: &Term, _f_reg: &Term, _denote: &Term) -> Result<Thm> {
    let wty = GrammarEnv::word_ty();
    let mem_head = Term::app(crate::init::set::set_mem(wty.clone()), w.clone());
    // (F_reg ⌜nt⌝) redex — read it out of the imp's conclusion.
    let (_a, b) = as_imp(imp.concl())
        .ok_or_else(|| covalence_core::Error::ConnectiveRule("S3: not ⟹".into()))?;
    let (_mem_w, f_at) = b
        .as_app()
        .ok_or_else(|| covalence_core::Error::ConnectiveRule("S3: mem not app".into()))?;
    let f_beta = Thm::beta_conv(f_at.clone())?; // ⊢ F_reg ⌜nt⌝ = ⟦r⟧
    let mem_eq = Thm::refl(mem_head)?.cong_app(f_beta)?; // ⊢ mem w (F_reg ⌜nt⌝) = mem w ⟦r⟧
    rewrite_imp_concl(imp.clone(), &mem_eq)
}

// ============================================================================
// Small term-structure helpers (∀ / ⟹ splitting).
// ============================================================================

/// A fixed free-variable name for opening `∀`-bodies in structural walks
/// (fresh w.r.t. the closed clause terms we split — they bind `w0, w1, …`).
const OPEN_VAR: &str = "_cfg_snd_v";

/// If `t = ∀x:τ. body` (`App(forall τ) (Abs τ body)`), return `(τ, body)` with
/// the bound variable *opened* at the fresh free variable [`OPEN_VAR`] (so a
/// later `all_intro(OPEN_VAR, τ)` re-closes it).
fn as_forall(t: &Term) -> Option<(Type, Term)> {
    let (head, lam) = t.as_app()?;
    let (ty, inner) = lam.as_abs()?;
    // Guard: the head is the `forall` constant at `ty`.
    if *head != covalence_core::defs::forall(ty.clone()) {
        return None;
    }
    let opened = covalence_core::subst::open(inner, &Term::free(OPEN_VAR, ty.clone()));
    Some((ty.clone(), opened))
}

/// If `t = a ⟹ b`, return `(a, b)`.
fn as_imp(t: &Term) -> Option<(&Term, &Term)> {
    let imp = covalence_core::defs::imp();
    let (f, b) = t.as_app()?;
    let (h, a) = f.as_app()?;
    (*h == imp).then_some((a, b))
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_grammar::cfg::{Cfg, NtId, Seg};
    use covalence_grammar::regex::Regex;
    use std::time::Instant;

    /// `S → a S b | ε` — the classic non-regular `aⁿbⁿ` language.
    fn anbn() -> (GrammarEnv, NtId) {
        let mut cfg = Cfg::new();
        let s = cfg.add_nt("S");
        cfg.add_prod(
            s,
            vec![
                Seg::term(Regex::Lit(b'a')),
                Seg::nt(s),
                Seg::term(Regex::Lit(b'b')),
            ],
        );
        cfg.add_prod(s, vec![]);
        (GrammarEnv::new(cfg).unwrap(), s)
    }

    /// A padded env: `anbn` + ~20 dummy single-terminal productions, to catch
    /// accidental per-clause discharge in `family_soundness` (a loose wall-clock
    /// guard: S1 must stay grammar-size-independent).
    fn padded() -> GrammarEnv {
        let mut cfg = Cfg::new();
        let s = cfg.add_nt("S");
        cfg.add_prod(
            s,
            vec![
                Seg::term(Regex::Lit(b'a')),
                Seg::nt(s),
                Seg::term(Regex::Lit(b'b')),
            ],
        );
        cfg.add_prod(s, vec![]);
        for i in 0..20u8 {
            let d = cfg.add_nt(format!("D{i}"));
            cfg.add_prod(d, vec![Seg::term(Regex::Lit(b'a' + (i % 5)))]);
        }
        GrammarEnv::new(cfg).unwrap()
    }

    /// A single-nonterminal Var-free env `S → lit 'a'` for S3.
    fn single_lit() -> (GrammarEnv, NtId, Term) {
        let mut cfg = Cfg::new();
        let s = cfg.add_nt("S");
        cfg.add_prod(s, vec![Seg::term(Regex::Lit(b'a'))]);
        let env = GrammarEnv::new(cfg).unwrap();
        // The reified ⌜lit 'a'⌝ : regex u8.
        let alpha = crate::init::regex::u8_alphabet();
        let r = crate::init::regex::r_lit(&alpha, covalence_hol_eval::mk_u8(b'a'));
        (env, s, r)
    }

    #[test]
    fn closed_fam_pins_two_beta_normal_form() {
        let (env, _s) = anbn();
        let wty = GrammarEnv::word_ty();
        let f = Term::free("F", Type::fun(Type::nat(), crate::init::set::set(wty)));
        let fam = closed_fam(&env, &f).unwrap();

        // The 2-β form has NO residual `(λn w. …) n w` d-application redexes: the
        // only application heads at `d`-positions are `set.mem`, not a λ. We
        // check this by asserting `fam` equals the independently-built 2-β
        // conjunction (the builder is the spec), and separately that it is *not*
        // the un-reduced form.
        let pred = family_pred(&f).unwrap();
        let rs = env.rule_set();
        let two_beta =
            crate::metalogic::binary::closed_conj2(&rs, &|n, w| apply_pred_2beta(&pred, n, w))
                .unwrap();
        assert_eq!(fam, two_beta, "closed_fam must be the 2-β conjunction");

        let unreduced = crate::metalogic::binary::closed_conj2(&rs, &|n, w| {
            pred.clone().apply(n.clone()).unwrap().apply(w.clone())
        })
        .unwrap();
        assert_ne!(fam, unreduced, "closed_fam must have the d-redexes reduced");

        // And the 2-β form is the β-normal form of the un-reduced form (for free
        // F nothing deeper is a redex).
        let nf = crate::init::eq::beta_nf(unreduced)
            .concl()
            .as_eq()
            .unwrap()
            .1
            .clone();
        assert_eq!(fam, nf, "closed_fam must equal β-nf of the un-reduced form");
    }

    #[test]
    fn family_soundness_anbn() {
        let (env, _s) = anbn();
        let thm = family_soundness(&env).unwrap();
        assert!(thm.hyps().is_empty());
        // Shape: ⊢ ∀F. ClosedFam_E F ⟹ ∀n w. Derives_E n w ⟹ mem w (F n).
        let (_fty, body) = as_forall(thm.concl()).expect("outermost ∀F");
        let (ant, _concl) = as_imp(&body).expect("ClosedFam ⟹ …");
        // The antecedent is exactly ClosedFam_E F.
        let wty = GrammarEnv::word_ty();
        let f = Term::free("F", Type::fun(Type::nat(), crate::init::set::set(wty)));
        // (as_forall opens F at OPEN_VAR; rebuild the antecedent at that name).
        let f_open = Term::free(OPEN_VAR, f.type_of().unwrap());
        assert_eq!(ant, &closed_fam(&env, &f_open).unwrap());
    }

    #[test]
    fn family_soundness_is_grammar_size_independent() {
        // S1 must be discharge-free: a ~22-production env proves as fast as the
        // 2-production one. Loose guard (< a few seconds) to catch accidental
        // per-clause discharge, not to benchmark.
        let env = padded();
        assert_eq!(env.n_clauses(), 22);
        let t0 = Instant::now();
        let thm = family_soundness(&env).unwrap();
        let dt = t0.elapsed();
        assert!(thm.hyps().is_empty());
        assert!(
            dt.as_secs() < 5,
            "family_soundness took {dt:?} — likely discharging per-clause"
        );
    }

    #[test]
    fn closed_fam_trivial_anbn() {
        let (env, _s) = anbn();
        let thm = closed_fam_trivial(&env).unwrap();
        assert!(thm.hyps().is_empty());
        // It proves exactly `ClosedFam_E F_triv`.
        assert_eq!(thm.concl(), &closed_fam(&env, &f_triv()).unwrap());
    }

    #[test]
    fn derives_in_family_anbn() {
        use crate::grammar::cfg::tactic::prove_derives;
        let (env, s) = anbn();
        // A real derivation ⊢ Derives_E ⌜S⌝ ⌜aabb⌝ from M2's tactic.
        let der = prove_derives(&env, s, b"aabb").unwrap().unwrap();
        assert!(der.hyps().is_empty());
        let thm = derives_in_family(&env, s, &der).unwrap();
        assert!(thm.hyps().is_empty());
        // ⊢ ∀F. ClosedFam_E F ⟹ mem ⌜aabb⌝ (F ⌜S⌝).
        let (_fty, body) = as_forall(thm.concl()).expect("outermost ∀F");
        assert!(as_imp(&body).is_some(), "ClosedFam ⟹ mem …");
    }

    #[test]
    fn s3_regular_agreement_single_lit() {
        let (env, s, r) = single_lit();
        let alpha = crate::init::regex::u8_alphabet();
        let thm = derives_in_family_regular(&env, s, &alpha, &r).unwrap();
        assert!(thm.hyps().is_empty());
        // ⊢ Derives_E ⌜0⌝ w ⟹ mem w ⟦⌜lit 'a'⌝⟧.
        assert!(as_imp(thm.concl()).is_some());
        assert_eq!(s.index(), 0);
    }
}
