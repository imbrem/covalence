//! **Generic interpretation / transport between Metamath-database logics** —
//! "induction on derivations" for *relating formal systems*. This is the engine
//! behind **"provable in `L1` ⟹ a translation is provable in `L2`", proved
//! once**: the long-term target is `Derivable_HOL(X) ⟹ Derivable_ZFC(σ X)`.
//!
//! ## The theorem
//!
//! Given a source logic `L1` and a target logic `L2` (both [`RuleSet`]s over the
//! *same* carrier `Φ`) and a **formula translation** `σ : Φ → Φ`,
//! [`transport`] proves, in one move,
//!
//! ```text
//!   ⊢ ∀A. Derivable_L1 A ⟹ Derivable_L2 (σ A)
//! ```
//!
//! It is **exactly an instance of [`crate::metalogic::rule_induction`]**,
//! specialised to the predicate
//!
//! ```text
//!   d := λx. Derivable_L2 (σ x)      ([`sigma_pred`])
//! ```
//!
//! Rule induction conjoins the caller-supplied `clause_sims` (one per `L1`
//! clause) into `Closed_L1 d` and discharges `Derivable_L1 A`'s impredicative
//! definition at `d`. Reduced to its conclusion, `d A` is `Derivable_L2 (σ A)`.
//!
//! ## The `clause_sims` are the per-rule **simulation obligations**
//!
//! The caller supplies one theorem per `L1` clause. Each must prove **exactly**
//! that `L1`-clause *instantiated at `d := sigma_pred(L2, σ)`* — i.e. the
//! statement
//!
//! ```text
//!   ∀v. d(ess₀) ∧ … ∧ d(essₙ) ⟹ d(concl)        (β: d X = Derivable_L2 (σ X))
//! ```
//!
//! which reads "**`σ` simulates this `L1` rule inside `L2`**": if the
//! `σ`-images of the premises are `L2`-derivable, so is the `σ`-image of the
//! conclusion. [`rule_induction`] re-checks every step (it conjoins the clause
//! conclusions and feeds them to the kernel), so a bogus simulation fails the
//! build rather than fabricating a transport.
//!
//! ## The worked instance: conservative extension / monotonicity (σ = id)
//!
//! `tests` builds two real [`mm_database`](crate::metalogic::mm_database) rule sets where the **target
//! extends the source** — the target database has all of the source's `|-`
//! assertions plus an extra axiom (same signature) — and transports with the
//! **identity** translation `σ := λx. x`. Each source clause is *literally also
//! a target clause*, so its simulation is "the source rule IS a target rule":
//! discharge the `σ`-image premises through the **target** clause via the
//! impredicative derivation constructor. The result is the genuine theorem
//!
//! ```text
//!   ⊢ ∀A. Derivable_S A ⟹ Derivable_T (id A)
//! ```
//!
//! — **conservative-extension / monotonicity for arbitrary Metamath databases**,
//! proved through the generic engine. (Contrast [`super::database::monotone`],
//! which proves the same for the *fixed* MP+axiom `Derivable_DB` rule frame; this
//! works for any database's full rule set, transported by [`rule_induction`].)
//!
//! A genuinely structural `σ` (a constant-symbol renaming, a connective mapping)
//! with its per-rule simulations honestly proved is the next step — see
//! [`SKELETONS.md`](./SKELETONS.md).

use covalence_core::{Result, Term, Type};
use covalence_hol_eval::EvalThm as Thm;

use super::{RuleSet, derivable, rule_induction};
use crate::init::ext::TermExt;

// ============================================================================
// The generic transport combinator
// ============================================================================

/// `σ x` — apply the translation `σ : Φ → Φ` to an encoded formula `x`.
fn sigma_at(sigma: &Term, x: &Term) -> Result<Term> {
    sigma.clone().apply(x.clone())
}

/// Assert that two rule sets share a carrier (transport needs `σ : Φ → Φ` with
/// the *same* `Φ` on both sides).
fn check_same_carrier(src: &RuleSet, tgt: &RuleSet) -> Result<()> {
    if src.phi != tgt.phi {
        return Err(covalence_core::Error::ConnectiveRule(format!(
            "transport_db: carrier mismatch ({:?} vs {:?})",
            src.phi, tgt.phi
        )));
    }
    Ok(())
}

/// The statement transported by [`transport`] *at a particular formula* `a`:
///
/// ```text
///   Derivable(src, a) ⟹ Derivable(tgt, σ a)
/// ```
///
/// (with `σ a := sigma.apply(a)`). A HOL `bool` term; `src`/`tgt` must share a
/// carrier `Φ`, `sigma : Φ → Φ`, `a : Φ`.
pub fn interp_stmt(src: &RuleSet, tgt: &RuleSet, sigma: &Term, a: &Term) -> Result<Term> {
    check_same_carrier(src, tgt)?;
    let der_src = derivable(src, a)?;
    let der_tgt = derivable(tgt, &sigma_at(sigma, a)?)?;
    der_src.imp(der_tgt)
}

/// The transport **induction predicate** `λx. Derivable(tgt, σ x)` — a
/// `Φ → bool` term (closed over a fresh `x`). This is the `d := pred` rule
/// induction instantiates `Derivable(src, ·)` with; reduced at any `e`, `pred e`
/// is `Derivable(tgt, σ e)`.
pub fn sigma_pred(tgt: &RuleSet, sigma: &Term) -> Result<Term> {
    let x = Term::free("x", tgt.phi.clone());
    let body = derivable(tgt, &sigma_at(sigma, &x)?)?; // Derivable(tgt, σ x)
    Ok(Term::abs(
        tgt.phi.clone(),
        covalence_core::subst::close(&body, "x"),
    ))
}

/// **Generic transport between Metamath-database logics.**
///
/// ```text
///   ⊢ ∀A. Derivable(src, A) ⟹ Derivable(tgt, σ A)
/// ```
///
/// Implemented as the single [`rule_induction`] move with predicate
/// [`sigma_pred`]`(tgt, σ)` and the caller's `clause_sims` as the per-clause
/// proofs. **`clause_sims` ARE the per-rule "σ simulates this rule in the
/// target" obligations**: `clause_sims[k]` must prove the `src` rule set's
/// `k`-th clause *laid out at `d := sigma_pred(tgt, σ)`* (the same order
/// [`RuleSet::clauses`] produces). The kernel re-checks each, so an incorrect
/// simulation makes this fail rather than mint an unsound theorem.
///
/// `src`/`tgt` must share a carrier; `sigma : Φ → Φ`. The result is over a free
/// `A : Φ` (universally closed), so it specialises to any concrete formula by
/// [`Thm::all_elim`].
pub fn transport(src: &RuleSet, tgt: &RuleSet, sigma: &Term, clause_sims: Vec<Thm>) -> Result<Thm> {
    check_same_carrier(src, tgt)?;
    let pred = sigma_pred(tgt, sigma)?;
    let a = Term::free("A", src.phi.clone());
    let deriv_a = derivable(src, &a)?; // Derivable(src, A)
    // `rule_induction` lands `⊢ ∀A. Derivable(src, A) ⟹ pred A`, where the
    // consequent `pred A` is the un-reduced redex `(λx. Derivable(tgt, σ x)) A`.
    // β-reduce it to the promised `Derivable(tgt, σ A)` so the conclusion is the
    // clean `∀A. Derivable(src, A) ⟹ Derivable(tgt, σ A)`.
    let raw = rule_induction(&pred, clause_sims, &deriv_a, "A", src.phi.clone())?;
    beta_reduce_consequent_under_forall(raw, &a, &pred, src.phi.clone())
}

/// Given `⊢ ∀A. P A ⟹ (pred) A` (the consequent a `pred`-redex at the bound
/// `A`), β-reduce `pred A` and re-generalise: `⊢ ∀A. P A ⟹ pred-body[A]`.
fn beta_reduce_consequent_under_forall(thm: Thm, a: &Term, pred: &Term, a_ty: Type) -> Result<Thm> {
    use crate::init::ext::ThmExt;
    let inst = thm.all_elim(a.clone())?; // ⊢ P A ⟹ pred A
    let pred_a = pred.clone().apply(a.clone())?; // (λx. …) A
    let beta = Thm::beta_conv(pred_a)?; // ⊢ pred A = Derivable(tgt, σ A)
    inst.rewrite(&beta)?.all_intro("A", a_ty) // ⊢ ∀A. P A ⟹ Derivable(tgt, σ A)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::metalogic::mm_database::{ClauseInfo, clause_infos, rule_set};
    use crate::metalogic::{closed_for_var, conj, conj_thms, nth_conjunct};
    use crate::metamath::{Database, parse, verify_all};

    fn assert_genuine(thm: &Thm) {
        assert!(thm.hyps().is_empty(), "theorem is hypothesis-free");
    }

    /// The identity translation `σ := λx. x` on the carrier `Φ = nat`.
    fn id_sigma() -> Term {
        let x = Term::free("__x", ClauseInfo::phi());
        Term::abs(ClauseInfo::phi(), covalence_core::subst::close(&x, "__x"))
    }

    // ---- the two databases: T extends S (same signature, one extra axiom) ----

    /// Source `S`: propositional calculus, `ax-1` / `ax-2` / `ax-mp`.
    const SRC: &str = "\
        $c ( ) -> wff |- $.
        $v ph ps ch $.
        wph $f wff ph $.
        wps $f wff ps $.
        wch $f wff ch $.
        wi $a wff ( ph -> ps ) $.
        ax-1 $a |- ( ph -> ( ps -> ph ) ) $.
        ax-2 $a |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $.
        ${
          mp.maj $e |- ph $.
          mp.min $e |- ( ph -> ps ) $.
          ax-mp $a |- ps $.
        $}
    ";

    /// Target `T`: `S` verbatim, **plus** one extra axiom `ax-3` (Peirce-shaped),
    /// in the same signature. Every `S`-clause (`ax-1`/`ax-2`/`ax-mp`) is a `T`
    /// clause, byte-for-byte; `T` is a conservative extension of `S`.
    const TGT: &str = "\
        $c ( ) -> wff |- $.
        $v ph ps ch $.
        wph $f wff ph $.
        wps $f wff ps $.
        wch $f wff ch $.
        wi $a wff ( ph -> ps ) $.
        ax-1 $a |- ( ph -> ( ps -> ph ) ) $.
        ax-2 $a |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $.
        ax-3 $a |- ( ( ( ph -> ps ) -> ph ) -> ph ) $.
        ${
          mp.maj $e |- ph $.
          mp.min $e |- ( ph -> ps ) $.
          ax-mp $a |- ps $.
        $}
    ";

    /// Build the `clause_sims` for the **σ = id, T ⊇ S** case: for each source
    /// `|-` clause `k`, prove the statement `src`'s rule set lays out at
    /// `d := sigma_pred(tgt, id)` by routing the `σ`-image premises through the
    /// *corresponding* target clause (which is byte-identical, since `T ⊇ S`).
    ///
    /// The proof of one clause (free metavars `vᵢ`):
    ///   * the clause body is `(⋀ d(essᵢ)) ⟹ d(concl)` with
    ///     `d X = Derivable(tgt, id X)` (β, then `id X = X` by β again);
    ///   * assume each `d(essᵢ)`, β-reduce to `Derivable(tgt, essᵢ)`;
    ///   * derive `Derivable(tgt, concl)` via the target clause `j` (open
    ///     `∀d'. Closed_T d' ⟹ d' …`, pull conjunct `j`, `all_elim` the metavars,
    ///     feed the premise conjunction) — the impredicative derivation
    ///     constructor;
    ///   * β-expand `Derivable(tgt, concl)` back to `d(concl)`, discharge the
    ///     antecedent, re-`∀` the metavars.
    fn id_clause_sims(src_db: &Database, tgt_db: &Database) -> Vec<Thm> {
        let tgt_rs = rule_set(tgt_db);
        let id = id_sigma();
        let pred = sigma_pred(&tgt_rs, &id).unwrap();
        let pred_apply = |x: &Term| pred.clone().apply(x.clone());

        let (src_infos, src_index) = clause_infos(src_db);
        let (_tgt_infos, tgt_index) = clause_infos(tgt_db);
        // The `|-` assertion labels in source-clause order.
        let mut src_labels: Vec<String> = vec![String::new(); src_infos.len()];
        for (label, &k) in &src_index {
            src_labels[k] = label.clone();
        }
        let n_tgt = tgt_index.len();

        src_infos
            .iter()
            .enumerate()
            .map(|(k, info)| {
                // The target clause index for the SAME assertion label.
                let j = *tgt_index
                    .get(&src_labels[k])
                    .expect("T extends S: every S clause label is a T clause label");
                simulate_via_target_clause(&tgt_rs, &pred_apply, info, j, n_tgt)
            })
            .collect()
    }

    /// Prove source clause `info` at `d := pred` by routing through target clause
    /// `j` (of `n_tgt`). `pred = λx. Derivable(tgt, id x)`; `info`'s encodings are
    /// byte-identical to target clause `j`'s (T ⊇ S, σ = id).
    fn simulate_via_target_clause(
        tgt_rs: &RuleSet,
        pred_apply: &dyn Fn(&Term) -> Result<Term>,
        info: &ClauseInfo,
        j: usize,
        n_tgt: usize,
    ) -> Thm {
        // Free metavariables (the ∀-binders); they appear free in the encodings.
        let phi = ClauseInfo::phi();

        // The target rule set's predicate var `d'` and its `Closed_T d'`.
        let d_prime = tgt_rs.d_var();
        let closed_t = closed_for_var(tgt_rs).unwrap();
        let assumed_closed = Thm::assume(closed_t.clone()).unwrap(); // {Closed_T d'} ⊢ Closed_T d'

        // For each essential premise eᵢ: assume `pred(eᵢ)`, β-reduce to
        // `Derivable(tgt, eᵢ)`, then turn into `d' eᵢ` under `Closed_T d'`.
        let mut pred_ess_terms = Vec::new(); // the `pred(eᵢ)` antecedent terms
        let mut d_prime_ess = Vec::new(); // {Closed_T d', pred(eᵢ)} ⊢ d' eᵢ
        for e in &info.ess_encs {
            let pred_e = pred_apply(e).unwrap(); // (λx. Der(tgt, id x)) eᵢ
            pred_ess_terms.push(pred_e.clone());
            let assume_pred_e = Thm::assume(pred_e.clone()).unwrap(); // {pred eᵢ} ⊢ pred eᵢ
            // β: pred eᵢ = Derivable(tgt, id eᵢ).
            let beta = Thm::beta_conv(pred_e.clone()).unwrap();
            let der_id_e = beta.eq_mp(assume_pred_e).unwrap(); // {pred eᵢ} ⊢ Der(tgt, id eᵢ)
            // id eᵢ = eᵢ : rewrite the carried formula to eᵢ.
            let der_e = rewrite_id_arg(tgt_rs, der_id_e, e); // {pred eᵢ} ⊢ Der(tgt, eᵢ)
            // Der(tgt, eᵢ) is `∀d'. Closed_T d' ⟹ d' eᵢ`; instantiate at d', MP.
            let d_e = der_e
                .all_elim(d_prime.clone())
                .unwrap()
                .imp_elim(assumed_closed.clone())
                .unwrap(); // {Closed_T d', pred eᵢ} ⊢ d' eᵢ
            d_prime_ess.push(d_e);
        }

        // Pull target clause j, specialise its metavars, feed premises → d' concl.
        let mut clause = nth_conjunct(assumed_closed.clone(), j, n_tgt).unwrap();
        for v in &info.float_vars {
            clause = clause
                .all_elim(Term::free(
                    crate::metalogic::mm_database::mv(v),
                    phi.clone(),
                ))
                .unwrap();
        }
        let d_concl = if d_prime_ess.is_empty() {
            clause // {Closed_T d'} ⊢ d' concl
        } else {
            clause.imp_elim(conj_thms(d_prime_ess).unwrap()).unwrap() // {Closed_T d', pred(essᵢ)…} ⊢ d' concl
        };

        // Discharge Closed_T d', generalise d' ⟹ Derivable(tgt, concl).
        let der_concl = d_concl
            .imp_intro(&closed_t)
            .unwrap()
            .all_intro("d", tgt_rs.pred_ty())
            .unwrap(); // {pred(essᵢ)…} ⊢ Derivable(tgt, concl)

        // β-expand `Derivable(tgt, concl)` back to `pred(concl)` (= id concl path).
        let pred_concl = pred_apply(&info.concl_enc).unwrap();
        let der_concl_id = rewrite_arg_to_id(tgt_rs, der_concl, &info.concl_enc); // ⊢ Der(tgt, id concl)
        let beta_concl = Thm::beta_conv(pred_concl.clone()).unwrap(); // ⊢ pred concl = Der(tgt, id concl)
        let pred_concl_thm = beta_concl.sym().unwrap().eq_mp(der_concl_id).unwrap(); // {pred(essᵢ)…} ⊢ pred concl

        // Discharge the premise conjunction (if any), re-∀ the metavars.
        let body = if pred_ess_terms.is_empty() {
            pred_concl_thm
        } else {
            let conj_ante = conj(pred_ess_terms).unwrap();
            // Re-split the assumed conjunction from `conj_ante` is implicit: the
            // hypotheses are the individual `pred(eᵢ)`; introduce the conjunction
            // by assuming it, projecting, and discharging.
            discharge_conj_antecedent(pred_concl_thm, &conj_ante)
        };

        let mut out = body;
        for v in info.float_vars.iter().rev() {
            out = out
                .all_intro(&crate::metalogic::mm_database::mv(v), phi.clone())
                .unwrap();
        }
        out
    }

    /// Given `Γ ⊢ q` whose hypotheses include each conjunct of `ante`
    /// (`c₀ ∧ (c₁ ∧ …)`), return `Γ' ⊢ ante ⟹ q` with the individual conjunct
    /// hypotheses replaced by the single conjunction: assume `ante`, split it into
    /// its conjuncts, cut each matching hypothesis of `q_thm`, then `imp_intro ante`.
    fn discharge_conj_antecedent(q_thm: Thm, ante: &Term) -> Thm {
        // Assume the conjunction, split into the individual conjuncts, and use
        // them to discharge `q_thm`'s matching hypotheses via `imp`/`MP`.
        let assume_ante = Thm::assume(ante.clone()).unwrap(); // {ante} ⊢ ante
        let conjuncts = split_conjunction(&assume_ante);
        // Discharge each conjunct hypothesis of `q_thm` by cut: imp_intro then
        // imp_elim with the conjunct.
        let mut acc = q_thm;
        for c in &conjuncts {
            let h = c.concl().clone();
            acc = acc.imp_intro(&h).unwrap().imp_elim(c.clone()).unwrap();
        }
        acc.imp_intro(ante).unwrap()
    }

    /// Split `{ante} ⊢ c₀ ∧ (c₁ ∧ …)` into `[{ante} ⊢ c₀, {ante} ⊢ c₁, …]`.
    fn split_conjunction(thm: &Thm) -> Vec<Thm> {
        let mut out = Vec::new();
        let mut cur = thm.clone();
        loop {
            // If the conclusion is a conjunction, peel the left and recurse right.
            let is_conj = {
                let c = cur.concl();
                c.as_app()
                    .and_then(|(f, _)| f.as_app())
                    .map(|(op, _)| format!("{op}").contains("bool.and"))
                    .unwrap_or(false)
            };
            if is_conj {
                out.push(cur.clone().and_elim_l().unwrap());
                cur = cur.and_elim_r().unwrap();
            } else {
                out.push(cur);
                break;
            }
        }
        out
    }

    /// `Γ ⊢ Derivable(tgt, id e)` → `Γ ⊢ Derivable(tgt, e)` (`id e = e` by β).
    fn rewrite_id_arg(tgt_rs: &RuleSet, thm: Thm, e: &Term) -> Thm {
        let id = id_sigma();
        let id_e = id.apply(e.clone()).unwrap();
        let beta = Thm::beta_conv(id_e).unwrap(); // ⊢ id e = e
        // The conclusion `Derivable(tgt, id e)` mentions `id e`; rewrite to `e`.
        let _ = tgt_rs;
        use crate::init::ext::ThmExt;
        thm.rewrite(&beta).unwrap()
    }

    /// `Γ ⊢ Derivable(tgt, e)` → `Γ ⊢ Derivable(tgt, id e)` (reverse of above).
    fn rewrite_arg_to_id(tgt_rs: &RuleSet, thm: Thm, e: &Term) -> Thm {
        let id = id_sigma();
        let id_e = id.apply(e.clone()).unwrap();
        let beta = Thm::beta_conv(id_e).unwrap(); // ⊢ id e = e
        let _ = tgt_rs;
        use crate::init::ext::ThmExt;
        thm.rewrite(&beta.sym().unwrap()).unwrap()
    }

    /// Derive `⊢ Derivable(rs, concl[v := args])` for the premise-free axiom
    /// clause `info` (index `k` of `n`), returning the theorem and the encoded
    /// instance formula. Mirrors `mm_database::derive_clause` for the no-premise
    /// case: open `∀d. Closed_rs d ⟹ d …`, pull conjunct `k`, `all_elim` the
    /// args (substituting the metavars), discharge `Closed_rs d`, generalise `d`.
    fn derive_axiom_instance(
        rs: &RuleSet,
        info: &ClauseInfo,
        k: usize,
        n: usize,
        args: &[Term],
    ) -> (Thm, Term) {
        assert!(info.ess_encs.is_empty(), "this helper is axiom-only");
        let closed_t = closed_for_var(rs).unwrap();
        let assumed = Thm::assume(closed_t.clone()).unwrap(); // {Closed d} ⊢ Closed d
        let mut clause = nth_conjunct(assumed, k, n).unwrap();
        for a in args {
            clause = clause.all_elim(a.clone()).unwrap(); // {Closed d} ⊢ d ⌜concl-inst⌝
        }
        // Read the instantiated formula off `d ⌜concl-inst⌝`.
        let formula = clause.concl().as_app().unwrap().1.clone();
        let der = clause
            .imp_intro(&closed_t)
            .unwrap()
            .all_intro("d", rs.pred_ty())
            .unwrap();
        (der, formula)
    }

    // ---- the tests ----

    #[test]
    fn interp_stmt_and_sigma_pred_are_well_typed() {
        let src_db = parse(SRC).unwrap();
        let tgt_db = parse(TGT).unwrap();
        let src_rs = rule_set(&src_db);
        let tgt_rs = rule_set(&tgt_db);
        let id = id_sigma();
        let a = Term::free("A", ClauseInfo::phi());

        let stmt = interp_stmt(&src_rs, &tgt_rs, &id, &a).unwrap();
        assert_eq!(stmt.type_of().unwrap(), Type::bool());

        let pred = sigma_pred(&tgt_rs, &id).unwrap();
        assert_eq!(
            pred.type_of().unwrap(),
            Type::fun(ClauseInfo::phi(), Type::bool())
        );
    }

    /// **The worked instance: conservative extension / monotonicity, σ = id.**
    /// `S` = prop calc (`ax-1`/`ax-2`/`ax-mp`); `T` = `S` + `ax-3`. Transport
    /// with `σ = id` yields the genuine theorem
    /// `⊢ ∀A. Derivable_S A ⟹ Derivable_T (id A)` — monotonicity for arbitrary
    /// Metamath databases, through the generic [`transport`] engine.
    #[test]
    fn id_transport_is_database_monotonicity() {
        let src_db = parse(SRC).unwrap();
        let tgt_db = parse(TGT).unwrap();
        assert_eq!(verify_all(&src_db).unwrap(), 0, "S has no $p to verify");
        assert_eq!(verify_all(&tgt_db).unwrap(), 0, "T has no $p to verify");

        let src_rs = rule_set(&src_db);
        let tgt_rs = rule_set(&tgt_db);
        let id = id_sigma();

        let clause_sims = id_clause_sims(&src_db, &tgt_db);
        // Sanity: one simulation per source `|-` clause (ax-1/ax-2/ax-mp = 3).
        assert_eq!(clause_sims.len(), 3, "three source `|-` clauses");

        let thm = transport(&src_rs, &tgt_rs, &id, clause_sims).unwrap();
        assert_genuine(&thm);

        // Shape: ∀A. Derivable_S A ⟹ Derivable_T (id A).
        let a = Term::free("A", ClauseInfo::phi());
        let expected = derivable(&src_rs, &a)
            .unwrap()
            .imp(derivable(&tgt_rs, &sigma_at(&id, &a).unwrap()).unwrap())
            .unwrap()
            .forall("A", ClauseInfo::phi())
            .unwrap();
        assert_eq!(
            thm.concl(),
            &expected,
            "transport has the monotonicity shape"
        );
    }

    /// The transported theorem genuinely *moves a fact across databases*:
    /// specialise it at a concrete `S`-derivation and land a `T`-derivation.
    #[test]
    fn id_transport_moves_a_concrete_fact() {
        let src_db = parse(SRC).unwrap();
        let tgt_db = parse(TGT).unwrap();
        let src_rs = rule_set(&src_db);
        let tgt_rs = rule_set(&tgt_db);
        let id = id_sigma();

        // The transport theorem ∀A. Der_S A ⟹ Der_T (id A).
        let clause_sims = id_clause_sims(&src_db, &tgt_db);
        let transp = transport(&src_rs, &tgt_rs, &id, clause_sims).unwrap();

        // An `S`-derivable formula: the `ax-1` axiom schema (clause 0) at a
        // concrete metavar instantiation. We derive `⊢ Derivable_S ⌜ax-1 inst⌝`
        // DIRECTLY over the transport's source rule set (so it is byte-identical
        // to `src_rs`, not a different `$p`-augmented one), via the impredicative
        // axiom-derivation constructor.
        let (src_infos, src_index) = clause_infos(&src_db);
        let k_ax1 = *src_index.get("ax-1").unwrap();
        let n_src = src_index.len();
        let info = &src_infos[k_ax1];
        // Instantiate ax-1's metavars `ph := var(0)`, `ps := var(1)` (concrete
        // `nat` literals — any closed `Φ` works for the demonstration).
        let phi = ClauseInfo::phi();
        let args: Vec<Term> = info
            .float_vars
            .iter()
            .enumerate()
            .map(|(i, _)| {
                covalence_hol_eval::mk_nat(covalence_types::Nat::from_inner((i as u32).into()))
            })
            .collect();
        let (der_s, formula) = derive_axiom_instance(&src_rs, info, k_ax1, n_src, &args);
        assert_genuine(&der_s);
        let _ = &phi;
        assert_eq!(der_s.concl(), &derivable(&src_rs, &formula).unwrap());

        // Transport: ∀A. … @ formula, then MP the source derivation.
        let der_t = transp
            .all_elim(formula.clone())
            .unwrap()
            .imp_elim(der_s)
            .unwrap(); // ⊢ Derivable_T (id formula)
        assert_genuine(&der_t);
        assert_eq!(
            der_t.concl(),
            &derivable(&tgt_rs, &sigma_at(&id, &formula).unwrap()).unwrap(),
            "the moved fact ranges over the target database T"
        );

        // It really is over T, not S (T's rule set has the extra ax-3 clause).
        assert_ne!(
            der_t.concl(),
            &derivable(&src_rs, &sigma_at(&id, &formula).unwrap()).unwrap(),
            "Derivable_T differs from Derivable_S (T has the extra ax-3 clause)"
        );
    }
}
