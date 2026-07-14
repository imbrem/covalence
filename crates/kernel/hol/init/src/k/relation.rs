//! **K reduction as a genuine relation on the binary inductive engine** — the
//! two-argument `KStep : Φ → Φ → bool` single-step relation and its
//! reflexive-transitive closure `KReduces = KStep*`, built on
//! [`crate::metalogic::binary`] (the same `RuleSet2` engine the CFG stratum and
//! the Lisp `Reduces` relation use).
//!
//! This is the **F2** layer of the K frontend (`notes/design/k-frontend.md`):
//! where [`super::reduce`] mints a *single* step as a tagged unary
//! `Derivable_KStep` judgement, here a step is a first-class binary membership
//! theorem `⊢ KStep a b`, and a *multi-step* run is a `⊢ KReduces a b` chain —
//! so `A →* B` (with `B` open) is directly statable and provable.
//!
//! ## The two relations
//!
//! Carriers `(A, B) = (Φ, Φ)` with `Φ = nat` (the reified configuration algebra,
//! [`super::encode`]). A configuration is [`super::encode::encode_pattern`]-d.
//!
//! - [`kstep_rule_set`] — `KStep`, one **base** clause per unconditional rewrite
//!   rule: `∀ x…. d (⌜LHS⌝) (⌜RHS⌝)`, `x…` the rule's element variables.
//!   Conditional rules (with `requires`) are skipped + reported (F1).
//! - [`kreduces_rule_set`] — `KReduces = KStep*`: `refl : ∀t. KReduces t t` and
//!   `step : ∀a b c. KStep a b ⟹ KReduces b c ⟹ KReduces a c` (the `KStep`
//!   antecedent is a [`Premise::Side`], the `KReduces` one a
//!   [`Premise::Derivation`]).
//!
//! No new trusted kernel rules: both relations are *defined* via the engine's
//! impredicative least fixpoint, so a closed configuration's `⊢ KReduces …` is
//! hypothesis-free syntactic data. Construct, don't trust: a driver (or an
//! external K engine) proposes which rule fires where; the kernel re-checks.

use std::collections::BTreeMap;

use covalence_core::{Error, Result, Term};
use covalence_hol_eval::EvalThm as Thm;
use covalence_k::fragment::RewriteRule;

use super::encode::{encode_pattern, metavar_name, phi, rule_metavars, subst_metavars};
use crate::init::ext::TermExt;
use crate::metalogic::binary::{Premise, RuleSet2, derivable2, derive_mixed};

fn rel_err(msg: impl Into<String>) -> Error {
    Error::ConnectiveRule(format!("k relation: {}", msg.into()))
}

/// One lowered rewrite rule: element-variable order + encoded endpoints.
struct LoweredRule {
    metavars: Vec<String>,
    lhs: Term,
    rhs: Term,
}

/// What [`kstep_rule_set`] lowered and skipped (conditional rules).
#[derive(Debug, Default, Clone)]
pub struct LoweringReport {
    pub lowered: usize,
    pub skipped: usize,
    pub skips: BTreeMap<String, usize>,
}

fn lower_rule(rule: &RewriteRule) -> Result<LoweredRule> {
    if rule.requires.is_some() {
        return Err(rel_err(
            "rule has a `requires` side condition (needs the F1 hooked-Bool theory)",
        ));
    }
    Ok(LoweredRule {
        metavars: rule_metavars(&rule.lhs, &rule.rhs),
        lhs: encode_pattern(&rule.lhs)?,
        rhs: encode_pattern(&rule.rhs)?,
    })
}

/// Build the `KStep` clause `∀ x…. d ⌜LHS⌝ ⌜RHS⌝` for a lowered rule.
fn step_clause(rule: &LoweredRule, d_apply: &dyn Fn(&Term, &Term) -> Result<Term>) -> Result<Term> {
    let mut body = d_apply(&rule.lhs, &rule.rhs)?;
    // Quantify element variables outermost-first (matches the `derive_mixed`
    // `word_args` order — metavars[0] binds outermost).
    for mv in rule.metavars.iter().rev() {
        body = body.forall(&metavar_name(mv), phi())?;
    }
    Ok(body)
}

/// The **`KStep` single-step rule set** of a set of rewrite rules: one base
/// clause per unconditional rule, in order. Conditional rules are skipped and
/// reported (sound-but-incomplete; clause `i` = the `i`-th *lowered* rule).
pub fn kstep_rule_set(rules: &[RewriteRule]) -> (RuleSet2<'static>, LoweringReport) {
    let mut lowered = Vec::new();
    let mut report = LoweringReport::default();
    for rule in rules {
        match lower_rule(rule) {
            Ok(lr) => {
                report.lowered += 1;
                lowered.push(lr);
            }
            Err(e) => {
                report.skipped += 1;
                let msg = e.to_string();
                let key = msg.rsplit(':').next().unwrap_or(&msg).trim().to_string();
                *report.skips.entry(key).or_default() += 1;
            }
        }
    }
    let rs = RuleSet2::new(phi(), phi(), move |d| {
        lowered.iter().map(|r| step_clause(r, d)).collect()
    });
    (rs, report)
}

/// `KReduces = KStep*`: `refl` (clause 0) + `step` (clause 1), over the given
/// `KStep` rule set.
pub fn kreduces_rule_set(step_rs: RuleSet2<'static>) -> RuleSet2<'static> {
    RuleSet2::new(phi(), phi(), move |d| {
        let tau = phi();
        // clause 0: ∀t. d t t.
        let tv = Term::free("t", tau.clone());
        let refl = d(&tv, &tv)?.forall("t", tau.clone())?;
        // clause 1: ∀a b c. KStep a b ⟹ d b c ⟹ d a c.
        let a = Term::free("a", tau.clone());
        let b = Term::free("b", tau.clone());
        let c = Term::free("c", tau.clone());
        let step_ab = derivable2(&step_rs, &a, &b)?;
        let body = step_ab.imp(d(&b, &c)?.imp(d(&a, &c)?)?)?;
        let step = body
            .forall("c", tau.clone())?
            .forall("b", tau.clone())?
            .forall("a", tau.clone())?;
        Ok(vec![refl, step])
    })
}

/// `KStep from to` (the proposition).
pub fn kstep_prop(step_rs: &RuleSet2, from: &Term, to: &Term) -> Result<Term> {
    derivable2(step_rs, from, to)
}

/// `KReduces from to` (the proposition).
pub fn kreduces_prop(reduces_rs: &RuleSet2, from: &Term, to: &Term) -> Result<Term> {
    derivable2(reduces_rs, from, to)
}

/// A single certified step: `⊢ KStep from to` plus its encoded endpoints.
pub struct KStepThm {
    pub from: Term,
    pub to: Term,
    pub thm: Thm,
}

/// **Fire rule `rule_idx`** of a `KStep` rule set at a concrete redex:
/// instantiate its element variables with `args` (the rule's `∀` order) and mint
/// `⊢ KStep ⌜LHS[args]⌝ ⌜RHS[args]⌝`. `n_rules = step_rs.n_clauses()?`; `rule` is
/// the source rule the clause was lowered from (to recover the endpoints).
pub fn prove_step(
    step_rs: &RuleSet2,
    rule_idx: usize,
    n_rules: usize,
    rule: &RewriteRule,
    args: &[Term],
) -> Result<KStepThm> {
    let thm = derive_mixed(step_rs, rule_idx, n_rules, args, vec![])?;
    let order = rule_metavars(&rule.lhs, &rule.rhs);
    let from = subst_metavars(&encode_pattern(&rule.lhs)?, &order, args)?;
    let to = subst_metavars(&encode_pattern(&rule.rhs)?, &order, args)?;
    Ok(KStepThm { from, to, thm })
}

/// `⊢ KReduces t t` (the reflexive clause).
pub fn prove_refl(reduces_rs: &RuleSet2, t: &Term) -> Result<Thm> {
    derive_mixed(reduces_rs, 0, 2, std::slice::from_ref(t), vec![])
}

/// `⊢ KReduces a c` from `⊢ KStep a b` and `⊢ KReduces b c` (the `step` clause).
pub fn prove_reduces_step(
    reduces_rs: &RuleSet2,
    a: &Term,
    b: &Term,
    c: &Term,
    step: Thm,
    rest: Thm,
) -> Result<Thm> {
    derive_mixed(
        reduces_rs,
        1,
        2,
        &[a.clone(), b.clone(), c.clone()],
        vec![Premise::Side(step), Premise::Derivation(rest)],
    )
}

/// Fold a **chain of single steps** `s₀ : a₀→a₁, s₁ : a₁→a₂, …, sₖ₋₁ : aₖ₋₁→aₖ`
/// into `⊢ KReduces a₀ aₖ`. An empty chain needs `endpoint` (the reflexive
/// `⊢ KReduces endpoint endpoint`); a non-empty chain ignores `endpoint` and ends
/// at `sₖ₋₁.to`. Consecutive steps must connect (`sᵢ.to == sᵢ₊₁.from`).
pub fn prove_reduces(reduces_rs: &RuleSet2, steps: Vec<KStepThm>, endpoint: &Term) -> Result<Thm> {
    let Some(last) = steps.last() else {
        return prove_refl(reduces_rs, endpoint);
    };
    let target = last.to.clone();
    // Fold right: rest starts as `⊢ KReduces target target`, then snoc each step
    // from the back so `rest : KReduces sᵢ.to target` grows to `KReduces a₀ …`.
    let mut rest = prove_refl(reduces_rs, &target)?;
    for s in steps.into_iter().rev() {
        rest = prove_reduces_step(reduces_rs, &s.from, &s.to, &target, s.thm, rest)?;
    }
    Ok(rest)
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_k::ast::{Pattern, Sort};

    fn assert_genuine(thm: &Thm) {
        assert!(
            thm.hyps().is_empty(),
            "reduction theorem must be hypothesis-free"
        );
    }

    fn app(sym: &str, args: Vec<Pattern>) -> Pattern {
        Pattern::App {
            symbol: sym.into(),
            sorts: vec![],
            args,
        }
    }
    fn int(v: &str) -> Pattern {
        Pattern::DV(Sort::App("SortInt".into(), vec![]), v.into())
    }
    fn cfg() -> Sort {
        Sort::App("SortCfg".into(), vec![])
    }
    fn rule(lhs: Pattern, rhs: Pattern) -> RewriteRule {
        RewriteRule {
            sort: cfg(),
            lhs,
            rhs,
            requires: None,
            ensures: None,
            priority: 50,
            label: None,
            unique_id: None,
        }
    }

    /// A tiny ground machine: count(0) → count(1) → done.
    fn count_rules() -> Vec<RewriteRule> {
        vec![
            rule(app("count", vec![int("0")]), app("count", vec![int("1")])),
            rule(app("count", vec![int("1")]), app("done", vec![])),
        ]
    }

    #[test]
    fn kstep_rule_set_has_one_clause_per_rule() {
        let (rs, report) = kstep_rule_set(&count_rules());
        assert_eq!(report.lowered, 2);
        assert_eq!(rs.n_clauses().unwrap(), 2);
    }

    #[test]
    fn single_step_is_a_membership_theorem() {
        let rules = count_rules();
        let (rs, _) = kstep_rule_set(&rules);
        let n = rs.n_clauses().unwrap();
        let s = prove_step(&rs, 0, n, &rules[0], &[]).unwrap();
        assert_genuine(&s.thm);
        // ⊢ KStep ⌜count(0)⌝ ⌜count(1)⌝.
        assert_eq!(s.thm.concl(), &kstep_prop(&rs, &s.from, &s.to).unwrap());
        assert_eq!(s.from, encode_pattern(&rules[0].lhs).unwrap());
        assert_eq!(s.to, encode_pattern(&rules[0].rhs).unwrap());
    }

    #[test]
    fn reflexive_reduces() {
        let (step_rs, _) = kstep_rule_set(&count_rules());
        let reduces_rs = kreduces_rule_set(step_rs);
        let t = encode_pattern(&app("done", vec![])).unwrap();
        let thm = prove_refl(&reduces_rs, &t).unwrap();
        assert_genuine(&thm);
        assert_eq!(thm.concl(), &kreduces_prop(&reduces_rs, &t, &t).unwrap());
    }

    /// The F2 headline: two single steps compose into a multi-step
    /// `⊢ KReduces ⌜count(0)⌝ ⌜done⌝`.
    #[test]
    fn multi_step_reduces_end_to_end() {
        let rules = count_rules();
        let (step_rs, _) = kstep_rule_set(&rules);
        let n = step_rs.n_clauses().unwrap();

        let s0 = prove_step(&step_rs, 0, n, &rules[0], &[]).unwrap(); // count(0) → count(1)
        let s1 = prove_step(&step_rs, 1, n, &rules[1], &[]).unwrap(); // count(1) → done
        let start = s0.from.clone();
        let end = s1.to.clone();

        let reduces_rs = kreduces_rule_set(step_rs);
        let thm = prove_reduces(&reduces_rs, vec![s0, s1], &start).unwrap();
        assert_genuine(&thm);
        assert_eq!(
            thm.concl(),
            &kreduces_prop(&reduces_rs, &start, &end).unwrap()
        );
    }

    #[test]
    fn parametric_rule_reduces_at_an_instance() {
        // rule loop(N) => done, fired at N := 7, then Reduces loop(7) done.
        let r = rule(app("loop", vec![evar("N")]), app("done", vec![]));
        let (step_rs, _) = kstep_rule_set(std::slice::from_ref(&r));
        let n = step_rs.n_clauses().unwrap();
        let seven = encode_pattern(&int("7")).unwrap();
        let s = prove_step(&step_rs, 0, n, &r, &[seven]).unwrap();
        assert_eq!(
            s.from,
            encode_pattern(&app("loop", vec![int("7")])).unwrap()
        );

        let start = s.from.clone();
        let end = s.to.clone();
        let reduces_rs = kreduces_rule_set(step_rs);
        let thm = prove_reduces(&reduces_rs, vec![s], &start).unwrap();
        assert_genuine(&thm);
        assert_eq!(
            thm.concl(),
            &kreduces_prop(&reduces_rs, &start, &end).unwrap()
        );
    }

    fn evar(id: &str) -> Pattern {
        Pattern::EVar(id.into(), Sort::App("SortInt".into(), vec![]))
    }

    #[test]
    fn conditional_rule_is_skipped() {
        let mut r = rule(app("count", vec![evar("N")]), app("done", vec![]));
        r.requires = Some(Pattern::Top(Sort::App("SortBool".into(), vec![])));
        let (rs, report) = kstep_rule_set(&[r]);
        assert_eq!(report.lowered, 0);
        assert_eq!(report.skipped, 1);
        assert_eq!(rs.n_clauses().unwrap(), 0);
    }
}
