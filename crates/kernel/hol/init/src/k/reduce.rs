//! **KORE rewrite rule → `Derivable_Step`** — lower the [`RewriteRule`]s a
//! [`covalence_k`] frontend extracts from a kompiled definition into a
//! [`crate::metalogic::RuleSet`] and drive it with the generic engine.
//!
//! This is the K analogue of [`crate::wasm::relation`]. Where SpecTec lowers an
//! *inductive judgement* `R(e)`, K lowers a *rewrite rule* `LHS => RHS`: the
//! single-step transition relation `Step`. Each rule becomes one clause
//!
//! ```text
//!   ∀ x…. d ⌜Step(LHS, RHS)⌝
//! ```
//!
//! over the reified carrier `Φ = nat` ([`super::encode`]), where `x…` are the
//! rule's element variables. A concrete reduction step is then a value
//! `⊢ Derivable_KStep ⌜Step(cfg, cfg')⌝` — pure syntactic data, oracle-free,
//! kernel-checked, built by instantiating the clause's metavariables with the
//! matched subterms (the "construct, don't trust" discipline: a K/LLVM engine can
//! *find* the redex and substitution; the kernel re-checks the instance).
//!
//! ## What "F0" means here
//!
//! F0 = **unconditional (ground-ish) rewriting**. A rule's `requires`/`ensures`
//! side conditions and its rule-`priority`/`owise` ordering are *not* modelled:
//! [`rule_set`] lowers only rules with no `requires` (a conditional rule needs
//! the hooked-`Bool` theory — F1; see `notes/design/k-frontend.md`). Multi-step
//! reduction `A →* B` is a *chain* of these single steps; the reflexive-transitive
//! closure relation is a later slice (see the generated open-work index).
//!
//! ## Reachability, not equality
//!
//! `Step` is a genuine binary *relation*, not an equation: a configuration
//! *steps to* another, it is not equal to it. So K reduction lowers through the
//! `Derivable_R` engine (like SpecTec reduction rules), **not** the equational
//! `⊢ from = to` route the `/lisp` reducer uses.

use std::collections::BTreeMap;

use covalence_core::{Error, Result, Term};
use covalence_hol_eval::EvalThm as Thm;
use covalence_k::ast::Definition;
use covalence_k::fragment::{RewriteRule, rewrite_rules};

use super::encode::{collect_metavars, encode_pattern, metavar_name, phi, step_body, tag};
use crate::init::ext::TermExt;
use crate::metalogic::{self, RuleSet};

/// The relation name every K single-step judgement is tagged with.
pub const STEP_REL: &str = "Step";

/// One lowered rewrite rule: its element-variable order (the `∀`/instantiation
/// order) and its encoded, `Step`-tagged conclusion judgement.
struct LoweredRule {
    /// Element variables, in universal-quantifier / instantiation order.
    metavars: Vec<String>,
    /// Encoded, relation-tagged `Step(LHS, RHS)` conclusion.
    concl: Term,
}

fn lower_err(msg: impl Into<String>) -> Error {
    Error::ConnectiveRule(format!("k relation: {}", msg.into()))
}

/// The `Step`-tagged encoding of a rewrite rule's `LHS => RHS`.
fn step_judgement(rule: &RewriteRule) -> Result<Term> {
    tag(STEP_REL, step_body(&rule.lhs, &rule.rhs)?)
}

/// Lower one **unconditional** rewrite rule into its `Step` conclusion and
/// element-variable order. Errors if the rule carries a `requires` side
/// condition (F1) — the caller decides whether to fail or skip.
fn lower_rule(rule: &RewriteRule) -> Result<LoweredRule> {
    if rule.requires.is_some() {
        return Err(lower_err(
            "rule has a `requires` side condition (needs the F1 hooked-Bool theory)",
        ));
    }
    let concl = step_judgement(rule)?;
    let mut metavars = Vec::new();
    collect_metavars(&rule.lhs, &mut metavars);
    collect_metavars(&rule.rhs, &mut metavars);
    Ok(LoweredRule { metavars, concl })
}

/// Build a clause `∀ x…. d ⌜Step(LHS, RHS)⌝` from a lowered rule, using the
/// engine-supplied `d_apply` for the `d ⌜·⌝` position.
fn clause_of(rule: &LoweredRule, d_apply: &dyn Fn(&Term) -> Result<Term>) -> Result<Term> {
    // body = d ⌜concl⌝ (F0 rules are premise-free); quantify metavars
    // outermost-first (metavars[0] binds outermost — matches the `all_elim`
    // order in `derive`). The bound name is the mangled leaf `k$v$<id>`.
    let mut body = d_apply(&rule.concl)?;
    for mv in rule.metavars.iter().rev() {
        body = body.forall(&metavar_name(mv), phi())?;
    }
    Ok(body)
}

/// A [`RuleSet`] from an explicit list of lowered rules.
fn rule_set_of(rules: Vec<LoweredRule>) -> RuleSet<'static> {
    RuleSet::new(phi(), move |d_apply| {
        rules.iter().map(|r| clause_of(r, d_apply)).collect()
    })
}

/// What [`rule_set`] lowered and what it skipped.
#[derive(Debug, Default, Clone)]
pub struct LoweringReport {
    /// Rules successfully lowered into `Step` clauses.
    pub lowered: usize,
    /// Rules skipped (conditional / not F0-expressible yet).
    pub skipped: usize,
    /// Skip reasons, bucketed (message tail → count).
    pub skips: BTreeMap<String, usize>,
}

/// The **single-step `Step` rule set** of a KORE definition: one clause per
/// unconditional rewrite rule (in the order [`rewrite_rules`] yields them),
/// **skipping** conditional rules and reporting them.
///
/// Sound but incomplete: skipped rules simply don't contribute clauses, so fewer
/// steps are derivable — never more (no silent truncation; the [`LoweringReport`]
/// records what was dropped). Clause `i` addresses the `i`-th *lowered* rule, the
/// index [`derive`] and [`step`] take.
pub fn rule_set(def: &Definition) -> (RuleSet<'static>, LoweringReport) {
    rule_set_from(&rewrite_rules(def))
}

/// [`rule_set`] over an explicit slice of already-extracted rewrite rules —
/// useful when the caller has filtered/reordered them.
pub fn rule_set_from(rules: &[RewriteRule]) -> (RuleSet<'static>, LoweringReport) {
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
    (rule_set_of(lowered), report)
}

/// `Derivable_KStep ⌜J⌝ := ∀d. Closed d ⟹ d ⌜J⌝` for a `Step` judgement `J`
/// already encoded (and relation-tagged) to a `Φ = nat` term. Build `J` with
/// [`super::encode::step_body`] + [`super::encode::tag`], or read it off a
/// [`derive`]d theorem's conclusion.
pub fn derivable(rs: &RuleSet, judgement: &Term) -> Result<Term> {
    metalogic::derivable(rs, judgement)
}

/// **Fire rule `rule_idx`** of a single-step rule set at a concrete redex:
/// instantiate its element variables with `args` (in the rule's quantifier
/// order — the `metavars` first-seen order of LHS then RHS) and mint
///
/// ```text
///   ⊢ Derivable_KStep ⌜Step(LHS[args], RHS[args])⌝
/// ```
///
/// `n_rules` is the clause count (`rs.n_clauses()?`); `args` must have exactly
/// one encoded term per element variable of rule `rule_idx`. The kernel re-checks
/// every instantiation, so a wrong arg count/shape fails to build rather than
/// fabricating a step. F0 rules are premise-free, so there are no premises to
/// discharge.
pub fn derive(rs: &RuleSet, rule_idx: usize, n_rules: usize, args: &[Term]) -> Result<Thm> {
    metalogic::apply::derive_axiom_instance(rs, rule_idx, n_rules, args)
}

/// A single certified reduction step: the concrete `⊢ Derivable_KStep
/// ⌜Step(from, to)⌝` theorem plus its two endpoint terms (encoded).
pub struct StepThm {
    /// The redex configuration (encoded `Φ = nat` term).
    pub from: Term,
    /// The contractum configuration (encoded `Φ = nat` term).
    pub to: Term,
    /// `⊢ Derivable_KStep ⌜Step(from, to)⌝`.
    pub thm: Thm,
}

/// Fire rule `rule_idx` and package the endpoints alongside the theorem, so the
/// caller can chain steps (`to` of one = `from` of the next) without re-encoding.
///
/// `from_rule`/`to_rule` are the rule's LHS/RHS patterns (used only to recover
/// the instantiated endpoint terms by substituting `args` through their own
/// encoding); pass the same [`RewriteRule`] the clause was lowered from.
pub fn step(
    rs: &RuleSet,
    rule_idx: usize,
    n_rules: usize,
    rule: &RewriteRule,
    args: &[Term],
) -> Result<StepThm> {
    let thm = derive(rs, rule_idx, n_rules, args)?;
    let from = instantiate(&rule.lhs, rule, args)?;
    let to = instantiate(&rule.rhs, rule, args)?;
    Ok(StepThm { from, to, thm })
}

/// Recover the instantiated endpoint term `pat[args]` by substituting each of the
/// rule's element-variable leaves `k$v$<id>` with the corresponding `args[i]`,
/// in the same first-seen order the clause quantifies (LHS then RHS).
fn instantiate(pat: &covalence_k::ast::Pattern, rule: &RewriteRule, args: &[Term]) -> Result<Term> {
    let mut metavars = Vec::new();
    collect_metavars(&rule.lhs, &mut metavars);
    collect_metavars(&rule.rhs, &mut metavars);
    if args.len() != metavars.len() {
        return Err(lower_err(format!(
            "expected {} argument(s) for the rule's element variables, got {}",
            metavars.len(),
            args.len()
        )));
    }
    let mut t = encode_pattern(pat)?;
    for (mv, a) in metavars.iter().zip(args) {
        // Each element variable is the free leaf `k$v$<id> : nat`; substitute the
        // matched (already-encoded) argument for it.
        let var = covalence_core::Var::new(metavar_name(mv), phi());
        t = covalence_core::subst::subst_free(&t, &var, a);
    }
    Ok(t)
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_k::ast::{Pattern, Sort};
    use covalence_k::parse::parse_definition;

    fn assert_genuine(thm: &Thm) {
        assert!(
            thm.hyps().is_empty(),
            "K step derivation must be hypothesis-free"
        );
    }

    fn int(v: &str) -> Pattern {
        Pattern::DV(Sort::App("SortInt".into(), vec![]), v.into())
    }
    fn app(sym: &str, args: Vec<Pattern>) -> Pattern {
        Pattern::App {
            symbol: sym.into(),
            sorts: vec![],
            args,
        }
    }
    fn evar(id: &str) -> Pattern {
        Pattern::EVar(id.into(), Sort::App("SortInt".into(), vec![]))
    }

    /// Two unconditional rules, built directly:
    ///   rule count(0)   => done          (ground)
    ///   rule count(N)   => count(N)       (one metavariable N — a self-loop, just
    ///                                       to exercise instantiation)
    fn count_rules() -> Vec<RewriteRule> {
        let sort = Sort::App("SortCfg".into(), vec![]);
        let ground = RewriteRule {
            sort: sort.clone(),
            lhs: app("count", vec![int("0")]),
            rhs: app("done", vec![]),
            requires: None,
            ensures: None,
            priority: 50,
            label: Some("count-zero".into()),
            unique_id: None,
        };
        let stepn = RewriteRule {
            sort,
            lhs: app("count", vec![evar("N")]),
            rhs: app("count", vec![evar("N")]),
            requires: None,
            ensures: None,
            priority: 50,
            label: Some("count-loop".into()),
            unique_id: None,
        };
        vec![ground, stepn]
    }

    #[test]
    fn rule_set_has_one_clause_per_unconditional_rule() {
        let rules = count_rules();
        let (rs, report) = rule_set_from(&rules);
        assert_eq!(report.lowered, 2);
        assert_eq!(report.skipped, 0);
        assert_eq!(rs.n_clauses().unwrap(), 2);
    }

    #[test]
    fn ground_rule_mints_a_step() {
        let rules = count_rules();
        let (rs, _) = rule_set_from(&rules);
        let n = rs.n_clauses().unwrap();

        // rule 0 (count(0) => done): no element variables, no args.
        let s = step(&rs, 0, n, &rules[0], &[]).unwrap();
        assert_genuine(&s.thm);

        // The conclusion is exactly Derivable_KStep of the encoded Step(count(0), done).
        let want = derivable(&rs, &step_judgement(&rules[0]).unwrap()).unwrap();
        assert_eq!(s.thm.concl(), &want);
        // Endpoints are the encoded configs.
        assert_eq!(s.from, encode_pattern(&rules[0].lhs).unwrap());
        assert_eq!(s.to, encode_pattern(&rules[0].rhs).unwrap());
    }

    #[test]
    fn parametric_rule_instantiates_its_metavariable() {
        let rules = count_rules();
        let (rs, _) = rule_set_from(&rules);
        let n = rs.n_clauses().unwrap();

        // rule 1 (count(N) => count(N)) at N := 7.
        let seven = encode_pattern(&int("7")).unwrap();
        let s = step(&rs, 1, n, &rules[1], &[seven.clone()]).unwrap();
        assert_genuine(&s.thm);

        // Endpoints are count(7): the metavariable was substituted, not left free.
        let want_cfg = encode_pattern(&app("count", vec![int("7")])).unwrap();
        assert_eq!(s.from, want_cfg);
        assert_eq!(s.to, want_cfg);
        // The theorem's conclusion mentions no free `k$v$N` leaf any more.
        let concl = format!("{:?}", s.thm.concl());
        assert!(
            !concl.contains("k$v$N"),
            "metavariable should be instantiated"
        );
    }

    #[test]
    fn conditional_rule_is_skipped_and_reported() {
        let sort = Sort::App("SortCfg".into(), vec![]);
        let cond = RewriteRule {
            sort,
            lhs: app("count", vec![evar("N")]),
            rhs: app("done", vec![]),
            requires: Some(Pattern::Top(Sort::App("SortBool".into(), vec![]))),
            ensures: None,
            priority: 50,
            label: None,
            unique_id: None,
        };
        let (rs, report) = rule_set_from(&[cond]);
        assert_eq!(report.lowered, 0);
        assert_eq!(report.skipped, 1);
        assert_eq!(rs.n_clauses().unwrap(), 0);
    }

    /// End-to-end from textual KORE: parse a hand-written kompiled-style
    /// definition, extract its rewrite rules, lower to a `Step` rule set, and
    /// mint a concrete reduction step.
    #[test]
    fn from_textual_kore() {
        // One unconditional rewrite axiom: count(0) => done.
        let src = r#"
[]
module COUNTER
  axiom{} \rewrites{SortCfg{}}(
    Lblcount{}(\dv{SortInt{}}("0")),
    Lbldone{}()
  ) [label{}("COUNTER.count-zero")]
endmodule []
"#;
        let def = parse_definition(src).unwrap();
        let rules = rewrite_rules(&def);
        assert_eq!(rules.len(), 1);
        let (rs, report) = rule_set_from(&rules);
        assert_eq!(report.lowered, 1);
        let n = rs.n_clauses().unwrap();
        let s = step(&rs, 0, n, &rules[0], &[]).unwrap();
        assert_genuine(&s.thm);
        assert_eq!(
            s.thm.concl(),
            &derivable(&rs, &step_judgement(&rules[0]).unwrap()).unwrap()
        );
    }
}
