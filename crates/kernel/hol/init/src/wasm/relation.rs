//! **SpecTec relation → `Derivable_R`** — lower `SpecTecDef::Rel` inductive
//! judgements (`⊢ instr : functype`, `s;f;e ↪ s';f';e'`, …) into a
//! [`crate::metalogic::RuleSet`] and drive it with the generic engine.
//!
//! This is the SpecTec analogue of [`crate::metalogic::toy`] — but *data-driven*
//! from a parsed relation instead of hand-written. Each [`SpecTecRule`] becomes
//! one closure clause
//!
//! ```text
//!   ∀ x…. d ⌜prem₀⌝ ⟹ … ⟹ d ⌜premₖ⌝ ⟹ d ⌜concl⌝
//! ```
//!
//! over the reified carrier `Φ = nat` ([`super::encode`]). Every judgement is
//! [`encode::tag`](crate::wasm::encode::tag)-ged with its **relation name**, so one rule set can mix many
//! mutually-referential relations and a cross-relation premise `R'(e)` is just
//! `d (rel.R' ⌜e⌝)` under the same `d`. A concrete judgement derivation is a value
//! `⊢ Derivable ⌜J⌝` — pure syntactic data, oracle-free, kernel-checked.
//!
//! ## Two entry points
//!
//! - [`rule_set`] — one relation, **all** its rules (errors if any rule can't be
//!   lowered): the "is this whole relation expressible" view. [`fn@derive`] applies
//!   a rule of it.
//! - [`spec_rule_set`] — a whole set of definitions (the real WASM spec), one
//!   combined rule set over every relation's rules, **skipping** rules it can't
//!   lower yet and reporting what it dropped ([`LoweringReport`]). Sound (fewer
//!   rules ⟹ fewer derivable judgements), incomplete — the honest way to grow
//!   coverage against the real spec.
//!
//! ## Not lowered yet (see `SKELETONS.md`)
//!
//! Side-condition (`if`/`let`) premises need the denotational leg (functions);
//! iterated (`…*`) premises need list recursion. Rules using them are rejected
//! ([`rule_set`]) / skipped ([`spec_rule_set`]).

use std::collections::BTreeMap;

use covalence_core::{Error, Result, Term, Thm};
use covalence_spectec::ast::{SpecTecDef, SpecTecPrem, SpecTecRule};

use super::encode::{collect_metavars, encode_exp, metavar_name, phi, tag};
use crate::init::ext::TermExt;
use crate::metalogic::{self, RuleSet};

/// One lowered rule: its relation-tagged conclusion/premise judgements plus the
/// metavariable order its clause quantifies over (also the `all_elim` order for
/// [`derive`]).
struct LoweredRule {
    /// Metavariables, in universal-quantifier / instantiation order.
    metavars: Vec<String>,
    /// Encoded, relation-tagged premise judgements (in order).
    premises: Vec<Term>,
    /// Encoded, relation-tagged conclusion judgement.
    concl: Term,
}

fn lower_err(msg: impl Into<String>) -> Error {
    Error::ConnectiveRule(format!("spectec relation: {}", msg.into()))
}

/// The relation-tagged encoding of a judgement `R(e)`.
fn judgement(rel: &str, e: &covalence_spectec::ast::SpecTecExp) -> Result<Term> {
    tag(rel, encode_exp(e)?)
}

/// Lower one SpecTec rule of relation `rel_name` into tagged premise/conclusion
/// terms and its metavariable order. Errors if a premise form isn't supported.
fn lower_rule(rel_name: &str, rule: &SpecTecRule) -> Result<LoweredRule> {
    let SpecTecRule::Rule { x, e, prs, .. } = rule;

    let concl = judgement(rel_name, e)?;

    let mut metavars = Vec::new();
    collect_metavars(e, &mut metavars);

    let mut premises = Vec::new();
    for pr in prs {
        match pr {
            // Any-relation inductive premise `R'(e')` — same `d`, tag `R'`.
            SpecTecPrem::Rule {
                x: pr_rel, e: pr_e, ..
            } => {
                collect_metavars(pr_e, &mut metavars);
                premises.push(judgement(pr_rel, pr_e)?);
            }
            SpecTecPrem::If { .. } | SpecTecPrem::Let { .. } => {
                return Err(lower_err(format!(
                    "rule `{x}`: side-condition premise not supported yet"
                )));
            }
            SpecTecPrem::Else | SpecTecPrem::Iter { .. } => {
                return Err(lower_err(format!(
                    "rule `{x}`: else/iterated premise not supported yet"
                )));
            }
        }
    }

    Ok(LoweredRule {
        metavars,
        premises,
        concl,
    })
}

/// Build a clause `∀ x…. d ⌜prem₀⌝ ⟹ … ⟹ d ⌜concl⌝` from a lowered rule, using
/// the engine-supplied `d_apply` for every `d ⌜·⌝` position.
fn clause_of(rule: &LoweredRule, d_apply: &dyn Fn(&Term) -> Result<Term>) -> Result<Term> {
    // body = d ⌜concl⌝, then fold premises in reverse as antecedents.
    let mut body = d_apply(&rule.concl)?;
    for prem in rule.premises.iter().rev() {
        body = d_apply(prem)?.imp(body)?;
    }
    // quantify metavars outermost-first (metavars[0] binds outermost). The
    // bound name is the *mangled* leaf `st$v$<id>` the encoder emits.
    for mv in rule.metavars.iter().rev() {
        body = body.forall(&metavar_name(mv), phi())?;
    }
    Ok(body)
}

/// Flatten `rec` groups: yield every `Rel` definition in `defs`.
fn relations(defs: &[SpecTecDef]) -> Vec<&SpecTecDef> {
    let mut out = Vec::new();
    fn go<'a>(d: &'a SpecTecDef, out: &mut Vec<&'a SpecTecDef>) {
        match d {
            SpecTecDef::Rel { .. } => out.push(d),
            SpecTecDef::Rec { ds } => ds.iter().for_each(|x| go(x, out)),
            _ => {}
        }
    }
    defs.iter().for_each(|d| go(d, &mut out));
    out
}

/// A [`RuleSet`] from an explicit list of lowered rules.
fn rule_set_of(rules: Vec<LoweredRule>) -> RuleSet<'static> {
    RuleSet::new(phi(), move |d_apply| {
        rules.iter().map(|r| clause_of(r, d_apply)).collect()
    })
}

/// The rule set of a **single** relation: one clause per rule, in rule order.
///
/// `def` must be a [`SpecTecDef::Rel`]; errors if *any* rule can't be lowered
/// (the "whole relation expressible" view). Clause `i` = rule `i`, so [`fn@derive`]
/// can address rules by their definition index.
pub fn rule_set(def: &SpecTecDef) -> Result<RuleSet<'static>> {
    let SpecTecDef::Rel { x, rules, .. } = def else {
        return Err(lower_err("definition is not a `rel`"));
    };
    let lowered = rules
        .iter()
        .map(|r| lower_rule(x, r))
        .collect::<Result<Vec<_>>>()?;
    Ok(rule_set_of(lowered))
}

/// What [`spec_rule_set`] lowered and what it skipped.
#[derive(Debug, Default, Clone)]
pub struct LoweringReport {
    /// Rules successfully lowered into clauses.
    pub lowered: usize,
    /// Rules skipped (couldn't be lowered yet).
    pub skipped: usize,
    /// Skip reasons, bucketed (message tail → count).
    pub skips: BTreeMap<String, usize>,
}

/// One **combined** rule set over *every* relation's rules in `defs` (the real
/// WASM spec), skipping rules that can't be lowered yet.
///
/// Sound but incomplete: skipped rules simply don't contribute clauses, so fewer
/// judgements are derivable — never more. The [`LoweringReport`] records exactly
/// what was dropped and why (no silent truncation). Clause order follows the
/// flattened relation/rule order over the *lowered* rules only.
pub fn spec_rule_set(defs: &[SpecTecDef]) -> (RuleSet<'static>, LoweringReport) {
    let mut lowered = Vec::new();
    let mut report = LoweringReport::default();
    for def in relations(defs) {
        let SpecTecDef::Rel { x, rules, .. } = def else {
            unreachable!()
        };
        for rule in rules {
            match lower_rule(x, rule) {
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
    }
    (rule_set_of(lowered), report)
}

/// `Derivable ⌜J⌝ := ∀d. Closed d ⟹ d ⌜J⌝` for a judgement `J` already encoded
/// (and relation-tagged) to a `Φ = nat` term. Build one with `judgement` /
/// [`super::encode::tag`].
pub fn derivable(rs: &RuleSet, judgement: &Term) -> Result<Term> {
    metalogic::derivable(rs, judgement)
}

/// **Apply rule `rule_idx`** of a rule set: instantiate its metavariables with
/// `args` (in the rule's quantifier order) and discharge its premises with the
/// supplied derivations, yielding `⊢ Derivable ⌜concl[args]⌝`.
///
/// `n_rules` is the clause count of `rs` (`rs.n_clauses()?`); `args` must have
/// exactly one entry per metavariable of rule `rule_idx`, and `premise_ders` one
/// `⊢ Derivable ⌜premᵢ[args]⌝` per premise, in order. The kernel re-checks every
/// instantiation and `imp_elim`, so a wrong arg/premise fails to build rather
/// than fabricating a derivation.
pub fn derive(
    rs: &RuleSet,
    rule_idx: usize,
    n_rules: usize,
    args: &[Term],
    premise_ders: Vec<Thm>,
) -> Result<Thm> {
    metalogic::derive_via_closed(rs, |assumed, _d_apply| {
        // The instantiated clause: peel the metavar `∀`s with the given args.
        let mut clause = metalogic::nth_conjunct(assumed.clone(), rule_idx, n_rules)?;
        for a in args {
            clause = clause.all_elim(a.clone())?;
        }
        // Turn each premise derivation `⊢ Derivable ⌜p⌝` into `d ⌜p⌝` under the
        // assumed `Closed d`, then discharge the clause's antecedents in order.
        for der in premise_ders {
            let d_p = der.all_elim(rs.d_var())?.imp_elim(assumed.clone())?;
            clause = clause.imp_elim(d_p)?;
        }
        Ok(clause)
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_spectec::ast::{MixOp, SpecTecExp, SpecTecRule, SpecTecTyp};

    fn var(id: &str) -> SpecTecExp {
        SpecTecExp::Var { id: id.into() }
    }
    fn mixop(s: &str) -> MixOp {
        MixOp::new(vec![s.to_string()])
    }
    fn zero() -> SpecTecExp {
        SpecTecExp::Case {
            op: mixop("zero"),
            e1: Box::new(SpecTecExp::Opt { eo: None }),
        }
    }
    fn succ(inner: SpecTecExp) -> SpecTecExp {
        SpecTecExp::Case {
            op: mixop("succ"),
            e1: Box::new(inner),
        }
    }

    /// A tiny inductive relation (built as AST directly — the same shape
    /// `covalence_spectec::parse::parse_defs` yields):
    ///
    /// ```text
    ///   relation Even:
    ///     rule z:                Even zero
    ///     rule ss:  Even n  ⟹  Even (succ (succ n))
    /// ```
    ///
    /// The relation identity comes from the `Rel` wrapper (the [`tag`]); the
    /// conclusion expression is just the argument.
    fn even_relation() -> SpecTecDef {
        let rule_z = SpecTecRule::Rule {
            x: "z".into(),
            ps: vec![],
            op: mixop("Even"),
            e: zero(),
            prs: vec![],
        };
        let rule_ss = SpecTecRule::Rule {
            x: "ss".into(),
            ps: vec![],
            op: mixop("Even"),
            e: succ(succ(var("n"))),
            prs: vec![SpecTecPrem::Rule {
                x: "Even".into(),
                as1: vec![],
                op: mixop("Even"),
                e: var("n"),
            }],
        };
        SpecTecDef::Rel {
            x: "Even".into(),
            ps: vec![],
            op: mixop("Even"),
            t: SpecTecTyp::Bool,
            rules: vec![rule_z, rule_ss],
        }
    }

    fn assert_genuine(thm: &Thm) {
        assert!(thm.hyps().is_empty(), "hypothesis-free");
    }

    #[test]
    fn rule_set_has_one_clause_per_rule() {
        let rs = rule_set(&even_relation()).unwrap();
        assert_eq!(rs.n_clauses().unwrap(), 2);
    }

    /// Derive `Even (succ (succ zero))` purely: axiom `z`, then rule `ss` at
    /// `n := zero` discharging the `Even n` premise. The witness is the tagged
    /// judgement `⊢ Derivable ⌜rel.Even (succ² zero)⌝`.
    #[test]
    fn derive_even_two() {
        let def = even_relation();
        let rs = rule_set(&def).unwrap();
        let n = rs.n_clauses().unwrap();

        // rule z (index 0): ⊢ Derivable ⌜rel.Even zero⌝
        let der_zero = derive(&rs, 0, n, &[], vec![]).unwrap();
        assert_genuine(&der_zero);
        assert_eq!(
            der_zero.concl(),
            &derivable(&rs, &judgement("Even", &zero()).unwrap()).unwrap()
        );

        // rule ss (index 1) at n := zero, premise discharged by der_zero.
        let arg_zero = encode_exp(&zero()).unwrap();
        let der_two = derive(&rs, 1, n, &[arg_zero], vec![der_zero]).unwrap();
        assert_genuine(&der_two);
        assert_eq!(
            der_two.concl(),
            &derivable(&rs, &judgement("Even", &succ(succ(zero()))).unwrap()).unwrap()
        );
    }

    /// A cross-relation premise now lowers: a second relation `Pos` whose rule
    /// references `Even`. `spec_rule_set` combines both into one rule set.
    #[test]
    fn cross_relation_premise_lowers() {
        let even = even_relation();
        let pos = SpecTecDef::Rel {
            x: "Pos".into(),
            ps: vec![],
            op: mixop("Pos"),
            t: SpecTecTyp::Bool,
            rules: vec![SpecTecRule::Rule {
                x: "p".into(),
                ps: vec![],
                op: mixop("Pos"),
                e: succ(var("n")),
                // premise references the OTHER relation Even.
                prs: vec![SpecTecPrem::Rule {
                    x: "Even".into(),
                    as1: vec![],
                    op: mixop("Even"),
                    e: var("n"),
                }],
            }],
        };
        let (rs, report) = spec_rule_set(&[even, pos]);
        assert_eq!(report.skipped, 0);
        assert_eq!(report.lowered, 3); // 2 Even + 1 Pos
        assert_eq!(rs.n_clauses().unwrap(), 3);
    }

    /// `spec_rule_set` skips (not fails on) an unsupported rule, and reports it.
    #[test]
    fn spec_rule_set_skips_and_reports() {
        let def = SpecTecDef::Rel {
            x: "R".into(),
            ps: vec![],
            op: mixop("R"),
            t: SpecTecTyp::Bool,
            rules: vec![
                SpecTecRule::Rule {
                    x: "ok".into(),
                    ps: vec![],
                    op: mixop("R"),
                    e: zero(),
                    prs: vec![],
                },
                SpecTecRule::Rule {
                    x: "bad".into(),
                    ps: vec![],
                    op: mixop("R"),
                    e: var("x"),
                    prs: vec![SpecTecPrem::If { e: var("x") }],
                },
            ],
        };
        let (rs, report) = spec_rule_set(&[def]);
        assert_eq!(report.lowered, 1);
        assert_eq!(report.skipped, 1);
        assert_eq!(rs.n_clauses().unwrap(), 1);
    }
}
