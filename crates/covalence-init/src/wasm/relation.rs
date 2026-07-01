//! **SpecTec relation → `Derivable_R`** — lower a `SpecTecDef::Rel` (an
//! inductive judgement: `⊢ instr : functype`, `s;f;e ↪ s';f';e'`, …) into a
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
//! over the reified carrier `Φ = nat` ([`super::encode`]): the conclusion and
//! each (same-relation) premise are [`encode_exp`]-ed, and the rule's
//! metavariables `x…` are the universally-quantified `nat` leaves. Derivability
//! is then the impredicative predicate the engine builds, and a concrete
//! judgement is a value `⊢ Derivable_R ⌜J⌝` — pure syntactic data, oracle-free,
//! kernel-checked at every step.
//!
//! ## Scope (phase 1)
//!
//! Only **premises that recurse into the same relation** (`SpecTecPrem::Rule`
//! with this relation's name) are lowered — the inductive core. Side-condition
//! (`if`/`let`) and cross-relation premises, and iterated (`…*`) premises, are
//! rejected for now (see `SKELETONS.md`); a rule that uses them contributes no
//! clause path yet.

use covalence_core::{Error, Result, Term, Thm};
use covalence_spectec::ast::{SpecTecDef, SpecTecPrem, SpecTecRule};

use super::encode::{collect_metavars, encode_exp, metavar_name, phi};
use crate::init::ext::TermExt;
use crate::metalogic::{self, RuleSet};

/// One lowered rule: its conclusion/premise expressions plus the metavariable
/// order its clause quantifies over (also the `all_elim` order for [`derive`]).
struct LoweredRule {
    /// Metavariables, in universal-quantifier / instantiation order.
    metavars: Vec<String>,
    /// Encoded premise judgements `⌜premᵢ⌝` (same-relation, in order).
    premises: Vec<Term>,
    /// Encoded conclusion judgement `⌜concl⌝`.
    concl: Term,
}

fn lower_err(msg: impl Into<String>) -> Error {
    Error::ConnectiveRule(format!("spectec relation: {}", msg.into()))
}

/// Lower one SpecTec rule of relation `rel_name` into premise/conclusion terms
/// and its metavariable order.
fn lower_rule(rel_name: &str, rule: &SpecTecRule) -> Result<LoweredRule> {
    let SpecTecRule::Rule { x, e, prs, .. } = rule;

    let concl = encode_exp(e)?;

    let mut metavars = Vec::new();
    collect_metavars(e, &mut metavars);

    let mut premises = Vec::new();
    for pr in prs {
        match pr {
            SpecTecPrem::Rule {
                x: pr_rel, e: pr_e, ..
            } if pr_rel == rel_name => {
                collect_metavars(pr_e, &mut metavars);
                premises.push(encode_exp(pr_e)?);
            }
            SpecTecPrem::Rule { x: pr_rel, .. } => {
                return Err(lower_err(format!(
                    "rule `{x}`: cross-relation premise `{pr_rel}` not supported yet"
                )));
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

/// Lower every rule of a relation. Returns the ordered lowered rules (clause
/// order = rule order in the definition).
fn lower_relation(def: &SpecTecDef) -> Result<Vec<LoweredRule>> {
    let SpecTecDef::Rel { x, rules, .. } = def else {
        return Err(lower_err("definition is not a `rel`"));
    };
    rules.iter().map(|r| lower_rule(x, r)).collect()
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

/// The relation's [`RuleSet`] over `Φ = nat`: one clause per rule.
///
/// `def` must be a [`SpecTecDef::Rel`]; the rules are lowered eagerly (so a
/// lowering error surfaces here, not mid-derivation).
pub fn rule_set(def: &SpecTecDef) -> Result<RuleSet<'static>> {
    let rules = lower_relation(def)?;
    Ok(RuleSet::new(phi(), move |d_apply| {
        rules.iter().map(|r| clause_of(r, d_apply)).collect()
    }))
}

/// `Derivable_R ⌜J⌝ := ∀d. Closed_R d ⟹ d ⌜J⌝` for a judgement `J` already
/// encoded to a `Φ = nat` term.
pub fn derivable(rs: &RuleSet, judgement: &Term) -> Result<Term> {
    metalogic::derivable(rs, judgement)
}

/// **Apply rule `rule_idx`** of the relation: instantiate its metavariables with
/// `args` (in the rule's quantifier order) and discharge its premises with the
/// supplied derivations, yielding `⊢ Derivable_R ⌜concl[args]⌝`.
///
/// `n_rules` is the clause count of `rs` (`rs.n_clauses()?`); `args` must have
/// exactly one entry per metavariable of rule `rule_idx`, and `premise_ders`
/// one `⊢ Derivable_R ⌜premᵢ[args]⌝` per premise, in order. The kernel re-checks
/// every instantiation and `imp_elim`, so a wrong arg/premise fails to build
/// rather than fabricating a derivation.
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
        // Turn each premise derivation `⊢ Derivable_R ⌜p⌝` into `d ⌜p⌝` under the
        // assumed `Closed_R d`, then discharge the clause's antecedents in order.
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
    use covalence_spectec::ast::{MixOp, SpecTecArg, SpecTecExp, SpecTecRule};

    fn var(id: &str) -> SpecTecExp {
        SpecTecExp::Var { id: id.into() }
    }

    /// A tiny inductive relation, built as AST directly (the same shape
    /// `covalence_spectec::parse::parse_defs` yields from S-expressions):
    ///
    /// ```text
    ///   relation Even:
    ///     rule z:                       Even (zero)
    ///     rule ss:  Even n  ⟹  Even (succ (succ n))
    /// ```
    ///
    /// `zero`/`succ` are case constructors; `n` is the rule metavariable.
    fn even_relation() -> SpecTecDef {
        let mixop = |s: &str| MixOp::new(vec![s.to_string()]);
        let zero = SpecTecExp::Case {
            op: mixop("zero"),
            e1: Box::new(SpecTecExp::Opt { eo: None }),
        };
        let succ = |inner: SpecTecExp| SpecTecExp::Case {
            op: mixop("succ"),
            e1: Box::new(inner),
        };
        // Even applied to its argument = a `call`-style judgement head.
        let even = |arg: SpecTecExp| SpecTecExp::Call {
            x: "Even".into(),
            as1: vec![SpecTecArg::Exp { e: arg }],
        };

        let rule_z = SpecTecRule::Rule {
            x: "z".into(),
            ps: vec![],
            op: mixop("Even"),
            e: even(zero.clone()),
            prs: vec![],
        };
        let rule_ss = SpecTecRule::Rule {
            x: "ss".into(),
            ps: vec![],
            op: mixop("Even"),
            e: even(succ(succ(var("n")))),
            prs: vec![SpecTecPrem::Rule {
                x: "Even".into(),
                as1: vec![],
                op: mixop("Even"),
                e: even(var("n")),
            }],
        };
        SpecTecDef::Rel {
            x: "Even".into(),
            ps: vec![],
            op: mixop("Even"),
            t: covalence_spectec::ast::SpecTecTyp::Bool,
            rules: vec![rule_z, rule_ss],
        }
    }

    fn assert_genuine(thm: &Thm) {
        assert!(thm.hyps().is_empty(), "hypothesis-free");
        assert!(thm.has_no_obs(), "oracle-free");
    }

    #[test]
    fn rule_set_has_one_clause_per_rule() {
        let rs = rule_set(&even_relation()).unwrap();
        assert_eq!(rs.n_clauses().unwrap(), 2);
    }

    /// Derive `Even (succ (succ zero))` purely: axiom `z`, then rule `ss`
    /// applied at `n := zero`, and project nothing — the derivation is the
    /// syntactic witness `⊢ Derivable_Even ⌜Even (succ² zero)⌝`.
    #[test]
    fn derive_even_two() {
        let def = even_relation();
        let rs = rule_set(&def).unwrap();
        let n = rs.n_clauses().unwrap();

        // Encoded pieces we will reference.
        let mixop = |s: &str| MixOp::new(vec![s.to_string()]);
        let zero = SpecTecExp::Case {
            op: mixop("zero"),
            e1: Box::new(SpecTecExp::Opt { eo: None }),
        };
        let succ = |inner: SpecTecExp| SpecTecExp::Case {
            op: mixop("succ"),
            e1: Box::new(inner),
        };
        let even = |arg: SpecTecExp| SpecTecExp::Call {
            x: "Even".into(),
            as1: vec![SpecTecArg::Exp { e: arg }],
        };

        // rule z (index 0), no metavars, no premises: ⊢ Derivable_Even ⌜Even zero⌝
        let der_zero = derive(&rs, 0, n, &[], vec![]).unwrap();
        assert_genuine(&der_zero);
        assert_eq!(
            der_zero.concl(),
            &derivable(&rs, &encode_exp(&even(zero.clone())).unwrap()).unwrap()
        );

        // rule ss (index 1) at n := zero, discharging the premise with der_zero.
        let arg_zero = encode_exp(&zero).unwrap();
        let der_two = derive(&rs, 1, n, &[arg_zero], vec![der_zero]).unwrap();
        assert_genuine(&der_two);
        assert_eq!(
            der_two.concl(),
            &derivable(&rs, &encode_exp(&even(succ(succ(zero)))).unwrap()).unwrap()
        );
    }

    #[test]
    fn unsupported_premise_errors_at_lowering() {
        let mixop = |s: &str| MixOp::new(vec![s.to_string()]);
        let def = SpecTecDef::Rel {
            x: "R".into(),
            ps: vec![],
            op: mixop("R"),
            t: covalence_spectec::ast::SpecTecTyp::Bool,
            rules: vec![SpecTecRule::Rule {
                x: "bad".into(),
                ps: vec![],
                op: mixop("R"),
                e: var("x"),
                prs: vec![SpecTecPrem::If { e: var("x") }],
            }],
        };
        assert!(rule_set(&def).is_err());
    }
}
