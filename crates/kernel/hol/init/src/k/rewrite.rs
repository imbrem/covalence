//! **High-level, K-shaped reducer** — lower a K definition's rewrite rules into
//! the reusable mid-level [`crate::metalogic::rewrite`] relation and *reduce K
//! programs*. This is the K instantiation of the layered stack
//! (`notes/vibes/k/reduction-demo-scope.md`): K-shaped API → `metalogic::rewrite`
//! → `metalogic::binary` → HOL-omega. Where [`super::relation`] hand-built the
//! `KStep`/`KReduces` relations, this delegates to the shared layer (which adds
//! generic congruence + a matcher + a driver), so a K program actually reduces:
//!
//! ```text
//!   ⊢ Reduces ⌜colorOf(Banana())⌝ ⌜Yellow()⌝        (K tutorial Lesson 1.2)
//!   ⊢ Reduces ⌜plus(s(s(z)), s(z))⌝ ⌜s(s(s(z)))⌝    (recursion + congruence)
//! ```
//!
//! Both **unconditional** and **conditional** (`requires`) rules are lowered: a
//! guarded rule fires only when its condition reduces to the truth constructor
//! (`true`/`tt`) in the unconditional stratum — the K Lesson 1.7 mechanism, done
//! hook-free (`⊢ Reduces ⌜max(1,2)⌝ ⌜2⌝` via a `leq` guard). Genuine builtin
//! hooks (`+Int`, `andBool`) remain F1. The reducer is the untrusted
//! construct-don't-trust driver; every `Reduces` witness is kernel-rechecked.

use std::collections::BTreeMap;

use covalence_computation::TransitionSystem;
use covalence_core::{Result, Term};
use covalence_hol_eval::EvalThm as Thm;
use covalence_k::fragment::RewriteRule;

use super::encode::{app_combinator, collect_metavars, encode_pattern, metavar_name, phi};
use crate::metalogic::rewrite::{Innermost, Matcher, RewriteRelation, Rule, StepThm};

/// The default truth constructor a `requires` condition must reduce to. K's
/// canonical `Bool` truth is `true`; the demos also use `tt`.
pub const DEFAULT_TRUTH: &str = "true";

/// What [`rewrite_relation`] lowered and skipped.
#[derive(Debug, Default, Clone)]
pub struct LoweringReport {
    pub lowered: usize,
    pub skipped: usize,
    /// How many of the lowered rules are conditional (`requires`).
    pub conditional: usize,
    pub skips: BTreeMap<String, usize>,
}

/// Lower a K `RewriteRule` into a mid-level [`Rule`] plus an optional encoded
/// guard (the `requires` condition). The rule's metavariables are collected from
/// LHS, RHS, **and** the guard (guard variables are bound by the LHS in K).
fn lower_rule(rule: &RewriteRule) -> Result<(Rule, Option<Term>)> {
    let mut raw = Vec::new();
    collect_metavars(&rule.lhs, &mut raw);
    collect_metavars(&rule.rhs, &mut raw);
    if let Some(req) = &rule.requires {
        collect_metavars(req, &mut raw);
    }
    let metavars = raw.into_iter().map(metavar_name).collect();
    let guard = rule.requires.as_ref().map(encode_pattern).transpose()?;
    Ok((
        Rule {
            metavars,
            lhs: encode_pattern(&rule.lhs)?,
            rhs: encode_pattern(&rule.rhs)?,
        },
        guard,
    ))
}

/// Build a [`RewriteRelation`] from a set of K rewrite rules, lowering
/// unconditional **and** conditional (`requires`) rules. A guarded rule fires
/// only when its condition reduces to `truth_sym()` in the unconditional stratum.
pub fn rewrite_relation(
    rules: &[RewriteRule],
    truth_sym: &str,
) -> (RewriteRelation, LoweringReport) {
    let mut lowered: Vec<(Rule, Option<Term>)> = Vec::new();
    let mut report = LoweringReport::default();
    for rule in rules {
        match lower_rule(rule) {
            Ok((r, guard)) => {
                report.lowered += 1;
                if guard.is_some() {
                    report.conditional += 1;
                }
                lowered.push((r, guard));
            }
            Err(e) => {
                report.skipped += 1;
                *report.skips.entry(e.to_string()).or_default() += 1;
            }
        }
    }
    let rel = if report.conditional == 0 {
        RewriteRelation::new(
            phi(),
            app_combinator(),
            lowered.into_iter().map(|(r, _)| r).collect(),
        )
    } else {
        // Truth constant = the encoded nullary constructor `truth_sym()`.
        let truth = encode_pattern(&covalence_k::ast::Pattern::App {
            symbol: truth_sym.into(),
            sorts: Vec::new(),
            args: Vec::new(),
        })
        .expect("nullary constructor encodes");
        RewriteRelation::with_guards(phi(), app_combinator(), lowered, truth)
    };
    (rel, report)
}

/// A K reducer over a fixed rule set: holds the lowered [`RewriteRelation`] and a
/// [`Matcher`], and reduces encoded K configurations. The K-shaped surface a
/// `KSession` (and a `/k` REPL) sits on.
pub struct KReducer {
    rel: RewriteRelation,
    matcher: Box<dyn Matcher>,
    report: LoweringReport,
}

impl KReducer {
    /// Build a reducer from K rewrite rules (leftmost-innermost matcher; `true`
    /// as the truth constructor for `requires` guards).
    pub fn new(rules: &[RewriteRule]) -> Self {
        Self::with_truth(rules, DEFAULT_TRUTH)
    }

    /// Build a reducer with an explicit truth constructor for `requires` guards
    /// (e.g. `"tt"` for a hand-written boolean language).
    pub fn with_truth(rules: &[RewriteRule], truth_sym: &str) -> Self {
        let (rel, report) = rewrite_relation(rules, truth_sym);
        KReducer {
            rel,
            matcher: Box::new(Innermost),
            report,
        }
    }

    /// Swap the redex-matching strategy.
    pub fn with_matcher(mut self, matcher: Box<dyn Matcher>) -> Self {
        self.matcher = matcher;
        self
    }

    /// The lowered relation (for stating props / advanced use).
    pub fn relation(&self) -> &RewriteRelation {
        &self.rel
    }

    /// What was lowered vs skipped.
    pub fn report(&self) -> &LoweringReport {
        &self.report
    }

    /// **Reduce** an encoded K configuration up to `fuel` steps:
    /// `(normal_form, ⊢ Reduces config normal_form)`.
    pub fn reduce(&self, config: &Term, fuel: usize) -> Result<(Term, Thm)> {
        self.rel.normalize(self.matcher.as_ref(), config, fuel)
    }

    /// Encode a KORE configuration pattern, then reduce it.
    pub fn reduce_pattern(
        &self,
        config: &covalence_k::ast::Pattern,
        fuel: usize,
    ) -> Result<(Term, Thm)> {
        let encoded = encode_pattern(config)?;
        self.reduce(&encoded, fuel)
    }

    /// Find and certify the next whole-configuration step.
    pub fn next_step(&self, config: &Term) -> Result<Option<StepThm>> {
        self.matcher
            .find(&self.rel, config)
            .map(|redex| self.rel.prove_step(config, &redex))
            .transpose()
    }
}

impl TransitionSystem for KReducer {
    type State = Term;
    type Outcome = Term;
    type Error = covalence_core::Error;

    fn halted(&self, state: &Term) -> Result<Option<Term>> {
        Ok(self
            .matcher
            .find(&self.rel, state)
            .is_none()
            .then(|| state.clone()))
    }

    fn transition(&self, state: Term) -> Result<Term> {
        self.next_step(&state)?
            .map(|step| step.to)
            .ok_or_else(|| covalence_core::Error::ConnectiveRule("k reducer is halted".into()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_computation::{Trace, trace};
    use covalence_k::ast::{Pattern, Sort};

    fn assert_genuine(thm: &Thm) {
        assert!(thm.hyps().is_empty(), "reduction must be hypothesis-free");
    }
    fn cfg() -> Sort {
        Sort::App("SortCfg".into(), vec![])
    }
    fn app(sym: &str, args: Vec<Pattern>) -> Pattern {
        Pattern::App {
            symbol: sym.into(),
            sorts: vec![],
            args,
        }
    }
    fn evar(id: &str) -> Pattern {
        Pattern::EVar(id.into(), cfg())
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

    /// K tutorial Lesson 1.2: colorOf(Banana()) => Yellow(), contentsOfJar(Jar(F)) => F.
    #[test]
    fn lesson_1_2_reduces() {
        let rules = vec![
            rule(
                app("colorOf", vec![app("Banana", vec![])]),
                app("Yellow", vec![]),
            ),
            rule(
                app("colorOf", vec![app("Blueberry", vec![])]),
                app("Blue", vec![]),
            ),
            rule(
                app("contentsOfJar", vec![app("Jar", vec![evar("F")])]),
                evar("F"),
            ),
        ];
        let k = KReducer::new(&rules);
        assert_eq!(k.report().lowered, 3);

        // colorOf(Banana()) →* Yellow()
        let (nf, thm) = k
            .reduce_pattern(&app("colorOf", vec![app("Banana", vec![])]), 20)
            .unwrap();
        assert_genuine(&thm);
        assert_eq!(nf, encode_pattern(&app("Yellow", vec![])).unwrap());
        assert_eq!(
            thm.concl(),
            &k.relation()
                .reduces_prop(
                    &encode_pattern(&app("colorOf", vec![app("Banana", vec![])])).unwrap(),
                    &nf
                )
                .unwrap()
        );

        // contentsOfJar(Jar(Apple())) →* Apple() (variable binding).
        let (nf2, thm2) = k
            .reduce_pattern(
                &app(
                    "contentsOfJar",
                    vec![app("Jar", vec![app("Apple", vec![])])],
                ),
                20,
            )
            .unwrap();
        assert_genuine(&thm2);
        assert_eq!(nf2, encode_pattern(&app("Apple", vec![])).unwrap());
    }

    #[test]
    fn generic_trace_agrees_with_certified_reduction() {
        let rules = vec![rule(
            app("colorOf", vec![app("Banana", vec![])]),
            app("Yellow", vec![]),
        )];
        let reducer = KReducer::new(&rules);
        let start = encode_pattern(&app("colorOf", vec![app("Banana", vec![])])).unwrap();
        let Trace {
            states,
            steps,
            outcome,
        } = trace(&reducer, start.clone(), 4).unwrap();
        let (normal_form, theorem) = reducer.reduce(&start, 4).unwrap();

        assert_eq!(steps, 1);
        assert_eq!(states.last(), Some(&normal_form));
        assert_eq!(outcome, Some(normal_form.clone()));
        assert_eq!(
            theorem.concl(),
            &reducer
                .relation()
                .reduces_prop(&start, &normal_form)
                .unwrap()
        );
    }

    /// PEANO recursion + congruence: plus(s(s(z)), s(z)) →* s(s(s(z))).
    #[test]
    fn peano_reduces() {
        let z = || app("z", vec![]);
        let s = |t: Pattern| app("s", vec![t]);
        let plus = |a: Pattern, b: Pattern| app("plus", vec![a, b]);
        let m = || evar("M");
        let n = || evar("N");
        let rules = vec![
            rule(plus(z(), n()), n()),
            rule(plus(s(m()), n()), s(plus(m(), n()))),
        ];
        let k = KReducer::new(&rules);
        let start = plus(s(s(z())), s(z()));
        let (nf, thm) = k.reduce_pattern(&start, 100).unwrap();
        assert_genuine(&thm);
        assert_eq!(nf, encode_pattern(&s(s(s(z())))).unwrap());
    }

    /// Conditional (`requires`) rules now lower as guarded rules, and fire only
    /// when the condition reduces to the truth constructor. `leq`/`max` demo.
    #[test]
    fn conditional_rules_fire_on_guard() {
        let s = |t: Pattern| app("s", vec![t]);
        let z = || app("z", vec![]);
        let leq = |a: Pattern, b: Pattern| app("leq", vec![a, b]);
        let m = || evar("M");
        let n = || evar("N");
        let mut rules = vec![
            rule(leq(z(), n()), app("tt", vec![])),
            rule(leq(s(m()), z()), app("ff", vec![])),
            rule(leq(s(m()), s(n())), leq(m(), n())),
            rule(app("max", vec![m(), n()]), n()),
            rule(app("max", vec![m(), n()]), m()),
        ];
        rules[3].requires = Some(leq(m(), n())); // max(M,N)=>N requires leq(M,N)
        rules[4].requires = Some(leq(n(), m())); // max(M,N)=>M requires leq(N,M)

        let k = KReducer::with_truth(&rules, "tt");
        assert_eq!(k.report().lowered, 5);
        assert_eq!(k.report().conditional, 2);

        // max(s(z), s(s(z))) →* s(s(z))
        let (nf, thm) = k
            .reduce_pattern(&app("max", vec![s(z()), s(s(z()))]), 1000)
            .unwrap();
        assert_genuine(&thm);
        assert_eq!(nf, encode_pattern(&s(s(z()))).unwrap());
    }
}
