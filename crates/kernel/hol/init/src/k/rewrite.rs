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
//! Only **unconditional** rules are lowered (conditional `requires` rules are the
//! F1 hooked-theory work — skipped + reported). The reducer is the untrusted
//! construct-don't-trust driver; every `Reduces` witness is kernel-rechecked.

use std::collections::BTreeMap;

use covalence_core::{Result, Term};
use covalence_hol_eval::EvalThm as Thm;
use covalence_k::fragment::RewriteRule;

use super::encode::{app_combinator, encode_pattern, metavar_name, phi, rule_metavars};
use crate::metalogic::rewrite::{Innermost, Matcher, RewriteRelation, Rule};

/// What [`lower_rules`] lowered and skipped (conditional rules).
#[derive(Debug, Default, Clone)]
pub struct LoweringReport {
    pub lowered: usize,
    pub skipped: usize,
    pub skips: BTreeMap<String, usize>,
}

/// Lower a K `RewriteRule` (KORE-extracted or `.k`-parsed) into a mid-level
/// [`Rule`]: encode LHS/RHS over the `Φ = nat` free algebra, with the element
/// variables (mangled `k$v$…` leaves) as metavariables.
fn lower_rule(rule: &RewriteRule) -> Result<Rule> {
    let metavars = rule_metavars(&rule.lhs, &rule.rhs)
        .into_iter()
        .map(metavar_name)
        .collect();
    Ok(Rule {
        metavars,
        lhs: encode_pattern(&rule.lhs)?,
        rhs: encode_pattern(&rule.rhs)?,
    })
}

/// Build a [`RewriteRelation`] from a set of K rewrite rules, lowering every
/// **unconditional** one (conditional rules are skipped + reported).
pub fn rewrite_relation(rules: &[RewriteRule]) -> (RewriteRelation, LoweringReport) {
    let mut lowered = Vec::new();
    let mut report = LoweringReport::default();
    for rule in rules {
        if rule.requires.is_some() {
            report.skipped += 1;
            *report
                .skips
                .entry("requires side condition (F1)".to_string())
                .or_default() += 1;
            continue;
        }
        match lower_rule(rule) {
            Ok(r) => {
                report.lowered += 1;
                lowered.push(r);
            }
            Err(e) => {
                report.skipped += 1;
                *report.skips.entry(e.to_string()).or_default() += 1;
            }
        }
    }
    (
        RewriteRelation::new(phi(), app_combinator(), lowered),
        report,
    )
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
    /// Build a reducer from K rewrite rules (leftmost-innermost matcher).
    pub fn new(rules: &[RewriteRule]) -> Self {
        let (rel, report) = rewrite_relation(rules);
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
}

#[cfg(test)]
mod tests {
    use super::*;
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

    #[test]
    fn conditional_rule_skipped() {
        let mut r = rule(app("f", vec![evar("X")]), app("g", vec![]));
        r.requires = Some(Pattern::Top(cfg()));
        let k = KReducer::new(&[r]);
        assert_eq!(k.report().lowered, 0);
        assert_eq!(k.report().skipped, 1);
    }
}
