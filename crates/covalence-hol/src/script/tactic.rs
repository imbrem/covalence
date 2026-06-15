//! `#by` — goal-directed **tactic mode**.
//!
//! Tactic mode is the imperative authoring layer: you start from a single
//! goal (the thing to prove now) plus a context of fixed variables and
//! available facts, and apply *tactics* that reduce the goal until it is
//! discharged. Crucially it is not a separate proof representation — it
//! **elaborates to a forward [`Drv`]**, which `check` then replays. So the
//! tree stays the certificate; `#by` is just a nicer way to build one.
//!
//! Tactics here:
//! - `(intro NAME)` — backward `⟹`/`∀` introduction (peel the goal,
//!   moving the antecedent into the context or fixing the bound variable);
//! - `(exact DRV)` — the **tree-mode discharger**: close the goal with an
//!   arbitrary forward proof term;
//! - `(assumption)` — close the goal with a context fact (an `intro`'d
//!   hypothesis or a `#have`'d lemma);
//! - `(tauto)` / `(refl)` — close by the corresponding decider;
//! - `(#have FACT BODY)` — prove `FACT` (in `(#proof …)` tree mode or a
//!   nested `(#by …)`), bind it into the context, and continue.

use covalence_core::{Term, TermKind, Type, defs, subst};
use covalence_sexp::SExpr;

use super::ScriptError;
use super::drv::{Drv, parse_drv};
use super::syntax::{Env, Scope, arity, head_sym, list, parse_term, sym};

type R<T> = Result<T, ScriptError>;

/// A local fact available in tactic mode: a term plus how to prove it —
/// `None` for an `intro`'d assumption (proved by `assume`, discharged by
/// the enclosing `imp-intro`), `Some(drv)` for a `#have`'d fact.
type Facts = Vec<(Term, Option<Drv>)>;

/// Elaborate a proof body — `(#proof DRV)` (tree mode) or `(#by STEP…)`
/// (tactic mode) — proving `goal`, into a forward [`Drv`].
pub fn elaborate_proof(goal: &Term, body: &SExpr, scope: &mut Scope, env: &Env) -> R<Drv> {
    let mut facts = Facts::new();
    elaborate_body(goal, body, scope, &mut facts, env)
}

fn elaborate_body(
    goal: &Term,
    body: &SExpr,
    scope: &mut Scope,
    facts: &mut Facts,
    env: &Env,
) -> R<Drv> {
    let ch = list(body, "proof body")?;
    match head_sym(ch)? {
        "#proof" => {
            arity(ch, 2, "#proof")?;
            parse_drv(&ch[1], scope, env)
        }
        "#by" => run(goal, &ch[1..], scope, facts, env),
        other => Err(ScriptError::Syntax(format!(
            "expected (#proof …) or (#by …), got `{other}`"
        ))),
    }
}

fn run(
    goal: &Term,
    steps: &[SExpr],
    scope: &mut Scope,
    facts: &mut Facts,
    env: &Env,
) -> R<Drv> {
    let Some((step, rest)) = steps.split_first() else {
        return Err(ScriptError::Syntax(format!(
            "#by: ran out of steps with the goal still open: {goal}"
        )));
    };
    let s = list(step, "tactic")?;
    match head_sym(s)? {
        // backward ⟹/∀ introduction
        "intro" => {
            arity(s, 2, "intro")?;
            let name = sym(&s[1], "intro name")?.to_string();
            if let Some((a, b)) = dest_imp(goal) {
                facts.push((a.clone(), None));
                let inner = run(&b, rest, scope, facts, env);
                facts.pop();
                Ok(Drv::ImpIntro {
                    phi: a,
                    body: Box::new(inner?),
                })
            } else if let Some((ty, body)) = dest_forall(goal) {
                let new_goal = subst::open(&body, &Term::free(name.as_str(), ty.clone()));
                scope.push((name.clone(), ty.clone()));
                let inner = run(&new_goal, rest, scope, facts, env);
                scope.pop();
                Ok(Drv::AllIntro {
                    name,
                    ty,
                    body: Box::new(inner?),
                })
            } else {
                Err(ScriptError::Syntax(format!(
                    "intro: goal is neither `⟹` nor `∀`: {goal}"
                )))
            }
        }
        // the tree-mode discharger
        "exact" => {
            arity(s, 2, "exact")?;
            parse_drv(&s[1], scope, env)
        }
        "assumption" => {
            arity(s, 1, "assumption")?;
            discharge_from_facts(goal, facts).ok_or_else(|| {
                ScriptError::Syntax(format!("assumption: no fact matches the goal {goal}"))
            })
        }
        "tauto" => {
            arity(s, 1, "tauto")?;
            Ok(Drv::Tauto(goal.clone()))
        }
        "refl" => {
            arity(s, 1, "refl")?;
            let (lhs, _) = dest_eq(goal).ok_or_else(|| {
                ScriptError::Syntax(format!("refl: goal is not an equation: {goal}"))
            })?;
            Ok(Drv::Refl(lhs))
        }
        // prove an intermediate fact, then continue with it in context
        "#have" => {
            arity(s, 3, "#have")?;
            let fact = parse_term(&s[1], scope, env)?;
            let sub = elaborate_body(&fact, &s[2], scope, facts, env)?;
            facts.push((fact, Some(sub)));
            let result = run(goal, rest, scope, facts, env);
            facts.pop();
            result
        }
        other => Err(ScriptError::Syntax(format!("unknown tactic: `{other}`"))),
    }
}

fn discharge_from_facts(goal: &Term, facts: &Facts) -> Option<Drv> {
    facts.iter().rev().find_map(|(t, src)| {
        (t == goal).then(|| match src {
            None => Drv::Assume(goal.clone()),
            Some(d) => d.clone(),
        })
    })
}

fn dest_imp(t: &Term) -> Option<(Term, Term)> {
    let imp = defs::imp();
    let TermKind::App(f, b) = t.kind() else {
        return None;
    };
    let TermKind::App(h, a) = f.kind() else {
        return None;
    };
    (*h == imp).then(|| (a.clone(), b.clone()))
}

fn dest_forall(t: &Term) -> Option<(Type, Term)> {
    let TermKind::App(h, abs) = t.kind() else {
        return None;
    };
    let TermKind::Abs(ty, body) = abs.kind() else {
        return None;
    };
    (*h == defs::forall(ty.clone())).then(|| (ty.clone(), body.clone()))
}

fn dest_eq(t: &Term) -> Option<(Term, Term)> {
    let TermKind::App(f, rhs) = t.kind() else {
        return None;
    };
    let TermKind::App(h, lhs) = f.kind() else {
        return None;
    };
    matches!(h.kind(), TermKind::Eq(_)).then(|| (lhs.clone(), rhs.clone()))
}
