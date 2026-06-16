//! `#by` — goal-directed **tactic mode**.
//!
//! A tactic here is the imperative job of driving a goal to discharge.
//! Unlike tree mode (`#proof DRV`), `#by` **produces a `Thm` directly** by
//! calling kernel rules on the focused goal — the shape a future
//! WASM-over-WIT tactic uses (inspect the goal, call rule ops, return a
//! thm handle). Since the system is proof-irrelevant — we keep the *fact*
//! `⊢ X`, not a proof object — there is no `Drv` to build here.
//!
//! Tactics:
//! - `(intro NAME)` — backward `⟹`/`∀` introduction;
//! - `(exact DRV)` — the **tree-mode discharger**: close the goal with a
//!   forward proof term (checked to a `Thm`);
//! - `(assumption)` — close with a context fact;
//! - `(tauto)` / `(refl)` — close by the corresponding decider;
//! - `(#have FACT BODY)` — prove `FACT` (in nested `#proof`/`#by`), add it
//!   to the context, and continue.
//!
//! The goal context is `{ target, hyps }` (hyps: `intro`'d assumptions or
//! `#have`'d lemmas) — the value a WASM tactic would see over the WIT. A
//! fully reified `Vec<Goal>` stack (for branching tactics / the WIT) is the
//! next step; today the focus is a single evolving goal.

use covalence_core::{Term, TermKind, Thm, Type, defs, subst};
use covalence_sexp::SExpr;

use super::ScriptError;
use super::drv::{check, parse_drv};
use super::syntax::{Env, Scope, arity, head_sym, list, parse_term, sym};
use crate::HolLightCtx;

type R<T> = Result<T, ScriptError>;

/// How a context fact is discharged into a `Thm`.
#[derive(Clone)]
enum Hyp {
    /// An `intro`'d assumption — proved by `Thm::assume`, discharged by the
    /// enclosing `imp-intro`.
    Assumed,
    /// A `#have`'d fact — the proven theorem itself.
    Proven(Thm),
}

/// The focused goal: a target plus the facts available to discharge it.
struct Goal {
    target: Term,
    hyps: Vec<(Term, Hyp)>,
}

/// Prove `goal` from a proof body — `(#proof DRV)` (tree mode) or
/// `(#by STEP…)` (tactic mode) — returning a kernel `Thm`.
pub fn prove(goal: &Term, body: &SExpr, scope: &mut Scope, env: &Env) -> R<Thm> {
    prove_with(goal, body, scope, &[], env)
}

fn prove_with(
    goal: &Term,
    body: &SExpr,
    scope: &mut Scope,
    hyps: &[(Term, Hyp)],
    env: &Env,
) -> R<Thm> {
    let ch = list(body, "proof body")?;
    match head_sym(ch)? {
        "#proof" => {
            arity(ch, 2, "#proof")?;
            check(&parse_drv(&ch[1], scope, env)?, env)
        }
        "#by" => {
            let mut g = Goal {
                target: goal.clone(),
                hyps: hyps.to_vec(),
            };
            run(&mut g, &ch[1..], scope, env)
        }
        other => Err(ScriptError::Syntax(format!(
            "expected (#proof …) or (#by …), got `{other}`"
        ))),
    }
}

fn run(goal: &mut Goal, steps: &[SExpr], scope: &mut Scope, env: &Env) -> R<Thm> {
    let Some((step, rest)) = steps.split_first() else {
        return Err(ScriptError::Syntax(format!(
            "#by: the goal is still open: {}",
            goal.target
        )));
    };
    let s = list(step, "tactic")?;
    match head_sym(s)? {
        // backward ⟹/∀ introduction — one or more names at once.
        "intro" => {
            if s.len() < 2 {
                return Err(ScriptError::Syntax("intro: expected at least one name".into()));
            }
            intro_names(goal, &s[1..], rest, scope, env)
        }
        // goal transformers (reduce to a single subgoal, wrap with a rule)
        "sym" => {
            arity(s, 1, "sym")?;
            let (a, b) = dest_eq(&goal.target).ok_or_else(|| {
                ScriptError::Syntax(format!("sym: goal is not an equation: {}", goal.target))
            })?;
            goal.target = HolLightCtx::new().mk_eq(b, a)?;
            Ok(run(goal, rest, scope, env)?.sym()?)
        }
        "not-intro" => {
            arity(s, 1, "not-intro")?;
            let p = dest_not(&goal.target).ok_or_else(|| {
                ScriptError::Syntax(format!("not-intro: goal is not `¬_`: {}", goal.target))
            })?;
            goal.target = HolLightCtx::new().mk_imp(p, Term::bool_lit(false));
            Ok(run(goal, rest, scope, env)?.not_intro()?)
        }
        // dischargers — close the goal; no tactics may follow.
        "exact" => {
            arity(s, 2, "exact")?;
            expect_done(rest, "exact")?;
            check(&parse_drv(&s[1], scope, env)?, env)
        }
        "assumption" => {
            arity(s, 1, "assumption")?;
            expect_done(rest, "assumption")?;
            let target = goal.target.clone();
            let mut src = None;
            for (t, h) in goal.hyps.iter().rev() {
                if *t == target {
                    src = Some(h.clone());
                    break;
                }
            }
            match src {
                Some(Hyp::Assumed) => Ok(Thm::assume(target)?),
                Some(Hyp::Proven(th)) => Ok(th),
                None => Err(ScriptError::Syntax(format!(
                    "assumption: no fact matches the goal {target}"
                ))),
            }
        }
        "tauto" => {
            arity(s, 1, "tauto")?;
            expect_done(rest, "tauto")?;
            Ok(crate::init::logic::tauto(&goal.target)?)
        }
        "refl" => {
            arity(s, 1, "refl")?;
            expect_done(rest, "refl")?;
            let (lhs, _) = dest_eq(&goal.target).ok_or_else(|| {
                ScriptError::Syntax(format!("refl: goal is not an equation: {}", goal.target))
            })?;
            Ok(Thm::refl(lhs)?)
        }
        "#have" => {
            arity(s, 3, "#have")?;
            let fact = parse_term(&s[1], scope, env)?;
            let sub = prove_with(&fact, &s[2], scope, &goal.hyps, env)?;
            goal.hyps.push((fact, Hyp::Proven(sub)));
            let result = run(goal, rest, scope, env);
            goal.hyps.pop();
            result
        }
        other => Err(ScriptError::Syntax(format!("unknown tactic: `{other}`"))),
    }
}

/// `(intro a b c …)` — introduce each name in turn (backward `⟹`/`∀`),
/// then continue with the remaining tactics.
fn intro_names(
    goal: &mut Goal,
    names: &[SExpr],
    rest: &[SExpr],
    scope: &mut Scope,
    env: &Env,
) -> R<Thm> {
    let Some((name_s, more)) = names.split_first() else {
        return run(goal, rest, scope, env);
    };
    let name = sym(name_s, "intro name")?.to_string();
    if let Some((a, b)) = dest_imp(&goal.target) {
        goal.hyps.push((a.clone(), Hyp::Assumed));
        goal.target = b;
        let inner = intro_names(goal, more, rest, scope, env);
        goal.hyps.pop();
        Ok(inner?.imp_intro(&a)?)
    } else if let Some((ty, body)) = dest_forall(&goal.target) {
        goal.target = subst::open(&body, &Term::free(name.as_str(), ty.clone()));
        scope.push((name.clone(), ty.clone()));
        let inner = intro_names(goal, more, rest, scope, env);
        scope.pop();
        Ok(inner?.all_intro(&name, ty)?)
    } else {
        Err(ScriptError::Syntax(format!(
            "intro: goal is neither `⟹` nor `∀`: {}",
            goal.target
        )))
    }
}

/// A discharging tactic closes the goal; reject any trailing tactics.
fn expect_done(rest: &[SExpr], tac: &str) -> R<()> {
    if rest.is_empty() {
        Ok(())
    } else {
        Err(ScriptError::Syntax(format!(
            "{tac}: the goal is closed, but {} more tactic(s) follow",
            rest.len()
        )))
    }
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

fn dest_not(t: &Term) -> Option<Term> {
    let not = defs::not();
    let TermKind::App(h, p) = t.kind() else {
        return None;
    };
    (*h == not).then(|| p.clone())
}
