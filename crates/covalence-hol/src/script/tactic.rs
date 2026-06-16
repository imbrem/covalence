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
            let ctx = HolLightCtx::new();
            if let Some(eq) = dest_not(&goal.target) {
                // `¬(a = b)`  →  subgoal `¬(b = a)`
                let (a, b) = dest_eq(&eq).ok_or_else(|| {
                    ScriptError::Syntax(format!(
                        "sym: `¬_` goal is not a negated equation: {}",
                        goal.target
                    ))
                })?;
                let ab = ctx.mk_eq(a.clone(), b.clone())?;
                goal.target = ctx.mk_not(ctx.mk_eq(b, a)?);
                let inner = run(goal, rest, scope, env)?; // ⊢ ¬(b = a)
                let f = inner.not_elim(Thm::assume(ab.clone())?.sym()?)?; // {a=b} ⊢ F
                Ok(f.imp_intro(&ab)?.not_intro()?) // ⊢ ¬(a = b)
            } else if let Some((a, b)) = dest_eq(&goal.target) {
                goal.target = ctx.mk_eq(b, a)?;
                Ok(run(goal, rest, scope, env)?.sym()?)
            } else {
                Err(ScriptError::Syntax(format!(
                    "sym: goal is not an equation or a negated equation: {}",
                    goal.target
                )))
            }
        }
        // Prove an implication by its contrapositive. `¬P ⟹ ¬Q` reduces to
        // `Q ⟹ P` (strips the negations); a general `a ⟹ b` reduces to
        // `¬b ⟹ ¬a` (classical, via `lem`).
        "contrapositive" => {
            arity(s, 1, "contrapositive")?;
            let (a, b) = dest_imp(&goal.target).ok_or_else(|| {
                ScriptError::Syntax(format!(
                    "contrapositive: goal is not an implication: {}",
                    goal.target
                ))
            })?;
            let ctx = HolLightCtx::new();
            match (dest_not(&a), dest_not(&b)) {
                (Some(p), Some(q)) => {
                    goal.target = ctx.mk_imp(q.clone(), p);
                    let inner = run(goal, rest, scope, env)?; // ⊢ Q ⟹ P
                    let p_thm = inner.imp_elim(Thm::assume(q.clone())?)?; // {Q} ⊢ P
                    let f = Thm::assume(a.clone())?.not_elim(p_thm)?; // {¬P, Q} ⊢ F
                    let nq = f.imp_intro(&q)?.not_intro()?; // {¬P} ⊢ ¬Q
                    Ok(nq.imp_intro(&a)?) // ⊢ ¬P ⟹ ¬Q
                }
                _ => {
                    let nb = ctx.mk_not(b.clone());
                    let na = ctx.mk_not(a.clone());
                    goal.target = ctx.mk_imp(nb.clone(), na);
                    let inner = run(goal, rest, scope, env)?; // ⊢ ¬b ⟹ ¬a
                    let left = Thm::assume(b.clone())?.imp_intro(&b)?; // ⊢ b ⟹ b
                    let na_thm = inner.imp_elim(Thm::assume(nb.clone())?)?; // {¬b} ⊢ ¬a
                    let f = na_thm.not_elim(Thm::assume(a.clone())?)?; // {¬b, a} ⊢ F
                    let right = f.false_elim(b.clone())?.imp_intro(&nb)?; // {a} ⊢ ¬b ⟹ b
                    let b_thm = Thm::lem(b)?.or_elim(left, right)?; // {a} ⊢ b
                    Ok(b_thm.imp_intro(&a)?) // ⊢ a ⟹ b
                }
            }
        }
        "not-intro" => {
            arity(s, 1, "not-intro")?;
            let p = dest_not(&goal.target).ok_or_else(|| {
                ScriptError::Syntax(format!("not-intro: goal is not `¬_`: {}", goal.target))
            })?;
            goal.target = HolLightCtx::new().mk_imp(p, Term::bool_lit(false));
            Ok(run(goal, rest, scope, env)?.not_intro()?)
        }
        // Rewrite the goal left-to-right with the equation proved by the
        // given (instantiated) tree-mode proof — the nat-reduction workhorse
        // (`rw (all-elim 0 (lemma add.base))`, `rw (assume IH)`, …). Every
        // occurrence of the LHS is replaced; the remaining goal is the
        // rewritten one.
        "rw" => {
            arity(s, 2, "rw")?;
            let eq = check(&parse_drv(&s[1], scope, env)?, env)?; // ⊢ lhs = rhs
            let cong = super::drv::rewrite_conv(&goal.target, &eq)?; // ⊢ G = G'
            let (_, gprime) = dest_eq(cong.concl()).ok_or_else(|| {
                ScriptError::Syntax("rw: rewrite did not yield an equation".into())
            })?;
            goal.target = gprime;
            let inner = run(goal, rest, scope, env)?; // ⊢ G'
            Ok(cong.sym()?.eq_mp(inner)?) // ⊢ G
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
        // nat induction on a `∀(v:nat). P v` goal, into base + step
        // subproofs.  `(induct v BASE STEP)`: BASE proves `P 0`; STEP proves
        // `P (S v)` with the IH `P v` available (`v` fixed). The β-conv
        // bookkeeping (the kernel's `nat_induct` keeps the motive applied,
        // un-reduced) is handled here.
        "induct" => {
            arity(s, 4, "induct")?;
            expect_done(rest, "induct")?;
            let var = sym(&s[1], "induct variable")?.to_string();
            let (ty, body) = dest_forall(&goal.target).ok_or_else(|| {
                ScriptError::Syntax(format!("induct: goal is not a `∀`: {}", goal.target))
            })?;
            if ty != Type::nat() {
                return Err(ScriptError::Syntax(format!(
                    "induct: goal quantifies over {ty}, not nat"
                )));
            }
            let p = Term::abs(Type::nat(), body.clone()); // the motive λv. P v
            let zero = Term::nat_lit(0u64);

            // base: prove P 0 (β-reduced), then β-expand to `p 0`.
            let base_body = prove_with(&subst::open(&body, &zero), &s[2], scope, &goal.hyps, env)?;
            let base = Thm::beta_conv(Term::app(p.clone(), zero))?
                .sym()?
                .eq_mp(base_body)?;

            // step: prove P (S v) with the IH `P v` in context (v fixed).
            let v = Term::free(var.as_str(), Type::nat());
            let ih = subst::open(&body, &v);
            let sv = Term::app(Term::succ(), v.clone());
            let mut step_hyps = goal.hyps.clone();
            step_hyps.push((ih.clone(), Hyp::Assumed));
            scope.push((var.clone(), Type::nat()));
            let step_body = prove_with(&subst::open(&body, &sv), &s[3], scope, &step_hyps, env);
            scope.pop();
            let step_imp = step_body?.imp_intro(&ih)?;
            // β-expand the two sides to `p v ⟹ p (S v)`.
            let ea = Thm::beta_conv(Term::app(p.clone(), v))?;
            let eb = Thm::beta_conv(Term::app(p, sv))?;
            let step = Thm::refl(defs::imp())?
                .mk_comb(ea.sym()?)?
                .mk_comb(eb.sym()?)?
                .eq_mp(step_imp)?;

            // ⊢ ∀n. p n, then β-normalise back to the goal's (reduced) form.
            let ind = Thm::nat_induct(base, step)?;
            let nf = crate::proofs::rewrite::beta_nf(ind.concl().clone());
            Ok(nf.eq_mp(ind)?)
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
