//! `#by` tactic mode and the **tactic registry**.
//!
//! Tactics are first-class entries in an [`Env`]'s tactic registry (the
//! primitives — `intro`, `sym`, `rw`, `induct`, … — are registered as part
//! of `core`). Dispatch is by name through that registry, so opening `core`
//! is what makes the primitives available.
//!
//! A tactic is a native Rust `fn` taking its own S-expression, the remaining
//! steps, and the mutable interpreter state [`Interp`]; it returns a `Thm`
//! for the current goal. (Goal-transformers recurse via [`Interp::run`].)
//! `Interp` owns the transient proof state — the goal, the context facts, and
//! the variable scope (`open_scope`/`close_scope`) — separate from the
//! importable namespace [`Env`]. A stricter, stack-guarded form (and a WASM
//! tactic ABI) is future work.

use std::collections::HashMap;

use covalence_core::{Term, TermKind, Thm, Type, defs, subst};
use covalence_sexp::SExpr;

use super::ScriptError;
use super::drv::{check, parse_drv, rewrite_conv};
use super::syntax::{Env, Scope, arity, head_sym, list, parse_term, sym};
use crate::HolLightCtx;

type R<T> = Result<T, ScriptError>;

/// How a context fact discharges into a `Thm`.
#[derive(Clone)]
pub enum Hyp {
    /// An `intro`'d assumption (proved by `assume`, discharged by the
    /// enclosing `imp-intro`).
    Assumed,
    /// A `#have`'d fact — the proven theorem.
    Proven(Thm),
}

/// A native tactic: `(s, rest, interp) -> Thm`. `s` is the tactic's own
/// S-expression (e.g. `(intro a b)`), `rest` the following steps.
pub type Tactic = for<'a> fn(&[SExpr], &[SExpr], &mut Interp<'a>) -> R<Thm>;

/// The mutable interpreter state during a `#by` block: the current goal,
/// the available context facts, and the variable scope. Borrows the
/// namespace [`Env`] (for tactic/name lookup) but owns the transient state.
pub struct Interp<'e> {
    env: &'e Env,
    goal: Term,
    hyps: Vec<(Term, Hyp)>,
    scope: Scope,
}

impl<'e> Interp<'e> {
    /// The namespace environment (tactic registry, consts, lemmas).
    pub fn env(&self) -> &Env {
        self.env
    }
    /// The current goal.
    pub fn goal(&self) -> &Term {
        &self.goal
    }
    /// Introduce a fixed variable into scope (for the duration until
    /// [`Interp::close_scope`]).
    pub fn open_scope(&mut self, name: &str, ty: Type) {
        self.scope.push((name.to_string(), ty));
    }
    /// Drop the innermost fixed variable.
    pub fn close_scope(&mut self) {
        self.scope.pop();
    }

    /// Dispatch the next tactic in `steps` (looked up by name in the
    /// environment's tactic registry), or error if the goal is still open.
    pub fn run(&mut self, steps: &[SExpr]) -> R<Thm> {
        let Some((step, rest)) = steps.split_first() else {
            return Err(ScriptError::Syntax(format!(
                "#by: the goal is still open: {}",
                self.goal
            )));
        };
        let s = list(step, "tactic")?;
        let name = head_sym(s)?;
        let tac = self
            .env
            .lookup_tactic(name)
            .ok_or_else(|| ScriptError::Syntax(format!("unknown tactic: `{name}`")))?;
        tac(s, rest, self)
    }
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
            let mut it = Interp {
                env,
                goal: goal.clone(),
                hyps: hyps.to_vec(),
                scope: scope.clone(),
            };
            it.run(&ch[1..])
        }
        other => Err(ScriptError::Syntax(format!(
            "expected (#proof …) or (#by …), got `{other}`"
        ))),
    }
}

/// The primitive tactics, registered as part of `core`.
pub fn core_tactics() -> HashMap<String, Tactic> {
    let mut t: HashMap<String, Tactic> = HashMap::new();
    t.insert("intro".into(), tac_intro);
    t.insert("exact".into(), tac_exact);
    t.insert("assumption".into(), tac_assumption);
    t.insert("tauto".into(), tac_tauto);
    t.insert("refl".into(), tac_refl);
    t.insert("sym".into(), tac_sym);
    t.insert("not-intro".into(), tac_not_intro);
    t.insert("contrapositive".into(), tac_contrapositive);
    t.insert("rw".into(), tac_rw);
    t.insert("induct".into(), tac_induct);
    t.insert("#have".into(), tac_have);
    t
}

// ============================================================================
// The primitive tactics
// ============================================================================

fn tac_intro(s: &[SExpr], rest: &[SExpr], it: &mut Interp) -> R<Thm> {
    if s.len() < 2 {
        return Err(ScriptError::Syntax("intro: expected at least one name".into()));
    }
    intro_names(&s[1..], rest, it)
}

fn intro_names(names: &[SExpr], rest: &[SExpr], it: &mut Interp) -> R<Thm> {
    let Some((name_s, more)) = names.split_first() else {
        return it.run(rest);
    };
    let name = sym(name_s, "intro name")?.to_string();
    if let Some((a, b)) = dest_imp(&it.goal) {
        it.hyps.push((a.clone(), Hyp::Assumed));
        it.goal = b;
        let inner = intro_names(more, rest, it);
        it.hyps.pop();
        Ok(inner?.imp_intro(&a)?)
    } else if let Some((ty, body)) = dest_forall(&it.goal) {
        it.goal = subst::open(&body, &Term::free(name.as_str(), ty.clone()));
        it.scope.push((name.clone(), ty.clone()));
        let inner = intro_names(more, rest, it);
        it.scope.pop();
        Ok(inner?.all_intro(&name, ty)?)
    } else {
        Err(ScriptError::Syntax(format!(
            "intro: goal is neither `⟹` nor `∀`: {}",
            it.goal
        )))
    }
}

fn tac_exact(s: &[SExpr], rest: &[SExpr], it: &mut Interp) -> R<Thm> {
    arity(s, 2, "exact")?;
    expect_done(rest, "exact")?;
    let env = it.env;
    check(&parse_drv(&s[1], &mut it.scope, env)?, env)
}

fn tac_assumption(s: &[SExpr], rest: &[SExpr], it: &mut Interp) -> R<Thm> {
    arity(s, 1, "assumption")?;
    expect_done(rest, "assumption")?;
    let target = it.goal.clone();
    let mut src = None;
    for (t, h) in it.hyps.iter().rev() {
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

fn tac_tauto(s: &[SExpr], rest: &[SExpr], it: &mut Interp) -> R<Thm> {
    arity(s, 1, "tauto")?;
    expect_done(rest, "tauto")?;
    Ok(crate::init::logic::tauto(&it.goal)?)
}

fn tac_refl(s: &[SExpr], rest: &[SExpr], it: &mut Interp) -> R<Thm> {
    arity(s, 1, "refl")?;
    expect_done(rest, "refl")?;
    let (lhs, _) = dest_eq(&it.goal)
        .ok_or_else(|| ScriptError::Syntax(format!("refl: goal is not an equation: {}", it.goal)))?;
    Ok(Thm::refl(lhs)?)
}

fn tac_sym(s: &[SExpr], rest: &[SExpr], it: &mut Interp) -> R<Thm> {
    arity(s, 1, "sym")?;
    let ctx = HolLightCtx::new();
    if let Some(eq) = dest_not(&it.goal) {
        let (a, b) = dest_eq(&eq).ok_or_else(|| {
            ScriptError::Syntax(format!(
                "sym: `¬_` goal is not a negated equation: {}",
                it.goal
            ))
        })?;
        let ab = ctx.mk_eq(a.clone(), b.clone())?;
        it.goal = ctx.mk_not(ctx.mk_eq(b, a)?);
        let inner = it.run(rest)?;
        let f = inner.not_elim(Thm::assume(ab.clone())?.sym()?)?;
        Ok(f.imp_intro(&ab)?.not_intro()?)
    } else if let Some((a, b)) = dest_eq(&it.goal) {
        it.goal = ctx.mk_eq(b, a)?;
        Ok(it.run(rest)?.sym()?)
    } else {
        Err(ScriptError::Syntax(format!(
            "sym: goal is not an equation or a negated equation: {}",
            it.goal
        )))
    }
}

fn tac_not_intro(s: &[SExpr], rest: &[SExpr], it: &mut Interp) -> R<Thm> {
    arity(s, 1, "not-intro")?;
    let p = dest_not(&it.goal)
        .ok_or_else(|| ScriptError::Syntax(format!("not-intro: goal is not `¬_`: {}", it.goal)))?;
    it.goal = HolLightCtx::new().mk_imp(p, Term::bool_lit(false));
    Ok(it.run(rest)?.not_intro()?)
}

fn tac_contrapositive(s: &[SExpr], rest: &[SExpr], it: &mut Interp) -> R<Thm> {
    arity(s, 1, "contrapositive")?;
    let (a, b) = dest_imp(&it.goal).ok_or_else(|| {
        ScriptError::Syntax(format!(
            "contrapositive: goal is not an implication: {}",
            it.goal
        ))
    })?;
    let ctx = HolLightCtx::new();
    match (dest_not(&a), dest_not(&b)) {
        (Some(p), Some(q)) => {
            it.goal = ctx.mk_imp(q.clone(), p);
            let inner = it.run(rest)?;
            let p_thm = inner.imp_elim(Thm::assume(q.clone())?)?;
            let f = Thm::assume(a.clone())?.not_elim(p_thm)?;
            let nq = f.imp_intro(&q)?.not_intro()?;
            Ok(nq.imp_intro(&a)?)
        }
        _ => {
            let nb = ctx.mk_not(b.clone());
            let na = ctx.mk_not(a.clone());
            it.goal = ctx.mk_imp(nb.clone(), na);
            let inner = it.run(rest)?;
            let left = Thm::assume(b.clone())?.imp_intro(&b)?;
            let na_thm = inner.imp_elim(Thm::assume(nb.clone())?)?;
            let f = na_thm.not_elim(Thm::assume(a.clone())?)?;
            let right = f.false_elim(b.clone())?.imp_intro(&nb)?;
            let b_thm = Thm::lem(b)?.or_elim(left, right)?;
            Ok(b_thm.imp_intro(&a)?)
        }
    }
}

fn tac_rw(s: &[SExpr], rest: &[SExpr], it: &mut Interp) -> R<Thm> {
    arity(s, 2, "rw")?;
    let env = it.env;
    let eq = check(&parse_drv(&s[1], &mut it.scope, env)?, env)?;
    let cong = rewrite_conv(&it.goal, &eq)?;
    let (_, gprime) = dest_eq(cong.concl())
        .ok_or_else(|| ScriptError::Syntax("rw: rewrite did not yield an equation".into()))?;
    it.goal = gprime;
    let inner = it.run(rest)?;
    Ok(cong.sym()?.eq_mp(inner)?)
}

fn tac_have(s: &[SExpr], rest: &[SExpr], it: &mut Interp) -> R<Thm> {
    arity(s, 3, "#have")?;
    let env = it.env;
    let fact = parse_term(&s[1], &mut it.scope, env)?;
    let sub = prove_with(&fact, &s[2], &mut it.scope, &it.hyps, env)?;
    it.hyps.push((fact, Hyp::Proven(sub)));
    let result = it.run(rest);
    it.hyps.pop();
    result
}

fn tac_induct(s: &[SExpr], rest: &[SExpr], it: &mut Interp) -> R<Thm> {
    arity(s, 4, "induct")?;
    expect_done(rest, "induct")?;
    let env = it.env;
    let var = sym(&s[1], "induct variable")?.to_string();
    let (ty, body) = dest_forall(&it.goal)
        .ok_or_else(|| ScriptError::Syntax(format!("induct: goal is not a `∀`: {}", it.goal)))?;
    if ty != Type::nat() {
        return Err(ScriptError::Syntax(format!(
            "induct: goal quantifies over {ty}, not nat"
        )));
    }
    let p = Term::abs(Type::nat(), body.clone());
    let zero = Term::nat_lit(0u64);

    let base_body = prove_with(&subst::open(&body, &zero), &s[2], &mut it.scope, &it.hyps, env)?;
    let base = Thm::beta_conv(Term::app(p.clone(), zero))?
        .sym()?
        .eq_mp(base_body)?;

    let v = Term::free(var.as_str(), Type::nat());
    let ih = subst::open(&body, &v);
    let sv = Term::app(Term::succ(), v.clone());
    let mut step_hyps = it.hyps.clone();
    step_hyps.push((ih.clone(), Hyp::Assumed));
    it.scope.push((var.clone(), Type::nat()));
    let step_body = prove_with(&subst::open(&body, &sv), &s[3], &mut it.scope, &step_hyps, env);
    it.scope.pop();
    let step_imp = step_body?.imp_intro(&ih)?;
    let ea = Thm::beta_conv(Term::app(p.clone(), v))?;
    let eb = Thm::beta_conv(Term::app(p, sv))?;
    let step = Thm::refl(defs::imp())?
        .mk_comb(ea.sym()?)?
        .mk_comb(eb.sym()?)?
        .eq_mp(step_imp)?;

    let ind = Thm::nat_induct(base, step)?;
    let nf = crate::proofs::rewrite::beta_nf(ind.concl().clone());
    Ok(nf.eq_mp(ind)?)
}

// ============================================================================
// Helpers
// ============================================================================

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
