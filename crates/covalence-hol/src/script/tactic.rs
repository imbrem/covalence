//! `#by` tactic mode and the **tactic registry**.
//!
//! Tactics are first-class entries in an [`Env`]'s tactic registry (the
//! primitives — `intro`, `sym`, `rw`, `induct`, … — are registered as part
//! of `core`). Dispatch is by name through that registry, so opening `core`
//! is what makes the primitives available.
//!
//! A tactic implements the **async** [`Tactic`] trait — `apply` takes its own
//! S-expression, the remaining steps, and the mutable interpreter state
//! [`Interp`], and returns a `Thm` for the current goal. Because `apply` is
//! `async`, a tactic may **await** mid-proof (a long-running observer, a peer
//! prover, the user). Goal-transformers recurse via [`Interp::run`] (also
//! async). Simple goal-closing tactics register as plain sync `fn`s (the
//! blanket impl); recursing ones are concrete types. `Interp` owns the
//! transient proof state — goal, context facts, variable scope — separate from
//! the importable namespace [`Env`]. (The kernel replay [`check`] stays sync.)

use std::collections::HashMap;
use std::sync::Arc;

use async_trait::async_trait;
use covalence_core::{Term, TermKind, Thm, Type, defs, subst};
use covalence_sexp::SExpr;

use super::ScriptError;
use super::drv::{CheckCtx, check, ctx_arity, rewrite_conv};
use super::env::Env;
use super::scope::Scope;
use super::syntax::{arity, head_sym, list, parse_term, sym};
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

/// An **inference** — a single registry-dispatched object usable in *either*
/// proof mode, via two methods:
///
/// - [`apply`](Tactic::apply) — **tactic mode** (`#by`): drive the focused goal
///   to a theorem. Gets the inference's own S-expression `s` (e.g.
///   `(intro a b)`), the following `rest` steps, and the mutable [`Interp`].
/// - [`rule`](Tactic::rule) — **tree mode** (`#proof`): combine the
///   sub-derivations of `(NAME args…)` into a theorem, self-parsing its args
///   through a [`CheckCtx`].
///
/// Both default to a "wrong mode" error, so a concrete inference implements
/// only the mode(s) it supports: a goal-only tactic (`intro`) overrides
/// `apply`; a forward rule (`trans`) overrides `rule`; a dual-mode inference
/// (`sym`, `refl`, `not-intro`, `rw`) overrides both — one object, no stapling.
///
/// FUTURE: a third facet, `rewrite(a) -> ⊢ a = b` (a **rewriter**), is planned
/// — what `rw` consumes. A lemma already casts to a rewriter today via
/// [`Env::rw_unify`](super::Env::rw_unify) (match its `∀x⃗. L = R` LHS against a
/// subterm); promoting that to an explicit facet lets a custom inference be a
/// rewriter just as it can be a tactic/rule, and `rw E1 E2 …` becomes "run these
/// rewriters in sequence".
///
/// This is a **trait**, not a bare `fn`, so an inference can carry state, be
/// backed by a WASM component, or run *async* — awaiting a long-running
/// observer, a peer prover, or the user. Object-safe via `#[async_trait]`, so
/// the [`Env`] registry holds `Arc<dyn Tactic>`. *Synchronous* goal-closing
/// tactics register as plain `fn`s through the blanket impl below.
#[async_trait]
pub trait Tactic: Send + Sync {
    /// Tactic mode (`#by`). Default: not usable as a tactic.
    async fn apply(&self, _s: &[SExpr], _rest: &[SExpr], _it: &mut Interp) -> R<Thm> {
        Err(ScriptError::Syntax(
            "this inference cannot be used as a `#by` tactic".into(),
        ))
    }
    /// Tree mode (`#proof`). Default: not usable as a derivation rule.
    async fn rule(&self, _args: &[SExpr], _ctx: &mut CheckCtx<'_>) -> R<Thm> {
        Err(ScriptError::Syntax(
            "this inference cannot be used as a `#proof` rule".into(),
        ))
    }
}

/// Any synchronous `fn`/closure of the right shape is a [`Tactic`], so the
/// goal-closing primitives register as plain functions and hosts can supply
/// closures (the `apply` body is sync — it does not await).
#[async_trait]
impl<F> Tactic for F
where
    F: Fn(&[SExpr], &[SExpr], &mut Interp) -> R<Thm> + Send + Sync,
{
    async fn apply(&self, s: &[SExpr], rest: &[SExpr], it: &mut Interp) -> R<Thm> {
        self(s, rest, it)
    }
}

/// The mutable interpreter state during a `#by` block: the current goal,
/// the available context facts, and the variable scope. **Owns** the namespace
/// [`Env`] (cheap to clone — it is on `imbl` persistent maps) along with the
/// transient state.
pub struct Interp {
    env: Env,
    goal: Term,
    hyps: Vec<(Term, Hyp)>,
    scope: Scope,
}

impl Interp {
    /// The namespace environment (tactic registry, consts, lemmas).
    pub fn env(&self) -> &Env {
        &self.env
    }
    /// The current goal.
    pub fn goal(&self) -> &Term {
        &self.goal
    }
    /// Mutable access to the variable scope — for a custom tactic (registered
    /// in another module) that needs to `check` sub-derivations against the
    /// interpreter's current binder context.
    pub fn scope_mut(&mut self) -> &mut Scope {
        &mut self.scope
    }

    /// The current context facts as discharged theorems — every `intro`'d
    /// assumption (as `⊢_{p} p` via `assume`) and every `#have`'d fact (its
    /// proven theorem). Lets a custom goal-closing tactic (e.g. `order`) pull
    /// the available facts *from context* in addition to its explicit args.
    pub fn context_facts(&self) -> Vec<Thm> {
        self.hyps
            .iter()
            .filter_map(|(t, h)| match h {
                Hyp::Assumed => Thm::assume(t.clone()).ok(),
                Hyp::Proven(thm) => Some(thm.clone()),
            })
            .collect()
    }
    /// Open a fresh variable group (closed as a unit by
    /// [`Interp::close_scope`]). Variable definition is separate — see
    /// [`Interp::define_var`].
    pub fn open_scope(&mut self) {
        self.scope.open();
    }
    /// Close the innermost variable group, dropping every variable defined
    /// in it.
    pub fn close_scope(&mut self) {
        self.scope.close();
    }
    /// Define a fixed variable in the current scope group.
    pub fn define_var(&mut self, name: &str, ty: Type) {
        self.scope.define(name.to_string(), ty);
    }

    /// Dispatch the next tactic in `steps` (looked up by name in the
    /// environment's tactic registry), or error if the goal is still open.
    /// `async` — a tactic may await (an observer, a peer, the user).
    pub async fn run(&mut self, steps: &[SExpr]) -> R<Thm> {
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
        tac.apply(s, rest, self).await
    }
}

/// Prove `goal` from a proof body — `(#proof DRV)` (tree mode) or
/// `(#by STEP…)` (tactic mode) — returning a kernel `Thm`.
pub async fn prove(goal: &Term, body: &SExpr, scope: &mut Scope, env: &Env) -> R<Thm> {
    prove_with(goal, body, scope, &[], env).await
}

async fn prove_with(
    goal: &Term,
    body: &SExpr,
    scope: &mut Scope,
    hyps: &[(Term, Hyp)],
    env: &Env,
) -> R<Thm> {
    let ch = list(body, "proof body")?;
    match head_sym(ch)? {
        // Tree mode: replay the derivation (which may now await a registry
        // rule).
        "#proof" => {
            arity(ch, 2, "#proof")?;
            check(&ch[1], &mut CheckCtx::new(env, scope)).await
        }
        // Tactic mode: the interpreter loop may await.
        "#by" => {
            let mut it = Interp {
                env: env.clone(),
                goal: goal.clone(),
                hyps: hyps.to_vec(),
                scope: scope.clone(),
            };
            it.run(&ch[1..]).await
        }
        other => Err(ScriptError::Syntax(format!(
            "expected (#proof …) or (#by …), got `{other}`"
        ))),
    }
}

/// The primitive tactics, registered as part of `core`.
pub fn core_tactics() -> HashMap<String, Arc<dyn Tactic>> {
    let mut t: HashMap<String, Arc<dyn Tactic>> = HashMap::new();
    let mut reg = |name: &str, tac: Arc<dyn Tactic>| {
        t.insert(name.into(), tac);
    };
    reg("intro", Arc::new(Intro));
    reg("derive", Arc::new(Derive));
    reg("drv", Arc::new(Derive));
    reg("assumption", Arc::new(tac_assumption));
    reg("refl", Arc::new(Refl));
    reg("sym", Arc::new(Sym));
    reg("not-intro", Arc::new(NotIntro));
    reg("contrapositive", Arc::new(Contrapositive));
    reg("rw", Arc::new(Rw));
    reg("beta", Arc::new(Beta));
    reg("funext", Arc::new(Funext));
    reg("#comp", Arc::new(Comp));
    reg("apply", Arc::new(Apply));
    reg("induct", Arc::new(Induct));
    reg("list-induct", Arc::new(ListInduct));
    reg("#have", Arc::new(Have));
    drop(reg);
    t
}

// ============================================================================
// The primitive tactics
// ============================================================================

/// `(intro a b …)`: strip leading `⟹`/`∀` binders, then run the rest.
struct Intro;
#[async_trait]
impl Tactic for Intro {
    async fn apply(&self, s: &[SExpr], rest: &[SExpr], it: &mut Interp) -> R<Thm> {
        if s.len() < 2 {
            return Err(ScriptError::Syntax(
                "intro: expected at least one name".into(),
            ));
        }
        intro_names(&s[1..], rest, it).await
    }
}

async fn intro_names(names: &[SExpr], rest: &[SExpr], it: &mut Interp) -> R<Thm> {
    let Some((name_s, more)) = names.split_first() else {
        return it.run(rest).await;
    };
    let name = sym(name_s, "intro name")?.to_string();
    if let Some((a, b)) = dest_imp(&it.goal) {
        it.hyps.push((a.clone(), Hyp::Assumed));
        it.goal = b;
        let inner = Box::pin(intro_names(more, rest, it)).await;
        it.hyps.pop();
        Ok(inner?.imp_intro(&a)?)
    } else if let Some((ty, body)) = dest_forall(&it.goal) {
        it.goal = subst::open(&body, &Term::free(name.as_str(), ty.clone()));
        it.scope.open();
        it.scope.define(name.clone(), ty.clone());
        let inner = Box::pin(intro_names(more, rest, it)).await;
        it.scope.close();
        Ok(inner?.all_intro(&name, ty)?)
    } else {
        Err(ScriptError::Syntax(format!(
            "intro: goal is neither `⟹` nor `∀`: {}",
            it.goal
        )))
    }
}

/// `(derive DERIV)` (alias `drv`): close the goal with a tree-mode derivation —
/// the bridge from tactic mode back into the proof-rule grammar. (Formerly
/// `exact`.) Async because `check` is async (a registry rule may await).
struct Derive;
#[async_trait]
impl Tactic for Derive {
    async fn apply(&self, s: &[SExpr], rest: &[SExpr], it: &mut Interp) -> R<Thm> {
        arity(s, 2, "derive")?;
        expect_done(rest, "derive")?;
        let env = it.env.clone();
        check(&s[1], &mut CheckCtx::new(&env, &mut it.scope)).await
    }
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

/// `(refl)` tactic / `(refl TERM)` rule: reflexivity `⊢ t = t`.
struct Refl;
#[async_trait]
impl Tactic for Refl {
    async fn apply(&self, s: &[SExpr], rest: &[SExpr], it: &mut Interp) -> R<Thm> {
        arity(s, 1, "refl")?;
        expect_done(rest, "refl")?;
        let (lhs, _) = dest_eq(&it.goal).ok_or_else(|| {
            ScriptError::Syntax(format!("refl: goal is not an equation: {}", it.goal))
        })?;
        Ok(Thm::refl(lhs)?)
    }
    async fn rule(&self, a: &[SExpr], c: &mut CheckCtx<'_>) -> R<Thm> {
        ctx_arity(a, 1, "refl")?;
        Ok(Thm::refl(c.term(&a[0])?)?)
    }
}

/// `(sym …)` tactic / `(sym SUB)` rule: flip an equation (or negated equation).
struct Sym;
#[async_trait]
impl Tactic for Sym {
    async fn apply(&self, s: &[SExpr], rest: &[SExpr], it: &mut Interp) -> R<Thm> {
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
            let inner = it.run(rest).await?;
            let f = inner.not_elim(Thm::assume(ab.clone())?.sym()?)?;
            Ok(f.imp_intro(&ab)?.not_intro()?)
        } else if let Some((a, b)) = dest_eq(&it.goal) {
            it.goal = ctx.mk_eq(b, a)?;
            Ok(it.run(rest).await?.sym()?)
        } else {
            Err(ScriptError::Syntax(format!(
                "sym: goal is not an equation or a negated equation: {}",
                it.goal
            )))
        }
    }
    async fn rule(&self, a: &[SExpr], c: &mut CheckCtx<'_>) -> R<Thm> {
        ctx_arity(a, 1, "sym")?;
        Ok(c.check(&a[0]).await?.sym()?)
    }
}

/// `(not-intro …)` tactic / `(not-intro SUB)` rule: introduce `¬`.
struct NotIntro;
#[async_trait]
impl Tactic for NotIntro {
    async fn apply(&self, s: &[SExpr], rest: &[SExpr], it: &mut Interp) -> R<Thm> {
        arity(s, 1, "not-intro")?;
        let p = dest_not(&it.goal).ok_or_else(|| {
            ScriptError::Syntax(format!("not-intro: goal is not `¬_`: {}", it.goal))
        })?;
        it.goal = HolLightCtx::new().mk_imp(p, Term::bool_lit(false));
        Ok(it.run(rest).await?.not_intro()?)
    }
    async fn rule(&self, a: &[SExpr], c: &mut CheckCtx<'_>) -> R<Thm> {
        ctx_arity(a, 1, "not-intro")?;
        Ok(c.check(&a[0]).await?.not_intro()?)
    }
}

/// `(contrapositive …)`: transform `a ⟹ b` into its contrapositive, run the
/// rest, then re-derive the original.
struct Contrapositive;
#[async_trait]
impl Tactic for Contrapositive {
    async fn apply(&self, s: &[SExpr], rest: &[SExpr], it: &mut Interp) -> R<Thm> {
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
                let inner = it.run(rest).await?;
                let p_thm = inner.imp_elim(Thm::assume(q.clone())?)?;
                let f = Thm::assume(a.clone())?.not_elim(p_thm)?;
                let nq = f.imp_intro(&q)?.not_intro()?;
                Ok(nq.imp_intro(&a)?)
            }
            _ => {
                let nb = ctx.mk_not(b.clone());
                let na = ctx.mk_not(a.clone());
                it.goal = ctx.mk_imp(nb.clone(), na);
                let inner = it.run(rest).await?;
                let left = Thm::assume(b.clone())?.imp_intro(&b)?;
                let na_thm = inner.imp_elim(Thm::assume(nb.clone())?)?;
                let f = na_thm.not_elim(Thm::assume(a.clone())?)?;
                let right = f.false_elim(b.clone())?.imp_intro(&nb)?;
                let b_thm = Thm::lem(b)?.or_elim(left, right)?;
                Ok(b_thm.imp_intro(&a)?)
            }
        }
    }
}

/// `(rw EQN… STEP…)`: rewrite the goal by each equation in turn, then run the
/// rest. Each `EQN` is a (possibly quantified) equation — bare lemma names work
/// — instantiated against the current goal by the rw-unification seam
/// ([`Env::rw_unify`]). (Toward the future *rewriter* inference kind: each arg
/// is a "rewriter" mapping the current term `a` to a proof `a = b`; a lemma
/// casts to one via `rw_unify`.)
struct Rw;
#[async_trait]
impl Tactic for Rw {
    async fn apply(&self, s: &[SExpr], rest: &[SExpr], it: &mut Interp) -> R<Thm> {
        if s.len() < 2 {
            return Err(ScriptError::Syntax(
                "rw: expected at least one equation".into(),
            ));
        }
        let env = it.env.clone();
        // Fold the equations into one congruence `⊢ goal = goal'`, threading the
        // intermediate term through each rewrite.
        let mut current = it.goal.clone();
        let mut cong: Option<Thm> = None;
        for e in &s[1..] {
            let eq = check(e, &mut CheckCtx::new(&env, &mut it.scope)).await?;
            let eq = env.rw_unify(&eq, &current)?;
            let step = rewrite_conv(&current, &eq)?; // ⊢ current = next
            let (_, next) = dest_eq(step.concl()).ok_or_else(|| {
                ScriptError::Syntax("rw: rewrite did not yield an equation".into())
            })?;
            current = next;
            cong = Some(match cong {
                None => step,
                Some(c) => c.trans(step)?,
            });
        }
        let cong = cong.expect("at least one equation"); // ⊢ goal = current
        it.goal = current;
        let inner = it.run(rest).await?;
        Ok(cong.sym()?.eq_mp(inner)?)
    }
    async fn rule(&self, a: &[SExpr], c: &mut CheckCtx<'_>) -> R<Thm> {
        // `(rw EQN… TARGET)` — rewrite TARGET's conclusion by each equation.
        if a.len() < 2 {
            return Err(ScriptError::Syntax(
                "rw: expected at least one equation and a target".into(),
            ));
        }
        let (eqns, last) = a.split_at(a.len() - 1);
        let mut thm = c.check(&last[0]).await?; // ⊢ TARGET
        for e in eqns {
            let eq = c.check(e).await?;
            let eq = c.env().rw_unify(&eq, thm.concl())?;
            let cong = rewrite_conv(thm.concl(), &eq)?; // ⊢ thm.concl = next
            thm = cong.eq_mp(thm)?;
        }
        Ok(thm)
    }
}

/// `(beta …)` tactic / `(beta TERM)` rule: the **normalizing** β step, routed
/// through the [`Env::beta`](super::Env::beta) seam (full β-normal form, beyond
/// the kernel's one-shot `beta-conv`).
///
/// - Tree mode `(beta TERM)` → `⊢ TERM = βnf(TERM)` — the β-equation, the
///   workhorse leaf of an equational chain.
/// - Tactic mode `(beta)` closes an equational goal `lhs = rhs` whenever the
///   two sides share a β-normal form, via the calc-default seam
///   ([`Env::comp_default`](super::Env::comp_default)). It does not run a
///   continuation — it is a goal-closing step.
struct Beta;
#[async_trait]
impl Tactic for Beta {
    async fn apply(&self, s: &[SExpr], rest: &[SExpr], it: &mut Interp) -> R<Thm> {
        arity(s, 1, "beta")?;
        expect_done(rest, "beta")?;
        let (lhs, rhs) = dest_eq(&it.goal).ok_or_else(|| {
            ScriptError::Syntax(format!("beta: goal is not an equation: {}", it.goal))
        })?;
        it.env.comp_default(&lhs, &rhs)
    }
    async fn rule(&self, a: &[SExpr], c: &mut CheckCtx<'_>) -> R<Thm> {
        ctx_arity(a, 1, "beta")?;
        let t = c.term(&a[0])?;
        c.env().beta(&t)
    }
}

/// `(funext …)` tactic / `(funext SUB)` rule: function extensionality, routed
/// through the [`Env::funext`](super::Env::funext) seam.
///
/// - Tree mode `(funext SUB)` — `SUB` proves the pointwise equality
///   (`⊢ ∀x. f x = g x` or `⊢ f x = g x` with `x` a fresh free point), and the
///   rule concludes `⊢ f = g`.
/// - Tactic mode `(funext x)` — turn an equational goal `f = g` between two
///   `α → β` functions into the pointwise goal `f x = g x` (over a fresh point
///   `x`), run the rest to prove it, then re-abstract + η-contract.
struct Funext;
#[async_trait]
impl Tactic for Funext {
    async fn apply(&self, s: &[SExpr], rest: &[SExpr], it: &mut Interp) -> R<Thm> {
        arity(s, 2, "funext")?;
        let name = sym(&s[1], "funext point")?.to_string();
        let (f, g) = dest_eq(&it.goal).ok_or_else(|| {
            ScriptError::Syntax(format!("funext: goal is not an equation: {}", it.goal))
        })?;
        let f_ty = f.type_of()?;
        let alpha = match f_ty.kind() {
            covalence_core::TypeKind::Fun(dom, _cod) => dom.clone(),
            _ => {
                return Err(ScriptError::Syntax(format!(
                    "funext: goal `{}` does not equate two functions",
                    it.goal
                )));
            }
        };
        let point = Term::free(name.as_str(), alpha.clone());
        let ctx = HolLightCtx::new();
        // The pointwise goal `f x = g x`.
        it.goal = ctx.mk_eq(Term::app(f, point.clone()), Term::app(g, point))?;
        it.scope.open();
        it.scope.define(name.clone(), alpha.clone());
        let inner = it.run(rest).await;
        it.scope.close();
        it.env.funext(&inner?)
    }
    async fn rule(&self, a: &[SExpr], c: &mut CheckCtx<'_>) -> R<Thm> {
        ctx_arity(a, 1, "funext")?;
        let sub = c.check(&a[0]).await?;
        c.env().funext(&sub)
    }
}

/// `(#comp HEAD STEP…)` — a **calculational / stepwise equational** proof
/// (`docs/surface-syntax.md` §5.1). The chain starts at `HEAD`; each `STEP` is
/// `(= RHS [JUST])`, asserting `prev = RHS`. The steps fold under `trans` into
/// one end-to-end `⊢ HEAD = <last RHS>`.
///
/// - An explicit `JUST` is any tree-mode derivation proving `⊢ prev = RHS`
///   (e.g. `(beta …)`, `(rw lemma …)`, `(apply foo …)`, a bare lemma name).
/// - An **omitted** `JUST` is closed by the *default handler*: the
///   `#:by DERIV`-named one if the block sets it, else the equational seam
///   [`Env::comp_default`](super::Env::comp_default). A step the default cannot
///   close is a diagnostic naming that step — never a silent gap.
///
/// `#comp` is a proof-level construct (a tree-mode rule), NOT a top-level
/// directive: it works anywhere a derivation does (`(#proof (#comp …))`, inside
/// `derive`, as a `#comp` step's own justification, …).
struct Comp;
#[async_trait]
impl Tactic for Comp {
    async fn rule(&self, a: &[SExpr], c: &mut CheckCtx<'_>) -> R<Thm> {
        if a.is_empty() {
            return Err(ScriptError::Syntax(
                "#comp: expected a head term and at least one step".into(),
            ));
        }
        // Optional `#:by DEFAULT` after the head: a tree-mode derivation that,
        // applied to a single step's `(= prev rhs)` equation goal, closes it.
        // We carry it as the SExpr of the default justification; an omitted
        // step substitutes it (its `prev`/`rhs` are spliced via the seam below
        // — for the built-in default we call `comp_default` directly).
        let head = c.term(&a[0])?;
        let mut idx = 1;
        let mut default: Option<&SExpr> = None;
        if a.get(idx).and_then(|s| s.as_symbol()) == Some("#:by") {
            default = a.get(idx + 1);
            if default.is_none() {
                return Err(ScriptError::Syntax(
                    "#comp: `#:by` must be followed by a default justification".into(),
                ));
            }
            idx += 2;
        }
        let steps = &a[idx..];
        if steps.is_empty() {
            return Err(ScriptError::Syntax("#comp: expected at least one step".into()));
        }
        let mut prev = head;
        let mut chain: Option<Thm> = None;
        for (i, step) in steps.iter().enumerate() {
            let st = list(step, "#comp step")?;
            // Each step is `(= RHS [JUST])`. (Only `=` for now; other relations
            // come with a transitivity registry — see §5.1.)
            if head_sym(st)? != "=" {
                return Err(ScriptError::Syntax(format!(
                    "#comp: step {} must be `(= RHS [JUST])`, got `{}`",
                    i + 1,
                    head_sym(st).unwrap_or("?")
                )));
            }
            if st.len() < 2 || st.len() > 3 {
                return Err(ScriptError::Syntax(format!(
                    "#comp: step {} must be `(= RHS)` or `(= RHS JUST)`",
                    i + 1
                )));
            }
            let rhs = c.term(&st[1])?;
            // The step equation `⊢ prev = rhs`.
            let step_eq = if let Some(just) = st.get(2) {
                // Explicit justification.
                comp_check_step(just, &prev, &rhs, i, c).await?
            } else if let Some(def) = default {
                // Omitted: run the block default handler on this step.
                comp_check_step(def, &prev, &rhs, i, c).await?
            } else {
                // Omitted, no block default: the equational seam.
                c.env().comp_default(&prev, &rhs).map_err(|e| {
                    ScriptError::Syntax(format!("#comp: step {} (omitted): {e}", i + 1))
                })?
            };
            // Fold into the running chain.
            chain = Some(match chain {
                None => step_eq,
                Some(ch) => ch.trans(step_eq)?,
            });
            prev = rhs;
        }
        Ok(chain.expect("at least one step"))
    }
}

/// Run a `#comp` step's justification and validate it proves `⊢ prev = rhs`.
async fn comp_check_step(
    just: &SExpr,
    prev: &Term,
    rhs: &Term,
    i: usize,
    c: &mut CheckCtx<'_>,
) -> R<Thm> {
    let eq = check(just, c).await?;
    let (l, r) = dest_eq(eq.concl()).ok_or_else(|| {
        ScriptError::Syntax(format!(
            "#comp: step {} justification did not prove an equation",
            i + 1
        ))
    })?;
    if &l != prev || &r != rhs {
        return Err(ScriptError::Syntax(format!(
            "#comp: step {} justification proved `{l} = {r}`, expected `{prev} = {rhs}`",
            i + 1
        )));
    }
    Ok(eq)
}

/// `(apply LEMMA PREMISE…)` — apply a lemma by first-order matching. The tactic
/// facet matches LEMMA's conclusion against the **goal** (instantiating its `∀`s
/// and type-vars), discharging any premises with the given sub-derivations and
/// closing the goal in one go (mirroring Coq's `apply`). The tree facet
/// `(apply LEMMA TARGET PREMISE…)` proves an explicit TARGET the same way.
/// Unification is delegated to [`Env::apply_unify`](super::Env::apply_unify) so
/// it can later be customised by a registered handler.
struct Apply;
#[async_trait]
impl Tactic for Apply {
    async fn apply(&self, s: &[SExpr], rest: &[SExpr], it: &mut Interp) -> R<Thm> {
        if s.len() < 2 {
            return Err(ScriptError::Syntax("apply: expected a lemma name".into()));
        }
        expect_done(rest, "apply")?;
        let name = sym(&s[1], "apply lemma")?.to_string();
        let env = it.env.clone();
        let lemma = lookup_lemma(&env, &name).await?;
        let mut thm = env.apply_unify(&lemma, &it.goal)?; // ⊢ P₁⟹…⟹goal
        for p in &s[2..] {
            let prem = check(p, &mut CheckCtx::new(&env, &mut it.scope)).await?;
            thm = thm.imp_elim(prem)?;
        }
        Ok(thm)
    }
    async fn rule(&self, a: &[SExpr], c: &mut CheckCtx<'_>) -> R<Thm> {
        if a.len() < 2 {
            return Err(ScriptError::Syntax(
                "apply: expected a lemma name and a target term".into(),
            ));
        }
        let name = c.name(&a[0])?;
        let target = c.term(&a[1])?;
        let env = c.env().clone();
        let lemma = lookup_lemma(&env, &name).await?;
        let mut thm = env.apply_unify(&lemma, &target)?;
        for p in &a[2..] {
            let prem = c.check(p).await?;
            thm = thm.imp_elim(prem)?;
        }
        Ok(thm)
    }
}

/// Look up a lemma by name (awaiting a still-`#spawn`-ing one).
async fn lookup_lemma(env: &Env, name: &str) -> R<Thm> {
    env.lookup_lemma(name)
        .await
        .ok_or_else(|| ScriptError::Unbound(format!("lemma `{name}`")))?
}

/// `(#have FACT PROOF STEP…)`: prove a fact, add it to context, run the rest.
struct Have;
#[async_trait]
impl Tactic for Have {
    async fn apply(&self, s: &[SExpr], rest: &[SExpr], it: &mut Interp) -> R<Thm> {
        arity(s, 3, "#have")?;
        let env = it.env.clone();
        let fact = parse_term(&s[1], &mut it.scope, &env)?;
        let sub = prove_with(&fact, &s[2], &mut it.scope, &it.hyps, &env).await?;
        it.hyps.push((fact, Hyp::Proven(sub)));
        let result = it.run(rest).await;
        it.hyps.pop();
        result
    }
}

/// `(induct VAR BASE STEP)`: nat induction on the leading `∀`.
struct Induct;
#[async_trait]
impl Tactic for Induct {
    async fn apply(&self, s: &[SExpr], rest: &[SExpr], it: &mut Interp) -> R<Thm> {
        arity(s, 4, "induct")?;
        expect_done(rest, "induct")?;
        let env = it.env.clone();
        let var = sym(&s[1], "induct variable")?.to_string();
        let (ty, body) = dest_forall(&it.goal).ok_or_else(|| {
            ScriptError::Syntax(format!("induct: goal is not a `∀`: {}", it.goal))
        })?;
        if ty != Type::nat() {
            return Err(ScriptError::Syntax(format!(
                "induct: goal quantifies over {ty}, not nat"
            )));
        }
        let p = Term::abs(Type::nat(), body.clone());
        let zero = Term::nat_lit(0u64);

        let base_body = prove_with(
            &subst::open(&body, &zero),
            &s[2],
            &mut it.scope,
            &it.hyps,
            &env,
        )
        .await?;
        let base = Thm::beta_conv(Term::app(p.clone(), zero))?
            .sym()?
            .eq_mp(base_body)?;

        let v = Term::free(var.as_str(), Type::nat());
        let ih = subst::open(&body, &v);
        let sv = Term::app(Term::succ(), v.clone());
        let mut step_hyps = it.hyps.clone();
        step_hyps.push((ih.clone(), Hyp::Assumed));
        it.scope.open();
        it.scope.define(var.clone(), Type::nat());
        let step_body = prove_with(
            &subst::open(&body, &sv),
            &s[3],
            &mut it.scope,
            &step_hyps,
            &env,
        )
        .await;
        it.scope.close();
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
}

/// `(list-induct VAR BASE STEP)`: structural list induction on the leading
/// `∀l. P l` (with `l : list α`). `BASE` proves `P nil`; `STEP` proves
/// `P (cons VAR xs)` for a fresh head `VAR : α` and tail `xs : list α`, with
/// the induction hypothesis `P xs` available as a context fact. Routed
/// through the genuine [`crate::init::list::list_induct`] theorem. `xs` is the
/// fixed name of the tail; the IH is the proposition `P xs`.
struct ListInduct;
#[async_trait]
impl Tactic for ListInduct {
    async fn apply(&self, s: &[SExpr], rest: &[SExpr], it: &mut Interp) -> R<Thm> {
        arity(s, 4, "list-induct")?;
        expect_done(rest, "list-induct")?;
        let env = it.env.clone();
        let var = sym(&s[1], "list-induct head variable")?.to_string();

        // Goal `∀l. body`, with `l : list α`.
        let (ty, body) = dest_forall(&it.goal).ok_or_else(|| {
            ScriptError::Syntax(format!("list-induct: goal is not a `∀`: {}", it.goal))
        })?;
        let alpha = dest_list(&ty).ok_or_else(|| {
            ScriptError::Syntax(format!("list-induct: goal quantifies over {ty}, not a list"))
        })?;
        let p = Term::abs(ty.clone(), body.clone()); // motive λl. body

        // base: ⊢ P nil, in the applied form `(λl. body) nil`.
        let nil = defs::nil(alpha.clone());
        let base_body = prove_with(
            &subst::open(&body, &nil),
            &s[2],
            &mut it.scope,
            &it.hyps,
            &env,
        )
        .await?;
        let pl_nil = Thm::beta_conv(Term::app(p.clone(), nil.clone()))?
            .sym()?
            .eq_mp(base_body)?; // ⊢ (λl. body) nil

        // step: under fresh `var : α`, `xs : list α`, IH `P xs`, prove
        // `P (cons var xs)`. Then ∀-close into `∀x xs. P xs ⟹ P (cons x xs)`.
        let la = ty.clone();
        let x = Term::free(var.as_str(), alpha.clone());
        let xs = Term::free("xs", la.clone());
        let ih = subst::open(&body, &xs); // P xs (β-reduced body)
        let consed = Term::app(Term::app(defs::cons(alpha.clone()), x.clone()), xs.clone());

        let mut step_hyps = it.hyps.clone();
        step_hyps.push((ih.clone(), Hyp::Assumed));
        it.scope.open();
        it.scope.define(var.clone(), alpha.clone());
        it.scope.define("xs".to_string(), la.clone());
        let step_body = prove_with(
            &subst::open(&body, &consed),
            &s[3],
            &mut it.scope,
            &step_hyps,
            &env,
        )
        .await;
        it.scope.close();
        let step_body = step_body?; // {P xs} ⊢ P (cons var xs)  (β-reduced)

        // Bridge both sides to the applied-motive form `(λl.body) xs ⟹
        // (λl.body)(cons x xs)` that `list_induct` consumes.
        let ea = Thm::beta_conv(Term::app(p.clone(), xs.clone()))?; // (λl.body) xs = P xs
        let eb = Thm::beta_conv(Term::app(p.clone(), consed.clone()))?; // (λl.body)(cons x xs) = …
        let step_imp = step_body.imp_intro(&ih)?; // ⊢ P xs ⟹ P (cons x xs)
        let cons_case = Thm::refl(defs::imp())?
            .mk_comb(ea.sym()?)?
            .mk_comb(eb.sym()?)?
            .eq_mp(step_imp)? // ⊢ (λl.body) xs ⟹ (λl.body)(cons x xs)
            .all_intro("xs", la)?
            .all_intro(&var, alpha.clone())?; // ⊢ ∀x xs. …

        let ind = crate::init::list::list_induct(&alpha, &p, pl_nil, cons_case)
            .map_err(ScriptError::Kernel)?; // ⊢ ∀l. (λl. body) l
        // β-normalise the applied-motive body back to `∀l. body`.
        let nf = crate::proofs::rewrite::beta_nf(ind.concl().clone());
        Ok(nf.eq_mp(ind)?)
    }
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

/// If `ty` is `list α` (a `list_spec` application), return its element type
/// `α`. Used by the `list-induct` tactic to recover the element type.
fn dest_list(ty: &Type) -> Option<Type> {
    let covalence_core::TypeKind::Spec(spec, args) = ty.kind() else {
        return None;
    };
    (spec.symbol().label() == defs::list_spec().symbol().label() && args.len() == 1)
        .then(|| args[0].clone())
}

fn dest_not(t: &Term) -> Option<Term> {
    let not = defs::not();
    let TermKind::App(h, p) = t.kind() else {
        return None;
    };
    (*h == not).then(|| p.clone())
}
