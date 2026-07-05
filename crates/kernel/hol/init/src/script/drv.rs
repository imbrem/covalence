//! The **proof replayer** ([`check`]) and the **derivation registry**.
//!
//! A `#proof` body is untrusted *data*: a transcript of which kernel rules to
//! apply, e.g. `(trans (refl a) (sym (foo)))`. It carries no soundness of
//! its own — [`check`] replays it by dispatching each head through the **rule
//! registry** ([`Env`]'s `rules`) and the matched [`Rule`] calls the real
//! `covalence-core` rules, each of which re-validates. A corrupt or hostile
//! proof can at worst fail to check or produce a different (still kernel-valid)
//! theorem; it can never manufacture an unsound `Thm`.
//!
//! Unlike a hardcoded interpreter, the proof-rule vocabulary lives in the
//! registry — exactly like the tactic registry. [`core_rules`] installs the
//! built-ins (`refl`, `trans`, `nat-induct`, …); a host can register its own
//! (possibly async — an observer, a peer prover, the user) without touching
//! this file. Each [`Rule`] gets the raw S-expr arguments plus a [`CheckCtx`],
//! so it **self-parses** its terms/types/sub-derivations — there is no separate
//! parse pass and no `Drv` AST. None of this is extra trust: registry rules
//! still bottom out in real kernel `Thm`s.
//!
//! [`check`] is **async** (a `Rule` may await) so it returns a `BoxFuture` —
//! the recursion through `Rule::apply` needs a known size.

use std::sync::Arc;

use async_trait::async_trait;
use covalence_core::{Term, TermKind, Thm, Type};
use covalence_sexp::SExpr;
use futures::future::BoxFuture;

use super::ScriptError;
use super::env::Env;
use super::scope::Scope;
use super::syntax::{head_sym, list, parse_term, parse_type, sym};
use super::tactic::Tactic;

type R<T> = Result<T, ScriptError>;

// ============================================================================
// CheckCtx — what a rule needs to resolve its arguments
// ============================================================================

/// The replay context handed to every `Rule`: the resolution [`Env`] and the
/// mutable proof [`Scope`]. A rule uses it to parse term/type/name arguments
/// and to recursively [`check`](CheckCtx::check) sub-derivations. Binder rules
/// extend the scope (via [`push_var`](CheckCtx::push_var)) for their sub-proof.
pub struct CheckCtx<'a> {
    env: &'a Env,
    scope: &'a mut Scope,
}

impl<'a> CheckCtx<'a> {
    /// Build a context over an environment and proof scope.
    pub fn new(env: &'a Env, scope: &'a mut Scope) -> Self {
        CheckCtx { env, scope }
    }

    /// The resolution environment (for rules that look up lemmas, etc.).
    pub fn env(&self) -> &Env {
        self.env
    }

    /// Parse a term argument, resolved against the env + current scope.
    pub fn term(&mut self, s: &SExpr) -> R<Term> {
        parse_term(s, self.scope, self.env)
    }

    /// Parse a type argument.
    pub fn ty(&self, s: &SExpr) -> R<Type> {
        parse_type(s, self.env)
    }

    /// Read a bare symbol argument (a variable / lemma name).
    pub fn name(&self, s: &SExpr) -> R<String> {
        Ok(sym(s, "name")?.to_string())
    }

    /// Extend the scope with a bound variable for a sub-derivation (paired with
    /// [`pop_var`](CheckCtx::pop_var)).
    pub fn push_var(&mut self, name: &str, ty: Type) {
        self.scope.open();
        self.scope.define(name.to_string(), ty);
    }

    /// Undo the most recent [`push_var`](CheckCtx::push_var).
    pub fn pop_var(&mut self) {
        self.scope.close();
    }

    /// Recursively replay a sub-derivation S-expr into a theorem.
    pub async fn check(&mut self, s: &SExpr) -> R<Thm> {
        check(s, self).await
    }
}

/// Check a rule received exactly `n` arguments (head excluded).
pub(super) fn ctx_arity(args: &[SExpr], n: usize, rule: &str) -> R<()> {
    if args.len() != n {
        return Err(ScriptError::Syntax(format!(
            "rule `{rule}` expects {n} argument(s), got {}",
            args.len()
        )));
    }
    Ok(())
}

// ============================================================================
// The replayer
// ============================================================================

// A derivation rule is just the tree-mode facet of a [`Tactic`]: given its raw
// S-expr arguments and a [`CheckCtx`], `Tactic::rule` self-parses (terms/types/
// sub-derivations) and produces a kernel theorem. The structs below override
// only `rule` (their `apply` defaults to a "not a tactic" error); the dual-mode
// inferences (`refl`/`sym`/`not-intro`/`rw`) live in `tactic.rs` and override
// both.

/// Replay a proof S-expr into a kernel theorem by dispatching its head through
/// the [`Env`] registry and invoking the matched inference's `rule` facet. The
/// sole kernel-coupled surface in the script layer (each built-in rule is
/// one-or-few kernel calls). `async` — a rule may await — so it returns a boxed
/// future (the recursion needs a known size).
pub fn check<'a>(s: &'a SExpr, ctx: &'a mut CheckCtx<'_>) -> BoxFuture<'a, R<Thm>> {
    Box::pin(async move {
        // A bare symbol `NAME` is a 0-witness reference (the lemma's statement);
        // a list `(head args…)` dispatches `head` with its args.
        if let Some(name) = s.as_symbol() {
            return resolve_head(name, &[], ctx).await;
        }
        let ch = list(s, "proof")?;
        resolve_head(head_sym(ch)?, &ch[1..], ctx).await
    })
}

/// Resolve a `#proof` head: a registered RULE (invoked with its args), else a
/// LEMMA name instantiated at the explicit term witnesses — `NAME` / `(NAME)` is
/// the lemma's full statement, `(NAME w…)` `all-elim`s it at `w…`. (`apply` is
/// the smarter, unifying form.)
async fn resolve_head(head: &str, args: &[SExpr], ctx: &mut CheckCtx<'_>) -> R<Thm> {
    if let Some(op) = ctx.env().lookup_rule(head) {
        return op.rule(args, ctx).await;
    }
    let lemma =
        ctx.env().lookup_lemma(head).await.ok_or_else(|| {
            ScriptError::Unbound(format!("unknown proof rule or lemma `{head}`"))
        })??;
    let mut thm = lemma;
    for w in args {
        let witness = ctx.term(w)?;
        thm = thm.all_elim(witness)?;
    }
    Ok(thm)
}

// ============================================================================
// Built-in rules
// ============================================================================

/// `(NAME TERM)` → build a theorem from one parsed term.
macro_rules! term_rule {
    ($S:ident, $name:literal, $build:expr) => {
        struct $S;
        #[async_trait]
        impl Tactic for $S {
            async fn rule(&self, a: &[SExpr], c: &mut CheckCtx<'_>) -> R<Thm> {
                ctx_arity(a, 1, $name)?;
                let t = c.term(&a[0])?;
                #[allow(clippy::redundant_closure_call)]
                ($build)(t)
            }
        }
    };
}

/// `(NAME SUB)` → `check(SUB).METHOD()`.
macro_rules! unary_rule {
    ($S:ident, $name:literal, $m:ident) => {
        struct $S;
        #[async_trait]
        impl Tactic for $S {
            async fn rule(&self, a: &[SExpr], c: &mut CheckCtx<'_>) -> R<Thm> {
                ctx_arity(a, 1, $name)?;
                let s = c.check(&a[0]).await?;
                Ok(s.$m()?)
            }
        }
    };
}

/// `(NAME A B)` → `check(A).METHOD(check(B))`.
macro_rules! binary_rule {
    ($S:ident, $name:literal, $m:ident) => {
        struct $S;
        #[async_trait]
        impl Tactic for $S {
            async fn rule(&self, a: &[SExpr], c: &mut CheckCtx<'_>) -> R<Thm> {
                ctx_arity(a, 2, $name)?;
                let x = c.check(&a[0]).await?;
                let y = c.check(&a[1]).await?;
                Ok(x.$m(y)?)
            }
        }
    };
}

/// `(NAME TERM SUB)` → combine a parsed term with one checked sub-derivation.
macro_rules! term_sub_rule {
    ($S:ident, $name:literal, $f:expr) => {
        struct $S;
        #[async_trait]
        impl Tactic for $S {
            async fn rule(&self, a: &[SExpr], c: &mut CheckCtx<'_>) -> R<Thm> {
                ctx_arity(a, 2, $name)?;
                let t = c.term(&a[0])?;
                let s = c.check(&a[1]).await?;
                #[allow(clippy::redundant_closure_call)]
                ($f)(t, s)
            }
        }
    };
}

// -- leaves -----------------------------------------------------------------
// (`refl` is dual-mode — its rule facet lives on the `Refl` inference in tactic.rs.)
term_rule!(AssumeRule, "assume", |t| Ok(Thm::assume(t)?));
term_rule!(LemRule, "lem", |t| Ok(Thm::lem(t)?));
// `(reduce-prim TERM)` → `⊢ TERM = value`: single-step closed primitive
// computation, routed through the untrusted cert-path driver
// (`covalence-hol-eval`) — same catalogue and conclusions as the legacy
// kernel rule it replaces, so existing `.cov` scripts replay unchanged.
term_rule!(ReducePrimRule, "reduce-prim", |t: Term| Ok(
    covalence_hol_eval::reduce(&t).ok_or(covalence_core::Error::NotReducible)?
));
term_rule!(UnfoldTermSpecRule, "unfold-term-spec", |t| Ok(
    Thm::unfold_term_spec(t)?
));
term_rule!(BetaConvRule, "beta-conv", |t| Ok(Thm::beta_conv(t)?));
// `(eta-conv (λx. f x))` → `⊢ (λx. f x) = f`.
term_rule!(EtaConvRule, "eta-conv", |t| Ok(Thm::eta_conv(t)?));
// `(reduce TERM)` → `⊢ TERM = TERM'` where TERM' is the full βι normal form
// (β-reduction + primitive constant folding); the conversion workhorse for
// subtype/spec proofs. `(delta TERM)` → `⊢ TERM = body` δ-unfolds the head
// `TermSpec` (one definitional step).
term_rule!(ReduceRule, "reduce", |t| Ok(
    <Term as crate::init::ext::TermExt>::reduce(&t)?
));
term_rule!(DeltaRule, "delta", |t| Ok(
    <Term as crate::init::ext::TermExt>::delta(&t)?
));
// `tauto`: prove a propositional / closed-arithmetic tautology via
// `crate::init::logic::tauto`.
term_rule!(TautoRule, "tauto", |t| Ok(crate::init::logic::tauto(&t)?));

/// `(select-ax PRED WITNESS)` → `⊢ PRED WITNESS ⟹ PRED (ε PRED)` — the Hilbert
/// ε axiom (choice). Used by the subtype/option/cond seam proofs.
struct SelectAxRule;
#[async_trait]
impl Tactic for SelectAxRule {
    async fn rule(&self, a: &[SExpr], c: &mut CheckCtx<'_>) -> R<Thm> {
        ctx_arity(a, 2, "select-ax")?;
        let p = c.term(&a[0])?;
        let x = c.term(&a[1])?;
        Ok(Thm::select_ax(p, x)?)
    }
}

/// `(prop-eq P Q)` → `⊢ P = Q` when `P` and `Q` are propositionally equal
/// (Shannon expansion over their shared atoms, via [`crate::init::logic::prop_eq`]).
/// The complete propositional decider — stronger than `tauto` (which only folds
/// trivial tautologies to `T`); the bridge the set-algebra proofs need.
struct PropEqRule;
#[async_trait]
impl Tactic for PropEqRule {
    async fn rule(&self, a: &[SExpr], c: &mut CheckCtx<'_>) -> R<Thm> {
        ctx_arity(a, 2, "prop-eq")?;
        let p = c.term(&a[0])?;
        let q = c.term(&a[1])?;
        Ok(crate::init::logic::prop_eq(&p, &q)?)
    }
}

/// `(exists-intro PRED WITNESS PROOF)` → from `PROOF : ⊢ PRED WITNESS`
/// conclude `⊢ ∃x. PRED x` (i.e. `⊢ exists[α] PRED`). `PRED : α → bool` and
/// `WITNESS : α` are parsed terms; `PROOF` is a checked sub-derivation.
struct ExistsIntroRule;
#[async_trait]
impl Tactic for ExistsIntroRule {
    async fn rule(&self, a: &[SExpr], c: &mut CheckCtx<'_>) -> R<Thm> {
        ctx_arity(a, 3, "exists-intro")?;
        let pred = c.term(&a[0])?;
        let witness = c.term(&a[1])?;
        let proof = c.check(&a[2]).await?;
        Ok(crate::init::logic::exists_intro(pred, witness, proof)?)
    }
}

/// `(exists-elim EX C STEP)` → from `EX : ⊢ ∃x. P x` and
/// `STEP : ⊢ ∀x. P x ⟹ C` (with `C` not depending on `x`) conclude `⊢ C`.
/// `EX` and `STEP` are checked sub-derivations; `C` is a parsed term.
struct ExistsElimRule;
#[async_trait]
impl Tactic for ExistsElimRule {
    async fn rule(&self, a: &[SExpr], c: &mut CheckCtx<'_>) -> R<Thm> {
        ctx_arity(a, 3, "exists-elim")?;
        let ex = c.check(&a[0]).await?;
        let goal = c.term(&a[1])?;
        let step = c.check(&a[2]).await?;
        Ok(crate::init::logic::exists_elim(ex, goal, step)?)
    }
}

/// `(congr HEAD EQ…)` → `⊢ head a₁ … = head b₁ …` from the per-argument
/// equations `EQ… : ⊢ aᵢ = bᵢ`. The n-ary generalization of `cong-arg` /
/// `cong-fn` — routed through the [`Env::congr`](crate::script::Env::congr)
/// congruence seam so a logic can later override it. `HEAD` is the common
/// function term; each `EQ` rewrites one argument position, left to right.
struct CongrRule;
#[async_trait]
impl Tactic for CongrRule {
    async fn rule(&self, a: &[SExpr], c: &mut CheckCtx<'_>) -> R<Thm> {
        if a.is_empty() {
            return Err(ScriptError::Syntax(
                "congr: expected a head term and zero or more argument equations".into(),
            ));
        }
        let head = c.term(&a[0])?;
        let mut arg_eqs = Vec::with_capacity(a.len() - 1);
        for e in &a[1..] {
            arg_eqs.push(c.check(e).await?);
        }
        c.env().congr(&head, &arg_eqs)
    }
}

/// `(unfold-at-1 OP ARG)` → `⊢ op arg = body[arg]` (one β-step).
struct UnfoldAt1Rule;
#[async_trait]
impl Tactic for UnfoldAt1Rule {
    async fn rule(&self, a: &[SExpr], c: &mut CheckCtx<'_>) -> R<Thm> {
        ctx_arity(a, 2, "unfold-at-1")?;
        let op = c.term(&a[0])?;
        let arg = c.term(&a[1])?;
        Ok(crate::proofs::rewrite::unfold_at_1(op, arg))
    }
}

/// `(unfold-at-2 OP A B)` → `⊢ op a b = body[a,b]`.
struct UnfoldAt2Rule;
#[async_trait]
impl Tactic for UnfoldAt2Rule {
    async fn rule(&self, a: &[SExpr], c: &mut CheckCtx<'_>) -> R<Thm> {
        ctx_arity(a, 3, "unfold-at-2")?;
        let op = c.term(&a[0])?;
        let x = c.term(&a[1])?;
        let y = c.term(&a[2])?;
        Ok(crate::proofs::rewrite::unfold_at_2(op, x, y))
    }
}

// -- unary ------------------------------------------------------------------
// (`sym`/`not-intro` are dual-mode — their rule facets are in tactic.rs.)
unary_rule!(AndElimLRule, "and-elim-l", and_elim_l);
unary_rule!(AndElimRRule, "and-elim-r", and_elim_r);

// -- term + sub -------------------------------------------------------------
term_sub_rule!(ImpIntroRule, "imp-intro", |t, s: Thm| Ok(s.imp_intro(&t)?));
term_sub_rule!(AllElimRule, "all-elim", |t, s: Thm| Ok(s.all_elim(t)?));
term_sub_rule!(OrIntroLRule, "or-intro-l", |t, s: Thm| Ok(s.or_intro_l(t)?));
term_sub_rule!(OrIntroRRule, "or-intro-r", |t, s: Thm| Ok(s.or_intro_r(t)?));
term_sub_rule!(
    FalseElimRule,
    "false-elim",
    |t, s: Thm| Ok(s.false_elim(t)?)
);
// `(cong-arg F SUB)` → `⊢ f a = f b` from `⊢ a = b`.
term_sub_rule!(CongArgRule, "cong-arg", |t, s: Thm| Ok(
    Thm::refl(t)?.mk_comb(s)?
));
// `(cong-fn ARG SUB)` → `⊢ f a = g a` from `⊢ f = g`.
term_sub_rule!(CongFnRule, "cong-fn", |t, s: Thm| Ok(
    s.mk_comb(Thm::refl(t)?)?
));

// -- name + term + sub ------------------------------------------------------
/// `(inst VAR TERM SUB)` — instantiate a free variable.
struct InstRule;
#[async_trait]
impl Tactic for InstRule {
    async fn rule(&self, a: &[SExpr], c: &mut CheckCtx<'_>) -> R<Thm> {
        ctx_arity(a, 3, "inst")?;
        let name = c.name(&a[0])?;
        let term = c.term(&a[1])?;
        let s = c.check(&a[2]).await?;
        Ok(s.inst(&name, term)?)
    }
}

/// `(inst-tfree VAR TYPE SUB)` — type-variable instantiation (HOL Light
/// `INST_TYPE`), the way a *polymorphic* lemma is applied at a concrete type.
struct InstTfreeRule;
#[async_trait]
impl Tactic for InstTfreeRule {
    async fn rule(&self, a: &[SExpr], c: &mut CheckCtx<'_>) -> R<Thm> {
        ctx_arity(a, 3, "inst-tfree")?;
        let name = c.name(&a[0])?;
        let ty = c.ty(&a[1])?;
        let s = c.check(&a[2]).await?;
        Ok(s.inst_tfree(&name, ty)?)
    }
}

// -- binder-introducing: NAME TYPE SUB (NAME is free in the sub-proof) -------
/// `(abs-rule VAR TYPE SUB)` — abstraction under a binder.
struct AbsRuleRule;
#[async_trait]
impl Tactic for AbsRuleRule {
    async fn rule(&self, a: &[SExpr], c: &mut CheckCtx<'_>) -> R<Thm> {
        ctx_arity(a, 3, "abs-rule")?;
        let name = c.name(&a[0])?;
        let ty = c.ty(&a[1])?;
        c.push_var(&name, ty.clone());
        let sub = c.check(&a[2]).await;
        c.pop_var();
        Ok(sub?.abs(&name, ty)?)
    }
}

/// `(all-intro VAR TYPE SUB)` — universal generalization.
struct AllIntroRule;
#[async_trait]
impl Tactic for AllIntroRule {
    async fn rule(&self, a: &[SExpr], c: &mut CheckCtx<'_>) -> R<Thm> {
        ctx_arity(a, 3, "all-intro")?;
        let name = c.name(&a[0])?;
        let ty = c.ty(&a[1])?;
        c.push_var(&name, ty.clone());
        let sub = c.check(&a[2]).await;
        c.pop_var();
        Ok(sub?.all_intro(&name, ty)?)
    }
}

// -- binary -----------------------------------------------------------------
binary_rule!(TransRule, "trans", trans);
binary_rule!(MkCombRule, "mk-comb", mk_comb);
binary_rule!(EqMpRule, "eq-mp", eq_mp);
binary_rule!(ImpElimRule, "imp-elim", imp_elim);
binary_rule!(DeductAntisymRule, "deduct-antisym", deduct_antisym);
binary_rule!(AndIntroRule, "and-intro", and_intro);
binary_rule!(NotElimRule, "not-elim", not_elim);

/// `(nat-induct BASE STEP)` → `∀n. P n` from the base case and step.
struct NatInductRule;
#[async_trait]
impl Tactic for NatInductRule {
    async fn rule(&self, a: &[SExpr], c: &mut CheckCtx<'_>) -> R<Thm> {
        ctx_arity(a, 2, "nat-induct")?;
        let base = c.check(&a[0]).await?;
        let step = c.check(&a[1]).await?;
        Ok(Thm::nat_induct(base, step)?)
    }
}

// -- ternary ----------------------------------------------------------------
/// `(or-elim DISJ LEFT RIGHT)` — case split on a disjunction.
struct OrElimRule;
#[async_trait]
impl Tactic for OrElimRule {
    async fn rule(&self, a: &[SExpr], c: &mut CheckCtx<'_>) -> R<Thm> {
        ctx_arity(a, 3, "or-elim")?;
        let disj = c.check(&a[0]).await?;
        let left = c.check(&a[1]).await?;
        let right = c.check(&a[2]).await?;
        Ok(disj.or_elim(left, right)?)
    }
}

// (`rw` is dual-mode — its rule facet is on the `Rw` inference in tactic.rs.)

/// The built-in derivation vocabulary — installed into every [`Env::core`].
/// Each entry is `(head, rule)`; a host may register more via
/// [`Env::register_rule`] without touching this file. The dual-mode inferences
/// (`refl`/`sym`/`not-intro`/`rw`) are NOT here — they are registered once as
/// tactics (`tactic.rs`) and carry their `rule` facet with them.
pub fn core_rules() -> Vec<(&'static str, Arc<dyn Tactic>)> {
    vec![
        // leaves
        ("assume", Arc::new(AssumeRule)),
        ("lem", Arc::new(LemRule)),
        ("reduce-prim", Arc::new(ReducePrimRule)),
        ("unfold-term-spec", Arc::new(UnfoldTermSpecRule)),
        ("unfold-at-1", Arc::new(UnfoldAt1Rule)),
        ("unfold-at-2", Arc::new(UnfoldAt2Rule)),
        ("beta-conv", Arc::new(BetaConvRule)),
        ("eta-conv", Arc::new(EtaConvRule)),
        ("reduce", Arc::new(ReduceRule)),
        ("delta", Arc::new(DeltaRule)),
        ("select-ax", Arc::new(SelectAxRule)),
        ("prop-eq", Arc::new(PropEqRule)),
        ("exists-intro", Arc::new(ExistsIntroRule)),
        ("exists-elim", Arc::new(ExistsElimRule)),
        ("tauto", Arc::new(TautoRule)),
        // unary
        ("and-elim-l", Arc::new(AndElimLRule)),
        ("and-elim-r", Arc::new(AndElimRRule)),
        // term + sub
        ("imp-intro", Arc::new(ImpIntroRule)),
        ("all-elim", Arc::new(AllElimRule)),
        ("or-intro-l", Arc::new(OrIntroLRule)),
        ("or-intro-r", Arc::new(OrIntroRRule)),
        ("false-elim", Arc::new(FalseElimRule)),
        ("cong-arg", Arc::new(CongArgRule)),
        ("cong-fn", Arc::new(CongFnRule)),
        ("congr", Arc::new(CongrRule)),
        // name + term/type + sub
        ("inst", Arc::new(InstRule)),
        ("inst-tfree", Arc::new(InstTfreeRule)),
        // binders
        ("abs-rule", Arc::new(AbsRuleRule)),
        ("all-intro", Arc::new(AllIntroRule)),
        // binary
        ("trans", Arc::new(TransRule)),
        ("mk-comb", Arc::new(MkCombRule)),
        ("eq-mp", Arc::new(EqMpRule)),
        ("imp-elim", Arc::new(ImpElimRule)),
        ("deduct-antisym", Arc::new(DeductAntisymRule)),
        ("and-intro", Arc::new(AndIntroRule)),
        ("not-elim", Arc::new(NotElimRule)),
        // ternary
        ("or-elim", Arc::new(OrElimRule)),
        ("nat-induct", Arc::new(NatInductRule)),
    ]
}

// ============================================================================
// Rewriting helper (used by the `rw` rule)
// ============================================================================

/// `⊢ t = t'` where `t'` is `t` with every occurrence of the equation's
/// LHS replaced by its RHS, built by congruence. Carries the equation's
/// hypotheses.
///
/// Does not descend under binders (`Abs`) — adequate for the
/// quantifier-free rewriting the tactic targets today; see SKELETONS.md.
pub(super) fn rewrite_conv(t: &Term, eq: &Thm) -> R<Thm> {
    let (lhs, _rhs) = dest_eq(eq.concl())
        .ok_or_else(|| ScriptError::Syntax("rw: equation theorem is not an `=`".into()))?;
    if *t == lhs {
        return Ok(eq.clone());
    }
    Ok(match t.kind() {
        TermKind::App(f, x) => rewrite_conv(f, eq)?.mk_comb(rewrite_conv(x, eq)?)?,
        _ => Thm::refl(t.clone())?,
    })
}

/// Destructure an `=`-headed term `App(App(Eq α, lhs), rhs)`.
fn dest_eq(t: &Term) -> Option<(Term, Term)> {
    let TermKind::App(f, rhs) = t.kind() else {
        return None;
    };
    let TermKind::App(h, lhs) = f.kind() else {
        return None;
    };
    matches!(h.kind(), TermKind::Eq(_)).then(|| (lhs.clone(), rhs.clone()))
}
