//! The prelude [`Env`] — the name→catalogue resolver and **namespace** object.
//!
//! [`Env`] is the single place that absorbs `covalence-core` `defs/` churn:
//! re-point a resolver here and every proof that mentions the name keeps
//! working unchanged. It holds **one** namespace — a name→[`Entry`] map — plus
//! the set of imported sub-namespaces. The transient proof state — the variable
//! [`super::scope::Scope`], goals — lives in [`super::tactic::Interp`], not here.
//!
//! The namespace is a single [`LazyMap`], so **every** kind of definition
//! (const, lemma, tactic, rule) is uniformly **lazy**: a binding may still be
//! computing (today only `#spawn`-ing lemmas; tomorrow a `bytes` const loaded
//! from the network — "one async task per definition"). This is deliberately
//! the *simple* unified design; finer-grained namespaces (separate const/type/
//! tactic spaces, qualified names) can come later.

use std::collections::BTreeSet;
use std::sync::Arc;

use covalence_core::defs::TypeSpec;
use covalence_core::{Term, TermKind, Thm, Type, defs, subst};
use futures::FutureExt;
use imbl::HashMap;
use smol_str::SmolStr;

use super::handle::LazyMap;
use super::unify::{Subst, match_term};
use super::{ScriptError, tactic::Tactic};

type R<T> = Result<T, ScriptError>;

/// How a head symbol resolves to a kernel term.
#[derive(Clone)]
pub enum ConstDef {
    /// A fully-built operator term, applied (curried) to the parsed
    /// argument terms. Monomorphic (the connectives, `nat.add`, …) or
    /// nullary (`true`/`false`).
    Op(Term),
    /// A **polymorphic** operator *scheme*: the carried term's free type
    /// variables are the schematic parameters. Each use site instantiates
    /// them with fresh metavariables, so the same constant can appear at
    /// several type instances within one term (e.g. `rel.converse` at
    /// `(a,b)` and `(b,a)`, or a product constructor at two element types).
    Poly(Term),
    /// Polymorphic HOL equality: the element type is inferred from the
    /// operands.
    Eq,
}

/// A single namespace entry — the kinds of definition share one map. Cloning is
/// cheap (`Arc` / `imbl`-backed kernel data).
///
/// There is **one** callable kind, [`Tactic`]: an inference usable in tactic
/// mode (`apply`), tree mode (`rule`), or both — so a dual-mode name (`sym`,
/// `refl`, `not-intro`, `rw`) is a single object, not two stapled together.
#[derive(Clone)]
enum Entry {
    Const(ConstDef),
    Lemma(Thm),
    Tactic(Arc<dyn Tactic>),
}

/// A name-resolution environment — the **namespace** part of the system: one
/// lazy name→[`Entry`] map (constants, proven lemmas, tactics, rules), plus the
/// set of imported (but not necessarily opened) sub-namespaces. Fields are
/// encapsulated behind methods.
///
/// Backed by [`imbl::HashMap`] **persistent** maps, so cloning an `Env` is
/// O(1) (structural sharing) and mutating a clone is cheap copy-on-write —
/// which is why [`super::tactic::Interp`] can afford to *own* its environment.
#[derive(Clone, Default)]
pub struct Env {
    /// The unified namespace: every definition kind, each possibly still
    /// **computing** (so all lookups are lazy; lemma lookup is `async`).
    entries: LazyMap<Entry>,
    imports: HashMap<String, Env>,
    /// User-defined **type constructors** introduced by the `#newtype` /
    /// `#subtype` / `#quot` directives, resolved by name when a later
    /// type/term is parsed (`parse_type`'s `(NAME ty…)` / bare-`NAME` case).
    /// Kept separate from `entries` because types live in a distinct
    /// namespace from terms (e.g. `option` is both a type ctor and carries
    /// term constructors), and a `TypeSpec` is not an [`Entry`].
    type_specs: HashMap<String, TypeSpec>,
}

impl Env {
    /// An empty environment.
    pub fn empty() -> Self {
        Env::default()
    }

    // -- lookups --------------------------------------------------------
    /// The constant bound to `name`, if it is a ready `Const` entry.
    pub fn lookup_const(&self, name: &str) -> Option<ConstDef> {
        match self.entries.get_ready(name)? {
            Entry::Const(c) => Some(c),
            _ => None,
        }
    }
    /// Look up a lemma, **awaiting** it if it is still computing (`#spawn`).
    /// `None` if unbound (or bound to a non-lemma); `Some(Err)` if its
    /// computation failed.
    pub async fn lookup_lemma(&self, name: &str) -> Option<Result<Thm, ScriptError>> {
        match self.entries.get(name).await? {
            Ok(Entry::Lemma(t)) => Some(Ok(t)),
            Ok(_) => None,
            Err(e) => Some(Err(e)),
        }
    }
    /// Synchronous peek: the lemma only if already proved (not still computing).
    pub fn lemma_ready(&self, name: &str) -> Option<Thm> {
        match self.entries.get_ready(name)? {
            Entry::Lemma(t) => Some(t),
            _ => None,
        }
    }
    /// The inference bound to `name` (tactic-mode dispatch). Same object as
    /// [`lookup_rule`](Env::lookup_rule) — modes differ, not the entry.
    pub fn lookup_tactic(&self, name: &str) -> Option<Arc<dyn Tactic>> {
        match self.entries.get_ready(name)? {
            Entry::Tactic(t) => Some(t),
            _ => None,
        }
    }
    /// The inference bound to `name` (tree-mode dispatch). The caller invokes
    /// its `rule` facet (which errors if the inference is tactic-only).
    pub fn lookup_rule(&self, name: &str) -> Option<Arc<dyn Tactic>> {
        self.lookup_tactic(name)
    }
    /// Whether `name` is bound to a lemma (ready *or* still `#spawn`-ing).
    pub fn has_lemma(&self, name: &str) -> bool {
        match self.entries.get_ready(name) {
            Some(Entry::Lemma(_)) => true,
            Some(_) => false,
            // No ready entry: a *pending* binding is always a #spawn-ing
            // lemma (the only kind that pends today).
            None => self.entries.contains(name),
        }
    }

    // -- definitions ----------------------------------------------------
    pub fn define_const(&mut self, name: impl Into<String>, c: ConstDef) {
        self.entries.insert_ready(name, Entry::Const(c));
    }
    pub fn define_lemma(&mut self, name: impl Into<String>, thm: Thm) {
        self.entries.insert_ready(name, Entry::Lemma(thm));
    }
    /// Bind a lemma to a **spawned** (`#spawn`) proof: a deferred async
    /// computation, polled cooperatively when the lemma is first referenced
    /// (or the theory is forced). Unlike the old `spawn_blocking`-on-a-thread
    /// task, it shares the prover's cooperative runtime — no nested `block_on`,
    /// so it may freely `await` sibling lemmas — and any *blocking* work is the
    /// FFI tactic's own responsibility, not the script layer's.
    pub fn define_spawned(
        &mut self,
        name: impl Into<String>,
        fut: futures::future::BoxFuture<'static, Result<Thm, ScriptError>>,
    ) {
        let fut = async move { Ok(Entry::Lemma(fut.await?)) }.boxed();
        self.entries.insert_pending(name, fut);
    }
    /// Register an inference (usable in tactic mode, tree mode, or both). A
    /// dual-mode inference is registered **once**, under one name.
    pub fn register_tactic(&mut self, name: impl Into<String>, t: Arc<dyn Tactic>) {
        self.entries.insert_ready(name, Entry::Tactic(t));
    }
    /// Alias of [`register_tactic`](Env::register_tactic) — an inference and a
    /// "rule" are the same kind of object now (one [`Tactic`], two modes).
    pub fn register_rule(&mut self, name: impl Into<String>, r: Arc<dyn Tactic>) {
        self.register_tactic(name, r);
    }

    /// Bind a **type constructor** `name` to a [`TypeSpec`] (the result of a
    /// `#newtype` / `#subtype` / `#quot` directive). Later types/terms resolve
    /// `(NAME ty…)` / bare `NAME` against this map.
    pub fn define_type(&mut self, name: impl Into<String>, spec: TypeSpec) {
        self.type_specs.insert(name.into(), spec);
    }

    /// The [`TypeSpec`] bound to `name`, if `name` was `#newtype`/`#subtype`/
    /// `#quot`-defined (or imported from such a module).
    pub fn lookup_type_spec(&self, name: &str) -> Option<TypeSpec> {
        self.type_specs.get(name).cloned()
    }

    /// Merge another environment's bindings in (it shadows existing entries
    /// of the same name). Touches the namespace (and the user type-ctor map)
    /// only — not the imports map.
    pub fn merge(&mut self, other: &Env) {
        self.entries.merge(&other.entries);
        for (name, spec) in &other.type_specs {
            self.type_specs.insert(name.clone(), spec.clone());
        }
    }

    /// `(#import NAME)`: register `env` as an importable namespace under
    /// `NAME` (not yet brought into scope — that is `(#open NAME)`).
    pub fn import(&mut self, name: impl Into<String>, env: Env) {
        self.imports.insert(name.into(), env);
    }

    /// The namespace previously `#import`ed under `name`.
    pub fn get_import(&self, name: &str) -> Option<&Env> {
        self.imports.get(name)
    }

    /// Merge another env's bindings in, each name qualified by `prefix`
    /// (`prefix.name`), or unchanged if `prefix` is empty.
    pub fn merge_prefixed(&mut self, other: &Env, prefix: &str) {
        self.entries.merge_prefixed(&other.entries, prefix);
        for (name, spec) in &other.type_specs {
            let qualified = if prefix.is_empty() {
                name.clone()
            } else {
                format!("{prefix}.{name}")
            };
            self.type_specs.insert(qualified, spec.clone());
        }
    }

    /// `(#open NAME)`: bring a previously-`#import`ed namespace's bindings
    /// into scope UNQUALIFIED (errors if `NAME` was not imported).
    pub fn open(&mut self, name: &str) -> R<()> {
        let opened =
            self.imports.get(name).cloned().ok_or_else(|| {
                ScriptError::Unbound(format!("environment not imported: `{name}`"))
            })?;
        self.merge(&opened);
        Ok(())
    }

    /// `(#use NAME)` / `(#use (#alias NAME PREFIX))`: bring a
    /// previously-`#import`ed namespace's bindings into scope QUALIFIED by
    /// `prefix` (default `NAME`), so e.g. `and.comm` becomes `logic.and.comm`.
    pub fn use_ns(&mut self, name: &str, prefix: &str) -> R<()> {
        let opened =
            self.imports.get(name).cloned().ok_or_else(|| {
                ScriptError::Unbound(format!("environment not imported: `{name}`"))
            })?;
        self.merge_prefixed(&opened, prefix);
        Ok(())
    }

    /// The `core` prelude — `covalence-core`'s `defs/` catalogue by dotted
    /// name **plus the primitive tactics and derivation rules**. Opening `core`
    /// is what makes `intro`/`sym`/`rw`/… available. This is the `defs/` churn
    /// boundary.
    pub fn core() -> Self {
        let mut e = Env::default();
        let mut op = |names: &[&str], t: Term| {
            for n in names {
                e.entries
                    .insert_ready((*n).to_string(), Entry::Const(ConstDef::Op(t.clone())));
            }
        };
        op(&["true"], Term::bool_lit(true));
        op(&["false"], Term::bool_lit(false));
        op(&["and", "/\\"], defs::and());
        op(&["or", "\\/"], defs::or());
        op(&["not", "~"], defs::not());
        op(&["imp", "==>"], defs::imp());
        op(&["iff", "<=>"], defs::iff());
        op(&["nat.add", "+"], defs::nat_add());
        op(&["nat.mul", "*"], defs::nat_mul());
        op(&["nat.sub"], defs::nat_sub());
        op(&["nat.pred"], defs::nat_pred());
        op(&["nat.le", "<="], defs::nat_le());
        op(&["nat.lt", "<"], defs::nat_lt());
        op(&["nat.pow"], defs::nat_pow());
        op(&["nat.shl"], defs::nat_shl());
        op(&["nat.shr"], defs::nat_shr());
        op(&["nat.div"], defs::nat_div());
        op(&["nat.mod"], defs::nat_mod());
        op(&["succ", "nat.succ"], Term::succ());
        drop(op);
        e.entries
            .insert_ready("=".to_string(), Entry::Const(ConstDef::Eq));
        e.entries
            .insert_ready("eq".to_string(), Entry::Const(ConstDef::Eq));
        for (name, tac) in super::tactic::core_tactics() {
            e.register_tactic(name, tac);
        }
        for (name, rule) in super::drv::core_rules() {
            e.register_rule(name, rule);
        }
        e
    }

    // -- unification seams ----------------------------------------------
    // These route lemma application through a method so a custom unifier can
    // be registered here later. `apply_unify` (general) and `rw_unify`
    // (equation-specific) are kept SEPARATE on purpose.

    /// **Apply-unification.** Instantiate `lemma` (`⊢ ∀x⃗. P₁⟹…⟹C`) so its
    /// conclusion `C` first-order-matches `target`, returning `⊢ P₁[σ]⟹…⟹target`
    /// (premises intact — the caller discharges them; with none it is just
    /// `⊢ target`). Untrusted matching, re-checked by `all_elim`/`inst_tfree`.
    pub fn apply_unify(&self, lemma: &Thm, target: &Term) -> R<Thm> {
        let (schematics, order, body) = open_foralls(lemma.concl());
        // Strip `⟹` premises to reach the conclusion `C`, and match against `target`.
        let mut concl = body;
        while let Some((_p, rest)) = dest_imp(&concl) {
            concl = rest;
        }
        let mut sub = Subst::default();
        match_term(&concl, target, &schematics, &mut sub).map_err(|()| {
            ScriptError::Syntax(format!("apply: lemma conclusion does not match `{target}`"))
        })?;
        instantiate(lemma, &order, &sub, "apply")
    }

    /// **Rw-unification** — the equation-matching analogue of
    /// [`apply_unify`](Env::apply_unify), kept SEPARATE so the two can grow
    /// independently. An already-instantiated `⊢ L = R` is used as given (the
    /// original `rw`); a **quantified** `⊢ ∀x⃗. L = R` is instantiated here by
    /// finding the first subterm of `target` that the LHS `L` matches — so
    /// `(rw EQN)` no longer needs a hand-written `all-elim` prefix on `EQN`.
    pub fn rw_unify(&self, eqn: &Thm, target: &Term) -> R<Thm> {
        if eqn.concl().as_eq().is_some() {
            return Ok(eqn.clone());
        }
        let (schematics, order, body) = open_foralls(eqn.concl());
        let (lhs, _rhs) = body.as_eq().ok_or_else(|| {
            ScriptError::Syntax("rw: the equation is not an `=` (nor a `∀`-quantified `=`)".into())
        })?;
        let sub = super::unify::find_match(lhs, target, &schematics).ok_or_else(|| {
            ScriptError::Syntax(format!(
                "rw: no subterm of `{target}` matches the equation's LHS `{lhs}`"
            ))
        })?;
        instantiate(eqn, &order, &sub, "rw")
    }

    // -- equational-reasoning seams -------------------------------------
    // Like the unification seams above, these route the β / congruence /
    // funext / calc-default operations through methods on `Env`, so a logic
    // can later swap them for its own handler set (the `HandlerSet` of
    // `docs/surface-compiler.md` §9 — `ctx.active.rewrite` / `.reduce`).
    // Today they are the model-agnostic HOL defaults, but they are *requested*
    // through this seam rather than hard-wired into the rules that use them.

    /// **β-reduction seam.** `⊢ t = nf`, where `nf` is the full β-normal form
    /// of `t` (every redex fired, including under binders). This is the
    /// *normalizing* β step `#comp` / the `beta` tactic request — strictly
    /// stronger than the kernel's one-shot `Thm::beta_conv` (a single
    /// outermost redex). The default is [`crate::proofs::rewrite::beta_nf`]
    /// (built from `refl`/`cong_app`/`abs`/`beta_conv`/`trans`); a logic may
    /// install a different reducer (δ-aware, primitive-folding, …) here.
    pub fn beta(&self, t: &Term) -> R<Thm> {
        Ok(crate::proofs::rewrite::beta_nf(t.clone()))
    }

    /// **Congruence seam.** From per-argument equations `⊢ aᵢ = bᵢ` build
    /// `⊢ head a₁ … aₙ = head b₁ … bₙ` by folding `mk_comb` over `head`'s
    /// reflexivity (the n-ary generalization of `cong-arg` / `cong-fn`).
    /// `head` is the common function; each `arg_eq` rewrites one argument
    /// position left-to-right. With no argument equations this is `⊢ head =
    /// head`. The kernel re-checks every `mk_comb`, so a bad shape errors
    /// rather than fabricating a theorem.
    pub fn congr(&self, head: &Term, arg_eqs: &[Thm]) -> R<Thm> {
        let mut thm = Thm::refl(head.clone())?;
        for arg_eq in arg_eqs {
            thm = thm.mk_comb(arg_eq.clone())?;
        }
        Ok(thm)
    }

    /// **Function-extensionality seam.** From a pointwise equality conclude
    /// the equality of the two functions. The pointwise input is either
    /// `⊢ ∀x. f x = g x` (the leading `∀` is stripped) or a bare
    /// `⊢ f x = g x` where `x = Free(name, α)` is the point variable — `name`
    /// must not occur free in the hypotheses (the side condition `Thm::abs`
    /// re-checks). The result `⊢ f = g` is obtained the HOL way: re-abstract
    /// over the point (`abs`) and η-contract both sides (`eta_conv`).
    pub fn funext(&self, pointwise: &Thm) -> R<Thm> {
        // If the conclusion is `∀x. f x = g x`, instantiate the `∀` at a fresh
        // free point first, then extensionalise over it.
        if let Some((ty, _body)) = dest_forall(pointwise.concl()) {
            let name = funext_fresh_point(pointwise);
            let point = Term::free(name.clone(), ty.clone());
            let app_eq = pointwise.clone().all_elim(point)?;
            return funext_over(&app_eq, &name, &ty);
        }
        // Otherwise the conclusion is already `f x = g x`; recover the point
        // variable from the LHS argument.
        let (lhs, _rhs) = pointwise
            .concl()
            .as_eq()
            .ok_or(covalence_core::Error::NotAnEquation)?;
        let (_f, x) = lhs
            .as_app()
            .ok_or_else(|| ScriptError::Syntax("funext: pointwise side is not `f x`".into()))?;
        let (name, ty) = match x.kind() {
            TermKind::Free(name, ty) => (name.to_string(), ty.clone()),
            _ => {
                return Err(ScriptError::Syntax(
                    "funext: the point `x` of `f x = g x` must be a free variable".into(),
                ));
            }
        };
        funext_over(pointwise, &name, &ty)
    }

    /// **Calc-default seam.** The `#comp` default equational handler: prove
    /// `⊢ lhs = rhs` for a step whose justification was omitted. The
    /// model-agnostic HOL default closes a step iff the two sides share a
    /// β-normal form — i.e. `lhs` and `rhs` are βη… no, β-convertible. It
    /// builds `⊢ lhs = βnf(lhs)`, `⊢ rhs = βnf(rhs)`, and joins them with
    /// `trans`/`sym` when the normal forms coincide; otherwise it errors,
    /// naming the step (so an un-closable step is a diagnostic, never a silent
    /// gap). A logic installs its own equational decision procedure here (a
    /// monoid normalizer, a reified-logic decider, …).
    pub fn comp_default(&self, lhs: &Term, rhs: &Term) -> R<Thm> {
        if lhs == rhs {
            return Ok(Thm::refl(lhs.clone())?);
        }
        let l_nf = self.beta(lhs)?; // ⊢ lhs = lnf
        let r_nf = self.beta(rhs)?; // ⊢ rhs = rnf
        let (_, lnf) = l_nf.concl().as_eq().ok_or(covalence_core::Error::NotAnEquation)?;
        let (_, rnf) = r_nf.concl().as_eq().ok_or(covalence_core::Error::NotAnEquation)?;
        if lnf != rnf {
            return Err(ScriptError::Syntax(format!(
                "#comp: the default handler cannot close `{lhs} = {rhs}` \
                 (β-normal forms differ: `{lnf}` vs `{rnf}`) — supply an explicit justification"
            )));
        }
        // ⊢ lhs = lnf = rnf = rhs.
        l_nf.trans(r_nf.sym()?).map_err(Into::into)
    }
}

/// `funext` over an explicit point: from `⊢ f x = g x` (`x = Free(name, α)`),
/// re-abstract and η-contract to `⊢ f = g`. Shared by the two entry shapes of
/// [`Env::funext`].
fn funext_over(app_eq: &Thm, name: &str, alpha: &Type) -> R<Thm> {
    let abs_eq = app_eq.clone().abs(name, alpha.clone())?; // ⊢ (λx. f x) = (λx. g x)
    let (l_abs, r_abs) = abs_eq
        .concl()
        .as_eq()
        .ok_or(covalence_core::Error::NotAnEquation)?;
    let eta_l = Thm::eta_conv(l_abs.clone())?; // ⊢ (λx. f x) = f
    let eta_r = Thm::eta_conv(r_abs.clone())?; // ⊢ (λx. g x) = g
    eta_l.sym()?.trans(abs_eq)?.trans(eta_r).map_err(Into::into)
}

/// A point-variable name not free in `thm`'s conclusion, for `funext` to
/// instantiate a `∀x. …` at.
fn funext_fresh_point(thm: &Thm) -> String {
    let concl = thm.concl();
    let mut i = 0usize;
    loop {
        let name = format!("_fext{i}");
        if !subst::has_free_var(concl, &name) {
            return name;
        }
        i += 1;
    }
}

/// Open a theorem-conclusion's `∀` prefix with fresh schematic free vars
/// (`?0`, `?1`, …), returning the hole-name set, their binder order, and the
/// opened body. Shared by the unification seams.
fn open_foralls(concl: &Term) -> (BTreeSet<SmolStr>, Vec<SmolStr>, Term) {
    let mut schematics = BTreeSet::new();
    let mut order: Vec<SmolStr> = Vec::new();
    let mut body = concl.clone();
    while let Some((ty, inner)) = dest_forall(&body) {
        let name = SmolStr::new(format!("?{}", order.len()));
        body = subst::open(&inner, &Term::free(name.clone(), ty));
        schematics.insert(name.clone());
        order.push(name);
    }
    (schematics, order, body)
}

/// Instantiate `thm` (a `∀x⃗. …`) with a matched substitution: type-vars first
/// (`inst_tfree`), then the `∀` witnesses in binder order (`all_elim`). `what`
/// labels the error if a hole was left undetermined.
fn instantiate(thm: &Thm, order: &[SmolStr], sub: &Subst, what: &str) -> R<Thm> {
    let mut t = thm.clone();
    // Apply the type substitution **simultaneously**. The matched `sub.types`
    // can be a permutation (e.g. `{'a↦'b, 'b↦'a}` when a lemma is used at a
    // swapped type ordering — `rel.converse` over the double-converse) or a
    // chained rename (`{'b↦'c, 'c↦'d}` matching `compose`'s type vars), and a
    // naive sequential `inst_tfree('a↦'b)` then `inst_tfree('b↦'a)` would
    // collapse both to `'a`. Route each source variable through a disjoint
    // fresh intermediate name first, so no later step recaptures an
    // already-substituted variable; each pass is still one kernel `inst_tfree`.
    let renames: Vec<(SmolStr, Type)> = sub
        .types
        .iter()
        .filter(|(tv, ty)| Type::tfree(tv.as_str()) != **ty)
        .map(|(tv, ty)| (tv.clone(), ty.clone()))
        .collect();
    if !renames.is_empty() {
        let tmp = |tv: &str| format!("?inst.{tv}");
        // Pass 1: each source `tv` → its private fresh intermediate.
        for (tv, _) in &renames {
            t = t.inst_tfree(tv, Type::tfree(tmp(tv)))?;
        }
        // Pass 2: each intermediate → the (original-named) target type.
        for (tv, ty) in &renames {
            t = t.inst_tfree(&tmp(tv), ty.clone())?;
        }
    }
    for name in order {
        let w = sub.terms.get(name).ok_or_else(|| {
            ScriptError::Syntax(format!(
                "{what}: a `∀` variable was left undetermined by matching"
            ))
        })?;
        t = t.all_elim(w.clone())?;
    }
    Ok(t)
}

/// `∀`/`⟹` shape probes for [`Env::apply_unify`].
fn dest_forall(t: &Term) -> Option<(Type, Term)> {
    let TermKind::App(h, abs) = t.kind() else {
        return None;
    };
    let TermKind::Abs(ty, body) = abs.kind() else {
        return None;
    };
    (*h == defs::forall(ty.clone())).then(|| (ty.clone(), body.clone()))
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
