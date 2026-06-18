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
//! computing (today only `#compute`-ing lemmas; tomorrow a `bytes` const loaded
//! from the network — "one async task per definition"). This is deliberately
//! the *simple* unified design; finer-grained namespaces (separate const/type/
//! tactic spaces, qualified names) can come later.

use std::collections::BTreeSet;
use std::sync::Arc;

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
    /// Look up a lemma, **awaiting** it if it is still computing (`#compute`).
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
    /// Whether `name` is bound to a lemma (ready *or* still `#compute`-ing).
    pub fn has_lemma(&self, name: &str) -> bool {
        match self.entries.get_ready(name) {
            Some(Entry::Lemma(_)) => true,
            Some(_) => false,
            // No ready entry: a *pending* binding is always a #compute-ing
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
    /// Bind a lemma to a still-running `#compute` (`spawn_blocking`) task; a
    /// later reference (or the force) just awaits it.
    pub fn define_computing(
        &mut self,
        name: impl Into<String>,
        task: tokio::task::JoinHandle<Result<Thm, ScriptError>>,
    ) {
        let fut = async move {
            let thm = task
                .await
                .map_err(|e| ScriptError::Syntax(format!("#compute task failed: {e}")))??;
            Ok(Entry::Lemma(thm))
        }
        .boxed();
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

    /// Merge another environment's bindings in (it shadows existing entries
    /// of the same name). Touches the namespace only — not the imports map.
    pub fn merge(&mut self, other: &Env) {
        self.entries.merge(&other.entries);
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
        // Open the `∀` prefix with fresh schematic free vars.
        let mut schematics = BTreeSet::new();
        let mut order: Vec<SmolStr> = Vec::new();
        let mut body = lemma.concl().clone();
        while let Some((ty, inner)) = dest_forall(&body) {
            let name = SmolStr::new(format!("?{}", order.len()));
            body = subst::open(&inner, &Term::free(name.clone(), ty));
            schematics.insert(name.clone());
            order.push(name);
        }
        // Strip `⟹` premises to reach the conclusion `C`.
        let mut concl = body;
        while let Some((_p, rest)) = dest_imp(&concl) {
            concl = rest;
        }
        // Match `C` against `target`.
        let mut sub = Subst::default();
        match_term(&concl, target, &schematics, &mut sub).map_err(|()| {
            ScriptError::Syntax(format!("apply: lemma conclusion does not match `{target}`"))
        })?;
        // Instantiate: type-vars first, then the `∀` witnesses in binder order.
        let mut thm = lemma.clone();
        for (tv, ty) in &sub.types {
            if Type::tfree(tv.as_str()) != *ty {
                thm = thm.inst_tfree(tv, ty.clone())?;
            }
        }
        for name in &order {
            let w = sub.terms.get(name).ok_or_else(|| {
                ScriptError::Syntax(
                    "apply: a `∀` variable was left undetermined by matching".into(),
                )
            })?;
            thm = thm.all_elim(w.clone())?;
        }
        Ok(thm)
    }

    /// **Rw-unification** — the equation-matching analogue of
    /// [`apply_unify`](Env::apply_unify), kept SEPARATE so a future
    /// equation-specific matcher (instantiate `∀x⃗. L = R` so `L` matches a
    /// subterm of `target`) hooks in here without touching `apply`. For now it
    /// is the identity — the equation is used as given (the original `rw`).
    pub fn rw_unify(&self, eqn: &Thm, _target: &Term) -> R<Thm> {
        Ok(eqn.clone())
    }
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
