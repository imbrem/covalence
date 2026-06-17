//! The prelude [`Env`] — the name→catalogue resolver and **namespace** object.
//!
//! [`Env`] is the single place that absorbs `covalence-core` `defs/` churn:
//! re-point a resolver here and every proof that mentions the name keeps
//! working unchanged. It holds the constant catalogue, the proven-lemma table,
//! the tactic registry, and the set of imported sub-namespaces — all behind
//! methods. The transient proof state — the variable [`super::scope::Scope`],
//! goals — lives in [`super::tactic::Interp`], not here.

use std::sync::Arc;

use covalence_core::{Term, Thm, defs};
use imbl::HashMap;

use super::drv::Rule;
use super::handle::LazyMap;
use super::{ScriptError, tactic::Tactic};

type R<T> = Result<T, ScriptError>;

/// Qualify a dotted name with a namespace `prefix` (`prefix.name`), or
/// leave it unchanged when `prefix` is empty.
fn qualify(prefix: &str, name: &str) -> String {
    if prefix.is_empty() {
        name.to_string()
    } else {
        format!("{prefix}.{name}")
    }
}

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

/// A name-resolution environment — the **namespace** part of the system:
/// constants, proven lemmas, and a tactic registry, plus the set of
/// imported (but not necessarily opened) sub-namespaces. Fields are
/// encapsulated behind methods; this will grow into a proper namespace
/// system (separate namespaces for consts/types/terms/tactics/…, qualified
/// names, `#import … as …`).
///
/// Backed by [`imbl::HashMap`] **persistent** maps, so cloning an `Env` is
/// O(1) (structural sharing) and mutating a clone is cheap copy-on-write —
/// which is why [`super::tactic::Interp`] can afford to *own* its environment.
#[derive(Clone, Default)]
pub struct Env {
    consts: HashMap<String, ConstDef>,
    /// Proven lemmas — a [`LazyMap`], so a lemma may still be **computing**
    /// (`#compute`) and `lookup_lemma` is **async**.
    lemmas: LazyMap<Thm>,
    tactics: HashMap<String, Arc<dyn Tactic>>,
    rules: HashMap<String, Arc<dyn Rule>>,
    imports: HashMap<String, Env>,
}

impl Env {
    /// An empty environment.
    pub fn empty() -> Self {
        Env::default()
    }

    // -- lookups --------------------------------------------------------
    pub fn lookup_const(&self, name: &str) -> Option<&ConstDef> {
        self.consts.get(name)
    }
    /// Look up a lemma, **awaiting** it if it is still computing (`#compute`).
    /// `None` if unbound; `Some(Err)` if its computation failed.
    pub async fn lookup_lemma(&self, name: &str) -> Option<Result<Thm, ScriptError>> {
        self.lemmas.get(name).await
    }
    /// Synchronous peek: the lemma only if already proved (not still computing).
    pub fn lemma_ready(&self, name: &str) -> Option<Thm> {
        self.lemmas.get_ready(name)
    }
    pub fn lookup_tactic(&self, name: &str) -> Option<Arc<dyn Tactic>> {
        self.tactics.get(name).cloned()
    }
    pub fn lookup_rule(&self, name: &str) -> Option<Arc<dyn Rule>> {
        self.rules.get(name).cloned()
    }
    pub fn has_lemma(&self, name: &str) -> bool {
        self.lemmas.contains(name)
    }

    // -- definitions ----------------------------------------------------
    pub fn define_const(&mut self, name: impl Into<String>, c: ConstDef) {
        self.consts.insert(name.into(), c);
    }
    pub fn define_lemma(&mut self, name: impl Into<String>, thm: Thm) {
        self.lemmas.insert_ready(name, thm);
    }
    /// Bind a lemma to a still-running `#compute` (`spawn_blocking`) task.
    pub fn define_computing(
        &mut self,
        name: impl Into<String>,
        task: tokio::task::JoinHandle<Result<Thm, ScriptError>>,
    ) {
        self.lemmas.insert_compute(name, task);
    }
    pub fn register_tactic(&mut self, name: impl Into<String>, t: Arc<dyn Tactic>) {
        self.tactics.insert(name.into(), t);
    }
    pub fn register_rule(&mut self, name: impl Into<String>, r: Arc<dyn Rule>) {
        self.rules.insert(name.into(), r);
    }

    /// Merge another environment's bindings in (it shadows existing entries
    /// of the same name). Touches namespaces only — not the imports map.
    pub fn merge(&mut self, other: &Env) {
        self.consts
            .extend(other.consts.iter().map(|(k, v)| (k.clone(), v.clone())));
        self.lemmas.merge(&other.lemmas);
        self.tactics
            .extend(other.tactics.iter().map(|(k, v)| (k.clone(), v.clone())));
        self.rules
            .extend(other.rules.iter().map(|(k, v)| (k.clone(), v.clone())));
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
        for (k, v) in &other.consts {
            self.consts.insert(qualify(prefix, k), v.clone());
        }
        self.lemmas.merge_prefixed(&other.lemmas, prefix);
        for (k, v) in &other.tactics {
            self.tactics.insert(qualify(prefix, k), v.clone());
        }
        for (k, v) in &other.rules {
            self.rules.insert(qualify(prefix, k), v.clone());
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
    /// name **plus the primitive tactics**. Opening `core` is what makes
    /// `intro`/`sym`/`rw`/… available. This is the `defs/` churn boundary.
    pub fn core() -> Self {
        let mut e = Env::default();
        let mut op = |names: &[&str], t: Term| {
            for n in names {
                e.consts.insert((*n).to_string(), ConstDef::Op(t.clone()));
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
        e.consts.insert("=".into(), ConstDef::Eq);
        e.consts.insert("eq".into(), ConstDef::Eq);
        for (name, tac) in super::tactic::core_tactics() {
            e.tactics.insert(name, tac);
        }
        e
    }
}
