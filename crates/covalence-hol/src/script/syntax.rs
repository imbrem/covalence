//! The prelude [`Env`] (name→catalogue resolver) and the type parser.
//!
//! Term building is delegated to the [`super::infer`] elaborator, so the
//! surface can leave types implicit; this module owns only the
//! *name-resolution* prelude (the `defs/` churn-absorber) and the explicit
//! type grammar. The [`Env`] is the single place that absorbs
//! `covalence-core` `defs/` churn: re-point a resolver here and every proof
//! that mentions the name keeps working unchanged.

use std::collections::HashMap;

use covalence_core::{Term, Thm, Type, defs};
use indexmap::IndexMap;
use covalence_sexp::{Atom, SExp, SExpr};

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
/// names, `#import … as …`). The transient proof state — the variable
/// [`Scope`], goals — lives in [`super::tactic::Interp`], not here.
#[derive(Clone, Default)]
pub struct Env {
    consts: HashMap<String, ConstDef>,
    lemmas: HashMap<String, Thm>,
    tactics: HashMap<String, Tactic>,
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
    pub fn lookup_lemma(&self, name: &str) -> Option<&Thm> {
        self.lemmas.get(name)
    }
    pub fn lookup_tactic(&self, name: &str) -> Option<Tactic> {
        self.tactics.get(name).copied()
    }
    pub fn has_lemma(&self, name: &str) -> bool {
        self.lemmas.contains_key(name)
    }

    // -- definitions ----------------------------------------------------
    pub fn define_const(&mut self, name: impl Into<String>, c: ConstDef) {
        self.consts.insert(name.into(), c);
    }
    pub fn define_lemma(&mut self, name: impl Into<String>, thm: Thm) {
        self.lemmas.insert(name.into(), thm);
    }
    pub fn register_tactic(&mut self, name: impl Into<String>, t: Tactic) {
        self.tactics.insert(name.into(), t);
    }

    /// Merge another environment's bindings in (it shadows existing entries
    /// of the same name). Touches namespaces only — not the imports map.
    pub fn merge(&mut self, other: &Env) {
        self.consts
            .extend(other.consts.iter().map(|(k, v)| (k.clone(), v.clone())));
        self.lemmas
            .extend(other.lemmas.iter().map(|(k, v)| (k.clone(), v.clone())));
        self.tactics
            .extend(other.tactics.iter().map(|(k, v)| (k.clone(), *v)));
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
        for (k, v) in &other.lemmas {
            self.lemmas.insert(qualify(prefix, k), v.clone());
        }
        for (k, v) in &other.tactics {
            self.tactics.insert(qualify(prefix, k), *v);
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
        e.tactics = super::tactic::core_tactics();
        e
    }
}

/// A scope of named, fully-typed variables (`fix`-declared, with types
/// inferred from the conclusion, plus binder variables introduced by
/// proof rules). Implicit/unannotated variables are resolved by the
/// elaborator, not here.
///
/// Backed by an [`IndexMap`] — ordered (insertion order is binder order, as
/// the elaborator wants) but with O(1) name lookup. Variables are pushed and
/// popped in **groups**: [`Scope::open`] starts a group, [`Scope::define`]
/// adds variables to the current group, and [`Scope::close`] drops the whole
/// group at once. Scope opening/closing is thus separate from variable
/// definition. (Shadowing a name already in an *outer* group overwrites it in
/// place; binder names are kept distinct in practice, so this does not bite.)
#[derive(Clone, Default)]
pub struct Scope {
    vars: IndexMap<String, Type>,
    /// Boundary stack: the `vars` length captured at each [`Scope::open`].
    groups: Vec<usize>,
}

impl Scope {
    /// An empty scope.
    pub fn new() -> Self {
        Scope::default()
    }

    /// A scope holding a single root group of `vars` (the `fix`-declared
    /// variables of a theorem).
    pub fn with_vars(vars: impl IntoIterator<Item = (String, Type)>) -> Self {
        let mut s = Scope::new();
        for (n, t) in vars {
            s.define(n, t);
        }
        s
    }

    /// Start a new variable group.
    pub fn open(&mut self) {
        self.groups.push(self.vars.len());
    }

    /// Drop the innermost group and every variable defined in it.
    pub fn close(&mut self) {
        let boundary = self.groups.pop().unwrap_or(0);
        self.vars.truncate(boundary);
    }

    /// Define a variable in the current group.
    pub fn define(&mut self, name: impl Into<String>, ty: Type) {
        self.vars.insert(name.into(), ty);
    }

    /// Look up a variable's type by name.
    pub fn get(&self, name: &str) -> Option<&Type> {
        self.vars.get(name)
    }

    /// The variables in scope, in binder order.
    pub fn iter(&self) -> impl Iterator<Item = (&String, &Type)> {
        self.vars.iter()
    }

    /// The number of variables in scope.
    pub fn len(&self) -> usize {
        self.vars.len()
    }

    /// Whether the scope holds no variables.
    pub fn is_empty(&self) -> bool {
        self.vars.is_empty()
    }
}

// ============================================================================
// Types
// ============================================================================

/// Parse a type: `bool`, `nat`, `'a` (type variable), `(fun A B …)` /
/// `(-> A B …)` (curried, right-associative), `(tfree NAME)`.
pub fn parse_type(s: &SExpr) -> R<Type> {
    match s {
        SExp::Atom(Atom::Symbol(name)) => {
            let n = name.as_str();
            match n {
                "bool" => Ok(Type::bool()),
                "nat" => Ok(Type::nat()),
                _ if n.starts_with('\'') => Ok(Type::tfree(&n[1..])),
                _ => Err(ScriptError::Syntax(format!("unknown type: {n}"))),
            }
        }
        SExp::Atom(_) => Err(ScriptError::Syntax("type: unexpected string atom".into())),
        SExp::List(ch) => match head_sym(ch)? {
            "tfree" => {
                arity(ch, 2, "tfree")?;
                Ok(Type::tfree(sym(&ch[1], "tfree name")?))
            }
            "fun" | "->" => {
                if ch.len() < 3 {
                    return Err(ScriptError::Syntax("fun: expected (fun A B …)".into()));
                }
                let mut tys = ch[1..].iter().map(parse_type).collect::<R<Vec<_>>>()?;
                let mut acc = tys.pop().unwrap();
                while let Some(t) = tys.pop() {
                    acc = Type::fun(t, acc);
                }
                Ok(acc)
            }
            other => Err(ScriptError::Syntax(format!("unknown type head: {other}"))),
        },
    }
}

// ============================================================================
// Terms — delegated to the inference elaborator
// ============================================================================

/// Build a term from the surface syntax against a fully-typed `scope`,
/// inferring any implicit types. (Thin wrapper over
/// [`super::infer::elaborate_term`]; `scope` mutability is unused here —
/// binders manage their own scope inside the elaborator.)
pub fn parse_term(s: &SExpr, scope: &mut Scope, env: &Env) -> R<Term> {
    super::infer::elaborate_term(s, &*scope, env)
}

// ============================================================================
// Small S-expression helpers (shared with the proof parser)
// ============================================================================

pub(crate) fn list<'a>(s: &'a SExpr, what: &str) -> R<&'a [SExpr]> {
    match s {
        SExp::List(ch) => Ok(ch),
        SExp::Atom(_) => Err(ScriptError::Syntax(format!("expected list for {what}"))),
    }
}

pub(crate) fn head_sym(ch: &[SExpr]) -> R<&str> {
    ch.first()
        .and_then(|h| h.as_symbol())
        .ok_or_else(|| ScriptError::Syntax("list head is not a symbol".into()))
}

pub(crate) fn sym<'a>(s: &'a SExpr, what: &str) -> R<&'a str> {
    s.as_symbol()
        .ok_or_else(|| ScriptError::Syntax(format!("{what}: not a symbol")))
}

pub(crate) fn arity(ch: &[SExpr], n: usize, what: &str) -> R<()> {
    if ch.len() == n {
        Ok(())
    } else {
        Err(ScriptError::Syntax(format!(
            "{what}: expected {n} elements, got {}",
            ch.len()
        )))
    }
}

/// Check a `(HEAD payload)` wrapper of arity 2 with the given head.
pub(crate) fn expect_head<'a>(ch: &'a [SExpr], head: &str) -> R<&'a SExpr> {
    if head_sym(ch)? != head {
        return Err(ScriptError::Syntax(format!("expected ({head} …)")));
    }
    arity(ch, 2, head)?;
    Ok(&ch[1])
}
