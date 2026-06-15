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
use covalence_sexp::{Atom, SExp, SExpr};

use super::ScriptError;

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

/// The name-resolution environment: the prelude of catalogue constants
/// plus the lemmas proven so far (referenceable by later proofs).
#[derive(Clone, Default)]
pub struct Env {
    pub consts: HashMap<String, ConstDef>,
    pub lemmas: HashMap<String, Thm>,
}

impl Env {
    /// An empty environment (no constants, no lemmas).
    pub fn empty() -> Self {
        Env::default()
    }

    /// Merge another environment in (its constants and lemmas shadow
    /// existing entries of the same name). This is what `(open NAME)`
    /// does once `NAME` is resolved to an `Env`.
    pub fn open(&mut self, other: &Env) {
        for (k, v) in &other.consts {
            self.consts.insert(k.clone(), v.clone());
        }
        for (k, v) in &other.lemmas {
            self.lemmas.insert(k.clone(), v.clone());
        }
    }

    /// The `core` prelude — exposes `covalence-core`'s `defs/` catalogue
    /// (the logic connectives + the nat operations) by dotted name. This
    /// is the churn boundary: a `defs/` refactor updates entries here,
    /// never a proof.
    pub fn core() -> Self {
        let mut c: HashMap<String, ConstDef> = HashMap::new();
        let mut op = |names: &[&str], t: Term| {
            for n in names {
                c.insert((*n).to_string(), ConstDef::Op(t.clone()));
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
        op(&["nat.le", "<="], defs::nat_le());
        op(&["nat.lt", "<"], defs::nat_lt());
        op(&["succ", "nat.succ"], Term::succ());
        drop(op);
        c.insert("=".into(), ConstDef::Eq);
        c.insert("eq".into(), ConstDef::Eq);
        Env {
            consts: c,
            lemmas: HashMap::new(),
        }
    }
}

/// A scope of named, fully-typed variables (`fix`-declared, with types
/// inferred from the conclusion, plus binder variables introduced by
/// proof rules). Implicit/unannotated variables are resolved by the
/// elaborator, not here.
pub type Scope = Vec<(String, Type)>;

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
    super::infer::elaborate_term(s, scope, env)
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
