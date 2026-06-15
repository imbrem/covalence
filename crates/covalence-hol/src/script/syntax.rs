//! The **name-resolving** term/type parser and the prelude [`Env`].
//!
//! This is the *ergonomic authoring* front-end: a human writes
//! `(and p q)` / `(forall (n nat) (= (nat.add n 0) n))`, and the parser
//! resolves each dotted catalogue name through [`Env`] into whatever the
//! kernel *currently* represents it as. The [`Env`] is therefore the
//! single place that absorbs `covalence-core` `defs/` churn: re-point a
//! resolver here and every proof that mentions the name keeps working
//! unchanged. (Contrast the low-level [`crate::sexp`] grammar, which
//! addresses the catalogue by *representation* — `(term-spec LABEL …)` —
//! and therefore moves whenever `defs/` does.)

use std::collections::HashMap;

use covalence_core::{Term, Thm, Type, defs, subst};
use covalence_sexp::{Atom, SExp, SExpr};

use super::ScriptError;
use crate::HolLightCtx;

type R<T> = Result<T, ScriptError>;

/// How a head symbol resolves to a kernel term.
pub enum ConstDef {
    /// A fully-built operator term, applied (curried) to the parsed
    /// argument terms. Monomorphic (the connectives, `nat.add`, …) or
    /// nullary (`true`/`false`).
    Op(Term),
    /// Polymorphic HOL equality: the element type is inferred from the
    /// first operand.
    Eq,
}

/// The name-resolution environment: the prelude of catalogue constants
/// plus the lemmas proven so far (referenceable by later proofs).
pub struct Env {
    pub consts: HashMap<String, ConstDef>,
    pub lemmas: HashMap<String, Thm>,
}

impl Env {
    /// The `core` prelude — exposes `covalence-core`'s `defs/` catalogue
    /// (the logic connectives + the nat operations) by dotted name.
    /// This is the churn boundary: a `defs/` refactor updates entries
    /// here, never a proof.
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

/// A lexical scope of named, typed variables (introduced by `fix` and by
/// binders). All are treated as `Free(name, ty)`; binders close them via
/// [`subst::close`] / `mk_forall` after the body is parsed.
pub type Scope = Vec<(String, Type)>;

fn scope_get(scope: &Scope, name: &str) -> Option<Type> {
    scope
        .iter()
        .rev()
        .find(|(n, _)| n == name)
        .map(|(_, t)| t.clone())
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
// Terms
// ============================================================================

enum Binder {
    Lam,
    Forall,
    Exists,
    Select,
}

/// Parse a term in the named/ergonomic surface syntax.
///
/// - a bare symbol resolves as: in-scope variable → non-negative integer
///   `nat` literal → nullary catalogue constant (`true`/`false`).
/// - `(HEAD args…)` dispatches on `HEAD`: the low-level escapes
///   (`free`/`const`/`bound`/`app`/`abs`), the binders
///   (`lam`/`forall`/`exists`/`select` over a `(name type)` var),
///   polymorphic `(= a b)`, else a catalogue constant applied to its
///   arguments.
pub fn parse_term(s: &SExpr, scope: &mut Scope, env: &Env) -> R<Term> {
    match s {
        SExp::Atom(Atom::Symbol(name)) => {
            let n = name.as_str();
            if let Some(ty) = scope_get(scope, n) {
                return Ok(Term::free(n, ty));
            }
            if let Ok(k) = n.parse::<u64>() {
                return Ok(Term::nat_lit(k));
            }
            match env.consts.get(n) {
                Some(ConstDef::Op(t)) => Ok(t.clone()),
                _ => Err(ScriptError::Unbound(n.into())),
            }
        }
        SExp::Atom(_) => Err(ScriptError::Syntax("term: unexpected string atom".into())),
        SExp::List(ch) => match head_sym(ch)? {
            "free" => {
                arity(ch, 3, "free")?;
                Ok(Term::free(sym(&ch[1], "free name")?, parse_type(&ch[2])?))
            }
            "const" => {
                arity(ch, 3, "const")?;
                Ok(Term::const_(sym(&ch[1], "const name")?, parse_type(&ch[2])?))
            }
            "bound" => {
                arity(ch, 2, "bound")?;
                let i = sym(&ch[1], "bound index")?
                    .parse::<u32>()
                    .map_err(|e| ScriptError::Syntax(format!("bound: {e}")))?;
                Ok(Term::bound(i))
            }
            "app" => {
                if ch.len() < 3 {
                    return Err(ScriptError::Syntax("app: expected (app f x …)".into()));
                }
                let mut it = ch[1..].iter();
                let mut acc = parse_term(it.next().unwrap(), scope, env)?;
                for a in it {
                    acc = Term::app(acc, parse_term(a, scope, env)?);
                }
                Ok(acc)
            }
            "abs" => {
                arity(ch, 3, "abs")?;
                Ok(Term::abs(parse_type(&ch[1])?, parse_term(&ch[2], scope, env)?))
            }
            "lam" | "λ" => parse_binder(ch, scope, env, Binder::Lam),
            "forall" | "∀" => parse_binder(ch, scope, env, Binder::Forall),
            "exists" | "∃" => parse_binder(ch, scope, env, Binder::Exists),
            "select" | "ε" => parse_binder(ch, scope, env, Binder::Select),
            "=" | "eq" => {
                arity(ch, 3, "eq")?;
                let a = parse_term(&ch[1], scope, env)?;
                let b = parse_term(&ch[2], scope, env)?;
                Ok(HolLightCtx::new().mk_eq(a, b)?)
            }
            other => match env.consts.get(other) {
                Some(ConstDef::Op(t)) => {
                    let mut acc = t.clone();
                    for a in &ch[1..] {
                        acc = Term::app(acc, parse_term(a, scope, env)?);
                    }
                    Ok(acc)
                }
                Some(ConstDef::Eq) => {
                    arity(ch, 3, other)?;
                    let a = parse_term(&ch[1], scope, env)?;
                    let b = parse_term(&ch[2], scope, env)?;
                    Ok(HolLightCtx::new().mk_eq(a, b)?)
                }
                None => Err(ScriptError::Unbound(other.into())),
            },
        },
    }
}

fn parse_binder(ch: &[SExpr], scope: &mut Scope, env: &Env, b: Binder) -> R<Term> {
    arity(ch, 3, "binder")?;
    let (name, ty) = parse_var(&ch[1])?;
    scope.push((name.clone(), ty.clone()));
    let body = parse_term(&ch[2], scope, env);
    scope.pop();
    let body = body?;
    let ctx = HolLightCtx::new();
    Ok(match b {
        Binder::Lam => Term::abs(ty, subst::close(&body, &name)),
        Binder::Forall => ctx.mk_forall(&name, ty, body),
        Binder::Exists => ctx.mk_exists(&name, ty, body),
        Binder::Select => ctx.mk_select(&name, ty, body),
    })
}

/// Parse a `(name type)` typed-variable form.
pub fn parse_var(s: &SExpr) -> R<(String, Type)> {
    let ch = list(s, "typed variable")?;
    arity(ch, 2, "typed variable")?;
    Ok((sym(&ch[0], "var name")?.to_string(), parse_type(&ch[1])?))
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
