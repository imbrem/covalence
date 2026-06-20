//! The type/term parser and shared S-expression helpers.
//!
//! Term building is delegated to the [`super::infer`] elaborator, so the
//! surface can leave types implicit; this module owns the explicit type
//! grammar and the small list/atom helpers shared with the proof parser. Name
//! resolution lives in [`super::env::Env`]; the variable scope in
//! [`super::scope::Scope`].

use covalence_core::{Term, Type, defs};
use covalence_sexp::{Atom, SExp, SExpr};

use super::{ScriptError, env::Env, scope::Scope};

type R<T> = Result<T, ScriptError>;

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
            // TypeSpec type constructors (two type-argument specs from defs/).
            // Syntax: `(rel A B)`, `(set A)`, `(option A)`, `(result A B)`.
            "rel" => {
                if ch.len() != 3 {
                    return Err(ScriptError::Syntax(
                        "rel: expected (rel A B)".into(),
                    ));
                }
                Ok(Type::spec(
                    defs::rel_spec(),
                    vec![parse_type(&ch[1])?, parse_type(&ch[2])?],
                ))
            }
            "set" => {
                if ch.len() != 2 {
                    return Err(ScriptError::Syntax("set: expected (set A)".into()));
                }
                Ok(Type::spec(defs::set_spec(), vec![parse_type(&ch[1])?]))
            }
            "option" => {
                if ch.len() != 2 {
                    return Err(ScriptError::Syntax(
                        "option: expected (option A)".into(),
                    ));
                }
                Ok(Type::spec(defs::option_spec(), vec![parse_type(&ch[1])?]))
            }
            "coprod" => {
                if ch.len() != 3 {
                    return Err(ScriptError::Syntax(
                        "coprod: expected (coprod A B)".into(),
                    ));
                }
                Ok(Type::spec(
                    defs::coprod_spec(),
                    vec![parse_type(&ch[1])?, parse_type(&ch[2])?],
                ))
            }
            "result" => {
                if ch.len() != 3 {
                    return Err(ScriptError::Syntax(
                        "result: expected (result A B)".into(),
                    ));
                }
                Ok(Type::spec(
                    defs::result_spec(),
                    vec![parse_type(&ch[1])?, parse_type(&ch[2])?],
                ))
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
