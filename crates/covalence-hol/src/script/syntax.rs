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
/// `(-> A B …)` (curried, right-associative), `(tfree NAME)`, a built-in
/// `TypeSpec` constructor (`rel`/`set`/`option`/`list`/`coprod`/`result`),
/// or a **user-defined** type constructor introduced by a `#newtype` /
/// `#subtype` / `#quot` directive (resolved against `env`).
pub fn parse_type(s: &SExpr, env: &Env) -> R<Type> {
    match s {
        SExp::Atom(Atom::Symbol(name)) => {
            let n = name.as_str();
            match n {
                "bool" => Ok(Type::bool()),
                "nat" => Ok(Type::nat()),
                "int" => Ok(Type::int()),
                "rat" => Ok(defs::rat_ty()),
                // `real` is shell-defined (`init::real`, not the kernel
                // catalogue), so it is resolved through that module rather
                // than `defs`.
                "real" => Ok(crate::init::real::real_ty()),
                "int.pos" => Ok(defs::int_pos_ty()),
                // text/byte element types (the `defs/text.rs` + `defs/bits.rs`
                // 0-ary subtypes): `char`, the fixed-width `uN`, `string`.
                "char" => Ok(defs::char_ty()),
                "string" => Ok(defs::string_ty()),
                "bytes" => Ok(Type::bytes()),
                "u8" => Ok(defs::u8_ty()),
                "u16" => Ok(defs::u16_ty()),
                "u32" => Ok(defs::u32_ty()),
                "u64" => Ok(defs::u64_ty()),
                "unit" => Ok(Type::unit()),
                _ if n.starts_with('\'') => Ok(Type::tfree(&n[1..])),
                // A signature sort / carrier alias (the `#sig`/`#model` machinery).
                _ if env.lookup_type_alias(n).is_some() => Ok(env.lookup_type_alias(n).unwrap()),
                // A user-defined 0-ary type constructor.
                _ => match env.lookup_type_spec(n) {
                    Some(spec) => Ok(applied_user_spec(spec)),
                    None => Err(ScriptError::Syntax(format!("unknown type: {n}"))),
                },
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
                let mut tys = ch[1..]
                    .iter()
                    .map(|c| parse_type(c, env))
                    .collect::<R<Vec<_>>>()?;
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
                    return Err(ScriptError::Syntax("rel: expected (rel A B)".into()));
                }
                Ok(Type::spec(
                    defs::rel_spec(),
                    vec![parse_type(&ch[1], env)?, parse_type(&ch[2], env)?],
                ))
            }
            "set" => {
                if ch.len() != 2 {
                    return Err(ScriptError::Syntax("set: expected (set A)".into()));
                }
                Ok(Type::spec(defs::set_spec(), vec![parse_type(&ch[1], env)?]))
            }
            "option" => {
                if ch.len() != 2 {
                    return Err(ScriptError::Syntax("option: expected (option A)".into()));
                }
                Ok(Type::spec(
                    defs::option_spec(),
                    vec![parse_type(&ch[1], env)?],
                ))
            }
            "list" => {
                if ch.len() != 2 {
                    return Err(ScriptError::Syntax("list: expected (list A)".into()));
                }
                Ok(Type::spec(
                    defs::list_spec(),
                    vec![parse_type(&ch[1], env)?],
                ))
            }
            "coprod" => {
                if ch.len() != 3 {
                    return Err(ScriptError::Syntax("coprod: expected (coprod A B)".into()));
                }
                Ok(Type::spec(
                    defs::coprod_spec(),
                    vec![parse_type(&ch[1], env)?, parse_type(&ch[2], env)?],
                ))
            }
            "result" => {
                if ch.len() != 3 {
                    return Err(ScriptError::Syntax("result: expected (result A B)".into()));
                }
                Ok(Type::spec(
                    defs::result_spec(),
                    vec![parse_type(&ch[1], env)?, parse_type(&ch[2], env)?],
                ))
            }
            // A user-defined type constructor applied to type arguments
            // `(NAME ty…)` (`#newtype`/`#subtype`/`#quot`-introduced).
            other => match env.lookup_type_spec(other) {
                Some(spec) => {
                    let args = ch[1..]
                        .iter()
                        .map(|c| parse_type(c, env))
                        .collect::<R<Vec<_>>>()?;
                    Ok(Type::spec(spec, args))
                }
                None => Err(ScriptError::Syntax(format!("unknown type head: {other}"))),
            },
        },
    }
}

/// Apply a freshly-resolved user `TypeSpec` at the type variables that occur
/// in its carrier (alphabetical `free_tvars` order, the kernel convention),
/// so a bare `NAME` reference yields the same `Type::spec(spec, ['a, 'b…])`
/// leaf the directive stored — mirroring `defs::cov::apply_spec`.
pub(crate) fn applied_user_spec(spec: covalence_core::defs::TypeSpec) -> Type {
    let args: Vec<Type> = match spec.ty() {
        Some(carrier) => carrier
            .free_tvars()
            .iter()
            .map(|v| Type::tfree(v.clone()))
            .collect(),
        None => Vec::new(),
    };
    Type::spec(spec, args)
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
