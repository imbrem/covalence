//! Lowering from S-expressions to the surface [`ast`](crate::surface::ast).
//!
//! Pure forms only: there is **no sugar**. The parser accepts exactly the
//! `#`-headed builtin grammar — `(#fn …)`, `(#sig …)`, `(#rw …)`, etc. The
//! informal arrows / colons used in `docs/surface-syntax.md` prose are not
//! a language feature and are not accepted here.

use covalence_sexp::{SExpr, parse as parse_sexp};
use covalence_types::Int;
use smol_str::SmolStr;

use super::ast::*;
use super::{Builtin, SurfaceError};

type Result<T> = std::result::Result<T, SurfaceError>;

fn malformed(msg: impl Into<String>) -> SurfaceError {
    SurfaceError::Malformed(msg.into())
}

// ============================================================================
// Entry points
// ============================================================================

/// Parse a sequence of surface [`Directive`]s from already-parsed
/// S-expressions. Each top-level S-expression is one directive.
pub fn parse(exprs: &[SExpr]) -> Result<Vec<Directive>> {
    exprs.iter().map(directive).collect()
}

/// Parse surface [`Directive`]s directly from source text, lexing through
/// [`covalence_sexp::parse`] (the Covalence dialect) first.
pub fn parse_str(src: &str) -> Result<Vec<Directive>> {
    let exprs = parse_sexp(src).map_err(|e| malformed(format!("s-expression syntax: {e}")))?;
    parse(&exprs)
}

// ============================================================================
// Small helpers over SExpr
// ============================================================================

/// The children of a non-empty list, or an error naming `ctx`.
fn list<'a>(e: &'a SExpr, ctx: &str) -> Result<&'a [SExpr]> {
    match e.as_list() {
        Some(items) if !items.is_empty() => Ok(items),
        Some(_) => Err(malformed(format!("empty list where {ctx} expected"))),
        None => Err(malformed(format!("expected {ctx}, found an atom"))),
    }
}

/// The symbol text of an atom, or an error naming `ctx`.
fn symbol<'a>(e: &'a SExpr, ctx: &str) -> Result<&'a str> {
    e.as_symbol()
        .ok_or_else(|| malformed(format!("expected {ctx} (a symbol)")))
}

/// The head symbol of a list, if it is a symbol.
fn head_symbol(items: &[SExpr]) -> Option<&str> {
    items.first().and_then(|e| e.as_symbol())
}

/// Require exactly `n` argument children (the slice *after* the head).
fn exact<'a>(args: &'a [SExpr], n: usize, form: &str) -> Result<&'a [SExpr]> {
    if args.len() == n {
        Ok(args)
    } else {
        Err(malformed(format!(
            "{form} takes {n} argument(s), got {}",
            args.len()
        )))
    }
}

// ============================================================================
// Kinds & types
// ============================================================================

fn kind(e: &SExpr) -> Result<Kind> {
    if let Some(s) = e.as_symbol() {
        return match Builtin::from_keyword(s) {
            Some(Builtin::Ty) => Ok(Kind::Ty),
            _ => Err(malformed(format!("`{s}` is not a kind (expected `#ty`)"))),
        };
    }
    let items = list(e, "a kind")?;
    match head_symbol(items).and_then(Builtin::from_keyword) {
        Some(Builtin::Fn) => {
            let ks = items[1..].iter().map(kind).collect::<Result<Vec<_>>>()?;
            if ks.len() < 2 {
                return Err(malformed("`(#fn …)` kind needs at least two parts"));
            }
            Ok(Kind::Fn(ks))
        }
        _ => Err(malformed("expected a kind: `#ty` or `(#fn …)`")),
    }
}

fn ty(e: &SExpr) -> Result<Ty> {
    if let Some(s) = e.as_symbol() {
        if let Some(b) = Builtin::from_keyword(s) {
            return match b {
                Builtin::Prop => Ok(Ty::Prop),
                Builtin::Bytes => Ok(Ty::Bytes),
                _ => Err(malformed(format!("`{s}` is not a type"))),
            };
        }
        if s.starts_with('\'') {
            return Ok(Ty::Var(SmolStr::new(s)));
        }
        // A nullary type former, e.g. `unit`.
        return Ok(Ty::App {
            head: Name(SmolStr::new(s)),
            args: Vec::new(),
        });
    }
    let items = list(e, "a type")?;
    match head_symbol(items) {
        Some(h) if Builtin::from_keyword(h) == Some(Builtin::Fn) => {
            let parts = items[1..].iter().map(ty).collect::<Result<Vec<_>>>()?;
            if parts.len() < 2 {
                return Err(malformed("`(#fn …)` type needs at least two parts"));
            }
            Ok(Ty::Fn(parts))
        }
        Some(h) if Builtin::from_keyword(h).is_some() => {
            Err(malformed(format!("`{h}` is not a type-forming builtin")))
        }
        Some(h) => {
            // `(F A …)` — application of a named type former.
            let args = items[1..].iter().map(ty).collect::<Result<Vec<_>>>()?;
            Ok(Ty::App {
                head: Name(SmolStr::new(h)),
                args,
            })
        }
        None => Err(malformed("a type former must be a name")),
    }
}

/// Parse the `(ty …)` argument list of `#abs` / `#rep`.
fn ty_args(e: &SExpr) -> Result<Vec<Ty>> {
    match e.as_list() {
        Some(items) => items.iter().map(ty).collect(),
        None => Err(malformed("expected a `(…)` list of type arguments")),
    }
}

// ============================================================================
// The term sublanguage
// ============================================================================

/// A binder `x` or `(x A)` — used by `#lam` and `#sel`.
fn binder(e: &SExpr) -> Result<(SmolStr, Option<Ty>)> {
    if let Some(s) = e.as_symbol() {
        return Ok((SmolStr::new(s), None));
    }
    let items = list(e, "a binder")?;
    let [name, t] = exact(items, 2, "a `(x A)` binder")? else {
        unreachable!()
    };
    Ok((SmolStr::new(symbol(name, "a binder name")?), Some(ty(t)?)))
}

fn term(e: &SExpr) -> Result<Term> {
    if let Some(s) = e.as_symbol() {
        if let Ok(n) = s.parse::<Int>() {
            return Ok(Term::Int(n));
        }
        if Builtin::from_keyword(s).is_some() {
            return Err(malformed(format!("`{s}` is a builtin, not a term")));
        }
        return Ok(Term::Var(Name(SmolStr::new(s))));
    }
    let items = list(e, "a term")?;
    if let Some(h) = head_symbol(items)
        && let Some(b) = Builtin::from_keyword(h)
    {
        return term_builtin(b, &items[1..]);
    }
    if items.len() == 1 {
        // `(x)` is just `x`.
        return term(&items[0]);
    }
    // Curried application `(f x y …)`.
    let head = Box::new(term(&items[0])?);
    let args = items[1..].iter().map(term).collect::<Result<Vec<_>>>()?;
    Ok(Term::App { head, args })
}

fn term_builtin(b: Builtin, args: &[SExpr]) -> Result<Term> {
    match b {
        Builtin::Lam => {
            let [bind, body] = exact(args, 2, "`(#lam BINDER BODY)`")? else {
                unreachable!()
            };
            let (param, ty) = binder(bind)?;
            Ok(Term::Lam {
                param,
                ty,
                body: Box::new(term(body)?),
            })
        }
        Builtin::Eq => {
            let [a, c] = exact(args, 2, "`(#eq A B)`")? else {
                unreachable!()
            };
            Ok(Term::Eq(Box::new(term(a)?), Box::new(term(c)?)))
        }
        Builtin::Sel => {
            let [bind, pred] = exact(args, 2, "`(#sel BINDER PRED)`")? else {
                unreachable!()
            };
            let (param, ty) = binder(bind)?;
            Ok(Term::Select {
                param,
                ty,
                pred: Box::new(term(pred)?),
            })
        }
        Builtin::Abs | Builtin::Rep => {
            let [spec, targs, body] = exact(args, 3, "`(#abs SPEC (TY…) BODY)`")? else {
                unreachable!()
            };
            let spec = Name(SmolStr::new(symbol(spec, "a spec name")?));
            let targs = ty_args(targs)?;
            let body = Box::new(term(body)?);
            Ok(if b == Builtin::Abs {
                Term::Abs {
                    spec,
                    args: targs,
                    body,
                }
            } else {
                Term::Rep {
                    spec,
                    args: targs,
                    body,
                }
            })
        }
        Builtin::Blob => {
            let [lit] = exact(args, 1, "`(#blob BYTES)`")? else {
                unreachable!()
            };
            let (_fmt, bytes) = lit
                .as_str()
                .ok_or_else(|| malformed("`#blob` payload must be a string literal"))?;
            Ok(Term::Blob(bytes.to_vec().into()))
        }
        other => Err(malformed(format!(
            "`{}` is not a term form",
            other.as_str()
        ))),
    }
}

// ============================================================================
// Directives
// ============================================================================

fn directive(e: &SExpr) -> Result<Directive> {
    let items = list(e, "a directive")?;
    let head =
        head_symbol(items).ok_or_else(|| malformed("a directive must start with a `#`-keyword"))?;
    let b = Builtin::from_keyword(head)
        .ok_or_else(|| malformed(format!("`{head}` is not a directive keyword")))?;
    let args = &items[1..];
    match b {
        Builtin::Theory => {
            let (name, rest) = args
                .split_first()
                .ok_or_else(|| malformed("`#theory` needs a name"))?;
            let name = SmolStr::new(symbol(name, "a theory name")?);
            let body = rest.iter().map(directive).collect::<Result<Vec<_>>>()?;
            Ok(Directive::Theory { name, body })
        }
        Builtin::TyDecl => Ok(Directive::TyDecl(
            args.iter().map(tydecl_item).collect::<Result<Vec<_>>>()?,
        )),
        Builtin::Decl => Ok(Directive::Decl(
            args.iter().map(sig).collect::<Result<Vec<_>>>()?,
        )),
        Builtin::Clause => Ok(Directive::Clause(
            args.iter().map(rule).collect::<Result<Vec<_>>>()?,
        )),
        Builtin::Def => def(args).map(Directive::Def),
        Builtin::Thm => thm(args).map(Directive::Thm),
        Builtin::Import => import(args).map(Directive::Import),
        other => Err(malformed(format!(
            "`{}` is not a top-level directive",
            other.as_str()
        ))),
    }
}

/// `(NAME PARAM… RESULT-KIND)`, e.g. `(option 'a #ty)`.
fn tydecl_item(e: &SExpr) -> Result<TyDeclItem> {
    let items = list(e, "a `#tydecl` item")?;
    if items.len() < 2 {
        return Err(malformed("a `#tydecl` item is `(NAME PARAM… RESULT-KIND)`"));
    }
    let name = SmolStr::new(symbol(&items[0], "a type-former name")?);
    let (result, params_src) = items[1..].split_last().expect("len >= 2 checked above");
    let params = params_src
        .iter()
        .map(|p| {
            let s = symbol(p, "a type parameter")?;
            if !s.starts_with('\'') {
                return Err(malformed(format!(
                    "type parameter `{s}` must start with `'`"
                )));
            }
            Ok(SmolStr::new(s))
        })
        .collect::<Result<Vec<_>>>()?;
    Ok(TyDeclItem {
        name,
        params,
        result: kind(result)?,
    })
}

/// `(#sig NAME TYPE)`.
fn sig(e: &SExpr) -> Result<Sig> {
    let items = list(e, "a `#sig`")?;
    if head_symbol(items).and_then(Builtin::from_keyword) != Some(Builtin::Sig) {
        return Err(malformed("a `#decl` entry must be `(#sig NAME TYPE)`"));
    }
    let [name, t] = exact(&items[1..], 2, "`(#sig NAME TYPE)`")? else {
        unreachable!()
    };
    Ok(Sig {
        name: SmolStr::new(symbol(name, "a constant name")?),
        ty: ty(t)?,
    })
}

/// `(#rw LHS RHS)`.
fn rule(e: &SExpr) -> Result<Rule> {
    let items = list(e, "a `#rw` rule")?;
    if head_symbol(items).and_then(Builtin::from_keyword) != Some(Builtin::Rw) {
        return Err(malformed("a `#clause` entry must be `(#rw LHS RHS)`"));
    }
    let [lhs, rhs] = exact(&items[1..], 2, "`(#rw LHS RHS)`")? else {
        unreachable!()
    };
    Ok(Rule {
        lhs: term(lhs)?,
        rhs: term(rhs)?,
    })
}

/// `(#def NAME SORT BODY)`.
fn def(args: &[SExpr]) -> Result<Def> {
    let [name, sort_e, body_e] = exact(args, 3, "`(#def NAME SORT BODY)`")? else {
        unreachable!()
    };
    let name = SmolStr::new(symbol(name, "a definition name")?);
    let sort_items = list(sort_e, "a `#def` sort")?;
    let sort = match head_symbol(sort_items).and_then(Builtin::from_keyword) {
        Some(Builtin::Ty) => {
            let params = sort_items[1..]
                .iter()
                .map(|p| Ok(SmolStr::new(symbol(p, "a type parameter")?)))
                .collect::<Result<Vec<_>>>()?;
            DefSort::Type { params }
        }
        Some(Builtin::Term) => {
            let [t] = exact(&sort_items[1..], 1, "`(#term TYPE)`")? else {
                unreachable!()
            };
            DefSort::Term(ty(t)?)
        }
        _ => return Err(malformed("a `#def` sort is `(#ty …)` or `(#term TYPE)`")),
    };
    let body = match body_e
        .as_list()
        .and_then(head_symbol)
        .and_then(Builtin::from_keyword)
    {
        Some(Builtin::Newtype) => {
            let items = body_e.as_list().expect("matched a list above");
            let [carrier] = exact(&items[1..], 1, "`(#newtype CARRIER)`")? else {
                unreachable!()
            };
            DefBody::Newtype(ty(carrier)?)
        }
        _ => DefBody::Term(term(body_e)?),
    };
    Ok(Def { name, sort, body })
}

/// `(#thm NAME STATEMENT (#by …))`.
fn thm(args: &[SExpr]) -> Result<ThmDecl> {
    let (name, rest) = args
        .split_first()
        .ok_or_else(|| malformed("`#thm` needs a name"))?;
    let name = SmolStr::new(symbol(name, "a theorem name")?);
    let (proof_e, stmt_src) = rest
        .split_last()
        .ok_or_else(|| malformed("`#thm` needs a statement and a `(#by …)` proof"))?;
    let proof = proof(proof_e)?;
    let statement = statement(stmt_src)?;
    Ok(ThmDecl {
        name,
        statement,
        proof,
    })
}

/// The statement children of a `#thm`: either a single `(#spec NAME)`, or
/// an optional `(#hyps …)` followed by a `(#concl TERM)`.
fn statement(src: &[SExpr]) -> Result<Statement> {
    if let [single] = src
        && let Some(items) = single.as_list()
        && head_symbol(items).and_then(Builtin::from_keyword) == Some(Builtin::Spec)
    {
        let [name] = exact(&items[1..], 1, "`(#spec NAME)`")? else {
            unreachable!()
        };
        return Ok(Statement::Spec(Name(SmolStr::new(symbol(
            name,
            "a spec name",
        )?))));
    }
    let mut hyps = Vec::new();
    let mut concl = None;
    for part in src {
        let items = list(part, "a `#thm` statement clause")?;
        match head_symbol(items).and_then(Builtin::from_keyword) {
            Some(Builtin::Hyps) => {
                hyps = items[1..].iter().map(term).collect::<Result<Vec<_>>>()?;
            }
            Some(Builtin::Concl) => {
                let [c] = exact(&items[1..], 1, "`(#concl TERM)`")? else {
                    unreachable!()
                };
                concl = Some(term(c)?);
            }
            _ => {
                return Err(malformed(
                    "`#thm` statement expects `#concl` / `#hyps` / `#spec`",
                ));
            }
        }
    }
    let concl = concl.ok_or_else(|| malformed("`#thm` statement needs a `(#concl TERM)`"))?;
    Ok(Statement::Sequent { hyps, concl })
}

/// `(#by STEP…)` — steps kept raw pending a tactic grammar (see §5).
fn proof(e: &SExpr) -> Result<Proof> {
    let items = list(e, "a `(#by …)` proof")?;
    if head_symbol(items).and_then(Builtin::from_keyword) != Some(Builtin::By) {
        return Err(malformed("a `#thm` proof must be `(#by …)`"));
    }
    Ok(Proof {
        steps: items[1..].to_vec(),
    })
}

/// `(#import NAME)` — by name only; by-hash content addressing is future
/// work (`docs/surface-syntax.md` §7).
fn import(args: &[SExpr]) -> Result<Import> {
    let [target] = exact(args, 1, "`(#import NAME)`")? else {
        unreachable!()
    };
    Ok(Import {
        name: SmolStr::new(symbol(target, "an import name")?),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn option_spec_round_trips() {
        let src = r#"
            (#theory option
              (#tydecl
                (option 'a #ty))
              (#decl
                (#sig none (option 'a))
                (#sig some (#fn 'a (option 'a)))
                (#sig case (#fn (option 'a) 'b (#fn 'a 'b) 'b)))
              (#clause
                (#rw e none)
                (#rw e (some a)))
              (#clause
                (#rw (case none b f) b))
              (#clause
                (#rw (case (some a) b f) (f a))))
        "#;
        let dirs = parse_str(src).expect("parse");
        let [Directive::Theory { name, body }] = dirs.as_slice() else {
            panic!("expected a single #theory, got {dirs:?}");
        };
        assert_eq!(name, "option");
        // tydecl, decl, clause, clause, clause
        assert_eq!(body.len(), 5);
        assert!(matches!(body[0], Directive::TyDecl(_)));
        let Directive::Decl(sigs) = &body[1] else {
            panic!("expected #decl");
        };
        assert_eq!(sigs.len(), 3);
        assert_eq!(sigs[0].name, "none");
        // some : 'a -> option 'a
        assert!(matches!(sigs[1].ty, Ty::Fn(_)));
    }

    #[test]
    fn def_with_lambda_and_coercion() {
        // some := λa. abs (inl a)
        let src = "(#def some (#term (#fn 'a (option 'a))) \
                   (#lam a (#abs option ('a) (inl a))))";
        let dirs = parse_str(src).expect("parse");
        let [Directive::Def(d)] = dirs.as_slice() else {
            panic!("expected a #def");
        };
        assert_eq!(d.name, "some");
        assert!(matches!(d.sort, DefSort::Term(Ty::Fn(_))));
        let DefBody::Term(Term::Lam { param, body, .. }) = &d.body else {
            panic!("expected a lambda body");
        };
        assert_eq!(param, "a");
        assert!(matches!(**body, Term::Abs { .. }));
    }

    #[test]
    fn newtype_def() {
        let dirs = parse_str("(#def option (#ty 'a) (#newtype (coprod 'a unit)))").unwrap();
        let [Directive::Def(d)] = dirs.as_slice() else {
            panic!();
        };
        assert!(matches!(d.sort, DefSort::Type { .. }));
        assert!(matches!(d.body, DefBody::Newtype(Ty::App { .. })));
    }

    #[test]
    fn thm_spec_and_sequent() {
        let dirs =
            parse_str("(#thm option/exhaustive (#spec option.exhaustive) (#by step1 step2))")
                .unwrap();
        let [Directive::Thm(t)] = dirs.as_slice() else {
            panic!();
        };
        assert!(matches!(t.statement, Statement::Spec(_)));
        assert_eq!(t.proof.steps.len(), 2);

        let dirs = parse_str("(#thm t (#concl (#eq a b)) (#by))").unwrap();
        let [Directive::Thm(t)] = dirs.as_slice() else {
            panic!();
        };
        assert!(matches!(
            t.statement,
            Statement::Sequent { ref hyps, .. } if hyps.is_empty()
        ));
    }

    #[test]
    fn int_literal_and_application() {
        let Term::App { head, args } = term(&parse_sexp("(nat.add 1 x)").unwrap()[0]).unwrap()
        else {
            panic!("expected application");
        };
        assert!(matches!(*head, Term::Var(_)));
        assert!(matches!(args[0], Term::Int(_)));
        assert!(matches!(args[1], Term::Var(_)));
    }

    #[test]
    fn import_by_name() {
        let dirs = parse_str("(#import option)").unwrap();
        let [Directive::Import(i)] = dirs.as_slice() else {
            panic!("expected an #import");
        };
        assert_eq!(i.name, "option");
        // Hash strings are not a thing yet.
        assert!(parse_str(r#"(#import "deadbeef")"#).is_err());
    }

    #[test]
    fn rejects_unknown_builtin() {
        assert!(parse_str("(#wat foo)").is_err());
        // bare arrow is not a thing — no sugar.
        assert!(
            ty(&parse_sexp("(-> 'a 'b)").unwrap()[0]).is_ok_and(|t| matches!(t, Ty::App { .. }))
        );
    }
}
