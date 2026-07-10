//! **THE canonical lowering** Haskell AST ⇒ [`SExpr`] — the one fixed
//! desugaring of the dialect, and the *only* consumer of Haskell syntax.
//!
//! Backends never see the Haskell AST: they interpret the S-expression IR at
//! the [`Realize`](crate::realize::Realize) seam, so a third-party producer
//! that writes S-expression text directly meets exactly the same backends
//! (that is the pipeline *Haskell dialect ⇒ S-expressions ⇒ backend*).
//!
//! # The desugaring
//!
//! | Haskell               | S-expression        |
//! |-----------------------|---------------------|
//! | nat literal `5`       | nat atom `5` (a covalence `Nat`) |
//! | string literal `"s"`  | string atom `"s"`   |
//! | variable `x`          | symbol `x`          |
//! | application `f x`     | `(f x)`             |
//! | lambda `\x -> b`      | `(lambda x b)`      |
//! | `let n = v in b`      | `(let n v b)`       |
//! | operator `l + r`      | `(+ l r)`           |
//!
//! A top-level declaration `f x y = body` desugars to nested lambdas —
//! `(lambda x (lambda y body'))` — and a module lowers to one
//! `(define f …)` form per declaration ([`decl_to_define`] /
//! [`module_to_sexprs`] / [`module_to_text`]).
//!
//! The [`lower`] / [`lower_decl`] drivers compose this canonical lowering
//! with a [`Realize`] backend, running the whole pipeline in one call.

use crate::ast::{Decl, Expr, Lit, Module};
use crate::realize::{Realize, realize};
use crate::sexpr::SExpr;

/// Lower an expression to the S-expression IR (the canonical desugaring —
/// total on the AST; see the module docs for the table).
pub fn expr_to_sexpr(e: &Expr) -> SExpr {
    match e {
        Expr::Lit(Lit::Nat(n)) => SExpr::Nat(n.clone()),
        Expr::Lit(Lit::Str(s)) => SExpr::Str(s.clone()),
        Expr::Var(name) => SExpr::sym(name.clone()),
        Expr::App(f, x) => SExpr::list(vec![expr_to_sexpr(f), expr_to_sexpr(x)]),
        Expr::Lam(param, body) => SExpr::list(vec![
            SExpr::sym("lambda"),
            SExpr::sym(param.clone()),
            expr_to_sexpr(body),
        ]),
        Expr::Let(name, val, body) => SExpr::list(vec![
            SExpr::sym("let"),
            SExpr::sym(name.clone()),
            expr_to_sexpr(val),
            expr_to_sexpr(body),
        ]),
        Expr::BinOp(op, l, r) => SExpr::list(vec![
            SExpr::sym(op.clone()),
            expr_to_sexpr(l),
            expr_to_sexpr(r),
        ]),
    }
}

/// Lower a top-level declaration, desugaring `f x y = body` into the nested
/// lambda `(lambda x (lambda y body'))`. Returns the defined name alongside
/// the lowered body.
pub fn decl_to_sexpr(d: &Decl) -> (String, SExpr) {
    let mut body = expr_to_sexpr(&d.body);
    for p in d.params.iter().rev() {
        body = SExpr::list(vec![SExpr::sym("lambda"), SExpr::sym(p.clone()), body]);
    }
    (d.name.clone(), body)
}

/// Lower a declaration to a `(define <name> <body>)` form — the module-level
/// interchange convention (`define` is a convention of the IR text, not a
/// checked construct).
pub fn decl_to_define(d: &Decl) -> SExpr {
    let (name, body) = decl_to_sexpr(d);
    SExpr::list(vec![SExpr::sym("define"), SExpr::sym(name), body])
}

/// Lower a whole module to one `(define …)` form per declaration.
pub fn module_to_sexprs(m: &Module) -> Vec<SExpr> {
    m.iter().map(decl_to_define).collect()
}

/// Lower a whole module to canonical text: one `(define …)` form per line.
/// Round-trips through [`crate::sexpr::parse_sexprs`].
pub fn module_to_text(m: &Module) -> String {
    let mut out = String::new();
    for d in m {
        out.push_str(&decl_to_define(d).to_text());
        out.push('\n');
    }
    out
}

/// Run the full pipeline on an expression: canonical lowering to [`SExpr`],
/// then realization through the backend.
pub fn lower<R: Realize>(e: &Expr, r: &mut R) -> Result<R::Out, R::Error> {
    realize(&expr_to_sexpr(e), r)
}

/// Run the full pipeline on a declaration (desugared to nested lambdas).
/// Returns the defined name alongside its realized body.
pub fn lower_decl<R: Realize>(d: &Decl, r: &mut R) -> Result<(String, R::Out), R::Error> {
    let (name, body) = decl_to_sexpr(d);
    Ok((name, realize(&body, r)?))
}
