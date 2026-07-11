//! The abstract syntax for the supported Haskell expression dialect.
//!
//! This is deliberately tiny: enough shape to demonstrate a pluggable lowering
//! and to grow toward a real `init/` dialect, no more. It covers literals,
//! variables, application, lambdas, `let`, infix operators, `if`/`then`/`else`,
//! and list / tuple / unit literals. See the crate docs for the exact
//! supported subset and [`crate`]'s `SKELETONS.md` for what is not yet modelled
//! (do-notation, guards, `where`, `case`, pattern matching, full layout).

use covalence_types::Nat;

/// A literal — kept small on purpose. The [`Lit::Nat`] case is the emphasized
/// one: numeric-literal realization is exactly what a backend is expected to
/// vary.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Lit {
    /// A natural-number literal, e.g. `5`. **A Haskell `Nat` literal is a
    /// covalence [`Nat`]** — arbitrary precision, no machine-integer cap.
    Nat(Nat),
    /// A string literal, e.g. `"hi"` (already unescaped).
    Str(String),
}

/// A Haskell expression.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr {
    /// A literal.
    Lit(Lit),
    /// A variable / identifier reference.
    Var(String),
    /// Application by juxtaposition: `f x`.
    App(Box<Expr>, Box<Expr>),
    /// A single-parameter lambda: `\x -> e`. Multi-parameter lambdas
    /// (`\x y -> e`) are parsed as nested [`Expr::Lam`].
    Lam(String, Box<Expr>),
    /// A `let x = e in e'` binding (single, non-recursive binder).
    Let(String, Box<Expr>, Box<Expr>),
    /// A binary operator application: `l <op> r`.
    BinOp(String, Box<Expr>, Box<Expr>),
    /// A conditional `if c then t else e`.
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    /// A list literal `[e1, e2, …]` (possibly empty).
    List(Vec<Expr>),
    /// A tuple literal `(e1, e2, …)` — always two or more elements (a
    /// one-element parenthesized expression is just that expression, and the
    /// zero-element `()` is the [unit][`Expr::Unit`]).
    Tuple(Vec<Expr>),
    /// The unit value `()`.
    Unit,
}

impl Expr {
    /// Convenience constructor for [`Expr::App`].
    pub fn app(f: Expr, x: Expr) -> Expr {
        Expr::App(Box::new(f), Box::new(x))
    }

    /// Convenience constructor for [`Expr::Lam`].
    pub fn lam(param: impl Into<String>, body: Expr) -> Expr {
        Expr::Lam(param.into(), Box::new(body))
    }

    /// Convenience constructor for [`Expr::Let`].
    pub fn let_(name: impl Into<String>, val: Expr, body: Expr) -> Expr {
        Expr::Let(name.into(), Box::new(val), Box::new(body))
    }

    /// Convenience constructor for [`Expr::BinOp`].
    pub fn binop(op: impl Into<String>, l: Expr, r: Expr) -> Expr {
        Expr::BinOp(op.into(), Box::new(l), Box::new(r))
    }

    /// Convenience constructor for [`Expr::If`].
    pub fn if_(c: Expr, t: Expr, e: Expr) -> Expr {
        Expr::If(Box::new(c), Box::new(t), Box::new(e))
    }
}

/// A top-level function definition: `name p1 p2 = body`.
///
/// The parameters are curried lambda binders; see
/// [`crate::lower::lower_decl`] for the desugaring
/// (`f x y = body` ⇝ `f = \x -> \y -> body`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Decl {
    /// The defined name.
    pub name: String,
    /// The parameter names, in order.
    pub params: Vec<String>,
    /// The definition body.
    pub body: Expr,
}

/// A module is a sequence of top-level declarations.
pub type Module = Vec<Decl>;
