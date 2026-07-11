//! The abstract syntax for the supported Haskell expression dialect.
//!
//! This is deliberately tiny: enough shape to demonstrate a pluggable lowering
//! and to grow toward a real `init/` dialect, no more. It covers literals,
//! variables, application, lambdas, `let`, infix operators, `if`/`then`/`else`,
//! and list / tuple / unit literals. See the crate docs for the exact
//! supported subset and [`crate`]'s `SKELETONS.md` for what is not yet modelled
//! (do-notation, guards, `where`, `case`, pattern matching, full layout).

use covalence_types::Nat;

/// A **type expression** — the minimal typing surface the dialect carries so a
/// *typed* backend can build well-typed HOL terms (there is no inference; the
/// types must be written). Covers a type variable (the monad carrier), a
/// possibly-applied type constructor (`nat`, `bool`, `option a`, `list a`), and
/// the function type `a -> b` (right-associative). See
/// [`crate::parse::parse_ty`] for the grammar.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ty {
    /// A type variable, e.g. `a` — a lowercase-initial identifier standing for
    /// a HOL free type variable. The monad carrier is one such variable.
    Var(String),
    /// A type constructor applied to zero or more arguments: `nat`, `bool`,
    /// `option a`, `list a`. The head is an identifier; base types are the
    /// zero-argument case.
    Con(String, Vec<Ty>),
    /// A function type `a -> b` (right-associative, so `a -> b -> c` parses as
    /// `a -> (b -> c)`).
    Fun(Box<Ty>, Box<Ty>),
}

impl Ty {
    /// A base type (nullary constructor): `Ty::base("nat")` = `nat`.
    pub fn base(name: impl Into<String>) -> Ty {
        Ty::Con(name.into(), Vec::new())
    }

    /// A type variable: `Ty::var("a")` = `a`.
    pub fn var(name: impl Into<String>) -> Ty {
        Ty::Var(name.into())
    }

    /// A function type `dom -> cod`.
    pub fn fun(dom: Ty, cod: Ty) -> Ty {
        Ty::Fun(Box::new(dom), Box::new(cod))
    }

    /// A type-constructor application `head arg1 arg2 …`.
    pub fn con(head: impl Into<String>, args: Vec<Ty>) -> Ty {
        Ty::Con(head.into(), args)
    }
}

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
    /// A single-parameter lambda: `\x -> e`, or the type-annotated form
    /// `\(x :: t) -> e` carrying the binder's type. Multi-parameter lambdas
    /// (`\x y -> e`) are parsed as nested [`Expr::Lam`]. The optional [`Ty`] is
    /// the minimal typing surface a *typed* backend consumes (the untyped
    /// [`crate::lower`] drops it); an unannotated binder leaves it `None`.
    Lam(String, Option<Ty>, Box<Expr>),
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

    /// Convenience constructor for an *unannotated* [`Expr::Lam`].
    pub fn lam(param: impl Into<String>, body: Expr) -> Expr {
        Expr::Lam(param.into(), None, Box::new(body))
    }

    /// Convenience constructor for a *type-annotated* [`Expr::Lam`]
    /// (`\(x :: t) -> body`).
    pub fn lam_ty(param: impl Into<String>, ty: Ty, body: Expr) -> Expr {
        Expr::Lam(param.into(), Some(ty), Box::new(body))
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
    /// The declared type signature, if a `name :: Ty` line preceded this
    /// definition (associated by name in [`crate::parse::parse_module`]).
    /// `None` when no signature was given. A *typed* backend uses the signature
    /// to type the parameters left-to-right; the untyped [`crate::lower`]
    /// ignores it.
    pub sig: Option<Ty>,
}

impl Decl {
    /// A signature-free declaration (`name p1 … = body`).
    pub fn new(name: impl Into<String>, params: Vec<String>, body: Expr) -> Decl {
        Decl {
            name: name.into(),
            params,
            body,
            sig: None,
        }
    }
}

/// A module is a sequence of top-level declarations.
pub type Module = Vec<Decl>;
