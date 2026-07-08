//! The pluggable lowering seam — the centerpiece of this crate.
//!
//! A [`Lower`] backend maps the parsed [`Expr`]/[`Decl`] AST onto its own
//! target type ([`Lower::Out`]). Every construct method has a **default impl**
//! that returns an "unsupported construct" error, so a backend overrides only
//! the subset it lowers. That is what lets *different* implementations target
//! *different* subsets of the dialect — most visibly, each backend chooses how
//! a numeric literal ([`Lower::nat_lit`]) is realised.
//!
//! The generic [`lower`] driver walks the AST bottom-up: children are lowered
//! first, then the parent method is called with the already-lowered children.

use crate::ast::{Decl, Expr, Lit};

/// A pluggable lowering of the Haskell AST into a backend-chosen target.
///
/// Each method corresponds to one AST construct. The defaults all fail with an
/// [`Unsupported`] error via [`Lower::unsupported`], so implementors override
/// only what they support.
pub trait Lower {
    /// The lowered representation this backend produces.
    type Out;
    /// This backend's error type. Must be constructible from an
    /// [`Unsupported`] so the default methods can report gaps.
    type Error: From<Unsupported>;

    /// Build the error returned by the default (unimplemented) methods.
    fn unsupported(construct: &'static str) -> Self::Error {
        Unsupported { construct }.into()
    }

    /// Lower a natural-number literal. **The construct backends most often
    /// vary** (e.g. a machine integer vs. a Peano numeral).
    fn nat_lit(&mut self, n: u128) -> Result<Self::Out, Self::Error> {
        let _ = n;
        Err(Self::unsupported("natural-number literal"))
    }

    /// Lower a string literal.
    fn str_lit(&mut self, s: &str) -> Result<Self::Out, Self::Error> {
        let _ = s;
        Err(Self::unsupported("string literal"))
    }

    /// Lower a variable reference.
    fn var(&mut self, name: &str) -> Result<Self::Out, Self::Error> {
        let _ = name;
        Err(Self::unsupported("variable"))
    }

    /// Lower an application, given the already-lowered function and argument.
    fn app(&mut self, f: Self::Out, x: Self::Out) -> Result<Self::Out, Self::Error> {
        let _ = (f, x);
        Err(Self::unsupported("application"))
    }

    /// Lower a lambda, given the already-lowered body.
    fn lam(&mut self, param: &str, body: Self::Out) -> Result<Self::Out, Self::Error> {
        let _ = (param, body);
        Err(Self::unsupported("lambda"))
    }

    /// Lower a `let`, given the already-lowered bound value and body.
    fn let_(
        &mut self,
        name: &str,
        val: Self::Out,
        body: Self::Out,
    ) -> Result<Self::Out, Self::Error> {
        let _ = (name, val, body);
        Err(Self::unsupported("let binding"))
    }

    /// Lower an infix operator application, given the already-lowered operands.
    fn binop(&mut self, op: &str, l: Self::Out, r: Self::Out) -> Result<Self::Out, Self::Error> {
        let _ = (op, l, r);
        Err(Self::unsupported("binary operator"))
    }
}

/// The error a default [`Lower`] method returns for a construct the backend
/// does not implement. Backends embed this in their own error type.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Unsupported {
    /// The name of the unsupported construct.
    pub construct: &'static str,
}

impl core::fmt::Display for Unsupported {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "unsupported construct: {}", self.construct)
    }
}

impl std::error::Error for Unsupported {}

/// Lower an expression bottom-up through a [`Lower`] backend.
pub fn lower<L: Lower>(e: &Expr, l: &mut L) -> Result<L::Out, L::Error> {
    match e {
        Expr::Lit(Lit::Nat(n)) => l.nat_lit(*n),
        Expr::Lit(Lit::Str(s)) => l.str_lit(s),
        Expr::Var(name) => l.var(name),
        Expr::App(f, x) => {
            let f = lower(f, l)?;
            let x = lower(x, l)?;
            l.app(f, x)
        }
        Expr::Lam(param, body) => {
            let body = lower(body, l)?;
            l.lam(param, body)
        }
        Expr::Let(name, val, body) => {
            let val = lower(val, l)?;
            let body = lower(body, l)?;
            l.let_(name, val, body)
        }
        Expr::BinOp(op, a, b) => {
            let a = lower(a, l)?;
            let b = lower(b, l)?;
            l.binop(op, a, b)
        }
    }
}

/// Lower a top-level declaration, desugaring `f x y = body` into the lambda
/// term `\x -> \y -> body` and then lowering that expression.
///
/// Returns the defined name alongside its lowered body.
pub fn lower_decl<L: Lower>(d: &Decl, l: &mut L) -> Result<(String, L::Out), L::Error> {
    let mut body = d.body.clone();
    for p in d.params.iter().rev() {
        body = Expr::lam(p.clone(), body);
    }
    let out = lower(&body, l)?;
    Ok((d.name.clone(), out))
}
