//! Demonstration [`Lower`] backends showing the pluggability of the seam.
//!
//! - [`SExprLower`] lowers the whole subset to a canonical S-expression string.
//! - [`PeanoLower`] is identical *except* it lowers numeric literals to Peano
//!   numerals — the same AST, a different numeric strategy.
//! - [`NoLitLower`] leaves [`Lower::nat_lit`] at its default, so any expression
//!   containing a numeric literal fails to lower while literal-free ones
//!   succeed — a backend supporting a strict subset.

use crate::lower::{Lower, Unsupported};

/// The error type shared by the string-producing demo backends.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LowerError(pub Unsupported);

impl From<Unsupported> for LowerError {
    fn from(u: Unsupported) -> Self {
        LowerError(u)
    }
}

impl core::fmt::Display for LowerError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.0.fmt(f)
    }
}

impl std::error::Error for LowerError {}

/// Lowers the entire supported subset to a canonical S-expression string.
#[derive(Clone, Copy, Debug, Default)]
pub struct SExprLower;

impl Lower for SExprLower {
    type Out = String;
    type Error = LowerError;

    fn nat_lit(&mut self, n: u128) -> Result<String, LowerError> {
        Ok(n.to_string())
    }

    fn str_lit(&mut self, s: &str) -> Result<String, LowerError> {
        Ok(format!("{s:?}"))
    }

    fn var(&mut self, name: &str) -> Result<String, LowerError> {
        Ok(name.to_string())
    }

    fn app(&mut self, f: String, x: String) -> Result<String, LowerError> {
        Ok(format!("({f} {x})"))
    }

    fn lam(&mut self, param: &str, body: String) -> Result<String, LowerError> {
        Ok(format!("(\\{param} -> {body})"))
    }

    fn let_(&mut self, name: &str, val: String, body: String) -> Result<String, LowerError> {
        Ok(format!("(let {name} = {val} in {body})"))
    }

    fn binop(&mut self, op: &str, l: String, r: String) -> Result<String, LowerError> {
        Ok(format!("({op} {l} {r})"))
    }
}

/// Same as [`SExprLower`] but lowers numeric literals to Peano numerals:
/// `0` ⇝ `Z`, `n` ⇝ `(S (S ... Z))` with `n` applications of `S`.
#[derive(Clone, Copy, Debug, Default)]
pub struct PeanoLower;

impl Lower for PeanoLower {
    type Out = String;
    type Error = LowerError;

    fn nat_lit(&mut self, n: u128) -> Result<String, LowerError> {
        let mut s = String::from("Z");
        for _ in 0..n {
            s = format!("(S {s})");
        }
        Ok(s)
    }

    fn str_lit(&mut self, s: &str) -> Result<String, LowerError> {
        SExprLower.str_lit(s)
    }

    fn var(&mut self, name: &str) -> Result<String, LowerError> {
        SExprLower.var(name)
    }

    fn app(&mut self, f: String, x: String) -> Result<String, LowerError> {
        SExprLower.app(f, x)
    }

    fn lam(&mut self, param: &str, body: String) -> Result<String, LowerError> {
        SExprLower.lam(param, body)
    }

    fn let_(&mut self, name: &str, val: String, body: String) -> Result<String, LowerError> {
        SExprLower.let_(name, val, body)
    }

    fn binop(&mut self, op: &str, l: String, r: String) -> Result<String, LowerError> {
        SExprLower.binop(op, l, r)
    }
}

/// A strict-subset backend: it lowers everything *except* numeric literals,
/// leaving [`Lower::nat_lit`] at its failing default. Lowering an expression
/// that mentions a numeric literal returns [`Unsupported`]; literal-free
/// expressions lower fine.
#[derive(Clone, Copy, Debug, Default)]
pub struct NoLitLower;

impl Lower for NoLitLower {
    type Out = String;
    type Error = LowerError;

    // Note: `nat_lit` deliberately NOT overridden — it keeps the default error.

    fn str_lit(&mut self, s: &str) -> Result<String, LowerError> {
        SExprLower.str_lit(s)
    }

    fn var(&mut self, name: &str) -> Result<String, LowerError> {
        SExprLower.var(name)
    }

    fn app(&mut self, f: String, x: String) -> Result<String, LowerError> {
        SExprLower.app(f, x)
    }

    fn lam(&mut self, param: &str, body: String) -> Result<String, LowerError> {
        SExprLower.lam(param, body)
    }

    fn let_(&mut self, name: &str, val: String, body: String) -> Result<String, LowerError> {
        SExprLower.let_(name, val, body)
    }

    fn binop(&mut self, op: &str, l: String, r: String) -> Result<String, LowerError> {
        SExprLower.binop(op, l, r)
    }
}
