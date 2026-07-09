//! The pluggable **SExpr ⇒ backend** seam — the centerpiece of this crate.
//!
//! A [`Realize`] backend interprets the [`SExpr`] interchange IR into its own
//! target type ([`Realize::Out`]). Every method has a **default impl** that
//! returns an "unsupported construct" error, so a backend overrides only the
//! subset it realizes. That is what lets *different* implementations target
//! *different* subsets of the IR — most visibly, each backend chooses how a
//! natural-number atom ([`Realize::nat`], a covalence [`Nat`]) is realised.
//!
//! This seam **succeeds the old AST-shaped `Lower` trait**: the pluggable
//! boundary used to sit at the Haskell AST, which forced every backend to
//! re-decide the desugaring of Haskell constructs. Now there is ONE canonical
//! Haskell ⇒ SExpr lowering ([`crate::lower`]) — the sole consumer of Haskell
//! syntax — and backends plug in *behind* it, at the S-expression boundary,
//! where third-party producers (hand-written S-expression text via
//! [`crate::sexpr::parse_sexpr`]) meet the exact same backends as the Haskell
//! front end.
//!
//! The generic [`realize`] driver walks the IR bottom-up: list items are
//! realized first, then [`Realize::list`] is called with the already-realized
//! items.

use covalence_types::Nat;

use crate::sexpr::SExpr;

/// A pluggable realization of the [`SExpr`] IR into a backend-chosen target.
///
/// Each method corresponds to one IR construct. The defaults all fail with an
/// [`Unsupported`] error via [`Realize::unsupported`], so implementors
/// override only what they support.
pub trait Realize {
    /// The realized representation this backend produces.
    type Out;
    /// This backend's error type. Must be constructible from an
    /// [`Unsupported`] so the default methods can report gaps.
    type Error: From<Unsupported>;

    /// Build the error returned by the default (unimplemented) methods.
    fn unsupported(construct: &'static str) -> Self::Error {
        Unsupported { construct }.into()
    }

    /// Realize a natural-number atom — a covalence [`Nat`], arbitrary
    /// precision. **The construct backends most often vary** (e.g. a decimal
    /// numeral vs. a Peano numeral).
    fn nat(&mut self, n: &Nat) -> Result<Self::Out, Self::Error> {
        let _ = n;
        Err(Self::unsupported("natural-number atom"))
    }

    /// Realize a string atom.
    fn string(&mut self, s: &str) -> Result<Self::Out, Self::Error> {
        let _ = s;
        Err(Self::unsupported("string atom"))
    }

    /// Realize a symbol atom (identifier, operator, or keyword such as
    /// `lambda` — the canonical lowering encodes binders as plain lists, so a
    /// backend that wants special binder treatment inspects its lists).
    fn symbol(&mut self, s: &str) -> Result<Self::Out, Self::Error> {
        let _ = s;
        Err(Self::unsupported("symbol atom"))
    }

    /// Realize a list, given the already-realized items (possibly empty).
    fn list(&mut self, items: Vec<Self::Out>) -> Result<Self::Out, Self::Error> {
        let _ = items;
        Err(Self::unsupported("list"))
    }
}

/// The error a default [`Realize`] method returns for a construct the backend
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

/// Realize an S-expression bottom-up through a [`Realize`] backend.
pub fn realize<R: Realize>(e: &SExpr, r: &mut R) -> Result<R::Out, R::Error> {
    match e {
        SExpr::Nat(n) => r.nat(n),
        SExpr::Str(s) => r.string(s),
        SExpr::Sym(s) => r.symbol(s),
        SExpr::List(items) => {
            let mut outs = Vec::with_capacity(items.len());
            for it in items {
                outs.push(realize(it, r)?);
            }
            r.list(outs)
        }
    }
}
