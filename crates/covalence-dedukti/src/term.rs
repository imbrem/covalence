//! The Dedukti term model: the λΠ-calculus modulo rewriting.
//!
//! Dedukti's object language is the **λΠ-calculus** (a.k.a. LF: the dependently
//! typed λ-calculus with `Type`/`Kind` sorts) **modulo a set of user rewrite
//! rules**. Every term is one of: the sort `Type`, an identifier reference
//! (a bound variable or a declared constant — *not* distinguished syntactically;
//! see [`Ref`]), an application, a λ-abstraction, or a (dependent) product.
//!
//! ## Faithful-to-source, names preserved
//!
//! Like [`covalence-metamath`](../../covalence-metamath)'s flat-symbol [`Expr`],
//! this representation is deliberately *faithful to the source*: binders keep
//! their written names ([`Symbol`]) and references are left **unresolved** — a
//! bare identifier is a [`Term::Ref`] regardless of whether it names a λ-bound
//! variable, a rewrite-rule context variable, or a global constant. Resolving
//! references to a binding (and the α-renaming / locally-nameless conversion the
//! kernel wants) is a *consumer* concern, deferred to the future HOL bridge in
//! `covalence-hol` — see the crate `SKELETONS.md`.

use core::fmt;
use smol_str::SmolStr;

/// An identifier as written in the source (a binder name, a constant name, or a
/// module name). Owned `SmolStr`; interning is a deferred north star.
pub type Symbol = SmolStr;

/// A reference to an identifier, optionally module-qualified (`module.name`).
///
/// A reference is **unresolved**: it may name a λ-bound variable, a rewrite-rule
/// context (pattern) variable, or a globally declared constant. Dedukti's
/// concrete syntax does not distinguish these — disambiguation needs the
/// surrounding binding structure plus the signature, and is left to consumers.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Ref {
    /// The module qualifier of a `module.name` reference, if any.
    pub module: Option<Symbol>,
    /// The (unqualified) identifier.
    pub name: Symbol,
}

impl Ref {
    /// An unqualified reference to `name`.
    pub fn new(name: impl Into<Symbol>) -> Self {
        Ref { module: None, name: name.into() }
    }

    /// A module-qualified reference `module.name`.
    pub fn qualified(module: impl Into<Symbol>, name: impl Into<Symbol>) -> Self {
        Ref { module: Some(module.into()), name: name.into() }
    }

    /// Whether this reference carries a module qualifier.
    pub fn is_qualified(&self) -> bool {
        self.module.is_some()
    }
}

impl fmt::Display for Ref {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.module {
            Some(m) => write!(f, "{m}.{}", self.name),
            None => write!(f, "{}", self.name),
        }
    }
}

/// A Dedukti term in the λΠ-calculus modulo rewriting.
///
/// Applications are left-associated (`f a b` = `App(App(f, a), b)`); products
/// (`->`) are right-associated. A binder name of `_` (an anonymous/wildcard
/// binder) is normalised to `None`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Term {
    /// The sort `Type` (the type of types; its own type `Kind` is implicit and
    /// not part of the surface syntax).
    Type,
    /// An identifier reference — a variable or a constant (see [`Ref`]).
    Ref(Ref),
    /// Application `f a` (left-associated for `f a b …`).
    App(Box<Term>, Box<Term>),
    /// λ-abstraction `x => body` or annotated `x : ty => body`. `binder` is
    /// `None` for an anonymous `_` binder.
    Abs {
        /// The bound variable name (`None` for `_`).
        binder: Option<Symbol>,
        /// The optional domain annotation (`x : ty => …`).
        ty: Option<Box<Term>>,
        /// The abstraction body.
        body: Box<Term>,
    },
    /// Dependent product `x : domain -> codomain`, or the non-dependent arrow
    /// `domain -> codomain` when `binder` is `None`.
    Pi {
        /// The bound variable name (`None` for a non-dependent arrow).
        binder: Option<Symbol>,
        /// The product domain.
        domain: Box<Term>,
        /// The product codomain (the variable scopes over this).
        codomain: Box<Term>,
    },
    /// A `{ t }` bracketed sub-pattern, occurring only on the left-hand side of
    /// rewrite rules (a Dedukti "dot pattern" / convertibility guard). It is
    /// *parsed* faithfully but carries no matching semantics here — see the
    /// crate `SKELETONS.md`.
    Bracket(Box<Term>),
}

impl Term {
    /// Construct an application `f a`.
    pub fn app(f: Term, a: Term) -> Term {
        Term::App(Box::new(f), Box::new(a))
    }

    /// Apply `head` to a sequence of arguments, left-associating.
    pub fn apply(head: Term, args: impl IntoIterator<Item = Term>) -> Term {
        args.into_iter().fold(head, Term::app)
    }

    /// Construct a λ-abstraction. A `binder` of `Some("_")` is normalised to the
    /// anonymous binder `None`.
    pub fn abs(binder: Option<Symbol>, ty: Option<Term>, body: Term) -> Term {
        Term::Abs {
            binder: normalise_binder(binder),
            ty: ty.map(Box::new),
            body: Box::new(body),
        }
    }

    /// Construct a (dependent) product. A `binder` of `Some("_")` is normalised
    /// to the non-dependent arrow `None`.
    pub fn pi(binder: Option<Symbol>, domain: Term, codomain: Term) -> Term {
        Term::Pi {
            binder: normalise_binder(binder),
            domain: Box::new(domain),
            codomain: Box::new(codomain),
        }
    }

    /// The unqualified-reference shorthand `Term::Ref(Ref::new(name))`.
    pub fn r(name: impl Into<Symbol>) -> Term {
        Term::Ref(Ref::new(name))
    }

    /// Decompose a (possibly nested) application into its head and argument
    /// spine, left-to-right. A non-application returns `(self, [])`.
    pub fn unfold_app(&self) -> (&Term, Vec<&Term>) {
        let mut args = Vec::new();
        let mut head = self;
        while let Term::App(f, a) = head {
            args.push(a.as_ref());
            head = f.as_ref();
        }
        args.reverse();
        (head, args)
    }

    /// Display-precedence level: `2` = atomic (no parens needed as an argument),
    /// `1` = application, `0` = abstraction/product (binds loosest).
    fn level(&self) -> u8 {
        match self {
            Term::Type | Term::Ref(_) | Term::Bracket(_) => 2,
            Term::App(..) => 1,
            Term::Abs { .. } | Term::Pi { .. } => 0,
        }
    }

    /// Write `self`, parenthesising if its natural level is looser than `need`.
    fn fmt_at(&self, f: &mut fmt::Formatter<'_>, need: u8) -> fmt::Result {
        if self.level() < need {
            write!(f, "(")?;
            self.fmt_raw(f)?;
            write!(f, ")")
        } else {
            self.fmt_raw(f)
        }
    }

    fn fmt_raw(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Type => write!(f, "Type"),
            Term::Ref(r) => write!(f, "{r}"),
            Term::Bracket(t) => write!(f, "{{ {t} }}"),
            Term::App(g, a) => {
                g.fmt_at(f, 1)?;
                write!(f, " ")?;
                a.fmt_at(f, 2)
            }
            Term::Abs { binder, ty, body } => {
                let b = binder.as_deref().unwrap_or("_");
                match ty {
                    Some(t) => {
                        write!(f, "{b} : ")?;
                        t.fmt_at(f, 1)?;
                        write!(f, " => ")?;
                    }
                    None => write!(f, "{b} => ")?,
                }
                body.fmt_at(f, 0)
            }
            Term::Pi { binder, domain, codomain } => {
                match binder {
                    Some(b) => {
                        write!(f, "{b} : ")?;
                        domain.fmt_at(f, 1)?;
                    }
                    None => domain.fmt_at(f, 1)?,
                }
                write!(f, " -> ")?;
                codomain.fmt_at(f, 0)
            }
        }
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_raw(f)
    }
}

/// Normalise an explicit `_` binder to the anonymous binder `None`.
fn normalise_binder(binder: Option<Symbol>) -> Option<Symbol> {
    match binder {
        Some(b) if b == "_" => None,
        other => other,
    }
}
