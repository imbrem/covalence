//! The **abstract S-expression value algebra** — one construction/observation
//! trait shared by every S-expression-shaped carrier in the tree
//! (design: `notes/vibes/lisp/abstract-sexpr-api.md` §1).
//!
//! [`AbstractSExpr`] is *Layer 1*: anything that can build and observe
//! atom/nil/cons values with payload injections. It is deliberately
//! kernel-agnostic — implementable by plain Rust data (the [`SurfaceSExpr`]
//! free instance over [`SExpr`] itself) as well as by kernel terms (the
//! carved `sexpr` and ACL2 carriers in `covalence-lisp`), so generic code
//! (readers, printers, golden tests, the metacircular ground fragment) runs
//! over all of them. The kernel layer (`KernelSExpr`: proved structural laws,
//! induction) lives with the kernel adapters, not here.
//!
//! What this trait is **not**: a program compiler (compile ≠ quote in the
//! value-semantics dialect; compilation is its own per-dialect axis) and not
//! a reduction interface (that is the `covalence-repl-core` axis).

use crate::types::{Atom, SExp, SExpr};
use covalence_types::Int;

/// A payload literal to inject as an atom. Extensible by enum variant, NOT by
/// a type-level payload parameter (see the design's non-goals): two payload
/// disciplines exist today (symbol bytes, integers) and a third would be a
/// new variant here plus per-impl support.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PayloadLit<'a> {
    /// A symbol atom's name bytes (also string-literal bytes).
    Sym(&'a [u8]),
    /// An integer atom. **Fallible on purpose** at [`AbstractSExpr::atom`]:
    /// this is exactly where dialects genuinely differ (no integers at all /
    /// free-var `(int n)` injection / genuine `aint` payload / negative
    /// rejection), and the trait exposes that instead of papering it over.
    Int(&'a Int),
}

/// An observed atom payload (the owned mirror of [`PayloadLit`]).
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PayloadOwned {
    /// A symbol atom's name bytes.
    Sym(Vec<u8>),
    /// An integer atom.
    Int(Int),
}

/// How [`AbstractSExpr::quote`] treats numeral *symbol* atoms in surface
/// data. This is the one deliberate policy seam between the dialects: the
/// value semantics and the relational dialects quote numerals-in-data as
/// uninterpreted symbol atoms; ACL2 quotes them as genuine integer payload.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum NumeralPolicy {
    /// Numerals in data stay symbol atoms (uninterpreted).
    #[default]
    Sym,
    /// Numerals in data become integer atoms ([`PayloadLit::Int`]).
    Int,
}

/// An abstract S-expression carrier: construction + observation of
/// atom/nil/cons values with payload injections.
///
/// `Value` is the dialect's value representation — [`SExpr`] for the free
/// surface instance, a kernel `Term` for theory-backed instances.
///
/// Constructors are total, untrusted *building*; observers are syntactic
/// recognizers on values (partial by design — an observer answering `None` /
/// `false` says "not syntactically this shape", never a theorem). Impls
/// differ in *capability* behind the same signatures (e.g. a free-variable
/// `(int n)` injection has no quantified arithmetic behind it, while a
/// genuine `int` payload does); that difference is documented on the impls
/// and nothing generic may prove through it.
pub trait AbstractSExpr {
    /// The dialect's value representation.
    type Value: Clone;
    /// A construction failure (unsupported payload, ill-typed build, …).
    type Error;

    // -- constructors (untrusted building) --

    /// The empty list / `nil` value.
    fn nil(&self) -> Self::Value;

    /// `cons h t` — prepend `h` onto `t`.
    fn cons(&self, h: Self::Value, t: Self::Value) -> Result<Self::Value, Self::Error>;

    /// Inject a payload literal as an atom value. Fallible on purpose — see
    /// [`PayloadLit::Int`].
    fn atom(&self, p: PayloadLit<'_>) -> Result<Self::Value, Self::Error>;

    // -- observers (syntactic recognizers; partial by design) --

    /// Observe a cons cell, returning `(head, tail)`.
    fn as_cons(&self, v: &Self::Value) -> Option<(Self::Value, Self::Value)>;

    /// Observe an atom, returning its decoded payload.
    fn as_atom(&self, v: &Self::Value) -> Option<PayloadOwned>;

    /// Is `v` the `nil` value?
    fn is_nil(&self, v: &Self::Value) -> bool;

    // -- surface bridge (defaults derived from the above) --

    /// The numeral policy [`quote`](Self::quote)'s default applies to
    /// numeral symbol atoms in data position.
    fn numeral_policy(&self) -> NumeralPolicy {
        NumeralPolicy::Sym
    }

    /// Surface data → value ("quote"): fold a parsed [`SExpr`] tree through
    /// [`nil`](Self::nil) / [`cons`](Self::cons) / [`atom`](Self::atom) with
    /// the dialect's [`numeral_policy`](Self::numeral_policy). Dialects with
    /// a richer datum discipline (e.g. ACL2's `nil`/`t` canonicalization)
    /// override this.
    fn quote(&self, data: &SExpr) -> Result<Self::Value, Self::Error> {
        match data {
            SExp::Atom(Atom::Symbol(s)) => {
                if self.numeral_policy() == NumeralPolicy::Int
                    && let Ok(n) = s.parse::<Int>()
                {
                    return self.atom(PayloadLit::Int(&n));
                }
                self.atom(PayloadLit::Sym(s.as_bytes()))
            }
            SExp::Atom(Atom::Str { bytes, .. }) => self.atom(PayloadLit::Sym(bytes)),
            SExp::List(items) => {
                let mut acc = self.nil();
                for it in items.iter().rev() {
                    let h = self.quote(it)?;
                    acc = self.cons(h, acc)?;
                }
                Ok(acc)
            }
        }
    }

    /// Value → surface data (rendering). `None` for a non-datum — a stuck
    /// term, an off-carrier literal, or an *improper* (dotted) list, which
    /// the surface [`SExpr`] tree cannot represent — the caller decides how
    /// to print those (dialect printers keep their dotted-pair / raw-term
    /// fallbacks).
    fn render(&self, v: &Self::Value) -> Option<SExpr> {
        if self.is_nil(v) {
            return Some(SExp::List(Vec::new()));
        }
        if let Some(p) = self.as_atom(v) {
            return Some(render_atom(&p));
        }
        if self.as_cons(v).is_some() {
            let mut items = Vec::new();
            let mut cur = v.clone();
            loop {
                if self.is_nil(&cur) {
                    return Some(SExp::List(items));
                }
                let (h, t) = self.as_cons(&cur)?;
                items.push(self.render(&h)?);
                cur = t;
            }
        }
        None
    }
}

/// Render an observed payload as a surface atom: integers as decimal
/// numerals, symbol bytes as a symbol when valid UTF-8, else a `b"…"`
/// string literal.
fn render_atom(p: &PayloadOwned) -> SExpr {
    match p {
        PayloadOwned::Int(n) => SExp::symbol(n.to_string()),
        PayloadOwned::Sym(b) => match String::from_utf8(b.clone()) {
            Ok(s) => SExp::symbol(s),
            Err(_) => SExp::string("b", b.clone()),
        },
    }
}

/// A [`SurfaceSExpr`] construction failure.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum SurfaceError {
    /// `cons` onto an atom tail: the surface [`SExpr`] tree has no dotted
    /// pairs.
    #[error("surface `SExpr` cannot represent a dotted pair (cons onto an atom tail)")]
    DottedTail,
}

/// The **free instance** on [`SExpr`] itself: values *are* parse trees, laws
/// are absent. `quote` ≈ identity modulo the numeral policy (numerals are
/// canonicalized to decimal symbols). Useful for carrier-generic tests and
/// the reader/printer round-trip harness.
#[derive(Debug, Clone, Copy, Default)]
pub struct SurfaceSExpr {
    policy: NumeralPolicy,
}

impl SurfaceSExpr {
    /// The default instance: numerals in data stay symbols.
    pub fn new() -> Self {
        SurfaceSExpr {
            policy: NumeralPolicy::Sym,
        }
    }

    /// An instance with an explicit numeral policy (under
    /// [`NumeralPolicy::Int`], numeral symbols observe as
    /// [`PayloadOwned::Int`]).
    pub fn with_policy(policy: NumeralPolicy) -> Self {
        SurfaceSExpr { policy }
    }
}

impl AbstractSExpr for SurfaceSExpr {
    type Value = SExpr;
    type Error = SurfaceError;

    fn nil(&self) -> SExpr {
        SExp::List(Vec::new())
    }

    fn cons(&self, h: SExpr, t: SExpr) -> Result<SExpr, SurfaceError> {
        match t {
            SExp::List(mut items) => {
                items.insert(0, h);
                Ok(SExp::List(items))
            }
            SExp::Atom(_) => Err(SurfaceError::DottedTail),
        }
    }

    fn atom(&self, p: PayloadLit<'_>) -> Result<SExpr, SurfaceError> {
        Ok(match p {
            // Numerals ARE symbols in the surface tree (the parser's truth);
            // an integer payload renders as its decimal numeral.
            PayloadLit::Int(n) => SExp::symbol(n.to_string()),
            PayloadLit::Sym(b) => match String::from_utf8(b.to_vec()) {
                Ok(s) => SExp::symbol(s),
                Err(_) => SExp::string("b", b.to_vec()),
            },
        })
    }

    fn as_cons(&self, v: &SExpr) -> Option<(SExpr, SExpr)> {
        match v {
            SExp::List(items) if !items.is_empty() => {
                Some((items[0].clone(), SExp::List(items[1..].to_vec())))
            }
            _ => None,
        }
    }

    fn as_atom(&self, v: &SExpr) -> Option<PayloadOwned> {
        match v {
            SExp::Atom(Atom::Symbol(s)) => {
                if self.policy == NumeralPolicy::Int
                    && let Ok(n) = s.parse::<Int>()
                {
                    return Some(PayloadOwned::Int(n));
                }
                Some(PayloadOwned::Sym(s.as_bytes().to_vec()))
            }
            SExp::Atom(Atom::Str { bytes, .. }) => Some(PayloadOwned::Sym(bytes.to_vec())),
            SExp::List(_) => None,
        }
    }

    fn is_nil(&self, v: &SExpr) -> bool {
        matches!(v, SExp::List(items) if items.is_empty())
    }

    fn numeral_policy(&self) -> NumeralPolicy {
        self.policy
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse;

    fn one(src: &str) -> SExpr {
        let mut v = parse(src).unwrap();
        assert_eq!(v.len(), 1, "expected one form in {src:?}");
        v.pop().unwrap()
    }

    fn roundtrip(c: &SurfaceSExpr, src: &str) {
        let data = one(src);
        let v = c.quote(&data).unwrap();
        let back = c.render(&v).expect("datum must render");
        assert_eq!(back, data, "round-trip mismatch for {src:?}");
    }

    #[test]
    fn surface_roundtrip() {
        let c = SurfaceSExpr::new();
        for src in ["foo", "()", "(a b c)", "(a (b c) () d)", "(1 2 3)"] {
            roundtrip(&c, src);
        }
        let ci = SurfaceSExpr::with_policy(NumeralPolicy::Int);
        for src in ["foo", "(1 2 3)", "(a 1 (2 b))"] {
            roundtrip(&ci, src);
        }
    }

    #[test]
    fn surface_observers() {
        let c = SurfaceSExpr::new();
        let v = c.quote(&one("(a b)")).unwrap();
        let (h, t) = c.as_cons(&v).unwrap();
        assert_eq!(c.as_atom(&h), Some(PayloadOwned::Sym(b"a".to_vec())));
        let (h2, t2) = c.as_cons(&t).unwrap();
        assert_eq!(c.as_atom(&h2), Some(PayloadOwned::Sym(b"b".to_vec())));
        assert!(c.is_nil(&t2));
        // Negative controls: observers answer None across shapes.
        assert!(c.as_cons(&h).is_none());
        assert!(c.as_atom(&v).is_none());
        assert!(!c.is_nil(&v));
    }

    #[test]
    fn surface_numeral_policy() {
        let sym = SurfaceSExpr::new();
        let int = SurfaceSExpr::with_policy(NumeralPolicy::Int);
        let n = one("42");
        // Sym policy: the numeral observes as its symbol bytes.
        assert_eq!(
            sym.as_atom(&sym.quote(&n).unwrap()),
            Some(PayloadOwned::Sym(b"42".to_vec()))
        );
        // Int policy: the numeral observes as an integer payload.
        assert_eq!(
            int.as_atom(&int.quote(&n).unwrap()),
            Some(PayloadOwned::Int("42".parse().unwrap()))
        );
        // atom(Int) → render → the decimal numeral, both policies.
        let forty_two: Int = "42".parse().unwrap();
        for c in [sym, int] {
            let v = c.atom(PayloadLit::Int(&forty_two)).unwrap();
            assert_eq!(c.render(&v), Some(SExp::symbol("42")));
        }
    }

    #[test]
    fn surface_no_dotted_pairs() {
        let c = SurfaceSExpr::new();
        let a = c.atom(PayloadLit::Sym(b"a")).unwrap();
        let b = c.atom(PayloadLit::Sym(b"b")).unwrap();
        assert_eq!(c.cons(a, b), Err(SurfaceError::DottedTail));
    }
}
