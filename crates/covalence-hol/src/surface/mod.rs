//! Surface syntax — a "generalized Haskell" authoring layer (**DESIGN
//! SKETCH; nothing here is wired into the kernel yet**).
//!
//! This module begins sketching the high-level language described in
//! [`docs/surface-syntax.md`]: an S-expression syntax for writing
//! theories, definitions, and proofs that *elaborates* down to the
//! kernel objects of `covalence-core`. The canonical low-level
//! S-expressions in [`crate::sexp`] are the *elaboration target*; this is
//! the layer a human writes.
//!
//! ## Everything is a pure S-expression
//!
//! There is **no infix syntax**. The arrows, colons, and rewrite arrows
//! in the design doc (`'a -> 'b`, `none : option 'a`, `lhs => rhs`) are
//! prose *sugar* only. The real language is pure S-expressions in which
//! every reserved word is a `#`-headed **builtin**:
//!
//! | sugar (doc prose) | pure form |
//! |---|---|
//! | `'a -> 'b` | `(#fn 'a 'b)` |
//! | `none : option 'a` | `(#sig none (option 'a))` |
//! | `lhs => rhs` | `(#rw lhs rhs)` |
//! | `(= a b)` | `(#eq a b)` |
//! | `λa. body` / `(lam a body)` | `(#lam a body)` |
//! | `(by …)` | `(#by …)` |
//!
//! Tokens fall into three lexical classes, by spelling alone (see
//! [`ast::Name::class`]):
//!
//! - `#…` — a **builtin** keyword ([`Builtin`]).
//! - `'…` — a **type variable**.
//! - everything else — an ordinary **name**: a dotted *catalogue*
//!   reference (`coprod.case`) or a *local* name (`option`, `e`, `f`).
//!
//! ## The term sublanguage
//!
//! A distinguished, self-contained fragment — [`ast::Term`] — is the
//! *term sublanguage*: a simply-typed lambda calculus (variables,
//! application, `#lam`, the kernel primitives `#eq`/`#sel`, the newtype
//! coercions `#abs`/`#rep`) in which `#def` bodies are written. It
//! deliberately has **no operational semantics of its own** — reduction
//! is the kernel's job. It is kept as a closed grammar because it is the
//! candidate we may eventually lift *into the TCB* as the native input
//! format for writing `defs/`, retiring the hand-written `Term::app` /
//! `Term::abs` plumbing in `covalence-core`.
//!
//! ## Status
//!
//! The AST ([`ast`]) is sketched; [`parse`] is a stub (see
//! `SKELETONS.md`). The elaborator (surface → low-level S-expr → kernel
//! object) is future work; see `docs/surface-syntax.md` §8.
//!
//! [`docs/surface-syntax.md`]: ../../../docs/surface-syntax.md

pub mod ast;

pub use ast::{
    Def, DefBody, DefSort, Directive, Import, ImportTarget, Kind, Name, NameClass, Proof, Rule,
    Sig, Statement, Term, ThmDecl, Ty, TyDeclItem,
};

/// The reserved `#`-headed keywords of the surface language.
///
/// This is the registry that makes [`NameClass::Builtin`] meaningful: a
/// token spelled `#foo` that is not one of these is a *malformed*
/// builtin, which the parser should reject rather than silently treat as
/// a name. The set is **provisional** — it will grow as the directive,
/// type, and term grammars are pinned down.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Builtin {
    // --- directive heads ---
    /// `#theory` — open a named theory scope.
    Theory,
    /// `#tydecl` — declare type formers + kinds.
    TyDecl,
    /// `#decl` — declare constants + signatures.
    Decl,
    /// `#clause` — an equational / Horn constraint (a disjunction of
    /// `#rw` rules).
    Clause,
    /// `#def` — a tight definition with a body.
    Def,
    /// `#thm` — a named theorem + proof.
    Thm,
    /// `#import` — a dependency edge.
    Import,

    // --- kinds & types ---
    /// `#ty` — the kind of proper types.
    Ty,
    /// `#prop` — the type of propositions.
    Prop,
    /// `#bytes` — the type of `#blob` literals.
    Bytes,
    /// `#fn` — the function-type / kind arrow.
    Fn,

    // --- statement / directive forms ---
    /// `#sig` — a `name : type` signature.
    Sig,
    /// `#rw` — a `lhs => rhs` rewrite rule.
    Rw,
    /// `#term` — the term sort tag of a `#def`, or a term-typed sequent.
    Term,
    /// `#newtype` — a newtype `#def` body.
    Newtype,
    /// `#spec` — a named spec obligation as a theorem statement.
    Spec,
    /// `#concl` — the conclusion of an explicit sequent.
    Concl,
    /// `#hyps` — the hypotheses of an explicit sequent.
    Hyps,
    /// `#by` — a proof script.
    By,

    // --- term sublanguage ---
    /// `#lam` — lambda abstraction.
    Lam,
    /// `#eq` — primitive equality `=`.
    Eq,
    /// `#sel` — Hilbert choice `ε`.
    Sel,
    /// `#abs` — `TypeSpec` carrier→wrapper coercion.
    Abs,
    /// `#rep` — `TypeSpec` wrapper→carrier coercion.
    Rep,
    /// `#blob` — a byte-string literal.
    Blob,
}

impl Builtin {
    /// The spelling of this builtin, including the leading `#`.
    pub fn as_str(self) -> &'static str {
        use Builtin::*;
        match self {
            Theory => "#theory",
            TyDecl => "#tydecl",
            Decl => "#decl",
            Clause => "#clause",
            Def => "#def",
            Thm => "#thm",
            Import => "#import",
            Ty => "#ty",
            Prop => "#prop",
            Bytes => "#bytes",
            Fn => "#fn",
            Sig => "#sig",
            Rw => "#rw",
            Term => "#term",
            Newtype => "#newtype",
            Spec => "#spec",
            Concl => "#concl",
            Hyps => "#hyps",
            By => "#by",
            Lam => "#lam",
            Eq => "#eq",
            Sel => "#sel",
            Abs => "#abs",
            Rep => "#rep",
            Blob => "#blob",
        }
    }

    /// Parse a builtin from its spelling (with the leading `#`). Returns
    /// `None` for any other token — including a malformed `#foo`.
    pub fn from_keyword(s: &str) -> Option<Builtin> {
        use Builtin::*;
        Some(match s {
            "#theory" => Theory,
            "#tydecl" => TyDecl,
            "#decl" => Decl,
            "#clause" => Clause,
            "#def" => Def,
            "#thm" => Thm,
            "#import" => Import,
            "#ty" => Ty,
            "#prop" => Prop,
            "#bytes" => Bytes,
            "#fn" => Fn,
            "#sig" => Sig,
            "#rw" => Rw,
            "#term" => Term,
            "#newtype" => Newtype,
            "#spec" => Spec,
            "#concl" => Concl,
            "#hyps" => Hyps,
            "#by" => By,
            "#lam" => Lam,
            "#eq" => Eq,
            "#sel" => Sel,
            "#abs" => Abs,
            "#rep" => Rep,
            "#blob" => Blob,
            _ => return None,
        })
    }
}

/// Errors from parsing / lowering the surface syntax.
#[derive(Debug, thiserror::Error)]
pub enum SurfaceError {
    /// A part of the surface front-end that is sketched but not yet
    /// implemented (see `SKELETONS.md`).
    #[error("surface syntax: not yet implemented: {0}")]
    NotImplemented(&'static str),
    /// A structural error in the S-expression shape.
    #[error("surface syntax: {0}")]
    Malformed(String),
}

/// Parse a sequence of surface [`Directive`]s from already-parsed
/// S-expressions (use [`covalence_sexp::parse`] to get the input).
///
/// **Skeleton:** the AST in [`ast`] is fully sketched but the lowering
/// from [`covalence_sexp::SExpr`] is not written yet. Tracked in
/// `SKELETONS.md`.
pub fn parse(_exprs: &[covalence_sexp::SExpr]) -> Result<Vec<Directive>, SurfaceError> {
    Err(SurfaceError::NotImplemented(
        "surface::parse: S-expression lowering to the directive AST",
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn builtins_round_trip() {
        for b in [
            Builtin::Theory,
            Builtin::Fn,
            Builtin::Lam,
            Builtin::Eq,
            Builtin::Rw,
            Builtin::Blob,
        ] {
            assert_eq!(Builtin::from_keyword(b.as_str()), Some(b));
            assert!(b.as_str().starts_with('#'));
        }
        assert_eq!(Builtin::from_keyword("#nope"), None);
        assert_eq!(Builtin::from_keyword("option"), None);
    }

    #[test]
    fn name_classes() {
        assert_eq!(Name("#fn".into()).class(), NameClass::Builtin);
        assert_eq!(Name("'a".into()).class(), NameClass::TyVar);
        assert_eq!(Name("coprod.case".into()).class(), NameClass::Catalogue);
        assert_eq!(Name("option".into()).class(), NameClass::Local);
    }

    #[test]
    fn parse_is_stubbed() {
        assert!(matches!(
            parse(&[]),
            Err(SurfaceError::NotImplemented(_))
        ));
    }
}
