//! Lower elaborated SpecTec declarations into `covalence-core` HOL objects.
//!
//! This is an **untrusted driver** (see crate docs and
//! `docs/metatheory.md` §"computational metatheory"): it consumes the
//! SpecTec AST that the WebAssembly specification is written in and emits
//! checkable kernel objects — `Type` / `TypeSpec` (and, later, `Term`
//! defining equations) — that enter the trusted core through the ordinary
//! kernel rules. Nothing here grows the TCB: a bug in this module can at
//! worst produce a kernel object that fails to type-check or denotes the
//! wrong thing; it cannot mint a false `Thm`, because every kernel object
//! it builds is re-checked by `covalence-core` before any theorem is
//! derived from it.
//!
//! # Scope (smallest end-to-end slice)
//!
//! This first slice lowers exactly **one** SpecTec form: a single-ident
//! `syntax` *alias* declaration — `syntax NAME = BASE` where `BASE` names
//! one of a small set of kernel base types (`nat`, `bool`, `int`,
//! `bytes`, `unit`). It produces a `covalence_core::ty::TypeSpec`
//! `newtype` over that base. Everything else — variant/record syntax,
//! parametric aliases, `def`/`rule`/`relation` lowering — is deferred;
//! see `SKELETONS.md`.
//!
//! The architecture is deliberately a thin `AST node -> Result<HOL
//! object, Diagnostic>` function, matching the rest of the crate's total,
//! `unsafe`-free, no-global-state style so the pass stays liftable into a
//! kernel-verified computation later.

use covalence_core::ty::{Type, TypeSpec};
use smol_str::SmolStr;

use crate::cst::{SyntaxBody, SyntaxDecl, Top};
use crate::source::{Diagnostic, Span};
use crate::token::Token;

/// The HOL object a lowered SpecTec declaration produces.
///
/// Only the alias-to-`TypeSpec` case is implemented in this slice; the
/// enum is shaped to grow (term defining-equations, relations) without a
/// breaking signature change.
#[derive(Debug, Clone)]
pub enum Lowered {
    /// A `syntax NAME = BASE` alias, lowered to a kernel `TypeSpec`
    /// newtype over `BASE`. Carries the spec plus the fully-applied
    /// (nullary) `Type::spec(..)` leaf for convenience.
    TypeAlias { name: SmolStr, spec: TypeSpec, ty: Type },
}

/// Map a SpecTec base-type identifier to the corresponding kernel
/// [`Type`]. Only the handful of leaf types this slice supports are
/// recognised; anything else is reported as "unsupported base type".
fn base_type(name: &str) -> Option<Type> {
    Some(match name {
        "nat" => Type::nat(),
        "bool" => Type::bool(),
        "int" => Type::int(),
        "bytes" => Type::bytes(),
        "unit" => Type::unit(),
        _ => return None,
    })
}

/// Lower a single SpecTec top-level form, if it is one this slice
/// handles. Returns `Ok(None)` for forms that are out of scope (so a
/// caller can fold over a whole file, lowering what it can), and
/// `Err(..)` for a form that *is* in scope but malformed.
pub fn lower_top(top: &Top) -> Result<Option<Lowered>, Diagnostic> {
    match top {
        Top::Syntax(decl) => lower_syntax(decl).map(Some),
        // Out of scope for this slice (see SKELETONS.md).
        _ => Ok(None),
    }
}

/// Lower a `syntax` declaration. Only the single-ident *alias* shape is
/// supported; variant / record / parametric / forward-declaration bodies
/// are rejected with a diagnostic.
pub fn lower_syntax(decl: &SyntaxDecl) -> Result<Lowered, Diagnostic> {
    if !decl.params.is_empty() {
        return Err(Diagnostic::error(
            decl.span,
            "lower: parametric `syntax` declarations are not yet supported",
        ));
    }

    let Some(body) = &decl.body else {
        return Err(Diagnostic::error(
            decl.span,
            "lower: forward-declared `syntax` (no body) cannot be lowered",
        ));
    };

    let SyntaxBody::Alias(run) = body else {
        return Err(Diagnostic::error(
            decl.span,
            "lower: only single-ident `syntax NAME = BASE` aliases are supported in this slice",
        ));
    };

    // The alias body must be exactly one identifier token naming a base
    // type. (Iter postfixes, applications, etc. are out of scope.)
    let base_span = run.span;
    let base_ident = single_ident(&run.tokens, base_span)?;

    let Some(base) = base_type(&base_ident) else {
        return Err(Diagnostic::error(
            base_span,
            format!("lower: unsupported base type `{base_ident}` in `syntax` alias"),
        ));
    };

    let name = SmolStr::new(&decl.name.text);
    let spec = TypeSpec::newtype(name.clone(), base);
    let ty = Type::spec(spec.clone(), Vec::new());
    Ok(Lowered::TypeAlias { name, spec, ty })
}

/// Extract the text of a token run that must be exactly one identifier.
fn single_ident(tokens: &[crate::token::Spanned], span: Span) -> Result<String, Diagnostic> {
    match tokens {
        [only] => match &only.token {
            Token::Ident(s) => Ok(s.clone()),
            other => Err(Diagnostic::error(
                only.span,
                format!(
                    "lower: expected a base-type identifier, found `{}`",
                    other.to_source_text()
                ),
            )),
        },
        [] => Err(Diagnostic::error(span, "lower: empty alias body")),
        _ => Err(Diagnostic::error(
            span,
            "lower: alias body must be a single identifier in this slice",
        )),
    }
}
