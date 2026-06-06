//! SpecTec concrete syntax tree.
//!
//! The CST is the parser's output: structured enough to walk, faithful
//! to source. No mixfix resolution, no semantic elaboration. Hint bodies
//! and rule-body expressions that depend on mixfix tables are stored as
//! opaque token spans (`TokenRun`) until Phase 2.
//!
//! Phase 1 covers `Top::Syntax` and `Top::DefSig`/`Top::DefClause`.
//! `Top::Other` is the placeholder for forms we tokenise but don't yet
//! parse.

use crate::source::Span;
use crate::token::Spanned;

/// One top-level item in a `.spectec` file.
#[derive(Clone, Debug)]
pub enum Top {
    /// `syntax NAME[/profile][(params)] [hints*] = ALTERNATIVES`
    /// or `syntax NAME[/profile][(params)]` (forward declaration).
    Syntax(SyntaxDecl),
    /// `def $NAME(params) : ret_ty [hints*]`
    DefSig(DefSig),
    /// `def $NAME(pattern_args) = rhs [-- premise]*`
    DefClause(DefClause),
    /// A top-level form that Phase 1 doesn't structurally parse. Stored
    /// as the raw token run so the file still round-trips. Phase 1's
    /// lexer-only tests can still verify this case.
    Other(TokenRun),
}

impl Top {
    pub fn span(&self) -> Span {
        match self {
            Top::Syntax(s) => s.span,
            Top::DefSig(d) => d.span,
            Top::DefClause(d) => d.span,
            Top::Other(t) => t.span,
        }
    }
}

/// `syntax` declaration.
#[derive(Clone, Debug)]
pub struct SyntaxDecl {
    pub span: Span,
    pub name: Ident,
    /// `Some("syn")` for `syntax foo/syn`, `Some("sem")` for
    /// `syntax foo/sem`, `None` otherwise.
    pub profile: Option<Ident>,
    /// Type parameters from `syntax foo(N)` / `syntax list(syntax X)`.
    /// Stored as raw runs in Phase 1.
    pub params: Vec<TokenRun>,
    pub hints: Vec<HintAtom>,
    /// `None` for forward declarations like
    /// `syntax rectype hint(desc "recursive type")  ;; forward decl`.
    pub body: Option<SyntaxBody>,
}

/// Body of a `syntax` declaration.
#[derive(Clone, Debug)]
pub enum SyntaxBody {
    /// `| ALT_1 | ALT_2 | ...` — variant type. Each alternative is the
    /// raw token run between `|` separators (or after `=` for the first).
    /// Phase 2 will further structure this.
    Variant(Vec<Alt>),
    /// `{ FIELD_NAME field_type, ... }` — record type.
    Record(Vec<RecordField>),
    /// A single non-variant body — alias or grammar-shaped. Stored as
    /// the raw run between `=` and the next top-level form.
    Alias(TokenRun),
}

/// One alternative of a variant `syntax` body, including any per-alternative
/// hints attached via `hint(...)` after the form.
#[derive(Clone, Debug)]
pub struct Alt {
    pub span: Span,
    pub body: TokenRun,
    pub hints: Vec<HintAtom>,
}

/// One field of a record `syntax` body.
#[derive(Clone, Debug)]
pub struct RecordField {
    pub span: Span,
    pub name: Ident,
    pub ty: TokenRun,
    pub hints: Vec<HintAtom>,
}

/// `def` signature: `def $NAME(arg_tys) : ret_ty`.
#[derive(Clone, Debug)]
pub struct DefSig {
    pub span: Span,
    pub name: Ident,
    /// Raw runs for the argument-type list (between the outer `(` and `)`,
    /// split on top-level commas).
    pub arg_tys: Vec<TokenRun>,
    pub ret_ty: TokenRun,
    pub hints: Vec<HintAtom>,
}

/// `def` clause: `def $NAME(patterns) = rhs -- premise*`.
#[derive(Clone, Debug)]
pub struct DefClause {
    pub span: Span,
    pub name: Ident,
    pub arg_pats: Vec<TokenRun>,
    pub rhs: TokenRun,
    pub premises: Vec<TokenRun>,
}

/// A `hint(...)` attached to a top-level form, alternative, or field. The
/// body is kept opaque in Phase 1.
#[derive(Clone, Debug)]
pub struct HintAtom {
    pub span: Span,
    pub body: TokenRun,
}

/// An identifier together with its source span.
#[derive(Clone, Debug)]
pub struct Ident {
    pub span: Span,
    pub text: String,
}

/// A contiguous run of tokens, kept verbatim. The Phase 2 elaborator
/// will re-parse these against the mixfix operator table.
#[derive(Clone, Debug)]
pub struct TokenRun {
    pub span: Span,
    pub tokens: Vec<Spanned>,
}

impl TokenRun {
    pub fn empty(span: Span) -> Self {
        Self {
            span,
            tokens: Vec::new(),
        }
    }
}
