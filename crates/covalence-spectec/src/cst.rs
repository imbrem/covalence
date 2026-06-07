//! SpecTec concrete syntax tree.
//!
//! The CST is the parser's output: structured enough to walk, faithful
//! to source. No mixfix resolution, no semantic elaboration. BinderHint
//! bodies, rule body expressions, and any context-dependent
//! interpretation are stored as opaque [`TokenRun`]s and resolved by
//! [`crate::elab`] using the relation/syntax-derived `OpTable`.
//!
//! All seven top-level forms have structural CST nodes:
//! [`Top::Syntax`], [`Top::DefSig`], [`Top::DefClause`], [`Top::Var`],
//! [`Top::Relation`], [`Top::Rule`], [`Top::Grammar`]. The
//! [`Top::Other`] variant is kept as a safety hatch; the parse-corpus
//! test asserts it stays empty on all WebAssembly 3.0 spec files.

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
    /// `var NAME : type [hints*]`
    Var(VarDecl),
    /// `relation NAME: <mixfix-template> [hints*]`
    Relation(RelationDecl),
    /// `rule NAME[/case]: <conclusion> [-- premise]* [hints*]`
    Rule(RuleDecl),
    /// `grammar NAME[/case][(params)] : ret [hints*] = <productions>`
    Grammar(GrammarDecl),
    /// Top-level form not yet recognised by Phase 1/2a. Kept as a safety
    /// hatch; the corpus test asserts this is empty.
    Other(TokenRun),
}

impl Top {
    pub fn span(&self) -> Span {
        match self {
            Top::Syntax(s) => s.span,
            Top::DefSig(d) => d.span,
            Top::DefClause(d) => d.span,
            Top::Var(v) => v.span,
            Top::Relation(r) => r.span,
            Top::Rule(r) => r.span,
            Top::Grammar(g) => g.span,
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
    /// `{ FIELD_NAME field_type, ... }` — record type. Slots in
    /// source order; `...` between commas produces `RecordSlot::Placeholder`
    /// so profile merging (`X/syn` + `X/sem`) can splice the other
    /// profile's fields at the placeholder position.
    Record(Vec<RecordSlot>),
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

/// One slot in a record body — either a real field or a `...`
/// placeholder for cross-profile splicing.
#[derive(Clone, Debug)]
pub enum RecordSlot {
    Real(RecordField),
    Placeholder,
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

/// `var NAME : type [hints*]` — declares a metavariable family.
#[derive(Clone, Debug)]
pub struct VarDecl {
    pub span: Span,
    pub name: Ident,
    pub ty: TokenRun,
    pub hints: Vec<HintAtom>,
}

/// `relation NAME: <mixfix-template> [hints*]` — declares an inductive
/// relation. The mixfix template (everything between `:` and the hints)
/// is kept as a raw `TokenRun`; Phase 2b/c elaborates it.
#[derive(Clone, Debug)]
pub struct RelationDecl {
    pub span: Span,
    pub name: Ident,
    pub template: TokenRun,
    pub hints: Vec<HintAtom>,
}

/// `rule NAME[/case]: <conclusion> [-- premise]* [hints*]` — one
/// inference rule of an inductive relation. Body kept opaque.
#[derive(Clone, Debug)]
pub struct RuleDecl {
    pub span: Span,
    pub name: Ident,
    /// `Some("refl")` for `rule Heaptype_sub/refl`, etc. Cases may
    /// themselves carry slashes (`rule Foo/bar/baz`); they're stored as
    /// the joined slash-separated text.
    pub case: Option<Ident>,
    pub conclusion: TokenRun,
    pub premises: Vec<TokenRun>,
    pub hints: Vec<HintAtom>,
}

/// `grammar NAME[/case][(params)] : ret [hints*] = <productions>` —
/// a binary or text format production rule.
#[derive(Clone, Debug)]
pub struct GrammarDecl {
    pub span: Span,
    pub name: Ident,
    pub case: Option<Ident>,
    pub params: Vec<TokenRun>,
    pub ret: TokenRun,
    pub hints: Vec<HintAtom>,
    /// `None` for forward declarations (no `= ...`).
    pub productions: Option<TokenRun>,
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
