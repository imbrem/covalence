//! SpecTec token types.
//!
//! Tokens are produced by [`crate::lex`] from raw source bytes and are
//! the input to [`crate::parse`]. Whitespace and line comments are
//! consumed by the lexer and never appear here.

use std::ops::Deref;

use crate::source::Span;

/// A token paired with its source span.
///
/// `Spanned` derefs to `Token` so token-classification methods
/// (`is_iter_postfix`, `as_ident`, …) can be called directly on a
/// `Spanned` value or reference: `s.as_ident()` works thanks to auto-deref,
/// instead of `s.token.as_ident()`. Pattern matching still uses
/// `Spanned { token: ..., .. }` since deref doesn't apply in patterns.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Spanned {
    pub token: Token,
    pub span: Span,
}

impl Deref for Spanned {
    type Target = Token;
    fn deref(&self) -> &Token {
        &self.token
    }
}

/// Iterate over `(index, &Spanned)` pairs of tokens at paren-depth 0
/// in `toks`. Used by walkers that need to split / find at the
/// "current scope" without descending into nested brackets — e.g.
/// `e1 ; e2` should split on the `;` at depth 0, not one inside
/// `(a ; b)`.
///
/// Tracks `( [ {` and `) ] }` uniformly. A token's `bracket_delta`
/// is applied AFTER deciding whether to yield it, so the opening
/// `(` itself is yielded at depth 0, the contents are skipped, and
/// the matching `)` is yielded at depth 0 again. This matches what
/// almost every walker wants.
pub fn at_top_level(toks: &[Spanned]) -> impl Iterator<Item = (usize, &Spanned)> {
    let mut depth: i32 = 0;
    toks.iter().enumerate().filter_map(move |(i, t)| {
        let here = depth == 0;
        depth += t.bracket_delta();
        here.then_some((i, t))
    })
}

/// SpecTec lexical token.
///
/// The set covers everything the upstream OCaml lexer produces. Some
/// rare or judgement-body-only forms are tokenised faithfully even though
/// the Phase 1 parser does not consume them (`Turnstile`, `Subtype`, etc.).
#[derive(Clone, Eq, PartialEq, Debug)]
pub enum Token {
    // ---- literals ----
    /// Identifier: letters, digits, underscores, primes. First character
    /// is a letter or underscore. Subscripts (e.g. `t_1`) and primes
    /// (e.g. `C'`, `C''`) are kept as part of the identifier text.
    Ident(String),
    /// Natural-number literal. Decimal or hexadecimal in source.
    /// Stored as an arbitrary-precision [`covalence_types::Nat`] —
    /// SpecTec source literals are not bounded by any machine type.
    /// The `spectec_ast` dump format clamps to `u64` downstream; we
    /// preserve precision through elaboration and clamp only at the
    /// converter boundary in [`crate::ast_doc`].
    Nat(covalence_types::Nat),
    /// Text literal: `"..."` with simple escape handling (`\n`, `\t`,
    /// `\\`, `\"`).
    Text(String),

    // ---- keywords ----
    /// `syntax`
    Syntax,
    /// `def`
    Def,
    /// `relation`
    Relation,
    /// `rule`
    Rule,
    /// `var`
    Var,
    /// `grammar`
    Grammar,
    /// `hint`
    BinderHint,
    /// `if`
    If,
    /// `let`
    Let,
    /// `else`
    Else,
    /// `otherwise`
    Otherwise,
    /// `eps` — the empty sequence
    Eps,

    // ---- brackets ----
    /// `(`
    LParen,
    /// `)`
    RParen,
    /// `[`
    LBracket,
    /// `]`
    RBracket,
    /// `{`
    LBrace,
    /// `}`
    RBrace,

    // ---- one-character punctuation ----
    /// `|`
    Pipe,
    /// `,`
    Comma,
    /// `.`
    Dot,
    /// `:`
    Colon,
    /// `;` (one)
    Semi,
    /// `=`
    Eq,
    /// `*`
    Star,
    /// `+`
    Plus,
    /// `?`
    Question,
    /// `^`
    Caret,
    /// `$`
    Dollar,
    /// `` ` ``
    Backtick,
    /// `-` (alone; the premise marker `--` is its own token below)
    Minus,
    /// `<`
    LessThan,
    /// `>`
    GreaterThan,
    /// `%`
    Percent,
    /// `/`
    Slash,
    /// `\`
    Backslash,
    /// `#` (appears in `show` and `macro` hints)
    Hash,
    /// `~` (logical negation, e.g. `~(w <- w'*)`)
    Tilde,
    /// `!` (appears in `show` hints, e.g. `hint(show !%)`)
    Bang,

    // ---- multi-character punctuation ----
    /// `--` (premise separator)
    DashDash,
    /// `...` (extension placeholder)
    DotDotDot,
    /// `->`
    Arrow,
    /// `|-` (turnstile)
    Turnstile,
    /// `<:` (subtype)
    Subtype,
    /// `~>`
    Step,
    /// `~>*`
    StepStar,
    /// `~~` (type expansion)
    Approx,
    /// `=/=`
    NotEq,
    /// `<=`
    LessEq,
    /// `>=`
    GreaterEq,
    /// `/\` (logical and)
    LogAnd,
    /// `\/` (logical or)
    LogOr,
    /// `++` (list concatenation)
    PlusPlus,
    /// `:=` (rare; appears in `show` hints)
    Assign,
    /// `=++` — path-extend operator: `e[path =++ e']` appends `e'`
    /// (a list) to the existing list at `path` inside `e`.
    EqPlusPlus,
    /// `=..` — path-extend operator variant: `e[path =.. e']`. Does
    /// not appear in wasm-3.0 corpus but recognised for completeness
    /// against the upstream OCaml lexer.
    EqDotDot,
}

impl Token {
    // -------- classification helpers --------
    //
    // These avoid the open-coded `matches!(t, Token::A | Token::B | ...)`
    // pattern that appears 50+ times across `parse`, `elab`, and
    // `ast_doc`. Naming is `is_X` for predicates and `as_X` for
    // accessors that pull the underlying value out.

    /// True for the three postfix iteration operators: `*`, `?`, `+`.
    pub fn is_iter_postfix(&self) -> bool {
        matches!(self, Token::Star | Token::Question | Token::Plus)
    }

    /// True for `(`, `[`, `{`.
    pub fn is_open_bracket(&self) -> bool {
        matches!(self, Token::LParen | Token::LBracket | Token::LBrace)
    }

    /// True for `)`, `]`, `}`.
    pub fn is_close_bracket(&self) -> bool {
        matches!(self, Token::RParen | Token::RBracket | Token::RBrace)
    }

    /// Depth-change for parenthesis tracking: `+1` for any open bracket,
    /// `-1` for any close bracket, `0` otherwise. Use to walk a token
    /// stream while maintaining bracket depth without three `match` arms.
    pub fn bracket_delta(&self) -> i32 {
        if self.is_open_bracket() {
            1
        } else if self.is_close_bracket() {
            -1
        } else {
            0
        }
    }

    /// `Some(name)` if this is `Token::Ident(name)`, else `None`.
    pub fn as_ident(&self) -> Option<&str> {
        match self {
            Token::Ident(s) => Some(s.as_str()),
            _ => None,
        }
    }

    /// `Some(n)` if this is `Token::Nat(n)`, else `None`.
    pub fn as_nat(&self) -> Option<&covalence_types::Nat> {
        match self {
            Token::Nat(n) => Some(n),
            _ => None,
        }
    }

    /// `Some(s)` if this is `Token::Text(s)`, else `None`.
    pub fn as_text(&self) -> Option<&str> {
        match self {
            Token::Text(s) => Some(s.as_str()),
            _ => None,
        }
    }

    /// True if this is `Token::Ident(_)`.
    pub fn is_ident(&self) -> bool {
        matches!(self, Token::Ident(_))
    }

    /// True if this token can stand alone as an atomic operand in an
    /// expression / grammar position (`Ident`, `Nat`, `Text`, `eps`).
    /// Used by walkers that count atoms or split on whitespace
    /// boundaries.
    pub fn is_atom(&self) -> bool {
        matches!(
            self,
            Token::Ident(_) | Token::Nat(_) | Token::Text(_) | Token::Eps,
        )
    }

    /// Static keyword lookup. Returns `Some(token)` if `s` is a SpecTec
    /// reserved word.
    pub(crate) fn keyword(s: &str) -> Option<Token> {
        Some(match s {
            "syntax" => Token::Syntax,
            "def" => Token::Def,
            "relation" => Token::Relation,
            "rule" => Token::Rule,
            "var" => Token::Var,
            "grammar" => Token::Grammar,
            "hint" => Token::BinderHint,
            "if" => Token::If,
            "let" => Token::Let,
            "else" => Token::Else,
            "otherwise" => Token::Otherwise,
            "eps" => Token::Eps,
            _ => return None,
        })
    }

    /// The source-text representation of this token, suitable for
    /// rendering inside a `MixOp` template string.
    ///
    /// Distinct from [`describe`](Self::describe), which returns a
    /// quoted diagnostic label like `` `|-` ``. This function returns
    /// the bare source characters: `|-`, `<=`, `~>`, `*`, etc.
    ///
    /// [`Token::Backtick`] returns an empty string because the OCaml
    /// SpecTec elaborator strips backticks from MixOp display
    /// (`` ` `` is a source-only escape that's invisible at AST
    /// rendering time).
    pub fn to_source_text(&self) -> String {
        match self {
            Token::Ident(s) => s.clone(),
            Token::Nat(n) => n.to_string(),
            Token::Text(s) => format!("\"{}\"", s),
            Token::Syntax => "syntax".into(),
            Token::Def => "def".into(),
            Token::Relation => "relation".into(),
            Token::Rule => "rule".into(),
            Token::Var => "var".into(),
            Token::Grammar => "grammar".into(),
            Token::BinderHint => "hint".into(),
            Token::If => "if".into(),
            Token::Let => "let".into(),
            Token::Else => "else".into(),
            Token::Otherwise => "otherwise".into(),
            Token::Eps => "eps".into(),
            Token::LParen => "(".into(),
            Token::RParen => ")".into(),
            Token::LBracket => "[".into(),
            Token::RBracket => "]".into(),
            Token::LBrace => "{".into(),
            Token::RBrace => "}".into(),
            Token::Pipe => "|".into(),
            Token::Comma => ",".into(),
            Token::Dot => ".".into(),
            Token::Colon => ":".into(),
            Token::Semi => ";".into(),
            Token::Eq => "=".into(),
            Token::Star => "*".into(),
            Token::Plus => "+".into(),
            Token::Question => "?".into(),
            Token::Caret => "^".into(),
            Token::Dollar => "$".into(),
            // Backticks are display-only escapes — invisible in MixOp.
            Token::Backtick => String::new(),
            Token::Minus => "-".into(),
            Token::LessThan => "<".into(),
            Token::GreaterThan => ">".into(),
            Token::Percent => "%".into(),
            Token::Slash => "/".into(),
            Token::Backslash => "\\".into(),
            Token::Hash => "#".into(),
            Token::Tilde => "~".into(),
            Token::Bang => "!".into(),
            Token::DashDash => "--".into(),
            Token::DotDotDot => "...".into(),
            Token::Arrow => "->".into(),
            Token::Turnstile => "|-".into(),
            Token::Subtype => "<:".into(),
            Token::Step => "~>".into(),
            Token::StepStar => "~>*".into(),
            Token::Approx => "~~".into(),
            Token::NotEq => "=/=".into(),
            Token::LessEq => "<=".into(),
            Token::GreaterEq => ">=".into(),
            Token::LogAnd => "/\\".into(),
            Token::LogOr => "\\/".into(),
            Token::PlusPlus => "++".into(),
            Token::Assign => ":=".into(),
            Token::EqPlusPlus => "=++".into(),
            Token::EqDotDot => "=..".into(),
        }
    }

    /// Short human-readable name used in diagnostic messages.
    pub fn describe(&self) -> &'static str {
        match self {
            Token::Ident(_) => "identifier",
            Token::Nat(_) => "natural-number literal",
            Token::Text(_) => "text literal",
            Token::Syntax => "`syntax`",
            Token::Def => "`def`",
            Token::Relation => "`relation`",
            Token::Rule => "`rule`",
            Token::Var => "`var`",
            Token::Grammar => "`grammar`",
            Token::BinderHint => "`hint`",
            Token::If => "`if`",
            Token::Let => "`let`",
            Token::Else => "`else`",
            Token::Otherwise => "`otherwise`",
            Token::Eps => "`eps`",
            Token::LParen => "`(`",
            Token::RParen => "`)`",
            Token::LBracket => "`[`",
            Token::RBracket => "`]`",
            Token::LBrace => "`{`",
            Token::RBrace => "`}`",
            Token::Pipe => "`|`",
            Token::Comma => "`,`",
            Token::Dot => "`.`",
            Token::Colon => "`:`",
            Token::Semi => "`;`",
            Token::Eq => "`=`",
            Token::Star => "`*`",
            Token::Plus => "`+`",
            Token::Question => "`?`",
            Token::Caret => "`^`",
            Token::Dollar => "`$`",
            Token::Backtick => "`` ` ``",
            Token::Minus => "`-`",
            Token::LessThan => "`<`",
            Token::GreaterThan => "`>`",
            Token::Percent => "`%`",
            Token::Slash => "`/`",
            Token::Backslash => "`\\`",
            Token::Hash => "`#`",
            Token::Tilde => "`~`",
            Token::Bang => "`!`",
            Token::DashDash => "`--`",
            Token::DotDotDot => "`...`",
            Token::Arrow => "`->`",
            Token::Turnstile => "`|-`",
            Token::Subtype => "`<:`",
            Token::Step => "`~>`",
            Token::StepStar => "`~>*`",
            Token::Approx => "`~~`",
            Token::NotEq => "`=/=`",
            Token::LessEq => "`<=`",
            Token::GreaterEq => "`>=`",
            Token::LogAnd => "`/\\`",
            Token::LogOr => "`\\/`",
            Token::PlusPlus => "`++`",
            Token::Assign => "`:=`",
            Token::EqPlusPlus => "`=++`",
            Token::EqDotDot => "`=..`",
        }
    }
}
