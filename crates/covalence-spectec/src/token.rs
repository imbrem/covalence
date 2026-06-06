//! SpecTec token types.
//!
//! Tokens are produced by [`crate::lex`] from raw source bytes and are
//! the input to [`crate::parse`]. Whitespace and line comments are
//! consumed by the lexer and never appear here.

use crate::source::Span;

/// A token paired with its source span.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Spanned {
    pub token: Token,
    pub span: Span,
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
    Hint,
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
    /// `:=` (rare)
    Assign,
}

impl Token {
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
            "hint" => Token::Hint,
            "if" => Token::If,
            "let" => Token::Let,
            "else" => Token::Else,
            "otherwise" => Token::Otherwise,
            "eps" => Token::Eps,
            _ => return None,
        })
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
            Token::Hint => "`hint`",
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
        }
    }
}
