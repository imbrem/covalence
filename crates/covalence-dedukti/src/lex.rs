//! The `.dk` lexer: source bytes → a flat token stream with byte spans.
//!
//! Dedukti's lexical grammar is small. Whitespace and `(; … ;)` comments
//! (nestable) separate tokens. Identifiers are `[a-zA-Z_][a-zA-Z0-9_!?']*` or
//! the `{| … |}` quoted form (which may contain any characters, used by
//! translators to carry source-language names verbatim). A `module.name`
//! qualified identifier lexes as a single [`Tok::Qid`]. The operator/punctuation
//! tokens are `:` `:=` `->` `=>` `-->` `==` `,` `.` `(` `)` `[` `]` `{` `}`, and
//! `#WORD` directives. Keywords are `Type`, `def`, `thm`, `injective`, `defac`,
//! `defacu`.

use crate::error::DkError;
use smol_str::SmolStr;

/// A lexical token.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Tok {
    /// The sort keyword `Type`.
    Type,
    /// The `def` keyword.
    Def,
    /// The `thm` keyword.
    Thm,
    /// The `injective` keyword.
    Inj,
    /// The `defac` keyword.
    DefAc,
    /// The `defacu` keyword.
    DefAcU,
    /// A plain (unqualified) identifier.
    Ident(SmolStr),
    /// A `module.name` qualified identifier.
    Qid(SmolStr, SmolStr),
    /// A `#WORD` directive head (the `WORD`, uppercased as written).
    Command(SmolStr),
    /// A `"…"` string literal (decoded: `\"` and `\\` unescaped).
    Str(String),
    /// `:`
    Colon,
    /// `:=`
    Assign,
    /// `,`
    Comma,
    /// `.`
    Dot,
    /// `->`
    Arrow,
    /// `=>`
    FatArrow,
    /// `-->`
    LongArrow,
    /// `==`
    Equal,
    /// `(`
    LParen,
    /// `)`
    RParen,
    /// `[`
    LSquare,
    /// `]`
    RSquare,
    /// `{`
    LBrace,
    /// `}`
    RBrace,
}

impl Tok {
    /// A short human-readable description for error messages.
    pub fn describe(&self) -> String {
        match self {
            Tok::Type => "`Type`".into(),
            Tok::Def => "`def`".into(),
            Tok::Thm => "`thm`".into(),
            Tok::Inj => "`injective`".into(),
            Tok::DefAc => "`defac`".into(),
            Tok::DefAcU => "`defacu`".into(),
            Tok::Ident(s) => format!("identifier `{s}`"),
            Tok::Qid(m, n) => format!("identifier `{m}.{n}`"),
            Tok::Command(s) => format!("`#{s}`"),
            Tok::Str(_) => "string literal".into(),
            Tok::Colon => "`:`".into(),
            Tok::Assign => "`:=`".into(),
            Tok::Comma => "`,`".into(),
            Tok::Dot => "`.`".into(),
            Tok::Arrow => "`->`".into(),
            Tok::FatArrow => "`=>`".into(),
            Tok::LongArrow => "`-->`".into(),
            Tok::Equal => "`==`".into(),
            Tok::LParen => "`(`".into(),
            Tok::RParen => "`)`".into(),
            Tok::LSquare => "`[`".into(),
            Tok::RSquare => "`]`".into(),
            Tok::LBrace => "`{`".into(),
            Tok::RBrace => "`}`".into(),
        }
    }
}

/// A token together with its byte span `[start, end)` in the source.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Spanned {
    /// The token.
    pub tok: Tok,
    /// Inclusive start byte offset.
    pub start: usize,
    /// Exclusive end byte offset.
    pub end: usize,
}

/// True if `b` may start an identifier. Dedukti identifiers may begin with a
/// digit (the object language has no numeric literals, so e.g. `def 1 := …`
/// names a symbol `1`); digit-led runs are therefore identifiers, not numbers.
fn is_ident_start(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_'
}

/// True if `b` may continue an identifier.
fn is_ident_cont(b: u8) -> bool {
    b.is_ascii_alphanumeric() || matches!(b, b'_' | b'!' | b'?' | b'\'')
}

/// Tokenise an entire `.dk` source.
pub fn lex(src: &str) -> Result<Vec<Spanned>, DkError> {
    let b = src.as_bytes();
    let n = b.len();
    let mut i = 0usize;
    let mut out = Vec::new();

    while i < n {
        let c = b[i];

        // Whitespace.
        if c.is_ascii_whitespace() {
            i += 1;
            continue;
        }

        // Comments `(; … ;)`, nestable.
        if c == b'(' && i + 1 < n && b[i + 1] == b';' {
            i = skip_comment(b, i)?;
            continue;
        }

        let start = i;

        // Quoted identifier `{| … |}` (vs. the `{` brace token).
        if c == b'{' && i + 1 < n && b[i + 1] == b'|' {
            let (name, j) = read_quoted_ident(src, b, i)?;
            i = j;
            i = finish_ident(src, b, i, name, &mut out, start);
            continue;
        }

        // Plain identifiers and keywords (possibly module-qualified).
        if is_ident_start(c) {
            let mut j = i + 1;
            while j < n && is_ident_cont(b[j]) {
                j += 1;
            }
            let name = SmolStr::new(&src[i..j]);
            i = j;
            i = finish_ident(src, b, i, name, &mut out, start);
            continue;
        }

        // Operators / punctuation.
        let (tok, len) = match c {
            b'(' => (Tok::LParen, 1),
            b')' => (Tok::RParen, 1),
            b'[' => (Tok::LSquare, 1),
            b']' => (Tok::RSquare, 1),
            b'{' => (Tok::LBrace, 1),
            b'}' => (Tok::RBrace, 1),
            b',' => (Tok::Comma, 1),
            b'.' => (Tok::Dot, 1),
            b':' if i + 1 < n && b[i + 1] == b'=' => (Tok::Assign, 2),
            b':' => (Tok::Colon, 1),
            b'-' if i + 2 < n && b[i + 1] == b'-' && b[i + 2] == b'>' => (Tok::LongArrow, 3),
            b'-' if i + 1 < n && b[i + 1] == b'>' => (Tok::Arrow, 2),
            b'=' if i + 1 < n && b[i + 1] == b'>' => (Tok::FatArrow, 2),
            b'=' if i + 1 < n && b[i + 1] == b'=' => (Tok::Equal, 2),
            b'#' => {
                let mut j = i + 1;
                while j < n && b[j].is_ascii_alphabetic() {
                    j += 1;
                }
                if j == i + 1 {
                    return Err(DkError::Lex {
                        pos: i,
                        message: "`#` must be followed by a directive name".into(),
                    });
                }
                let name = SmolStr::new(&src[i + 1..j]);
                out.push(Spanned { tok: Tok::Command(name), start, end: j });
                i = j;
                continue;
            }
            b'"' => {
                let (s, j) = read_string(src, b, i)?;
                out.push(Spanned { tok: Tok::Str(s), start, end: j });
                i = j;
                continue;
            }
            other => {
                return Err(DkError::Lex {
                    pos: i,
                    message: format!("unexpected character `{}`", other as char),
                });
            }
        };
        out.push(Spanned { tok, start, end: start + len });
        i += len;
    }

    Ok(out)
}

/// Having read an identifier `name` ending at `i`, look for a `.second`
/// qualifier and emit either a [`Tok::Qid`], a keyword token, or [`Tok::Ident`].
/// Returns the new cursor.
fn finish_ident(
    src: &str,
    b: &[u8],
    mut i: usize,
    name: SmolStr,
    out: &mut Vec<Spanned>,
    start: usize,
) -> usize {
    let n = b.len();
    // Module qualification: `name.second`, where `.` is immediately followed by
    // an identifier start or a `{|` quoted identifier (otherwise the `.` is a
    // statement terminator).
    if i < n && b[i] == b'.' && i + 1 < n && (is_ident_start(b[i + 1]) || (b[i + 1] == b'{' && i + 2 < n && b[i + 2] == b'|')) {
        i += 1; // consume `.`
        let second_start = i;
        let (second, j) = if b[i] == b'{' {
            // A quoted second component cannot fail here (we peeked `{|`).
            read_quoted_ident(src, b, i).expect("checked `{|`")
        } else {
            let mut j = i + 1;
            while j < n && is_ident_cont(b[j]) {
                j += 1;
            }
            (SmolStr::new(&src[second_start..j]), j)
        };
        out.push(Spanned { tok: Tok::Qid(name, second), start, end: j });
        return j;
    }

    let tok = match name.as_str() {
        "Type" => Tok::Type,
        "def" => Tok::Def,
        "thm" => Tok::Thm,
        "injective" => Tok::Inj,
        "defac" => Tok::DefAc,
        "defacu" => Tok::DefAcU,
        _ => Tok::Ident(name),
    };
    out.push(Spanned { tok, start, end: i });
    i
}

/// Skip a nestable `(; … ;)` comment starting at `i` (which points at `(`).
/// Returns the cursor just past the matching `;)`.
fn skip_comment(b: &[u8], i: usize) -> Result<usize, DkError> {
    let n = b.len();
    let mut depth = 0usize;
    let mut k = i;
    while k + 1 < n {
        if b[k] == b'(' && b[k + 1] == b';' {
            depth += 1;
            k += 2;
        } else if b[k] == b';' && b[k + 1] == b')' {
            depth -= 1;
            k += 2;
            if depth == 0 {
                return Ok(k);
            }
        } else {
            k += 1;
        }
    }
    Err(DkError::Lex { pos: i, message: "unterminated `(; … ;)` comment".into() })
}

/// Read a `{| … |}` quoted identifier starting at `i` (which points at `{`).
/// Returns the inner text and the cursor just past `|}`.
fn read_quoted_ident(src: &str, b: &[u8], i: usize) -> Result<(SmolStr, usize), DkError> {
    let n = b.len();
    let inner = i + 2; // past `{|`
    let mut k = inner;
    while k + 1 < n {
        if b[k] == b'|' && b[k + 1] == b'}' {
            return Ok((SmolStr::new(&src[inner..k]), k + 2));
        }
        k += 1;
    }
    Err(DkError::Lex { pos: i, message: "unterminated `{| … |}` identifier".into() })
}

/// Read a `"…"` string literal starting at `i` (which points at `"`).
/// Handles `\"` and `\\` escapes. Returns the decoded value and the cursor
/// just past the closing quote.
fn read_string(src: &str, b: &[u8], i: usize) -> Result<(String, usize), DkError> {
    let n = b.len();
    let mut k = i + 1;
    let mut s = String::new();
    while k < n {
        match b[k] {
            b'"' => return Ok((s, k + 1)),
            b'\\' if k + 1 < n => {
                match b[k + 1] {
                    b'"' => s.push('"'),
                    b'\\' => s.push('\\'),
                    b'n' => s.push('\n'),
                    b't' => s.push('\t'),
                    other => {
                        s.push('\\');
                        s.push(other as char);
                    }
                }
                k += 2;
            }
            _ => {
                // Copy one UTF-8 scalar (string literals may carry non-ASCII).
                let ch = src[k..].chars().next().unwrap();
                s.push(ch);
                k += ch.len_utf8();
            }
        }
    }
    Err(DkError::Lex { pos: i, message: "unterminated string literal".into() })
}
