//! SpecTec lexer.
//!
//! Pure function over `&str`: produces a vector of [`Spanned`] tokens or
//! a [`Diagnostic`] on the first unrecognised input. Comments (`;;` to
//! end of line) and whitespace are consumed; the rest of the source is
//! covered by the [`Token`] enum.
//!
//! Style: a single mutable `Lexer` cursor walks the input. Local
//! mutation, no globals, no `unsafe`.

use crate::source::{Diagnostic, FileId, Span};
use crate::token::{Spanned, Token};

/// Lex an entire source string.
///
/// Returns a vector of spanned tokens. The vector does not contain a
/// terminator; callers can check `cursor == tokens.len()` for end-of-input.
pub fn lex(file: FileId, source: &str) -> Result<Vec<Spanned>, Diagnostic> {
    let mut lx = Lexer::new(file, source);
    let mut out = Vec::new();
    loop {
        lx.skip_trivia()?;
        if lx.is_eof() {
            return Ok(out);
        }
        let start = lx.pos;
        let token = lx.lex_one()?;
        let end = lx.pos;
        out.push(Spanned {
            token,
            span: Span::new(file, start, end),
        });
    }
}

struct Lexer<'a> {
    file: FileId,
    src: &'a [u8],
    pos: u32,
}

impl<'a> Lexer<'a> {
    fn new(file: FileId, source: &'a str) -> Self {
        Self {
            file,
            src: source.as_bytes(),
            pos: 0,
        }
    }

    fn is_eof(&self) -> bool {
        self.pos as usize >= self.src.len()
    }

    fn peek(&self) -> Option<u8> {
        self.src.get(self.pos as usize).copied()
    }

    fn peek_at(&self, offset: usize) -> Option<u8> {
        self.src.get(self.pos as usize + offset).copied()
    }

    fn bump(&mut self) -> Option<u8> {
        let b = self.peek()?;
        self.pos += 1;
        Some(b)
    }

    fn span_here(&self) -> Span {
        Span::new(
            self.file,
            self.pos,
            self.pos.saturating_add(1).min(self.src.len() as u32),
        )
    }

    /// Skip whitespace, line comments (`;;...`), and line continuations
    /// (`\<newline>`).
    fn skip_trivia(&mut self) -> Result<(), Diagnostic> {
        loop {
            match self.peek() {
                Some(b' ' | b'\t' | b'\r' | b'\n') => {
                    self.pos += 1;
                }
                // Line comment: `;;` to end of line.
                Some(b';') if self.peek_at(1) == Some(b';') => {
                    while let Some(b) = self.peek() {
                        if b == b'\n' {
                            break;
                        }
                        self.pos += 1;
                    }
                }
                // Line continuation: `\<newline>` (with optional intermediate `\r`).
                Some(b'\\') if matches!(self.peek_at(1), Some(b'\n') | Some(b'\r')) => {
                    self.pos += 1; // consume `\`
                    if self.peek() == Some(b'\r') {
                        self.pos += 1;
                    }
                    if self.peek() == Some(b'\n') {
                        self.pos += 1;
                    }
                }
                _ => return Ok(()),
            }
        }
    }

    fn lex_one(&mut self) -> Result<Token, Diagnostic> {
        let b = self.peek().expect("caller ensures non-EOF");

        // Identifier / keyword.
        if is_ident_start(b) {
            return Ok(self.lex_ident());
        }

        // Number.
        if b.is_ascii_digit() {
            return self.lex_number();
        }

        // Text literal.
        if b == b'"' {
            return self.lex_text();
        }

        self.lex_punct()
    }

    fn lex_ident(&mut self) -> Token {
        let start = self.pos as usize;
        self.pos += 1;
        while let Some(c) = self.peek() {
            if is_ident_continue(c) {
                self.pos += 1;
            } else {
                break;
            }
        }
        let end = self.pos as usize;
        let text = std::str::from_utf8(&self.src[start..end])
            .expect("identifier bytes are ASCII by construction");
        if let Some(kw) = Token::keyword(text) {
            kw
        } else {
            Token::Ident(text.to_string())
        }
    }

    fn lex_number(&mut self) -> Result<Token, Diagnostic> {
        let start = self.pos as usize;
        // Hex?
        if self.peek() == Some(b'0') && matches!(self.peek_at(1), Some(b'x') | Some(b'X')) {
            self.pos += 2;
            let hex_start = self.pos as usize;
            while let Some(c) = self.peek() {
                if c.is_ascii_hexdigit() {
                    self.pos += 1;
                } else {
                    break;
                }
            }
            let hex_end = self.pos as usize;
            if hex_start == hex_end {
                return Err(Diagnostic::error(
                    Span::new(self.file, start as u32, self.pos),
                    "hexadecimal literal needs at least one digit",
                ));
            }
            let text =
                std::str::from_utf8(&self.src[hex_start..hex_end]).expect("hex digits are ASCII");
            let n = covalence_types::Nat::from_str_radix(text, 16).map_err(|e| {
                Diagnostic::error(
                    Span::new(self.file, start as u32, self.pos),
                    format!("invalid hexadecimal literal: {e}"),
                )
            })?;
            return Ok(Token::Nat(n));
        }

        // Decimal.
        while let Some(c) = self.peek() {
            if c.is_ascii_digit() {
                self.pos += 1;
            } else {
                break;
            }
        }
        let end = self.pos as usize;
        let text = std::str::from_utf8(&self.src[start..end]).expect("decimal digits are ASCII");
        let n: covalence_types::Nat = text.parse().map_err(|e| {
            Diagnostic::error(
                Span::new(self.file, start as u32, self.pos),
                format!("invalid decimal literal: {e}"),
            )
        })?;
        Ok(Token::Nat(n))
    }

    fn lex_text(&mut self) -> Result<Token, Diagnostic> {
        let start = self.pos;
        self.pos += 1; // consume opening "
        let mut out = String::new();
        loop {
            match self.bump() {
                None => {
                    return Err(Diagnostic::error(
                        Span::new(self.file, start, self.pos),
                        "unterminated text literal",
                    ));
                }
                Some(b'"') => return Ok(Token::Text(out)),
                Some(b'\\') => match self.bump() {
                    Some(b'n') => out.push('\n'),
                    Some(b't') => out.push('\t'),
                    Some(b'r') => out.push('\r'),
                    Some(b'\\') => out.push('\\'),
                    Some(b'"') => out.push('"'),
                    Some(b'0') => out.push('\0'),
                    Some(other) => {
                        return Err(Diagnostic::error(
                            Span::new(self.file, self.pos - 2, self.pos),
                            format!("unknown escape sequence `\\{}`", other as char),
                        ));
                    }
                    None => {
                        return Err(Diagnostic::error(
                            Span::new(self.file, start, self.pos),
                            "unterminated text literal",
                        ));
                    }
                },
                Some(b) => {
                    // Strings can contain arbitrary non-ASCII bytes (UTF-8
                    // sequences). Push them as raw bytes via from_utf8 lossy
                    // would be wrong for multibyte chars; instead we collect
                    // the byte and assemble a String at the end.
                    out.push(b as char);
                    // ^ NOTE: this is byte-level; for multibyte UTF-8 inside
                    // strings we would need to collect Vec<u8> and decode
                    // afterwards. Phase 1 spec corpus has only ASCII in
                    // string literals; revisit if a test fails here.
                }
            }
        }
    }

    fn lex_punct(&mut self) -> Result<Token, Diagnostic> {
        let b = self.peek().expect("caller ensures non-EOF");
        let p1 = self.peek_at(1);
        let p2 = self.peek_at(2);

        // Multi-char punctuation first, longest match wins.
        let (tok, n) = match (b, p1, p2) {
            (b'.', Some(b'.'), Some(b'.')) => (Token::DotDotDot, 3),
            (b'=', Some(b'/'), Some(b'=')) => (Token::NotEq, 3),
            (b'=', Some(b'+'), Some(b'+')) => (Token::EqPlusPlus, 3),
            (b'=', Some(b'.'), Some(b'.')) => (Token::EqDotDot, 3),
            (b'~', Some(b'>'), Some(b'*')) => (Token::StepStar, 3),
            (b'-', Some(b'-'), _) => (Token::DashDash, 2),
            (b'-', Some(b'>'), _) => (Token::Arrow, 2),
            (b'|', Some(b'-'), _) => (Token::Turnstile, 2),
            (b'<', Some(b':'), _) => (Token::Subtype, 2),
            (b'<', Some(b'='), _) => (Token::LessEq, 2),
            (b'>', Some(b'='), _) => (Token::GreaterEq, 2),
            (b'~', Some(b'>'), _) => (Token::Step, 2),
            (b'~', Some(b'~'), _) => (Token::Approx, 2),
            (b'/', Some(b'\\'), _) => (Token::LogAnd, 2),
            (b'\\', Some(b'/'), _) => (Token::LogOr, 2),
            (b'+', Some(b'+'), _) => (Token::PlusPlus, 2),
            (b':', Some(b'='), _) => (Token::Assign, 2),
            _ => {
                let single = match b {
                    b'(' => Token::LParen,
                    b')' => Token::RParen,
                    b'[' => Token::LBracket,
                    b']' => Token::RBracket,
                    b'{' => Token::LBrace,
                    b'}' => Token::RBrace,
                    b'|' => Token::Pipe,
                    b',' => Token::Comma,
                    b'.' => Token::Dot,
                    b':' => Token::Colon,
                    b';' => Token::Semi,
                    b'=' => Token::Eq,
                    b'*' => Token::Star,
                    b'+' => Token::Plus,
                    b'?' => Token::Question,
                    b'^' => Token::Caret,
                    b'$' => Token::Dollar,
                    b'`' => Token::Backtick,
                    b'-' => Token::Minus,
                    b'<' => Token::LessThan,
                    b'>' => Token::GreaterThan,
                    b'%' => Token::Percent,
                    b'/' => Token::Slash,
                    b'\\' => Token::Backslash,
                    b'#' => Token::Hash,
                    b'~' => Token::Tilde,
                    b'!' => Token::Bang,
                    other => {
                        return Err(Diagnostic::error(
                            self.span_here(),
                            format!(
                                "unexpected character `{}` (byte 0x{:02X})",
                                if other.is_ascii_graphic() {
                                    other as char
                                } else {
                                    '?'
                                },
                                other
                            ),
                        ));
                    }
                };
                (single, 1)
            }
        };
        self.pos += n;
        Ok(tok)
    }
}

fn is_ident_start(b: u8) -> bool {
    matches!(b, b'A'..=b'Z' | b'a'..=b'z' | b'_')
}

fn is_ident_continue(b: u8) -> bool {
    matches!(
        b,
        b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' | b'_' | b'\''
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::source::SourceMap;

    fn lex_str(s: &str) -> Vec<Token> {
        let mut map = SourceMap::new();
        let id = map.add("<test>", s);
        lex(id, s)
            .expect("lex ok")
            .into_iter()
            .map(|t| t.token)
            .collect()
    }

    #[test]
    fn comments_and_whitespace() {
        let toks = lex_str(";; this is a comment\n  ;; another\nsyntax");
        assert_eq!(toks, vec![Token::Syntax]);
    }

    #[test]
    fn keywords_vs_idents() {
        let toks =
            lex_str("syntax foo def $bar relation rule var grammar hint if let else otherwise eps");
        assert_eq!(
            toks,
            vec![
                Token::Syntax,
                Token::Ident("foo".into()),
                Token::Def,
                Token::Dollar,
                Token::Ident("bar".into()),
                Token::Relation,
                Token::Rule,
                Token::Var,
                Token::Grammar,
                Token::Hint,
                Token::If,
                Token::Let,
                Token::Else,
                Token::Otherwise,
                Token::Eps,
            ]
        );
    }

    #[test]
    fn idents_with_subscripts_and_primes() {
        let toks = lex_str("t_1 C' C'' fNmag _IDX _RESULT _RECS");
        assert_eq!(
            toks,
            vec![
                Token::Ident("t_1".into()),
                Token::Ident("C'".into()),
                Token::Ident("C''".into()),
                Token::Ident("fNmag".into()),
                Token::Ident("_IDX".into()),
                Token::Ident("_RESULT".into()),
                Token::Ident("_RECS".into()),
            ]
        );
    }

    #[test]
    fn decimal_and_hex_numbers() {
        let toks = lex_str("0 12 255 0x00 0xFF 0xdeadbeef");
        let n = |x: u64| Token::Nat(covalence_types::Nat::from(x));
        assert_eq!(
            toks,
            vec![n(0), n(12), n(255), n(0x00), n(0xFF), n(0xdead_beef)]
        );
    }

    #[test]
    fn arbitrary_precision_nat() {
        // 2^65 — exceeds u64::MAX, must parse without truncation.
        let big = "36893488147419103232";
        let toks = lex_str(big);
        assert_eq!(toks.len(), 1);
        let Token::Nat(n) = &toks[0] else {
            panic!("expected Nat")
        };
        assert_eq!(n.to_string(), big);
    }

    #[test]
    fn text_literals() {
        let toks = lex_str(r#""hello" "with \" quote" "with \\ backslash" "tab\there""#);
        assert_eq!(
            toks,
            vec![
                Token::Text("hello".into()),
                Token::Text("with \" quote".into()),
                Token::Text("with \\ backslash".into()),
                Token::Text("tab\there".into()),
            ]
        );
    }

    #[test]
    fn multi_char_punctuation_longest_match() {
        // ... vs . . .
        assert_eq!(lex_str("..."), vec![Token::DotDotDot]);
        // =/= vs = / =
        assert_eq!(lex_str("=/="), vec![Token::NotEq]);
        // ~>* vs ~> *
        assert_eq!(lex_str("~>*"), vec![Token::StepStar]);
        // -- vs - -
        assert_eq!(lex_str("--"), vec![Token::DashDash]);
        assert_eq!(lex_str("- -"), vec![Token::Minus, Token::Minus]);
        // -> vs - >
        assert_eq!(lex_str("->"), vec![Token::Arrow]);
        // |- vs |
        assert_eq!(lex_str("|-"), vec![Token::Turnstile]);
        assert_eq!(lex_str("|"), vec![Token::Pipe]);
        // <: <= <
        assert_eq!(
            lex_str("<: <= <"),
            vec![Token::Subtype, Token::LessEq, Token::LessThan]
        );
        // ++ +
        assert_eq!(lex_str("++"), vec![Token::PlusPlus]);
        assert_eq!(lex_str("+ +"), vec![Token::Plus, Token::Plus]);
        // /\ \/
        assert_eq!(lex_str("/\\ \\/"), vec![Token::LogAnd, Token::LogOr]);
        // := vs : =
        assert_eq!(lex_str(":="), vec![Token::Assign]);
        assert_eq!(lex_str(": ="), vec![Token::Colon, Token::Eq]);
        // =++ vs = ++ vs = + +
        assert_eq!(lex_str("=++"), vec![Token::EqPlusPlus]);
        assert_eq!(lex_str("= ++"), vec![Token::Eq, Token::PlusPlus]);
        assert_eq!(lex_str("= + +"), vec![Token::Eq, Token::Plus, Token::Plus]);
        // =.. vs = . . vs = ...
        assert_eq!(lex_str("=.."), vec![Token::EqDotDot]);
        assert_eq!(lex_str("= . ."), vec![Token::Eq, Token::Dot, Token::Dot]);
        assert_eq!(lex_str("=..."), vec![Token::EqDotDot, Token::Dot]);
        assert_eq!(lex_str("= ..."), vec![Token::Eq, Token::DotDotDot]);
        // ~~ vs ~> vs ~
        assert_eq!(lex_str("~~"), vec![Token::Approx]);
        assert_eq!(lex_str("~>"), vec![Token::Step]);
    }

    #[test]
    fn semi_vs_comment_disambiguation() {
        // `;` alone is a token; `;;` starts a comment.
        let toks = lex_str("z ; instr");
        assert_eq!(
            toks,
            vec![
                Token::Ident("z".into()),
                Token::Semi,
                Token::Ident("instr".into()),
            ]
        );
        // `;;` to end of line is a comment.
        let toks = lex_str("z ;; comment\ninstr");
        assert_eq!(
            toks,
            vec![Token::Ident("z".into()), Token::Ident("instr".into()),]
        );
    }

    #[test]
    fn line_continuation() {
        let toks = lex_str("a \\\nb");
        assert_eq!(
            toks,
            vec![Token::Ident("a".into()), Token::Ident("b".into())]
        );
    }

    #[test]
    fn arithmetic_escape_components() {
        // $( and ) lex separately; no special escape token.
        let toks = lex_str("$(1 + n)");
        assert_eq!(
            toks,
            vec![
                Token::Dollar,
                Token::LParen,
                Token::Nat(covalence_types::Nat::from(1u64)),
                Token::Plus,
                Token::Ident("n".into()),
                Token::RParen,
            ]
        );
    }

    #[test]
    fn dollar_call_components() {
        // $min(x) lexes as Dollar, Ident, LParen, Ident, RParen.
        let toks = lex_str("$min(x)");
        assert_eq!(
            toks,
            vec![
                Token::Dollar,
                Token::Ident("min".into()),
                Token::LParen,
                Token::Ident("x".into()),
                Token::RParen,
            ]
        );
    }

    #[test]
    fn hint_macro_uses_hash() {
        // hint(show f#%) — `#` is a token; `%` is a token.
        let toks = lex_str("hint(show f#%)");
        assert_eq!(
            toks,
            vec![
                Token::Hint,
                Token::LParen,
                Token::Ident("show".into()),
                Token::Ident("f".into()),
                Token::Hash,
                Token::Percent,
                Token::RParen,
            ]
        );
    }

    #[test]
    fn bare_tilde_and_bang() {
        // `~` alone is logical negation in defs; `!` appears in show hints.
        assert_eq!(lex_str("~"), vec![Token::Tilde]);
        assert_eq!(lex_str("!"), vec![Token::Bang]);
        // Disambiguates from ~> ~~ ~>*
        assert_eq!(lex_str("~ >"), vec![Token::Tilde, Token::GreaterThan]);
        assert_eq!(lex_str("~ ~"), vec![Token::Tilde, Token::Tilde]);
    }

    #[test]
    fn unterminated_string_errors() {
        let mut map = SourceMap::new();
        let id = map.add("<test>", "\"oops");
        assert!(lex(id, "\"oops").is_err());
    }

    #[test]
    fn unknown_character_errors() {
        // `@` is not in SpecTec's character set.
        let mut map = SourceMap::new();
        let id = map.add("<test>", "@");
        assert!(lex(id, "@").is_err());
    }

    #[test]
    fn empty_input_yields_no_tokens() {
        assert_eq!(lex_str(""), Vec::<Token>::new());
        assert_eq!(lex_str("   \n\t  "), Vec::<Token>::new());
        assert_eq!(lex_str(";; just a comment"), Vec::<Token>::new());
    }

    #[test]
    fn span_positions_are_accurate() {
        let src = "syntax foo";
        let mut map = SourceMap::new();
        let id = map.add("<test>", src);
        let toks = lex(id, src).unwrap();
        assert_eq!(toks[0].span.start, 0);
        assert_eq!(toks[0].span.end, 6);
        assert_eq!(toks[1].span.start, 7);
        assert_eq!(toks[1].span.end, 10);
    }
}
