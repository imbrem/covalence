use std::fmt;
use std::io;

use pretty::{Arena, DocAllocator, DocBuilder};

const DEFAULT_WIDTH: usize = 80;
const INDENT: isize = 2;

/// A parsed S-expression.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SExp {
    /// An atom: symbol, numeral, keyword, etc. Stored as-is from the source.
    Atom(String),
    /// A quoted string (contents are unescaped).
    String(String),
    /// A quoted symbol `|...|` (contents stored without pipes).
    QuotedSymbol(String),
    /// A parenthesized list of S-expressions.
    List(Vec<SExp>),
}

/// A parse error with byte offset.
#[derive(Debug, Clone)]
pub struct ParseError {
    pub offset: usize,
    pub message: String,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "offset {}: {}", self.offset, self.message)
    }
}

impl std::error::Error for ParseError {}

/// Parse a string into a sequence of S-expressions.
pub fn parse(input: &str) -> Result<Vec<SExp>, ParseError> {
    let mut parser = Parser::new(input);
    let mut result = Vec::new();
    loop {
        parser.skip_whitespace_and_comments();
        if parser.is_eof() {
            break;
        }
        result.push(parser.parse_sexp()?);
    }
    Ok(result)
}

struct Parser<'a> {
    input: &'a str,
    pos: usize,
}

impl<'a> Parser<'a> {
    fn new(input: &'a str) -> Self {
        Parser { input, pos: 0 }
    }

    fn is_eof(&self) -> bool {
        self.pos >= self.input.len()
    }

    fn peek(&self) -> Option<u8> {
        self.input.as_bytes().get(self.pos).copied()
    }

    fn advance(&mut self) {
        self.pos += 1;
    }

    fn skip_whitespace_and_comments(&mut self) {
        loop {
            // Skip whitespace
            while let Some(b) = self.peek() {
                if b.is_ascii_whitespace() {
                    self.advance();
                } else {
                    break;
                }
            }
            // Skip line comments starting with ;
            if self.peek() == Some(b';') {
                while let Some(b) = self.peek() {
                    self.advance();
                    if b == b'\n' {
                        break;
                    }
                }
            } else {
                break;
            }
        }
    }

    fn parse_sexp(&mut self) -> Result<SExp, ParseError> {
        match self.peek() {
            None => Err(ParseError {
                offset: self.pos,
                message: "unexpected end of input".into(),
            }),
            Some(b'(') => self.parse_list(),
            Some(b'"') => self.parse_string(),
            Some(b'|') => self.parse_quoted_symbol(),
            Some(b')') => Err(ParseError {
                offset: self.pos,
                message: "unexpected ')'".into(),
            }),
            Some(_) => self.parse_atom(),
        }
    }

    fn parse_list(&mut self) -> Result<SExp, ParseError> {
        let open = self.pos;
        self.advance(); // skip '('
        let mut items = Vec::new();
        loop {
            self.skip_whitespace_and_comments();
            if self.is_eof() {
                return Err(ParseError {
                    offset: open,
                    message: "unclosed '('".into(),
                });
            }
            if self.peek() == Some(b')') {
                self.advance();
                return Ok(SExp::List(items));
            }
            items.push(self.parse_sexp()?);
        }
    }

    fn parse_string(&mut self) -> Result<SExp, ParseError> {
        let start = self.pos;
        self.advance(); // skip opening '"'
        let mut s = String::new();
        loop {
            match self.peek() {
                None => {
                    return Err(ParseError {
                        offset: start,
                        message: "unterminated string".into(),
                    });
                }
                Some(b'"') => {
                    self.advance();
                    return Ok(SExp::String(s));
                }
                Some(b'\\') => {
                    self.advance();
                    match self.peek() {
                        Some(b'\\') => {
                            s.push('\\');
                            self.advance();
                        }
                        Some(b'"') => {
                            s.push('"');
                            self.advance();
                        }
                        Some(b'n') => {
                            s.push('\n');
                            self.advance();
                        }
                        Some(b't') => {
                            s.push('\t');
                            self.advance();
                        }
                        Some(b'r') => {
                            s.push('\r');
                            self.advance();
                        }
                        Some(b'a') => {
                            s.push('\x07');
                            self.advance();
                        }
                        Some(b'b') => {
                            s.push('\x08');
                            self.advance();
                        }
                        Some(b'f') => {
                            s.push('\x0c');
                            self.advance();
                        }
                        Some(b'v') => {
                            s.push('\x0b');
                            self.advance();
                        }
                        Some(b'x') => {
                            self.advance();
                            let c = self.parse_hex_escape(2, start)?;
                            s.push(c);
                        }
                        Some(b'u') => {
                            self.advance();
                            if self.peek() == Some(b'{') {
                                self.advance();
                                let c = self.parse_hex_escape_until_brace(start)?;
                                s.push(c);
                            } else {
                                let c = self.parse_hex_escape(4, start)?;
                                s.push(c);
                            }
                        }
                        Some(b'U') => {
                            self.advance();
                            let c = self.parse_hex_escape(8, start)?;
                            s.push(c);
                        }
                        Some(other) => {
                            // Be permissive: keep the backslash + char
                            s.push('\\');
                            s.push(other as char);
                            self.advance();
                        }
                        None => {
                            return Err(ParseError {
                                offset: start,
                                message: "unterminated string escape".into(),
                            });
                        }
                    }
                }
                Some(b) => {
                    // Handle multi-byte UTF-8 properly
                    let remaining = &self.input[self.pos..];
                    if let Some(c) = remaining.chars().next() {
                        s.push(c);
                        self.pos += c.len_utf8();
                    } else {
                        s.push(b as char);
                        self.advance();
                    }
                }
            }
        }
    }

    fn parse_hex_escape(&mut self, digits: usize, string_start: usize) -> Result<char, ParseError> {
        let mut n: u32 = 0;
        for _ in 0..digits {
            match self.peek() {
                Some(b) if b.is_ascii_hexdigit() => {
                    n = n * 16
                        + match b {
                            b'0'..=b'9' => (b - b'0') as u32,
                            b'a'..=b'f' => (b - b'a' + 10) as u32,
                            b'A'..=b'F' => (b - b'A' + 10) as u32,
                            _ => unreachable!(),
                        };
                    self.advance();
                }
                _ => {
                    return Err(ParseError {
                        offset: string_start,
                        message: "invalid hex escape".into(),
                    });
                }
            }
        }
        char::from_u32(n).ok_or_else(|| ParseError {
            offset: string_start,
            message: format!("invalid unicode codepoint: U+{:04X}", n),
        })
    }

    fn parse_hex_escape_until_brace(&mut self, string_start: usize) -> Result<char, ParseError> {
        let mut n: u32 = 0;
        let mut count = 0;
        loop {
            match self.peek() {
                Some(b'}') => {
                    self.advance();
                    if count == 0 {
                        return Err(ParseError {
                            offset: string_start,
                            message: "empty \\u{} escape".into(),
                        });
                    }
                    return char::from_u32(n).ok_or_else(|| ParseError {
                        offset: string_start,
                        message: format!("invalid unicode codepoint: U+{:04X}", n),
                    });
                }
                Some(b) if b.is_ascii_hexdigit() => {
                    n = n * 16
                        + match b {
                            b'0'..=b'9' => (b - b'0') as u32,
                            b'a'..=b'f' => (b - b'a' + 10) as u32,
                            b'A'..=b'F' => (b - b'A' + 10) as u32,
                            _ => unreachable!(),
                        };
                    count += 1;
                    self.advance();
                }
                _ => {
                    return Err(ParseError {
                        offset: string_start,
                        message: "invalid \\u{...} escape".into(),
                    });
                }
            }
        }
    }

    fn parse_quoted_symbol(&mut self) -> Result<SExp, ParseError> {
        let start = self.pos;
        self.advance(); // skip opening '|'
        let mut s = String::new();
        loop {
            match self.peek() {
                None => {
                    return Err(ParseError {
                        offset: start,
                        message: "unterminated quoted symbol".into(),
                    });
                }
                Some(b'|') => {
                    self.advance();
                    return Ok(SExp::QuotedSymbol(s));
                }
                Some(b'\\') => {
                    // SMT-LIB says no backslashes inside |...|,
                    // but we're permissive: just include it
                    s.push('\\');
                    self.advance();
                }
                Some(_) => {
                    let remaining = &self.input[self.pos..];
                    if let Some(c) = remaining.chars().next() {
                        s.push(c);
                        self.pos += c.len_utf8();
                    }
                }
            }
        }
    }

    fn parse_atom(&mut self) -> Result<SExp, ParseError> {
        let start = self.pos;
        while let Some(b) = self.peek() {
            if b.is_ascii_whitespace()
                || b == b'('
                || b == b')'
                || b == b';'
                || b == b'"'
                || b == b'|'
            {
                break;
            }
            self.advance();
        }
        let text = &self.input[start..self.pos];
        if text.is_empty() {
            return Err(ParseError {
                offset: start,
                message: "expected atom".into(),
            });
        }
        Ok(SExp::Atom(text.to_owned()))
    }
}

/// Compute (line, col) from byte offset in source text (0-based).
pub fn offset_to_line_col(text: &str, offset: usize) -> (u32, u32) {
    let mut line = 0u32;
    let mut col = 0u32;
    for (i, b) in text.bytes().enumerate() {
        if i == offset {
            return (line, col);
        }
        if b == b'\n' {
            line += 1;
            col = 0;
        } else {
            col += 1;
        }
    }
    (line, col)
}

/// Pretty-print a sequence of S-expressions.
pub fn prettyprint(sexps: &[SExp], writer: &mut dyn io::Write) -> io::Result<()> {
    let arena = Arena::<()>::new();
    let docs: Vec<_> = sexps.iter().map(|s| sexp_to_doc(&arena, s)).collect();
    if docs.is_empty() {
        return Ok(());
    }
    let doc = arena.intersperse(docs, arena.hardline());
    doc.1.render(DEFAULT_WIDTH, writer)
}

fn sexp_to_doc<'a>(arena: &'a Arena<'a>, sexp: &SExp) -> DocBuilder<'a, Arena<'a>> {
    match sexp {
        SExp::Atom(s) => arena.text(s.clone()),
        SExp::String(s) => arena.text(format!("\"{}\"", escape_string(s))),
        SExp::QuotedSymbol(s) => arena.text(format!("|{}|", s)),
        SExp::List(items) => {
            if items.is_empty() {
                return arena.text("()");
            }
            let elems: Vec<_> = items.iter().map(|s| sexp_to_doc(arena, s)).collect();
            let sep = arena.line();
            arena
                .text("(")
                .append(
                    arena
                        .line_()
                        .append(arena.intersperse(elems, sep))
                        .nest(INDENT),
                )
                .append(arena.line_())
                .append(arena.text(")"))
                .group()
        }
    }
}

fn escape_string(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            '\r' => out.push_str("\\r"),
            '\x07' => out.push_str("\\a"),
            '\x08' => out.push_str("\\b"),
            '\x0c' => out.push_str("\\f"),
            '\x0b' => out.push_str("\\v"),
            c => out.push(c),
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fmt(input: &str) -> String {
        let sexps = parse(input).unwrap();
        let mut buf = Vec::new();
        prettyprint(&sexps, &mut buf).unwrap();
        String::from_utf8(buf).unwrap()
    }

    #[test]
    fn parse_atom() {
        assert_eq!(parse("foo").unwrap(), vec![SExp::Atom("foo".into())]);
    }

    #[test]
    fn parse_keyword() {
        assert_eq!(parse(":key").unwrap(), vec![SExp::Atom(":key".into())]);
    }

    #[test]
    fn parse_numeral() {
        assert_eq!(parse("42").unwrap(), vec![SExp::Atom("42".into())]);
    }

    #[test]
    fn parse_string() {
        assert_eq!(
            parse(r#""hello world""#).unwrap(),
            vec![SExp::String("hello world".into())]
        );
    }

    #[test]
    fn parse_string_escapes() {
        assert_eq!(
            parse(r#""a\"b\\c""#).unwrap(),
            vec![SExp::String("a\"b\\c".into())]
        );
        assert_eq!(
            parse(r#""line\nbreak""#).unwrap(),
            vec![SExp::String("line\nbreak".into())]
        );
    }

    #[test]
    fn parse_quoted_symbol() {
        assert_eq!(
            parse("|hello world|").unwrap(),
            vec![SExp::QuotedSymbol("hello world".into())]
        );
    }

    #[test]
    fn parse_empty_list() {
        assert_eq!(parse("()").unwrap(), vec![SExp::List(vec![])]);
    }

    #[test]
    fn parse_simple_list() {
        assert_eq!(
            parse("(+ 1 2)").unwrap(),
            vec![SExp::List(vec![
                SExp::Atom("+".into()),
                SExp::Atom("1".into()),
                SExp::Atom("2".into()),
            ])]
        );
    }

    #[test]
    fn parse_nested_list() {
        assert_eq!(
            parse("(assert (= x 0))").unwrap(),
            vec![SExp::List(vec![
                SExp::Atom("assert".into()),
                SExp::List(vec![
                    SExp::Atom("=".into()),
                    SExp::Atom("x".into()),
                    SExp::Atom("0".into()),
                ]),
            ])]
        );
    }

    #[test]
    fn parse_comments() {
        assert_eq!(
            parse("; comment\nfoo").unwrap(),
            vec![SExp::Atom("foo".into())]
        );
        assert_eq!(
            parse("(a ; comment\nb)").unwrap(),
            vec![SExp::List(vec![
                SExp::Atom("a".into()),
                SExp::Atom("b".into()),
            ])]
        );
    }

    #[test]
    fn parse_multiple_top_level() {
        let result = parse("(set-logic QF_LIA)\n(check-sat)").unwrap();
        assert_eq!(result.len(), 2);
    }

    #[test]
    fn error_unclosed_paren() {
        assert!(parse("(foo").is_err());
    }

    #[test]
    fn error_unexpected_close() {
        assert!(parse(")").is_err());
    }

    #[test]
    fn error_unterminated_string() {
        assert!(parse("\"hello").is_err());
    }

    #[test]
    fn prettyprint_atom() {
        assert_eq!(fmt("foo"), "foo");
    }

    #[test]
    fn prettyprint_string() {
        assert_eq!(fmt(r#""hello""#), r#""hello""#);
    }

    #[test]
    fn prettyprint_simple_list() {
        assert_eq!(fmt("(+ 1 2)"), "(+ 1 2)");
    }

    #[test]
    fn prettyprint_nested() {
        assert_eq!(fmt("(assert (= x 0))"), "(assert (= x 0))");
    }

    #[test]
    fn prettyprint_multiple() {
        assert_eq!(
            fmt("(set-logic QF_LIA)\n(check-sat)"),
            "(set-logic QF_LIA)\n(check-sat)"
        );
    }

    #[test]
    fn prettyprint_long_list_breaks() {
        let input = "(this-is-a-very-long-command with many arguments that should definitely exceed the eighty character line width limit)";
        let output = fmt(input);
        assert!(output.contains('\n'), "long list should break: {output}");
    }

    #[test]
    fn roundtrip() {
        let inputs = [
            "(set-logic QF_LIA)",
            "(declare-fun x () Int)",
            "(assert (= (+ x 1) 2))",
            "(check-sat)",
            "(exit)",
            r#"(set-info :source "test")"#,
            "(assert (not (= |foo bar| 0)))",
        ];
        for input in inputs {
            let parsed = parse(input).unwrap();
            let mut buf = Vec::new();
            prettyprint(&parsed, &mut buf).unwrap();
            let output = String::from_utf8(buf).unwrap();
            let reparsed = parse(&output).unwrap_or_else(|e| {
                panic!("failed to reparse {input:?}: {e}\noutput: {output:?}")
            });
            assert_eq!(parsed, reparsed, "roundtrip mismatch for {input:?}");
        }
    }

    #[test]
    fn offset_to_line_col_basic() {
        let text = "abc\ndef\nghi";
        assert_eq!(offset_to_line_col(text, 0), (0, 0));
        assert_eq!(offset_to_line_col(text, 3), (0, 3));
        assert_eq!(offset_to_line_col(text, 4), (1, 0));
        assert_eq!(offset_to_line_col(text, 8), (2, 0));
    }

    #[test]
    fn atom_stops_at_pipe() {
        assert_eq!(
            parse("foo|bar|").unwrap(),
            vec![
                SExp::Atom("foo".into()),
                SExp::QuotedSymbol("bar".into()),
            ]
        );
    }

    #[test]
    fn roundtrip_control_chars() {
        let inputs = [
            r#""\a\b\f\v""#,
            r#""\n\t\r""#,
            r#""hello\"world""#,
            r#""back\\slash""#,
        ];
        for input in inputs {
            let parsed = parse(input).unwrap();
            let mut buf = Vec::new();
            prettyprint(&parsed, &mut buf).unwrap();
            let output = String::from_utf8(buf).unwrap();
            let reparsed = parse(&output).unwrap_or_else(|e| {
                panic!("failed to reparse {input:?}: {e}\noutput: {output:?}")
            });
            assert_eq!(parsed, reparsed, "roundtrip mismatch for {input:?}");
        }
    }

    #[test]
    fn parse_empty() {
        assert_eq!(parse("").unwrap(), vec![]);
        assert_eq!(parse("  \n  ").unwrap(), vec![]);
        assert_eq!(parse("; just a comment\n").unwrap(), vec![]);
    }
}
