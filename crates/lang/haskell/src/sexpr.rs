//! The **S-expression interchange IR** — the middle stage of the pipeline
//! *Haskell dialect ⇒ S-expressions ⇒ backend*.
//!
//! Third-party producers and consumers plug in HERE: they can hand this crate
//! S-expression **text** (never touching Haskell syntax) via [`parse_sexpr`] /
//! [`parse_sexprs`], or consume the canonical text this crate prints via
//! [`SExpr::to_text`], and a backend interprets the IR at the
//! [`Realize`](crate::realize::Realize) seam. The Haskell front end is just
//! one producer of this IR (see [`crate::lower`]).
//!
//! # The IR
//!
//! An [`SExpr`] is a list tree over three atom kinds:
//!
//! - [`SExpr::Sym`] — a symbol (identifier, operator, keyword like `lambda`);
//! - [`SExpr::Nat`] — a natural-number atom carrying the **covalence
//!   arbitrary-precision [`Nat`]** (a Haskell `Nat` literal is a covalence
//!   `Nat`, not a machine integer — there is no `u128` cap anywhere);
//! - [`SExpr::Str`] — a string atom (already unescaped).
//!
//! # Grammar (canonical text format)
//!
//! ```text
//! forms  := trivia (form trivia)*
//! form   := list | string | nat | symbol
//! list   := '(' forms ')'
//! string := '"' (escape | any char except '"' or '\')* '"'
//! escape := '\n' | '\t' | '\r' | '\0' | '\\' | '\"'
//! nat    := [0-9]+                        -- an all-digit atom run
//! symbol := a non-all-digit atom run
//! trivia := spaces / tabs / CR / LF and ';' line comments
//! ```
//!
//! The **delimiters** are whitespace, `(`, `)`, `"`, and `;`. An *atom run*
//! is a maximal run of non-delimiter characters: if it consists entirely of
//! ASCII digits it reads as a [`SExpr::Nat`] (arbitrary precision), otherwise
//! as a [`SExpr::Sym`]. So `123` is a nat while `1abc`, `+`, `x'`, and
//! `mapOption` are symbols.
//!
//! # Canonical printing
//!
//! [`SExpr::to_text`] (also the [`core::fmt::Display`] impl) prints the
//! **canonical text**: single-line, one space between list items, nats in
//! decimal, strings quoted with exactly the escapes above, symbols verbatim.
//! `parse_sexpr(e.to_text()) == e` holds for every tree whose symbols are
//! *bare* (see [`is_bare_symbol`]): non-empty, free of delimiter characters,
//! and not all digits. Symbols produced by the Haskell front end are always
//! bare; there is no quoted-symbol form (`|…|`) in this grammar — see the
//! crate the generated open-work index.
//!
//! # Relation to `covalence-sexp` and the kernel reader
//!
//! The workspace S-expression library `covalence-sexp` is a *generic,
//! dialect-parametrized* reader whose default atoms are symbols and strings —
//! numerals stay symbols there. This IR is deliberately crate-local because
//! the interchange format wants a **first-class arbitrary-precision `Nat`
//! atom** and a **canonical** (deterministic, single-line) printer. The
//! grammar is kept a near-subset of `covalence-sexp`'s Covalence dialect
//! (canonical output contains no comments and no quoted symbols, so it parses
//! under both), and mirrors the kernel-side `sexpr_parse` reader
//! (`crates/kernel/hol/init/src/init/sexpr_parse.rs`): atoms are maximal
//! non-delimiter runs, lists are `(e₁ … eₙ)`.

use core::fmt;
use std::str::FromStr;

pub use covalence_types::Nat;

/// An S-expression: the interchange IR between the Haskell front end and the
/// pluggable backends. See the module docs for the text grammar.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SExpr {
    /// A symbol atom (identifier, operator, or keyword such as `lambda`).
    Sym(String),
    /// A natural-number atom — the covalence arbitrary-precision [`Nat`].
    Nat(Nat),
    /// A string atom (unescaped contents).
    Str(String),
    /// A parenthesized list of forms.
    List(Vec<SExpr>),
}

impl SExpr {
    /// Convenience constructor for [`SExpr::Sym`].
    pub fn sym(s: impl Into<String>) -> SExpr {
        SExpr::Sym(s.into())
    }

    /// Convenience constructor for [`SExpr::Nat`].
    pub fn nat(n: impl Into<Nat>) -> SExpr {
        SExpr::Nat(n.into())
    }

    /// Convenience constructor for [`SExpr::Str`].
    pub fn string(s: impl Into<String>) -> SExpr {
        SExpr::Str(s.into())
    }

    /// Convenience constructor for [`SExpr::List`].
    pub fn list(items: Vec<SExpr>) -> SExpr {
        SExpr::List(items)
    }

    /// Print the canonical text (see the module docs). Round-trips through
    /// [`parse_sexpr`] whenever every symbol is bare ([`is_bare_symbol`]).
    pub fn to_text(&self) -> String {
        self.to_string()
    }
}

impl fmt::Display for SExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SExpr::Sym(s) => {
                debug_assert!(
                    is_bare_symbol(s),
                    "printing non-bare symbol {s:?} — it will not round-trip"
                );
                f.write_str(s)
            }
            SExpr::Nat(n) => write!(f, "{n}"),
            SExpr::Str(s) => f.write_str(&quote_string(s)),
            SExpr::List(items) => {
                f.write_str("(")?;
                for (i, it) in items.iter().enumerate() {
                    if i > 0 {
                        f.write_str(" ")?;
                    }
                    write!(f, "{it}")?;
                }
                f.write_str(")")
            }
        }
    }
}

/// Is `s` a *bare* symbol — printable such that it reads back as the same
/// [`SExpr::Sym`]? True iff `s` is non-empty, contains no delimiter character
/// (whitespace, `(`, `)`, `"`, `;`), and is not all ASCII digits (an all-digit
/// run reads back as a [`SExpr::Nat`]).
pub fn is_bare_symbol(s: &str) -> bool {
    !s.is_empty() && !s.bytes().all(|b| b.is_ascii_digit()) && !s.chars().any(is_delimiter_char)
}

fn is_delimiter_char(c: char) -> bool {
    matches!(c, ' ' | '\t' | '\r' | '\n' | '(' | ')' | '"' | ';')
}

/// Quote and escape a string atom's contents for the canonical text:
/// `"` `\` `\n` `\t` `\r` `\0` are escaped, everything else is verbatim.
pub fn quote_string(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            '\r' => out.push_str("\\r"),
            '\0' => out.push_str("\\0"),
            other => out.push(other),
        }
    }
    out.push('"');
    out
}

/// A parse error with a byte offset into the input text.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SExprParseError {
    /// Human-readable message.
    pub message: String,
    /// Byte offset into the parsed source where the error was detected.
    pub pos: usize,
}

impl SExprParseError {
    fn new(message: impl Into<String>, pos: usize) -> SExprParseError {
        SExprParseError {
            message: message.into(),
            pos,
        }
    }
}

impl fmt::Display for SExprParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "s-expression parse error at byte {}: {}",
            self.pos, self.message
        )
    }
}

impl std::error::Error for SExprParseError {}

/// Parse exactly one S-expression, requiring that all input (up to trailing
/// trivia) is consumed.
pub fn parse_sexpr(src: &str) -> Result<SExpr, SExprParseError> {
    let mut r = Reader { src, pos: 0 };
    let e = r.form()?;
    r.skip_trivia();
    if r.pos != src.len() {
        return Err(SExprParseError::new("trailing input after form", r.pos));
    }
    Ok(e)
}

/// Parse a whole sequence of S-expressions (e.g. a lowered module: one
/// `(define …)` form per declaration), separated by trivia.
pub fn parse_sexprs(src: &str) -> Result<Vec<SExpr>, SExprParseError> {
    let mut r = Reader { src, pos: 0 };
    let mut out = Vec::new();
    loop {
        r.skip_trivia();
        if r.pos == src.len() {
            return Ok(out);
        }
        out.push(r.form()?);
    }
}

struct Reader<'a> {
    src: &'a str,
    pos: usize,
}

impl Reader<'_> {
    fn peek(&self) -> Option<u8> {
        self.src.as_bytes().get(self.pos).copied()
    }

    /// Skip whitespace and `;` line comments.
    fn skip_trivia(&mut self) {
        let bytes = self.src.as_bytes();
        while self.pos < bytes.len() {
            match bytes[self.pos] {
                b' ' | b'\t' | b'\r' | b'\n' => self.pos += 1,
                b';' => {
                    while self.pos < bytes.len() && bytes[self.pos] != b'\n' {
                        self.pos += 1;
                    }
                }
                _ => break,
            }
        }
    }

    fn form(&mut self) -> Result<SExpr, SExprParseError> {
        self.skip_trivia();
        match self.peek() {
            None => Err(SExprParseError::new("expected an S-expression", self.pos)),
            Some(b'(') => self.list(),
            Some(b')') => Err(SExprParseError::new("unmatched `)`", self.pos)),
            Some(b'"') => self.string(),
            Some(_) => self.atom(),
        }
    }

    fn list(&mut self) -> Result<SExpr, SExprParseError> {
        let start = self.pos;
        self.pos += 1; // consume '('
        let mut items = Vec::new();
        loop {
            self.skip_trivia();
            match self.peek() {
                None => return Err(SExprParseError::new("unclosed `(`", start)),
                Some(b')') => {
                    self.pos += 1;
                    return Ok(SExpr::List(items));
                }
                Some(_) => items.push(self.form()?),
            }
        }
    }

    fn string(&mut self) -> Result<SExpr, SExprParseError> {
        let start = self.pos;
        let bytes = self.src.as_bytes();
        self.pos += 1; // consume '"'
        let mut s = String::new();
        loop {
            if self.pos >= bytes.len() {
                return Err(SExprParseError::new("unterminated string", start));
            }
            match bytes[self.pos] {
                b'"' => {
                    self.pos += 1;
                    return Ok(SExpr::Str(s));
                }
                b'\\' => {
                    self.pos += 1;
                    let Some(&e) = bytes.get(self.pos) else {
                        return Err(SExprParseError::new("unterminated escape", start));
                    };
                    let ch = match e {
                        b'n' => '\n',
                        b't' => '\t',
                        b'r' => '\r',
                        b'0' => '\0',
                        b'\\' => '\\',
                        b'"' => '"',
                        other => {
                            return Err(SExprParseError::new(
                                format!("unknown escape `\\{}`", other as char),
                                self.pos,
                            ));
                        }
                    };
                    s.push(ch);
                    self.pos += 1;
                }
                _ => {
                    // Copy one UTF-8 char from the source.
                    let ch = self.src[self.pos..].chars().next().unwrap();
                    s.push(ch);
                    self.pos += ch.len_utf8();
                }
            }
        }
    }

    /// A maximal non-delimiter run: all-ASCII-digits ⇒ [`SExpr::Nat`]
    /// (arbitrary precision), otherwise ⇒ [`SExpr::Sym`].
    fn atom(&mut self) -> Result<SExpr, SExprParseError> {
        let start = self.pos;
        let bytes = self.src.as_bytes();
        while self.pos < bytes.len() && !is_delimiter_byte(bytes[self.pos]) {
            self.pos += 1;
        }
        let text = &self.src[start..self.pos];
        if text.bytes().all(|b| b.is_ascii_digit()) {
            let n = Nat::from_str(text)
                .map_err(|e| SExprParseError::new(format!("invalid nat atom: {e}"), start))?;
            Ok(SExpr::Nat(n))
        } else {
            Ok(SExpr::Sym(text.to_string()))
        }
    }
}

/// A byte-level delimiter test. Delimiters are all ASCII, so scanning bytes
/// never splits a multi-byte UTF-8 character.
fn is_delimiter_byte(b: u8) -> bool {
    matches!(b, b' ' | b'\t' | b'\r' | b'\n' | b'(' | b')' | b'"' | b';')
}

#[cfg(test)]
mod tests {
    use super::*;

    fn roundtrip(e: &SExpr) {
        let text = e.to_text();
        let back = parse_sexpr(&text).unwrap_or_else(|err| panic!("re-parse `{text}`: {err}"));
        assert_eq!(&back, e, "round-trip through `{text}`");
    }

    #[test]
    fn parses_atoms() {
        assert_eq!(parse_sexpr("foo").unwrap(), SExpr::sym("foo"));
        assert_eq!(parse_sexpr("+").unwrap(), SExpr::sym("+"));
        assert_eq!(parse_sexpr("x'").unwrap(), SExpr::sym("x'"));
        assert_eq!(parse_sexpr("42").unwrap(), SExpr::nat(42u64));
        // A digit-leading but not all-digit run is a symbol.
        assert_eq!(parse_sexpr("1abc").unwrap(), SExpr::sym("1abc"));
    }

    #[test]
    fn nat_atoms_are_arbitrary_precision() {
        // 2^128 — strictly greater than u128::MAX.
        let big = "340282366920938463463374607431768211456";
        let e = parse_sexpr(big).unwrap();
        assert_eq!(e, SExpr::Nat(big.parse().unwrap()));
        assert_eq!(e.to_text(), big);
    }

    #[test]
    fn parses_strings_with_escapes() {
        assert_eq!(
            parse_sexpr(r#""hi\n\"there\"""#).unwrap(),
            SExpr::string("hi\n\"there\"")
        );
        assert_eq!(parse_sexpr(r#""""#).unwrap(), SExpr::string(""));
    }

    #[test]
    fn parses_lists_and_trivia() {
        assert_eq!(parse_sexpr("()").unwrap(), SExpr::list(vec![]));
        assert_eq!(
            parse_sexpr("( f ; comment\n  x 12 \"s\" )").unwrap(),
            SExpr::list(vec![
                SExpr::sym("f"),
                SExpr::sym("x"),
                SExpr::nat(12u64),
                SExpr::string("s"),
            ])
        );
    }

    #[test]
    fn parses_nested_lists() {
        assert_eq!(
            parse_sexpr("(lambda x (f (g x)))").unwrap(),
            SExpr::list(vec![
                SExpr::sym("lambda"),
                SExpr::sym("x"),
                SExpr::list(vec![
                    SExpr::sym("f"),
                    SExpr::list(vec![SExpr::sym("g"), SExpr::sym("x")]),
                ]),
            ])
        );
    }

    #[test]
    fn parse_sexprs_reads_a_sequence() {
        let forms = parse_sexprs("(a 1) ; two forms\n(b 2)\n").unwrap();
        assert_eq!(forms.len(), 2);
        assert_eq!(forms[0].to_text(), "(a 1)");
        assert_eq!(forms[1].to_text(), "(b 2)");
        assert_eq!(parse_sexprs("  ; only trivia\n").unwrap(), vec![]);
    }

    #[test]
    fn canonical_text_round_trips() {
        roundtrip(&SExpr::sym("mapOption"));
        roundtrip(&SExpr::nat(0u64));
        roundtrip(&SExpr::Nat(
            "340282366920938463463374607431768211457".parse().unwrap(),
        ));
        roundtrip(&SExpr::string("a \"quoted\"\nline\twith \\ zero\0"));
        roundtrip(&SExpr::list(vec![]));
        roundtrip(&SExpr::list(vec![
            SExpr::sym("let"),
            SExpr::sym("x"),
            SExpr::nat(5u64),
            SExpr::list(vec![SExpr::sym("+"), SExpr::sym("x"), SExpr::nat(1u64)]),
        ]));
    }

    #[test]
    fn errors_have_positions() {
        assert_eq!(parse_sexpr("").unwrap_err().pos, 0);
        assert_eq!(parse_sexpr("(f x").unwrap_err().pos, 0); // unclosed `(` points at it
        assert_eq!(parse_sexpr(")").unwrap_err().pos, 0);
        assert_eq!(
            parse_sexpr("f x").unwrap_err().message,
            "trailing input after form"
        );
        assert!(
            parse_sexpr("\"oops")
                .unwrap_err()
                .message
                .contains("unterminated")
        );
        assert!(
            parse_sexpr(r#""\q""#)
                .unwrap_err()
                .message
                .contains("unknown escape")
        );
    }

    #[test]
    fn bare_symbol_predicate() {
        assert!(is_bare_symbol("foo"));
        assert!(is_bare_symbol("+"));
        assert!(is_bare_symbol("1abc"));
        assert!(!is_bare_symbol(""));
        assert!(!is_bare_symbol("123")); // would re-read as a nat
        assert!(!is_bare_symbol("has space"));
        assert!(!is_bare_symbol("paren("));
        assert!(!is_bare_symbol("semi;colon"));
    }
}
