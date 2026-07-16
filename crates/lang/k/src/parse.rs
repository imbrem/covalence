//! A hand-written recursive-descent parser for textual KORE
//! (`definition.kore`), per the haskell-backend's `docs/kore-syntax.md`.
//!
//! # Lexical notes
//!
//! - Comments: `//` line and `/* … */` block (non-nesting).
//! - Identifiers match `[a-zA-Z][a-zA-Z0-9'-]*` — **apostrophe and dash are
//!   identifier characters** (K name-mangles, e.g. `Lbl'-LT-'k'-GT-`,
//!   `'Unds'`, `'Stop'`). Consequently keywords like `hooked-sort` lex as one
//!   identifier, and `\left-assoc` as one connective name.
//! - A `\` may start an identifier **only** for the builtin connectives
//!   (`\and`, `\rewrites`, …); declared symbols are plain identifiers.
//! - Set variables are written `@Name` (stored with the `@`).
//! - Strings are double-quoted with `\n \t \r \f \" \\` and `\xHH` /
//!   `\uHHHH` / `\UHHHHHHHH` escapes (`\u`/`\U` must denote valid scalar
//!   values; anything else is a clean [`ParseError`]).
//!
//! # Grammar notes
//!
//! - `\and`/`\or` are **multiary** (the 2025-01 grammar change): zero or more
//!   arguments are accepted; binary is the common case in older dumps.
//! - `\mu`/`\nu` take **no** sort parameter — empty braces `{}`.
//! - `\left-assoc{}(f{S…}(p1,…,pn))` / `\right-assoc{}(…)` (n ≥ 2) are
//!   expanded **by the parser** into nested binary applications of `f`
//!   (there is no AST node for them).

use smol_str::SmolStr;

use crate::ast::{Definition, Module, Pattern, Sentence, Sort};

/// A parse error with a byte offset into the input.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("parse error at byte {offset}: {message}")]
pub struct ParseError {
    /// Byte offset into the parsed source where the error was detected.
    pub offset: usize,
    /// Human-readable message.
    pub message: String,
}

impl ParseError {
    fn new(message: impl Into<String>, offset: usize) -> ParseError {
        ParseError {
            offset,
            message: message.into(),
        }
    }
}

/// Map a byte `offset` into `src` to a 1-based `(line, column)` pair, for
/// error messages. Columns count bytes within the line.
pub fn line_col(src: &str, offset: usize) -> (usize, usize) {
    let clamped = offset.min(src.len());
    let mut line = 1;
    let mut col = 1;
    for b in src[..clamped].bytes() {
        if b == b'\n' {
            line += 1;
            col = 1;
        } else {
            col += 1;
        }
    }
    (line, col)
}

/// Parse a whole KORE definition: `[attrs] module*`.
pub fn parse_definition(src: &str) -> Result<Definition, ParseError> {
    let mut p = Parser::new(src)?;
    let attrs = p.attrs()?;
    let mut modules = Vec::new();
    while !p.at_eof() {
        modules.push(p.module()?);
    }
    Ok(Definition { attrs, modules })
}

/// Parse a single KORE pattern (the whole input must be one pattern).
/// Primarily for tests.
pub fn parse_pattern(src: &str) -> Result<Pattern, ParseError> {
    let mut p = Parser::new(src)?;
    let pat = p.pattern()?;
    if !p.at_eof() {
        return Err(ParseError::new("expected end of input", p.offset()));
    }
    Ok(pat)
}

// ---------------------------------------------------------------------------
// Lexer
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
enum Tok {
    /// Plain identifier (also all keywords: `module`, `hooked-sort`, …).
    Id(SmolStr),
    /// Backslash identifier — a builtin connective name, stored with the `\`.
    BackslashId(SmolStr),
    /// Set variable `@Name`, stored with the `@`.
    SetVar(SmolStr),
    /// String literal (escapes decoded).
    Str(String),
    LBrace,
    RBrace,
    LParen,
    RParen,
    LBracket,
    RBracket,
    Comma,
    Colon,
    ColonEq,
}

impl Tok {
    fn describe(&self) -> String {
        match self {
            Tok::Id(s) => format!("identifier `{s}`"),
            Tok::BackslashId(s) => format!("`{s}`"),
            Tok::SetVar(s) => format!("set variable `{s}`"),
            Tok::Str(_) => "string literal".to_string(),
            Tok::LBrace => "`{`".to_string(),
            Tok::RBrace => "`}`".to_string(),
            Tok::LParen => "`(`".to_string(),
            Tok::RParen => "`)`".to_string(),
            Tok::LBracket => "`[`".to_string(),
            Tok::RBracket => "`]`".to_string(),
            Tok::Comma => "`,`".to_string(),
            Tok::Colon => "`:`".to_string(),
            Tok::ColonEq => "`:=`".to_string(),
        }
    }
}

fn is_id_start(b: u8) -> bool {
    b.is_ascii_alphabetic()
}

fn is_id_continue(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'\'' || b == b'-'
}

fn lex(src: &str) -> Result<Vec<(Tok, usize)>, ParseError> {
    let bytes = src.as_bytes();
    let mut toks = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        let b = bytes[i];
        match b {
            b' ' | b'\t' | b'\r' | b'\n' => i += 1,
            b'/' if bytes.get(i + 1) == Some(&b'/') => {
                while i < bytes.len() && bytes[i] != b'\n' {
                    i += 1;
                }
            }
            b'/' if bytes.get(i + 1) == Some(&b'*') => {
                let start = i;
                i += 2;
                loop {
                    if i + 1 >= bytes.len() {
                        return Err(ParseError::new("unterminated block comment", start));
                    }
                    if bytes[i] == b'*' && bytes[i + 1] == b'/' {
                        i += 2;
                        break;
                    }
                    i += 1;
                }
            }
            b'{' => {
                toks.push((Tok::LBrace, i));
                i += 1;
            }
            b'}' => {
                toks.push((Tok::RBrace, i));
                i += 1;
            }
            b'(' => {
                toks.push((Tok::LParen, i));
                i += 1;
            }
            b')' => {
                toks.push((Tok::RParen, i));
                i += 1;
            }
            b'[' => {
                toks.push((Tok::LBracket, i));
                i += 1;
            }
            b']' => {
                toks.push((Tok::RBracket, i));
                i += 1;
            }
            b',' => {
                toks.push((Tok::Comma, i));
                i += 1;
            }
            b':' => {
                if bytes.get(i + 1) == Some(&b'=') {
                    toks.push((Tok::ColonEq, i));
                    i += 2;
                } else {
                    toks.push((Tok::Colon, i));
                    i += 1;
                }
            }
            b'@' => {
                let start = i;
                i += 1;
                if i >= bytes.len() || !is_id_start(bytes[i]) {
                    return Err(ParseError::new("expected identifier after `@`", start));
                }
                while i < bytes.len() && is_id_continue(bytes[i]) {
                    i += 1;
                }
                toks.push((Tok::SetVar(SmolStr::new(&src[start..i])), start));
            }
            b'\\' => {
                let start = i;
                i += 1;
                if i >= bytes.len() || !is_id_start(bytes[i]) {
                    return Err(ParseError::new("expected identifier after `\\`", start));
                }
                while i < bytes.len() && is_id_continue(bytes[i]) {
                    i += 1;
                }
                toks.push((Tok::BackslashId(SmolStr::new(&src[start..i])), start));
            }
            b'"' => {
                let start = i;
                let (s, next) = lex_string(src, i)?;
                toks.push((Tok::Str(s), start));
                i = next;
            }
            b if is_id_start(b) => {
                let start = i;
                while i < bytes.len() && is_id_continue(bytes[i]) {
                    i += 1;
                }
                toks.push((Tok::Id(SmolStr::new(&src[start..i])), start));
            }
            _ => {
                return Err(ParseError::new(
                    format!(
                        "unexpected character `{}`",
                        &src[i..].chars().next().unwrap()
                    ),
                    i,
                ));
            }
        }
    }
    Ok(toks)
}

/// Lex a string literal starting at the opening quote; returns the decoded
/// string and the offset just past the closing quote.
fn lex_string(src: &str, open: usize) -> Result<(String, usize), ParseError> {
    let bytes = src.as_bytes();
    let mut out = String::new();
    let mut i = open + 1;
    loop {
        let Some(&b) = bytes.get(i) else {
            return Err(ParseError::new("unterminated string literal", open));
        };
        match b {
            b'"' => return Ok((out, i + 1)),
            b'\\' => {
                let esc_at = i;
                let Some(&e) = bytes.get(i + 1) else {
                    return Err(ParseError::new("unterminated escape sequence", esc_at));
                };
                match e {
                    b'n' => {
                        out.push('\n');
                        i += 2;
                    }
                    b't' => {
                        out.push('\t');
                        i += 2;
                    }
                    b'r' => {
                        out.push('\r');
                        i += 2;
                    }
                    b'f' => {
                        out.push('\u{c}');
                        i += 2;
                    }
                    b'"' => {
                        out.push('"');
                        i += 2;
                    }
                    b'\\' => {
                        out.push('\\');
                        i += 2;
                    }
                    b'x' => {
                        let v = hex_escape(src, esc_at, i + 2, 2)?;
                        out.push(char::from(v as u8));
                        i += 4;
                    }
                    b'u' => {
                        let v = hex_escape(src, esc_at, i + 2, 4)?;
                        out.push(scalar(v, esc_at)?);
                        i += 6;
                    }
                    b'U' => {
                        let v = hex_escape(src, esc_at, i + 2, 8)?;
                        out.push(scalar(v, esc_at)?);
                        i += 10;
                    }
                    _ => {
                        return Err(ParseError::new(
                            format!("unsupported escape `\\{}`", char::from(e)),
                            esc_at,
                        ));
                    }
                }
            }
            b'\n' => return Err(ParseError::new("newline in string literal", i)),
            _ => {
                // Copy one UTF-8 character verbatim.
                let c = src[i..].chars().next().unwrap();
                out.push(c);
                i += c.len_utf8();
            }
        }
    }
}

/// Read exactly `digits` hex digits at byte `at`; `esc_at` is the escape's
/// own offset (for errors).
fn hex_escape(src: &str, esc_at: usize, at: usize, digits: usize) -> Result<u32, ParseError> {
    let hex = src
        .get(at..at + digits)
        .ok_or_else(|| ParseError::new("truncated hex escape", esc_at))?;
    u32::from_str_radix(hex, 16)
        .map_err(|_| ParseError::new(format!("invalid hex escape `{hex}`"), esc_at))
}

fn scalar(v: u32, esc_at: usize) -> Result<char, ParseError> {
    char::from_u32(v)
        .ok_or_else(|| ParseError::new(format!("escape U+{v:X} is not a scalar value"), esc_at))
}

// ---------------------------------------------------------------------------
// Parser
// ---------------------------------------------------------------------------

struct Parser<'s> {
    src: &'s str,
    toks: Vec<(Tok, usize)>,
    pos: usize,
}

impl<'s> Parser<'s> {
    fn new(src: &'s str) -> Result<Parser<'s>, ParseError> {
        Ok(Parser {
            src,
            toks: lex(src)?,
            pos: 0,
        })
    }

    fn at_eof(&self) -> bool {
        self.pos >= self.toks.len()
    }

    /// Byte offset of the current token (or end of input).
    fn offset(&self) -> usize {
        self.toks
            .get(self.pos)
            .map_or(self.src.len(), |(_, off)| *off)
    }

    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.pos).map(|(t, _)| t)
    }

    fn next(&mut self) -> Option<(Tok, usize)> {
        let t = self.toks.get(self.pos).cloned();
        if t.is_some() {
            self.pos += 1;
        }
        t
    }

    fn err_here(&self, message: impl Into<String>) -> ParseError {
        ParseError::new(message, self.offset())
    }

    fn expect(&mut self, want: Tok) -> Result<(), ParseError> {
        match self.next() {
            Some((t, _)) if t == want => Ok(()),
            Some((t, off)) => Err(ParseError::new(
                format!("expected {}, found {}", want.describe(), t.describe()),
                off,
            )),
            None => Err(ParseError::new(
                format!("expected {}, found end of input", want.describe()),
                self.src.len(),
            )),
        }
    }

    /// Consume any identifier.
    fn ident(&mut self, what: &str) -> Result<SmolStr, ParseError> {
        match self.next() {
            Some((Tok::Id(s), _)) => Ok(s),
            Some((t, off)) => Err(ParseError::new(
                format!("expected {what}, found {}", t.describe()),
                off,
            )),
            None => Err(ParseError::new(
                format!("expected {what}, found end of input"),
                self.src.len(),
            )),
        }
    }

    /// Consume the exact keyword `kw` (keywords are ordinary identifiers).
    fn keyword(&mut self, kw: &str) -> Result<(), ParseError> {
        match self.next() {
            Some((Tok::Id(s), _)) if s == kw => Ok(()),
            Some((t, off)) => Err(ParseError::new(
                format!("expected `{kw}`, found {}", t.describe()),
                off,
            )),
            None => Err(ParseError::new(
                format!("expected `{kw}`, found end of input"),
                self.src.len(),
            )),
        }
    }

    /// True if the current token is exactly the identifier `kw`.
    fn at_keyword(&self, kw: &str) -> bool {
        matches!(self.peek(), Some(Tok::Id(s)) if s == kw)
    }

    // -- attribute / list helpers ------------------------------------------

    /// `'[' pattern-list ']'` — mandatory in the grammar everywhere it occurs.
    fn attrs(&mut self) -> Result<Vec<Pattern>, ParseError> {
        self.expect(Tok::LBracket)?;
        let attrs = self.comma_list(Tok::RBracket, Parser::pattern)?;
        self.expect(Tok::RBracket)?;
        Ok(attrs)
    }

    /// Parse a possibly-empty comma-separated list; stops before `end`
    /// (which is *not* consumed).
    fn comma_list<T>(
        &mut self,
        end: Tok,
        mut item: impl FnMut(&mut Self) -> Result<T, ParseError>,
    ) -> Result<Vec<T>, ParseError> {
        let mut items = Vec::new();
        if self.peek() == Some(&end) {
            return Ok(items);
        }
        loop {
            items.push(item(self)?);
            if self.peek() == Some(&Tok::Comma) {
                self.next();
            } else {
                return Ok(items);
            }
        }
    }

    /// `'{' ident-list '}'` — sort variable binders.
    fn sort_vars(&mut self) -> Result<Vec<SmolStr>, ParseError> {
        self.expect(Tok::LBrace)?;
        let vars = self.comma_list(Tok::RBrace, |p| p.ident("sort variable"))?;
        self.expect(Tok::RBrace)?;
        Ok(vars)
    }

    /// `'{' sort-list '}'`.
    fn sort_params(&mut self) -> Result<Vec<Sort>, ParseError> {
        self.expect(Tok::LBrace)?;
        let sorts = self.comma_list(Tok::RBrace, Parser::sort)?;
        self.expect(Tok::RBrace)?;
        Ok(sorts)
    }

    /// `'(' sort-list ')'`.
    fn sort_args(&mut self) -> Result<Vec<Sort>, ParseError> {
        self.expect(Tok::LParen)?;
        let sorts = self.comma_list(Tok::RParen, Parser::sort)?;
        self.expect(Tok::RParen)?;
        Ok(sorts)
    }

    /// `'(' pattern-list ')'`.
    fn pattern_args(&mut self) -> Result<Vec<Pattern>, ParseError> {
        self.expect(Tok::LParen)?;
        let pats = self.comma_list(Tok::RParen, Parser::pattern)?;
        self.expect(Tok::RParen)?;
        Ok(pats)
    }

    // -- grammar ------------------------------------------------------------

    fn module(&mut self) -> Result<Module, ParseError> {
        self.keyword("module")?;
        let name = self.ident("module name")?;
        let mut sentences = Vec::new();
        while !self.at_keyword("endmodule") {
            if self.at_eof() {
                return Err(self.err_here("expected sentence or `endmodule`, found end of input"));
            }
            sentences.push(self.sentence()?);
        }
        self.keyword("endmodule")?;
        let attrs = self.attrs()?;
        Ok(Module {
            name,
            sentences,
            attrs,
        })
    }

    fn sentence(&mut self) -> Result<Sentence, ParseError> {
        let off = self.offset();
        let kw = self.ident("sentence keyword")?;
        match kw.as_str() {
            "import" => {
                let name = self.ident("module name")?;
                let attrs = self.attrs()?;
                Ok(Sentence::Import { name, attrs })
            }
            "sort" | "hooked-sort" => {
                let hooked = kw == "hooked-sort";
                let name = self.ident("sort name")?;
                let vars = self.sort_vars()?;
                let attrs = self.attrs()?;
                Ok(Sentence::Sort {
                    hooked,
                    name,
                    vars,
                    attrs,
                })
            }
            "symbol" | "hooked-symbol" => {
                let hooked = kw == "hooked-symbol";
                let name = self.ident("symbol name")?;
                let sort_vars = self.sort_vars()?;
                let arg_sorts = self.sort_args()?;
                self.expect(Tok::Colon)?;
                let ret = self.sort()?;
                let attrs = self.attrs()?;
                Ok(Sentence::Symbol {
                    hooked,
                    name,
                    sort_vars,
                    arg_sorts,
                    ret,
                    attrs,
                })
            }
            "alias" => {
                let name = self.ident("alias name")?;
                let sort_vars = self.sort_vars()?;
                let arg_sorts = self.sort_args()?;
                self.expect(Tok::Colon)?;
                let ret = self.sort()?;
                self.keyword("where")?;
                let lhs_off = self.offset();
                let lhs = self.pattern()?;
                if !matches!(lhs, Pattern::App { .. }) {
                    return Err(ParseError::new(
                        "alias left-hand side must be an application pattern",
                        lhs_off,
                    ));
                }
                self.expect(Tok::ColonEq)?;
                let rhs = self.pattern()?;
                let attrs = self.attrs()?;
                Ok(Sentence::Alias {
                    name,
                    sort_vars,
                    arg_sorts,
                    ret,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                    attrs,
                })
            }
            "axiom" | "claim" => {
                let sort_vars = self.sort_vars()?;
                let pattern = self.pattern()?;
                let attrs = self.attrs()?;
                if kw == "axiom" {
                    Ok(Sentence::Axiom {
                        sort_vars,
                        pattern,
                        attrs,
                    })
                } else {
                    Ok(Sentence::Claim {
                        sort_vars,
                        pattern,
                        attrs,
                    })
                }
            }
            _ => Err(ParseError::new(
                format!("expected a sentence keyword, found identifier `{kw}`"),
                off,
            )),
        }
    }

    fn sort(&mut self) -> Result<Sort, ParseError> {
        let name = self.ident("sort")?;
        if self.peek() == Some(&Tok::LBrace) {
            let params = self.sort_params()?;
            Ok(Sort::App(name, params))
        } else {
            Ok(Sort::Var(name))
        }
    }

    fn pattern(&mut self) -> Result<Pattern, ParseError> {
        match self.peek() {
            Some(Tok::Str(_)) => {
                let Some((Tok::Str(s), _)) = self.next() else {
                    unreachable!()
                };
                Ok(Pattern::String(s))
            }
            Some(Tok::SetVar(_)) => {
                let Some((Tok::SetVar(name), _)) = self.next() else {
                    unreachable!()
                };
                self.expect(Tok::Colon)?;
                let sort = self.sort()?;
                Ok(Pattern::SVar(name, sort))
            }
            Some(Tok::BackslashId(_)) => {
                let Some((Tok::BackslashId(name), off)) = self.next() else {
                    unreachable!()
                };
                self.connective(&name, off)
            }
            Some(Tok::Id(_)) => {
                let name = self.ident("identifier")?;
                match self.peek() {
                    Some(Tok::LBrace) => {
                        let sorts = self.sort_params()?;
                        let args = self.pattern_args()?;
                        Ok(Pattern::App {
                            symbol: name,
                            sorts,
                            args,
                        })
                    }
                    Some(Tok::Colon) => {
                        self.next();
                        let sort = self.sort()?;
                        Ok(Pattern::EVar(name, sort))
                    }
                    _ => Err(self.err_here(format!(
                        "expected `{{` (application) or `:` (variable) after `{name}`"
                    ))),
                }
            }
            Some(t) => {
                let msg = format!("expected pattern, found {}", t.describe());
                Err(self.err_here(msg))
            }
            None => Err(ParseError::new(
                "expected pattern, found end of input",
                self.src.len(),
            )),
        }
    }

    /// One sort parameter in braces: `'{' sort '}'`.
    fn one_sort_param(&mut self) -> Result<Sort, ParseError> {
        self.expect(Tok::LBrace)?;
        let s = self.sort()?;
        self.expect(Tok::RBrace)?;
        Ok(s)
    }

    /// Two sort parameters: `'{' sort ',' sort '}'`.
    fn two_sort_params(&mut self) -> Result<(Sort, Sort), ParseError> {
        self.expect(Tok::LBrace)?;
        let a = self.sort()?;
        self.expect(Tok::Comma)?;
        let b = self.sort()?;
        self.expect(Tok::RBrace)?;
        Ok((a, b))
    }

    /// An element-variable binder `x : sort` (as in `\exists`/`\forall`).
    fn evar_binder(&mut self) -> Result<(SmolStr, Sort), ParseError> {
        let name = self.ident("element variable")?;
        self.expect(Tok::Colon)?;
        let sort = self.sort()?;
        Ok((name, sort))
    }

    /// A set-variable binder `@x : sort` (as in `\mu`/`\nu`).
    fn svar_binder(&mut self) -> Result<(SmolStr, Sort), ParseError> {
        match self.next() {
            Some((Tok::SetVar(name), _)) => {
                self.expect(Tok::Colon)?;
                let sort = self.sort()?;
                Ok((name, sort))
            }
            Some((t, off)) => Err(ParseError::new(
                format!("expected set variable (`@x`), found {}", t.describe()),
                off,
            )),
            None => Err(ParseError::new(
                "expected set variable (`@x`), found end of input",
                self.src.len(),
            )),
        }
    }

    /// Parse a builtin `\…` connective, `name` including the backslash and
    /// `off` its byte offset (for errors).
    fn connective(&mut self, name: &str, off: usize) -> Result<Pattern, ParseError> {
        match name {
            "\\top" | "\\bottom" => {
                let s = self.one_sort_param()?;
                self.expect(Tok::LParen)?;
                self.expect(Tok::RParen)?;
                Ok(if name == "\\top" {
                    Pattern::Top(s)
                } else {
                    Pattern::Bottom(s)
                })
            }
            "\\not" | "\\next" => {
                let s = self.one_sort_param()?;
                self.expect(Tok::LParen)?;
                let p = self.pattern()?;
                self.expect(Tok::RParen)?;
                Ok(if name == "\\not" {
                    Pattern::Not(s, Box::new(p))
                } else {
                    Pattern::Next(s, Box::new(p))
                })
            }
            // Multiary since the 2025-01 grammar change; binary in older dumps.
            "\\and" | "\\or" => {
                let s = self.one_sort_param()?;
                let args = self.pattern_args()?;
                Ok(if name == "\\and" {
                    Pattern::And(s, args)
                } else {
                    Pattern::Or(s, args)
                })
            }
            "\\implies" | "\\iff" | "\\rewrites" => {
                let s = self.one_sort_param()?;
                self.expect(Tok::LParen)?;
                let a = Box::new(self.pattern()?);
                self.expect(Tok::Comma)?;
                let b = Box::new(self.pattern()?);
                self.expect(Tok::RParen)?;
                Ok(match name {
                    "\\implies" => Pattern::Implies(s, a, b),
                    "\\iff" => Pattern::Iff(s, a, b),
                    _ => Pattern::Rewrites(s, a, b),
                })
            }
            "\\exists" | "\\forall" => {
                let sort = self.one_sort_param()?;
                self.expect(Tok::LParen)?;
                let (var, var_sort) = self.evar_binder()?;
                self.expect(Tok::Comma)?;
                let body = Box::new(self.pattern()?);
                self.expect(Tok::RParen)?;
                Ok(if name == "\\exists" {
                    Pattern::Exists {
                        sort,
                        var,
                        var_sort,
                        body,
                    }
                } else {
                    Pattern::Forall {
                        sort,
                        var,
                        var_sort,
                        body,
                    }
                })
            }
            // NOTE: \mu/\nu take NO sort parameter — empty braces.
            "\\mu" | "\\nu" => {
                self.expect(Tok::LBrace)?;
                self.expect(Tok::RBrace)?;
                self.expect(Tok::LParen)?;
                let (var, var_sort) = self.svar_binder()?;
                self.expect(Tok::Comma)?;
                let body = Box::new(self.pattern()?);
                self.expect(Tok::RParen)?;
                Ok(if name == "\\mu" {
                    Pattern::Mu {
                        var,
                        var_sort,
                        body,
                    }
                } else {
                    Pattern::Nu {
                        var,
                        var_sort,
                        body,
                    }
                })
            }
            "\\ceil" | "\\floor" => {
                let (arg_sort, sort) = self.two_sort_params()?;
                self.expect(Tok::LParen)?;
                let arg = Box::new(self.pattern()?);
                self.expect(Tok::RParen)?;
                Ok(if name == "\\ceil" {
                    Pattern::Ceil {
                        arg_sort,
                        sort,
                        arg,
                    }
                } else {
                    Pattern::Floor {
                        arg_sort,
                        sort,
                        arg,
                    }
                })
            }
            "\\equals" | "\\in" => {
                let (arg_sort, sort) = self.two_sort_params()?;
                self.expect(Tok::LParen)?;
                let lhs = Box::new(self.pattern()?);
                self.expect(Tok::Comma)?;
                let rhs = Box::new(self.pattern()?);
                self.expect(Tok::RParen)?;
                Ok(if name == "\\equals" {
                    Pattern::Equals {
                        arg_sort,
                        sort,
                        lhs,
                        rhs,
                    }
                } else {
                    Pattern::In {
                        arg_sort,
                        sort,
                        lhs,
                        rhs,
                    }
                })
            }
            "\\dv" => {
                let s = self.one_sort_param()?;
                self.expect(Tok::LParen)?;
                let lit = match self.next() {
                    Some((Tok::Str(lit), _)) => lit,
                    Some((t, off)) => {
                        return Err(ParseError::new(
                            format!("expected string literal in `\\dv`, found {}", t.describe()),
                            off,
                        ));
                    }
                    None => {
                        return Err(ParseError::new(
                            "expected string literal in `\\dv`, found end of input",
                            self.src.len(),
                        ));
                    }
                };
                self.expect(Tok::RParen)?;
                Ok(Pattern::DV(s, lit))
            }
            // Expanded by the parser into nested binary applications.
            "\\left-assoc" | "\\right-assoc" => {
                self.expect(Tok::LBrace)?;
                self.expect(Tok::RBrace)?;
                self.expect(Tok::LParen)?;
                let inner_off = self.offset();
                let inner = self.pattern()?;
                self.expect(Tok::RParen)?;
                let Pattern::App {
                    symbol,
                    sorts,
                    args,
                } = inner
                else {
                    return Err(ParseError::new(
                        format!("`{name}` requires an application pattern argument"),
                        inner_off,
                    ));
                };
                if args.len() < 2 {
                    return Err(ParseError::new(
                        format!("`{name}` requires at least two application arguments"),
                        inner_off,
                    ));
                }
                let fold2 = |a: Pattern, b: Pattern| Pattern::App {
                    symbol: symbol.clone(),
                    sorts: sorts.clone(),
                    args: vec![a, b],
                };
                let mut it = args.into_iter();
                Ok(if name == "\\left-assoc" {
                    let first = it.next().unwrap();
                    it.fold(first, fold2)
                } else {
                    let mut rev = it.rev();
                    let last = rev.next().unwrap();
                    rev.fold(last, |acc, x| fold2(x, acc))
                })
            }
            _ => Err(ParseError::new(
                format!("unknown builtin connective `{name}`"),
                off,
            )),
        }
    }
}
