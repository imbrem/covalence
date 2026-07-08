//! A hand-written recursive-descent parser for the supported Haskell subset.
//!
//! No external dependencies: a small lexer produces position-tagged tokens and
//! a precedence-climbing parser turns them into [`Expr`]/[`Decl`] values.
//!
//! # Supported subset
//!
//! Expressions ([`parse_expr`]):
//!
//! - identifiers (`foo`, `map`, `x'`, `f2`);
//! - natural-number literals (`0`, `42`) — up to [`u128`];
//! - string literals (`"hi\n"`) with `\n \t \\ \" \r \0` escapes;
//! - lambdas `\x -> e` and the sugar `\x y -> e` (⇝ nested lambdas);
//! - application by juxtaposition, left-associative and tighter than any
//!   operator (`f x y` = `(f x) y`);
//! - parenthesisation `( e )`;
//! - `let x = e in e'` (a single, non-recursive binder);
//! - the infix operators `==` (prec 4), `+` `-` (prec 6, left-assoc), `*`
//!   (prec 7, left-assoc). Operator operands are applications, so a lambda or
//!   `let` must be parenthesised to sit under an operator (as in Haskell).
//!
//! Modules ([`parse_module`]): newline-separated top-level definitions
//! `name p1 p2 = expr`, one per logical line. A line indented relative to the
//! previous one continues it (layout-lite); there is no full layout algorithm.
//!
//! Everything else (do-notation, guards, `where`, type signatures, pattern
//! matching, multi-clause definitions, full layout) is out of scope — see the
//! crate `SKELETONS.md`.

use crate::ast::{Decl, Expr, Lit, Module};

/// A parse error with a byte offset into the input.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParseError {
    /// Human-readable message.
    pub message: String,
    /// Byte offset into the parsed source where the error was detected.
    pub pos: usize,
}

impl ParseError {
    fn new(message: impl Into<String>, pos: usize) -> ParseError {
        ParseError {
            message: message.into(),
            pos,
        }
    }
}

impl core::fmt::Display for ParseError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "parse error at byte {}: {}", self.pos, self.message)
    }
}

impl std::error::Error for ParseError {}

// ---------------------------------------------------------------------------
// Lexer
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq)]
enum Tok {
    Ident(String),
    Nat(u128),
    Str(String),
    Lambda,
    Arrow,
    Equals,
    LParen,
    RParen,
    Op(String),
    Let,
    In,
}

#[derive(Clone, Debug)]
struct Token {
    tok: Tok,
    pos: usize,
}

fn is_ident_start(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_'
}

fn is_ident_cont(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_' || c == '\''
}

fn lex(src: &str) -> Result<Vec<Token>, ParseError> {
    let bytes = src.as_bytes();
    let mut i = 0;
    let mut out = Vec::new();
    while i < bytes.len() {
        let c = bytes[i] as char;
        match c {
            ' ' | '\t' | '\r' | '\n' => {
                i += 1;
            }
            '\\' => {
                out.push(Token {
                    tok: Tok::Lambda,
                    pos: i,
                });
                i += 1;
            }
            '(' => {
                out.push(Token {
                    tok: Tok::LParen,
                    pos: i,
                });
                i += 1;
            }
            ')' => {
                out.push(Token {
                    tok: Tok::RParen,
                    pos: i,
                });
                i += 1;
            }
            '"' => {
                let start = i;
                i += 1;
                let mut s = String::new();
                loop {
                    if i >= bytes.len() {
                        return Err(ParseError::new("unterminated string literal", start));
                    }
                    let d = bytes[i] as char;
                    match d {
                        '"' => {
                            i += 1;
                            break;
                        }
                        '\\' => {
                            i += 1;
                            if i >= bytes.len() {
                                return Err(ParseError::new("unterminated escape", start));
                            }
                            let e = bytes[i] as char;
                            let ch = match e {
                                'n' => '\n',
                                't' => '\t',
                                'r' => '\r',
                                '0' => '\0',
                                '\\' => '\\',
                                '"' => '"',
                                other => {
                                    return Err(ParseError::new(
                                        format!("unknown escape `\\{other}`"),
                                        i,
                                    ));
                                }
                            };
                            s.push(ch);
                            i += 1;
                        }
                        _ => {
                            // Copy one UTF-8 char from the original source.
                            let rest = &src[i..];
                            let ch = rest.chars().next().unwrap();
                            s.push(ch);
                            i += ch.len_utf8();
                        }
                    }
                }
                out.push(Token {
                    tok: Tok::Str(s),
                    pos: start,
                });
            }
            '-' if i + 1 < bytes.len() && bytes[i + 1] as char == '>' => {
                out.push(Token {
                    tok: Tok::Arrow,
                    pos: i,
                });
                i += 2;
            }
            '=' if i + 1 < bytes.len() && bytes[i + 1] as char == '=' => {
                out.push(Token {
                    tok: Tok::Op("==".into()),
                    pos: i,
                });
                i += 2;
            }
            '=' => {
                out.push(Token {
                    tok: Tok::Equals,
                    pos: i,
                });
                i += 1;
            }
            '+' | '*' | '-' => {
                out.push(Token {
                    tok: Tok::Op(c.to_string()),
                    pos: i,
                });
                i += 1;
            }
            c if c.is_ascii_digit() => {
                let start = i;
                while i < bytes.len() && (bytes[i] as char).is_ascii_digit() {
                    i += 1;
                }
                let text = &src[start..i];
                let n: u128 = text
                    .parse()
                    .map_err(|_| ParseError::new("numeric literal out of range", start))?;
                out.push(Token {
                    tok: Tok::Nat(n),
                    pos: start,
                });
            }
            c if is_ident_start(c) => {
                let start = i;
                i += 1;
                while i < bytes.len() && is_ident_cont(bytes[i] as char) {
                    i += 1;
                }
                let text = &src[start..i];
                let tok = match text {
                    "let" => Tok::Let,
                    "in" => Tok::In,
                    _ => Tok::Ident(text.to_string()),
                };
                out.push(Token { tok, pos: start });
            }
            other => {
                return Err(ParseError::new(
                    format!("unexpected character `{other}`"),
                    i,
                ));
            }
        }
    }
    Ok(out)
}

// ---------------------------------------------------------------------------
// Parser
// ---------------------------------------------------------------------------

struct Parser {
    toks: Vec<Token>,
    /// Cursor into `toks`.
    idx: usize,
    /// Byte length of the source (for end-of-input errors).
    end: usize,
}

impl Parser {
    fn new(toks: Vec<Token>, end: usize) -> Parser {
        Parser { toks, idx: 0, end }
    }

    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.idx).map(|t| &t.tok)
    }

    fn peek_pos(&self) -> usize {
        self.toks.get(self.idx).map_or(self.end, |t| t.pos)
    }

    fn bump(&mut self) -> Option<&Token> {
        let t = self.toks.get(self.idx);
        if t.is_some() {
            self.idx += 1;
        }
        t
    }

    fn expect(&mut self, want: &Tok, what: &str) -> Result<(), ParseError> {
        match self.peek() {
            Some(t) if t == want => {
                self.idx += 1;
                Ok(())
            }
            _ => Err(ParseError::new(format!("expected {what}"), self.peek_pos())),
        }
    }

    /// `expr := lambda | let | opexpr`
    fn expr(&mut self) -> Result<Expr, ParseError> {
        match self.peek() {
            Some(Tok::Lambda) => self.lambda(),
            Some(Tok::Let) => self.let_expr(),
            _ => self.op_expr(0),
        }
    }

    /// `lambda := '\' ident+ '->' expr`
    fn lambda(&mut self) -> Result<Expr, ParseError> {
        self.expect(&Tok::Lambda, "`\\`")?;
        let mut params = Vec::new();
        while let Some(Tok::Ident(name)) = self.peek() {
            params.push(name.clone());
            self.idx += 1;
        }
        if params.is_empty() {
            return Err(ParseError::new(
                "lambda needs at least one parameter",
                self.peek_pos(),
            ));
        }
        self.expect(&Tok::Arrow, "`->`")?;
        let body = self.expr()?;
        // Desugar `\x y -> e` into nested single lambdas.
        let mut acc = body;
        for p in params.into_iter().rev() {
            acc = Expr::lam(p, acc);
        }
        Ok(acc)
    }

    /// `let := 'let' ident '=' expr 'in' expr`
    fn let_expr(&mut self) -> Result<Expr, ParseError> {
        self.expect(&Tok::Let, "`let`")?;
        let end = self.end;
        let name = match self.bump() {
            Some(Token {
                tok: Tok::Ident(n), ..
            }) => n.clone(),
            other => {
                let pos = other.map_or(end, |t| t.pos);
                return Err(ParseError::new("expected binder name after `let`", pos));
            }
        };
        self.expect(&Tok::Equals, "`=`")?;
        let val = self.expr()?;
        self.expect(&Tok::In, "`in`")?;
        let body = self.expr()?;
        Ok(Expr::let_(name, val, body))
    }

    /// Precedence-climbing over infix operators; operands are applications.
    fn op_expr(&mut self, min_prec: u8) -> Result<Expr, ParseError> {
        let mut left = self.app_expr()?;
        while let Some(Tok::Op(op)) = self.peek() {
            let prec = op_prec(op);
            if prec < min_prec {
                break;
            }
            let op = op.clone();
            self.idx += 1;
            // All supported operators are left-associative.
            let right = self.op_expr(prec + 1)?;
            left = Expr::binop(op, left, right);
        }
        Ok(left)
    }

    /// `app_expr := atom+` (left-associative juxtaposition).
    fn app_expr(&mut self) -> Result<Expr, ParseError> {
        let mut acc = self.atom()?;
        while self.starts_atom() {
            let arg = self.atom()?;
            acc = Expr::app(acc, arg);
        }
        Ok(acc)
    }

    fn starts_atom(&self) -> bool {
        matches!(
            self.peek(),
            Some(Tok::Ident(_) | Tok::Nat(_) | Tok::Str(_) | Tok::LParen)
        )
    }

    /// `atom := nat | str | ident | '(' expr ')'`
    fn atom(&mut self) -> Result<Expr, ParseError> {
        let pos = self.peek_pos();
        match self.peek().cloned() {
            Some(Tok::Nat(n)) => {
                self.idx += 1;
                Ok(Expr::Lit(Lit::Nat(n)))
            }
            Some(Tok::Str(s)) => {
                self.idx += 1;
                Ok(Expr::Lit(Lit::Str(s)))
            }
            Some(Tok::Ident(name)) => {
                self.idx += 1;
                Ok(Expr::Var(name))
            }
            Some(Tok::LParen) => {
                self.idx += 1;
                let e = self.expr()?;
                self.expect(&Tok::RParen, "`)`")?;
                Ok(e)
            }
            _ => Err(ParseError::new("expected an expression", pos)),
        }
    }
}

fn op_prec(op: &str) -> u8 {
    match op {
        "==" => 4,
        "+" | "-" => 6,
        "*" => 7,
        _ => 0,
    }
}

/// Parse a single expression, requiring that all input is consumed.
pub fn parse_expr(src: &str) -> Result<Expr, ParseError> {
    let toks = lex(src)?;
    let mut p = Parser::new(toks, src.len());
    let e = p.expr()?;
    if p.idx != p.toks.len() {
        return Err(ParseError::new(
            "trailing input after expression",
            p.peek_pos(),
        ));
    }
    Ok(e)
}

/// Parse a whole module: newline-separated `name p1 p2 = expr` definitions.
///
/// Blank lines are ignored. A line whose first character is whitespace is
/// treated as a continuation of the previous definition (layout-lite).
pub fn parse_module(src: &str) -> Result<Module, ParseError> {
    let mut decls = Module::new();
    // Group physical lines into logical declarations, tracking the byte offset
    // of each group's start so errors point into the original source.
    let mut offset = 0usize;
    let mut groups: Vec<(usize, String)> = Vec::new();
    for line in src.split_inclusive('\n') {
        let trimmed = line.trim();
        let is_blank = trimmed.is_empty();
        let is_continuation = line.chars().next().is_some_and(|c| c == ' ' || c == '\t');
        if !is_blank && is_continuation && !groups.is_empty() {
            let last = groups.last_mut().unwrap();
            last.1.push(' ');
            last.1.push_str(trimmed);
        } else if !is_blank {
            groups.push((offset, trimmed.to_string()));
        }
        offset += line.len();
    }

    for (start, text) in groups {
        decls.push(parse_decl(&text, start)?);
    }
    Ok(decls)
}

/// Parse one declaration `name p1 p2 = expr`. `base` is the byte offset of the
/// declaration in the enclosing source, used to relocate error positions.
fn parse_decl(text: &str, base: usize) -> Result<Decl, ParseError> {
    let toks = lex(text).map_err(|e| relocate(e, base))?;
    let mut p = Parser::new(toks, text.len());

    let text_len = text.len();
    let name = match p.bump() {
        Some(Token {
            tok: Tok::Ident(n), ..
        }) => n.clone(),
        other => {
            let pos = other.map_or(text_len, |t| t.pos);
            return Err(relocate(
                ParseError::new("declaration must start with a name", pos),
                base,
            ));
        }
    };

    let mut params = Vec::new();
    loop {
        match p.peek() {
            Some(Tok::Ident(n)) => {
                params.push(n.clone());
                p.idx += 1;
            }
            Some(Tok::Equals) => {
                p.idx += 1;
                break;
            }
            _ => {
                return Err(relocate(
                    ParseError::new("expected a parameter name or `=`", p.peek_pos()),
                    base,
                ));
            }
        }
    }

    let body = p.expr().map_err(|e| relocate(e, base))?;
    if p.idx != p.toks.len() {
        return Err(relocate(
            ParseError::new("trailing input after declaration body", p.peek_pos()),
            base,
        ));
    }
    Ok(Decl { name, params, body })
}

fn relocate(mut e: ParseError, base: usize) -> ParseError {
    e.pos += base;
    e
}
