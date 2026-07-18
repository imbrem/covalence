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
//! - natural-number literals (`0`, `42`) — arbitrary precision (the
//!   covalence [`Nat`](covalence_types::Nat); there is no machine-integer
//!   cap);
//! - string literals (`"hi\n"`) with `\n \t \\ \" \r \0` escapes;
//! - lambdas `\x -> e` and the sugar `\x y -> e` (⇝ nested lambdas);
//! - application by juxtaposition, left-associative and tighter than any
//!   operator (`f x y` = `(f x) y`);
//! - parenthesisation `( e )`;
//! - `let x = e in e'` (a single, non-recursive binder);
//! - `if c then t else e` conditionals;
//! - list literals `[e1, e2, …]` (possibly empty), tuple literals
//!   `(e1, e2, …)` (two or more elements), and unit `()`;
//! - the infix operators `==` (prec 4), `+` `-` (prec 6, left-assoc), `*`
//!   (prec 7, left-assoc). Operator operands are applications, so a lambda or
//!   `let` must be parenthesised to sit under an operator (as in Haskell).
//! - `--` line comments and nested `{- … -}` block comments (skipped by the
//!   lexer, so they may appear anywhere whitespace may).
//!
//! Modules ([`parse_module`]): newline-separated top-level definitions
//! `name p1 p2 = expr`, one per logical line. A line indented relative to the
//! previous one continues it (layout-lite); there is no full layout algorithm.
//! A top-level **type-signature** line `name :: Ty` is parsed into a
//! [`Ty`](crate::ast::Ty) and attached to the following same-named definition
//! (its [`Decl::sig`](crate::ast::Decl::sig)); a lambda parameter may also be
//! type-annotated as `\(x :: Ty) -> e`.
//!
//! **Type expressions** ([`parse_ty`], the [`Ty`](crate::ast::Ty) grammar):
//!
//! ```text
//! ty      := ty_app ('->' ty)?         -- function arrow, right-assoc
//! ty_app  := ty_atom+                  -- constructor application `option a`
//! ty_atom := ident | '(' ty ')'
//! ```
//!
//! A bare identifier is a **type variable** unless it is a recognised base
//! type / constructor (`nat` `bool` `unit` `int` `bytes` `option` `list`) — the
//! dialect spells both lowercase, so the split is by that fixed table. There is
//! **no type inference**: a typed backend consumes exactly the written types.
//!
//! Everything else (do-notation, guards, `where`, `case`, pattern matching,
//! multi-clause definitions, full layout, `data`/`class`/`instance`) is out of
//! scope — see the crate the generated open-work index.

use covalence_types::Nat;

use crate::ast::{Decl, Expr, Item, Lit, Module, Theorem, ThmModule, Ty};

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
    Nat(Nat),
    Str(String),
    Lambda,
    Arrow,
    Equals,
    LParen,
    RParen,
    LBracket,
    RBracket,
    Comma,
    Op(String),
    Let,
    In,
    If,
    Then,
    Else,
    /// The `theorem` keyword introducing a theorem declaration.
    Theorem,
    /// The `axiom` keyword introducing an axiom declaration.
    Axiom,
    /// A `.` — separates a theorem/axiom name from its equation statement
    /// (`theorem NAME. <equation>`).
    Dot,
    /// A `::` type-signature / type-annotation separator. Its right-hand side
    /// is a type expression ([`Parser::ty`]): in a module a `name :: Ty` line
    /// attaches to the following definition, and in a lambda `\(x :: Ty) -> e`
    /// it annotates the binder.
    ColonColon,
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
            // `--` line comment: runs to end of line (but `-->` etc. are still
            // comments in this dialect — a `--` run always starts a comment).
            '-' if i + 1 < bytes.len() && bytes[i + 1] as char == '-' => {
                while i < bytes.len() && bytes[i] as char != '\n' {
                    i += 1;
                }
            }
            // `{- … -}` block comment, nesting-aware (Haskell semantics).
            '{' if i + 1 < bytes.len() && bytes[i + 1] as char == '-' => {
                let start = i;
                i += 2;
                let mut depth = 1u32;
                while i < bytes.len() && depth > 0 {
                    if i + 1 < bytes.len() && bytes[i] as char == '{' && bytes[i + 1] as char == '-'
                    {
                        depth += 1;
                        i += 2;
                    } else if i + 1 < bytes.len()
                        && bytes[i] as char == '-'
                        && bytes[i + 1] as char == '}'
                    {
                        depth -= 1;
                        i += 2;
                    } else {
                        i += 1;
                    }
                }
                if depth > 0 {
                    return Err(ParseError::new("unterminated block comment", start));
                }
            }
            '[' => {
                out.push(Token {
                    tok: Tok::LBracket,
                    pos: i,
                });
                i += 1;
            }
            ']' => {
                out.push(Token {
                    tok: Tok::RBracket,
                    pos: i,
                });
                i += 1;
            }
            ',' => {
                out.push(Token {
                    tok: Tok::Comma,
                    pos: i,
                });
                i += 1;
            }
            // A `.` separating a theorem/axiom name from its equation statement.
            // Not otherwise used in the dialect (no qualified names, no
            // composition operator), so it is unambiguous here.
            '.' => {
                out.push(Token {
                    tok: Tok::Dot,
                    pos: i,
                });
                i += 1;
            }
            ':' if i + 1 < bytes.len() && bytes[i + 1] as char == ':' => {
                out.push(Token {
                    tok: Tok::ColonColon,
                    pos: i,
                });
                i += 2;
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
                // Arbitrary precision — a digit run always parses.
                let n: Nat = text
                    .parse()
                    .map_err(|_| ParseError::new("invalid numeric literal", start))?;
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
                    "if" => Tok::If,
                    "then" => Tok::Then,
                    "else" => Tok::Else,
                    "theorem" => Tok::Theorem,
                    "axiom" => Tok::Axiom,
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
            other => Err(ParseError::new(
                format!("expected {what}, found {}", describe(other)),
                self.peek_pos(),
            )),
        }
    }

    /// `expr := lambda | let | if | opexpr`
    fn expr(&mut self) -> Result<Expr, ParseError> {
        match self.peek() {
            Some(Tok::Lambda) => self.lambda(),
            Some(Tok::Let) => self.let_expr(),
            Some(Tok::If) => self.if_expr(),
            _ => self.op_expr(0),
        }
    }

    /// `if := 'if' expr 'then' expr 'else' expr`
    fn if_expr(&mut self) -> Result<Expr, ParseError> {
        self.expect(&Tok::If, "`if`")?;
        let c = self.expr()?;
        self.expect(&Tok::Then, "`then`")?;
        let t = self.expr()?;
        self.expect(&Tok::Else, "`else`")?;
        let e = self.expr()?;
        Ok(Expr::if_(c, t, e))
    }

    /// `lambda := '\' ident+ '->' expr`
    fn lambda(&mut self) -> Result<Expr, ParseError> {
        self.expect(&Tok::Lambda, "`\\`")?;
        // Each parameter is a bare `x` (no annotation) or a parenthesised,
        // type-annotated `(x :: t)`.
        let mut params: Vec<(String, Option<Ty>)> = Vec::new();
        loop {
            match self.peek() {
                Some(Tok::Ident(name)) => {
                    params.push((name.clone(), None));
                    self.idx += 1;
                }
                Some(Tok::LParen) => {
                    self.idx += 1;
                    let end = self.end;
                    let name = match self.bump() {
                        Some(Token {
                            tok: Tok::Ident(n), ..
                        }) => n.clone(),
                        other => {
                            let pos = other.map_or(end, |t| t.pos);
                            return Err(ParseError::new(
                                "expected a parameter name after `(`",
                                pos,
                            ));
                        }
                    };
                    self.expect(&Tok::ColonColon, "`::`")?;
                    let ty = self.ty()?;
                    self.expect(&Tok::RParen, "`)`")?;
                    params.push((name, Some(ty)));
                }
                _ => break,
            }
        }
        if params.is_empty() {
            return Err(ParseError::new(
                "lambda needs at least one parameter",
                self.peek_pos(),
            ));
        }
        self.expect(&Tok::Arrow, "`->`")?;
        let body = self.expr()?;
        // Desugar `\x (y :: t) -> e` into nested single lambdas.
        let mut acc = body;
        for (p, ty) in params.into_iter().rev() {
            acc = Expr::Lam(p, ty, Box::new(acc));
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
            Some(Tok::Ident(_) | Tok::Nat(_) | Tok::Str(_) | Tok::LParen | Tok::LBracket)
        )
    }

    /// `atom := nat | str | ident | paren | list`
    ///
    /// `paren := '(' ')'                 -- unit`
    /// `       | '(' expr ')'            -- grouping`
    /// `       | '(' expr (',' expr)+ ')'-- tuple`
    /// `list  := '[' ']' | '[' expr (',' expr)* ']'`
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
            Some(Tok::LParen) => self.paren(),
            Some(Tok::LBracket) => self.list_lit(),
            other => Err(ParseError::new(
                format!("expected an expression, found {}", describe(other.as_ref())),
                pos,
            )),
        }
    }

    /// A parenthesized form: `()` (unit), `(e)` (grouping), or
    /// `(e1, e2, …)` (tuple).
    fn paren(&mut self) -> Result<Expr, ParseError> {
        self.expect(&Tok::LParen, "`(`")?;
        if self.peek() == Some(&Tok::RParen) {
            self.idx += 1;
            return Ok(Expr::Unit);
        }
        let first = self.expr()?;
        if self.peek() == Some(&Tok::RParen) {
            self.idx += 1;
            return Ok(first);
        }
        // A comma ⇒ tuple.
        let mut items = vec![first];
        while self.peek() == Some(&Tok::Comma) {
            self.idx += 1;
            items.push(self.expr()?);
        }
        self.expect(&Tok::RParen, "`)` or `,`")?;
        Ok(Expr::Tuple(items))
    }

    /// A list literal `[e1, e2, …]` (possibly empty).
    fn list_lit(&mut self) -> Result<Expr, ParseError> {
        self.expect(&Tok::LBracket, "`[`")?;
        let mut items = Vec::new();
        if self.peek() == Some(&Tok::RBracket) {
            self.idx += 1;
            return Ok(Expr::List(items));
        }
        items.push(self.expr()?);
        while self.peek() == Some(&Tok::Comma) {
            self.idx += 1;
            items.push(self.expr()?);
        }
        self.expect(&Tok::RBracket, "`]` or `,`")?;
        Ok(Expr::List(items))
    }

    // -- Type expressions -----------------------------------------------------

    /// `ty := ty_app ('->' ty)?` — the function arrow is right-associative.
    fn ty(&mut self) -> Result<Ty, ParseError> {
        let dom = self.ty_app()?;
        if self.peek() == Some(&Tok::Arrow) {
            self.idx += 1;
            let cod = self.ty()?;
            Ok(Ty::fun(dom, cod))
        } else {
            Ok(dom)
        }
    }

    /// `ty_app := ty_atom+` — juxtaposition is type-constructor application
    /// (`option a`, `list a`). A single atom is just that atom; a run applies
    /// the (identifier) head to the following atoms.
    fn ty_app(&mut self) -> Result<Ty, ParseError> {
        let head = self.ty_atom()?;
        if !self.starts_ty_atom() {
            return Ok(head);
        }
        // Applied form: the head must be a constructor identifier.
        let head_name = match head {
            Ty::Con(name, args) if args.is_empty() => name,
            Ty::Var(name) => name,
            _ => {
                return Err(ParseError::new(
                    "only a type constructor may be applied to arguments",
                    self.peek_pos(),
                ));
            }
        };
        let mut args = Vec::new();
        while self.starts_ty_atom() {
            args.push(self.ty_atom()?);
        }
        Ok(Ty::Con(head_name, args))
    }

    fn starts_ty_atom(&self) -> bool {
        matches!(self.peek(), Some(Tok::Ident(_) | Tok::LParen))
    }

    /// `ty_atom := ident | '(' ty ')'`. A bare identifier is a type variable
    /// unless it names a recognised base type / constructor (see
    /// [`is_known_tycon`]).
    fn ty_atom(&mut self) -> Result<Ty, ParseError> {
        let pos = self.peek_pos();
        match self.peek().cloned() {
            Some(Tok::Ident(name)) => {
                self.idx += 1;
                if is_known_tycon(&name) {
                    Ok(Ty::Con(name, Vec::new()))
                } else {
                    Ok(Ty::Var(name))
                }
            }
            Some(Tok::LParen) => {
                self.idx += 1;
                let inner = self.ty()?;
                self.expect(&Tok::RParen, "`)`")?;
                Ok(inner)
            }
            other => Err(ParseError::new(
                format!("expected a type, found {}", describe(other.as_ref())),
                pos,
            )),
        }
    }
}

/// Is `name` a recognised (built-in) type constructor, as opposed to a type
/// variable? The dialect uses lowercase spellings for both, so the split is by
/// this fixed table rather than by case. Anything else is a type *variable*.
fn is_known_tycon(name: &str) -> bool {
    matches!(
        name,
        "nat" | "bool" | "unit" | "int" | "bytes" | "option" | "list"
    )
}

/// A short human-readable name for a token (for error messages).
fn describe(t: Option<&Tok>) -> String {
    match t {
        None => "end of input".to_string(),
        Some(Tok::Ident(n)) => format!("identifier `{n}`"),
        Some(Tok::Nat(n)) => format!("number `{n}`"),
        Some(Tok::Str(_)) => "a string literal".to_string(),
        Some(Tok::Lambda) => "`\\`".to_string(),
        Some(Tok::Arrow) => "`->`".to_string(),
        Some(Tok::Equals) => "`=`".to_string(),
        Some(Tok::LParen) => "`(`".to_string(),
        Some(Tok::RParen) => "`)`".to_string(),
        Some(Tok::LBracket) => "`[`".to_string(),
        Some(Tok::RBracket) => "`]`".to_string(),
        Some(Tok::Comma) => "`,`".to_string(),
        Some(Tok::Op(op)) => format!("operator `{op}`"),
        Some(Tok::Let) => "`let`".to_string(),
        Some(Tok::In) => "`in`".to_string(),
        Some(Tok::If) => "`if`".to_string(),
        Some(Tok::Then) => "`then`".to_string(),
        Some(Tok::Else) => "`else`".to_string(),
        Some(Tok::ColonColon) => "`::`".to_string(),
        Some(Tok::Theorem) => "`theorem`".to_string(),
        Some(Tok::Axiom) => "`axiom`".to_string(),
        Some(Tok::Dot) => "`.`".to_string(),
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

/// Parse a single **type expression** (the [`Ty`] grammar: type variables,
/// base/applied constructors, function arrows), requiring that all input is
/// consumed. Used by module signatures and annotated lambda parameters.
pub fn parse_ty(src: &str) -> Result<Ty, ParseError> {
    let toks = lex(src)?;
    let mut p = Parser::new(toks, src.len());
    let t = p.ty()?;
    if p.idx != p.toks.len() {
        return Err(ParseError::new("trailing input after type", p.peek_pos()));
    }
    Ok(t)
}

/// Split source into logical-declaration groups (comment-blanked, layout-lite
/// continuation), each tagged with its byte offset in the original source.
///
/// Shared by [`parse_module`] and [`parse_items`]: blank out comments first
/// (preserving byte offsets and newlines) so a `{- … -}` block comment may span
/// physical lines without derailing the continuation logic, then group physical
/// lines — a line beginning with whitespace continues the previous group.
fn group_declarations(src: &str) -> Result<Vec<(usize, String)>, ParseError> {
    let blanked = strip_comments_to_spaces(src)?;
    let src: &str = &blanked;
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
    Ok(groups)
}

/// Parse a whole module: newline-separated `name p1 p2 = expr` definitions.
///
/// Blank lines are ignored. A line whose first character is whitespace is
/// treated as a continuation of the previous definition (layout-lite). Theorem
/// / axiom declarations are **ignored** by this entry point — use
/// [`parse_items`] to get the definition-**and**-theorem view.
pub fn parse_module(src: &str) -> Result<Module, ParseError> {
    let items = parse_items(src)?;
    Ok(items
        .into_iter()
        .filter_map(|it| match it {
            Item::Def(d) => Some(d),
            Item::Thm(_) => None,
        })
        .collect())
}

/// Parse a whole module into the richer **definition-and-theorem** view: a
/// sequence of [`Item`]s (value definitions and `theorem` / `axiom`
/// declarations) in source order.
///
/// This is the surface the proof linker consumes: theorem statements are the
/// stable interface, their proofs supplied externally (in the S-expression
/// proof file) and linked by name. Signatures (`name :: Ty`) attach to the
/// following same-named definition **or** theorem.
pub fn parse_items(src: &str) -> Result<ThmModule, ParseError> {
    let groups = group_declarations(src)?;
    let mut items = ThmModule::new();
    // A pending signature `name :: Ty` attaches to the next definition or
    // theorem of the same name (Haskell convention: the signature precedes it).
    let mut pending_sig: Option<(String, Ty)> = None;
    for (start, text) in groups {
        match parse_decl(&text, start)? {
            DeclItem::Sig(name, ty) => {
                pending_sig = Some((name, ty));
            }
            DeclItem::Def(mut d) => {
                if let Some((sig_name, ty)) = pending_sig.take()
                    && sig_name == d.name
                {
                    d.sig = Some(ty);
                }
                items.push(Item::Def(d));
            }
            DeclItem::Thm(mut t) => {
                if let Some((sig_name, ty)) = pending_sig.take()
                    && sig_name == t.name
                {
                    t.sig = Some(ty);
                }
                items.push(Item::Thm(t));
            }
        }
    }
    Ok(items)
}

/// One parsed top-level item: a type signature `name :: Ty` (attached to the
/// following definition/theorem), a value definition, or a theorem/axiom.
enum DeclItem {
    Sig(String, Ty),
    Def(Decl),
    Thm(Theorem),
}

/// Parse one top-level item — either a value definition `name p1 p2 = expr` or
/// a type-signature line `name :: Ty`. `base` is the byte offset of the item in
/// the enclosing source, used to relocate error positions.
///
/// A signature is now **parsed into a [`Ty`]** (no longer discarded): the type
/// is checked and returned so [`parse_module`] can attach it to the following
/// definition of the same name.
fn parse_decl(text: &str, base: usize) -> Result<DeclItem, ParseError> {
    let toks = lex(text).map_err(|e| relocate(e, base))?;
    let mut p = Parser::new(toks, text.len());

    // A theorem / axiom declaration: `theorem NAME. <equation>`. Its statement
    // reuses the EXPRESSION grammar (`p.expr()`), NOT the type grammar — a
    // theorem states an equation, not a type.
    if matches!(p.peek(), Some(Tok::Theorem | Tok::Axiom)) {
        let axiom = p.peek() == Some(&Tok::Axiom);
        p.idx += 1;
        let end = text.len();
        let name = match p.bump() {
            Some(Token {
                tok: Tok::Ident(n), ..
            }) => n.clone(),
            other => {
                let pos = other.map_or(end, |t| t.pos);
                let kw = if axiom { "axiom" } else { "theorem" };
                return Err(relocate(
                    ParseError::new(format!("expected a name after `{kw}`"), pos),
                    base,
                ));
            }
        };
        p.expect(&Tok::Dot, "`.` after the theorem name")
            .map_err(|e| relocate(e, base))?;
        let statement = p.expr().map_err(|e| relocate(e, base))?;
        if p.idx != p.toks.len() {
            return Err(relocate(
                ParseError::new("trailing input after theorem statement", p.peek_pos()),
                base,
            ));
        }
        return Ok(DeclItem::Thm(Theorem {
            name,
            statement,
            sig: None,
            axiom,
        }));
    }

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

    // A type-signature line `name :: Ty` — parse the type and hand it back.
    if p.peek() == Some(&Tok::ColonColon) {
        p.idx += 1;
        let ty = p.ty().map_err(|e| relocate(e, base))?;
        if p.idx != p.toks.len() {
            return Err(relocate(
                ParseError::new("trailing input after type signature", p.peek_pos()),
                base,
            ));
        }
        return Ok(DeclItem::Sig(name, ty));
    }

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
    Ok(DeclItem::Def(Decl {
        name,
        params,
        body,
        sig: None,
    }))
}

fn relocate(mut e: ParseError, base: usize) -> ParseError {
    e.pos += base;
    e
}

/// Replace every comment (`--` line, `{- … -}` nested block) with spaces,
/// preserving byte offsets, newlines, and all non-comment bytes verbatim.
///
/// This is applied by [`parse_module`] before the line grouper so that
/// comments — including block comments that span physical lines — never
/// disturb the layout-lite continuation logic, while error positions still
/// point into the original source. Strings are respected (a `--` or `{-`
/// inside a string literal is not a comment).
fn strip_comments_to_spaces(src: &str) -> Result<String, ParseError> {
    let bytes = src.as_bytes();
    // Start from an exact byte-length copy; overwrite only comment bytes.
    let mut out: Vec<u8> = bytes.to_vec();
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            // A string literal — copy through untouched (offsets already match).
            b'"' => {
                i += 1;
                while i < bytes.len() && bytes[i] != b'"' {
                    if bytes[i] == b'\\' {
                        i += 1;
                    }
                    i += 1;
                }
                if i < bytes.len() {
                    i += 1; // closing quote
                }
            }
            b'-' if i + 1 < bytes.len() && bytes[i + 1] == b'-' => {
                while i < bytes.len() && bytes[i] != b'\n' {
                    out[i] = b' ';
                    i += 1;
                }
            }
            b'{' if i + 1 < bytes.len() && bytes[i + 1] == b'-' => {
                let start = i;
                let mut depth = 1u32;
                out[i] = b' ';
                out[i + 1] = b' ';
                i += 2;
                while i < bytes.len() && depth > 0 {
                    if i + 1 < bytes.len() && bytes[i] == b'{' && bytes[i + 1] == b'-' {
                        depth += 1;
                        out[i] = b' ';
                        out[i + 1] = b' ';
                        i += 2;
                    } else if i + 1 < bytes.len() && bytes[i] == b'-' && bytes[i + 1] == b'}' {
                        depth -= 1;
                        out[i] = b' ';
                        out[i + 1] = b' ';
                        i += 2;
                    } else {
                        // Preserve newlines so line structure survives.
                        if bytes[i] != b'\n' {
                            out[i] = b' ';
                        }
                        i += 1;
                    }
                }
                if depth > 0 {
                    return Err(ParseError::new("unterminated block comment", start));
                }
            }
            _ => i += 1,
        }
    }
    // The overwrite kept the buffer valid UTF-8 (only ASCII bytes were touched,
    // and only outside multi-byte sequences since delimiters are all ASCII).
    Ok(String::from_utf8(out).expect("comment blanking preserves UTF-8"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn strip_comments_preserves_length_and_strings() {
        // Byte offsets are preserved: only comment bytes become spaces.
        let src = "a -- c\nb {- x -} c";
        let out = strip_comments_to_spaces(src).unwrap();
        assert_eq!(out.len(), src.len());
        assert_eq!(out, "a     \nb         c");
        // A `--` / `{-` inside a string literal is NOT a comment.
        let src = r#"x = "a -- b {- c"#.to_string() + "\"";
        assert_eq!(strip_comments_to_spaces(&src).unwrap(), src);
    }

    #[test]
    fn unterminated_block_comment_errors() {
        let err = strip_comments_to_spaces("a {- oops").unwrap_err();
        assert!(err.message.contains("unterminated block comment"));
        assert_eq!(err.pos, 2);
    }

    #[test]
    fn nested_block_comment_lexes_as_whitespace() {
        // `f {- a {- b -} c -} x` ⇒ just `f x` after comment removal.
        let toks = lex("f {- a {- b -} c -} x").unwrap();
        let kinds: Vec<_> = toks.into_iter().map(|t| t.tok).collect();
        assert_eq!(kinds, vec![Tok::Ident("f".into()), Tok::Ident("x".into())]);
    }

    #[test]
    fn signature_line_offsets_are_relocated() {
        // The bad token is in the SECOND definition; its position must point
        // past the signature line (relocation works).
        let src = "f :: nat\nf = )";
        let err = parse_module(src).unwrap_err();
        assert!(err.pos >= "f :: nat\n".len(), "pos was {}", err.pos);
    }

    // -- Type-expression parsing --------------------------------------------

    #[test]
    fn parses_base_and_variable_types() {
        // Known constructors are `Con`; anything else is a variable.
        assert_eq!(parse_ty("nat").unwrap(), Ty::base("nat"));
        assert_eq!(parse_ty("bool").unwrap(), Ty::base("bool"));
        assert_eq!(parse_ty("a").unwrap(), Ty::var("a"));
        assert_eq!(parse_ty("mcar").unwrap(), Ty::var("mcar"));
    }

    #[test]
    fn parses_function_and_applied_types() {
        // `->` is right-associative.
        assert_eq!(
            parse_ty("a -> a -> a").unwrap(),
            Ty::fun(Ty::var("a"), Ty::fun(Ty::var("a"), Ty::var("a")))
        );
        // Constructor application: `option a`, `list a`.
        assert_eq!(
            parse_ty("option a").unwrap(),
            Ty::con("option", vec![Ty::var("a")])
        );
        // Application binds tighter than the arrow, and parens group.
        assert_eq!(
            parse_ty("(a -> option a) -> option a").unwrap(),
            Ty::fun(
                Ty::fun(Ty::var("a"), Ty::con("option", vec![Ty::var("a")])),
                Ty::con("option", vec![Ty::var("a")]),
            )
        );
    }

    #[test]
    fn type_parse_errors_have_positions() {
        assert!(parse_ty("").is_err());
        // A dangling arrow.
        assert!(parse_ty("a ->").is_err());
        // Trailing junk.
        assert_eq!(
            parse_ty("a )").unwrap_err().message,
            "trailing input after type"
        );
    }

    #[test]
    fn signature_attaches_to_following_definition() {
        let m = parse_module("f :: nat -> nat\nf x = x").unwrap();
        assert_eq!(m.len(), 1);
        assert_eq!(m[0].sig, Some(Ty::fun(Ty::base("nat"), Ty::base("nat"))));
    }

    #[test]
    fn mismatched_signature_name_is_not_attached() {
        // A signature for `g` does not attach to a definition of `f`.
        let m = parse_module("g :: nat\nf x = x").unwrap();
        assert_eq!(m.len(), 1);
        assert_eq!(m[0].name, "f");
        assert_eq!(m[0].sig, None);
    }

    // -- Theorem / axiom declarations ---------------------------------------

    #[test]
    fn parses_theorem_equation_statement() {
        // A theorem's statement is an EQUATION expression, not a type.
        let items = parse_items("theorem add_base. 0 + m == m").unwrap();
        assert_eq!(items.len(), 1);
        let Item::Thm(t) = &items[0] else {
            panic!("expected a theorem item")
        };
        assert_eq!(t.name, "add_base");
        assert!(!t.axiom);
        // `0 + m == m` parses as `(0 + m) == m` — a `==` BinOp at the top.
        assert_eq!(
            t.statement,
            Expr::binop(
                "==",
                Expr::binop("+", Expr::Lit(Lit::Nat(0u64.into())), Expr::Var("m".into())),
                Expr::Var("m".into()),
            )
        );
    }

    #[test]
    fn parses_axiom_and_attaches_signature() {
        let src = "peano :: nat\naxiom refl_zero. 0 == 0";
        let items = parse_items(src).unwrap();
        // Signature name `peano` does not match `refl_zero`, so it is dropped.
        assert_eq!(items.len(), 1);
        let Item::Thm(t) = &items[0] else {
            panic!("expected a theorem item")
        };
        assert!(t.axiom);
        assert_eq!(t.sig, None);

        // A matching signature attaches.
        let items = parse_items("thm :: nat\ntheorem thm. 0 == 0").unwrap();
        let Item::Thm(t) = &items[0] else {
            panic!("theorem")
        };
        assert_eq!(t.sig, Some(Ty::base("nat")));
    }

    #[test]
    fn parse_module_ignores_theorems() {
        // The legacy definition-only view skips theorem declarations.
        let src = "f x = x\ntheorem t. 0 == 0";
        let m = parse_module(src).unwrap();
        assert_eq!(m.len(), 1);
        assert_eq!(m[0].name, "f");
    }

    #[test]
    fn theorem_needs_a_dot() {
        // `theorem NAME <equation>` without the `.` is a parse error.
        assert!(parse_items("theorem t 0 == 0").is_err());
    }

    #[test]
    fn annotated_lambda_param_carries_its_type() {
        // `\(x :: a) -> x` desugars to an annotated single lambda.
        let e = parse_expr(r"\(x :: a) -> x").unwrap();
        assert_eq!(e, Expr::lam_ty("x", Ty::var("a"), Expr::Var("x".into())));
        // Mixed: bare then annotated.
        let e2 = parse_expr(r"\f (x :: a) -> f x").unwrap();
        assert_eq!(
            e2,
            Expr::lam(
                "f",
                Expr::lam_ty(
                    "x",
                    Ty::var("a"),
                    Expr::app(Expr::Var("f".into()), Expr::Var("x".into())),
                ),
            )
        );
    }
}
