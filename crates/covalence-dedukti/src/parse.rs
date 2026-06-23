//! The `.dk` parser: a token stream → a [`Signature`].
//!
//! A hand-written recursive-descent parser over the [`lex`](crate::lex) token
//! stream, following Dedukti's grammar (see the crate docs). Operator
//! precedence: application binds tighter than the products `->` (right
//! associative) and abstractions `=>`, which bind loosest. A leading
//! `pid :` / `pid =>` selects a binder form; otherwise a term is an application
//! optionally followed by `-> codomain`.

use crate::entry::{
    Claim, Command, ContextVar, DeclKind, Declaration, Definition, Entry, Param, RewriteRule,
    Signature, Theorem,
};
use crate::error::DkError;
use crate::lex::{Spanned, Tok, lex};
use crate::term::{Ref, Symbol, Term};

/// Parse a `.dk` source into a [`Signature`].
pub fn parse(src: &str) -> Result<Signature, DkError> {
    let toks = lex(src)?;
    let mut p = Parser { src, toks, pos: 0, allow_bracket: false };
    let mut entries = Vec::new();
    while p.peek().is_some() {
        entries.push(p.entry()?);
    }
    Ok(Signature { entries })
}

struct Parser<'a> {
    src: &'a str,
    toks: Vec<Spanned>,
    pos: usize,
    /// Whether `{ … }` bracketed (dot/guard) patterns are permitted here. Only
    /// true while parsing a rewrite-rule left-hand side; elsewhere a `{` is a
    /// named-rule marker or invalid, never an atomic term — so an rhs like
    /// `--> zero {next} […]` does not absorb the next rule's `{name}`.
    allow_bracket: bool,
}

type R<T> = Result<T, DkError>;

impl Parser<'_> {
    // --- token cursor ---

    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.pos).map(|s| &s.tok)
    }

    fn peek_at(&self, n: usize) -> Option<&Tok> {
        self.toks.get(self.pos + n).map(|s| &s.tok)
    }

    fn bump(&mut self) -> Option<Spanned> {
        let s = self.toks.get(self.pos).cloned();
        if s.is_some() {
            self.pos += 1;
        }
        s
    }

    /// Byte offset of the current token (end-of-source if exhausted).
    fn pos_byte(&self) -> usize {
        self.toks.get(self.pos).map(|s| s.start).unwrap_or(self.src.len())
    }

    fn unexpected<T>(&self, expected: &str) -> R<T> {
        match self.toks.get(self.pos) {
            Some(s) => Err(DkError::Unexpected {
                pos: s.start,
                expected: expected.to_string(),
                found: s.tok.describe(),
            }),
            None => Err(DkError::UnexpectedEof { expected: expected.to_string() }),
        }
    }

    fn expect(&mut self, want: &Tok, label: &str) -> R<()> {
        if self.peek() == Some(want) {
            self.bump();
            Ok(())
        } else {
            self.unexpected(label)
        }
    }

    /// Consume a plain identifier (used for binder/parameter names).
    fn ident(&mut self) -> R<Symbol> {
        match self.peek() {
            Some(Tok::Ident(_)) => match self.bump().unwrap().tok {
                Tok::Ident(s) => Ok(s),
                _ => unreachable!(),
            },
            _ => self.unexpected("an identifier"),
        }
    }

    /// Consume an identifier or qualified identifier as a [`Ref`].
    fn ref_ident(&mut self) -> R<Ref> {
        match self.peek() {
            Some(Tok::Ident(_)) | Some(Tok::Qid(..)) => match self.bump().unwrap().tok {
                Tok::Ident(s) => Ok(Ref::new(s)),
                Tok::Qid(m, n) => Ok(Ref::qualified(m, n)),
                _ => unreachable!(),
            },
            _ => self.unexpected("an identifier"),
        }
    }

    /// Consume a module name (an identifier; a qualified name is rendered
    /// `m.n`). Used by `#NAME` / `#REQUIRE`.
    fn module_name(&mut self) -> R<Symbol> {
        match self.peek() {
            Some(Tok::Ident(_)) | Some(Tok::Qid(..)) => match self.bump().unwrap().tok {
                Tok::Ident(s) => Ok(s),
                Tok::Qid(m, n) => Ok(Symbol::new(format!("{m}.{n}"))),
                _ => unreachable!(),
            },
            _ => self.unexpected("a module name"),
        }
    }

    // --- entries ---

    fn entry(&mut self) -> R<Entry> {
        match self.peek() {
            Some(Tok::Def) => {
                self.bump();
                self.definition()
            }
            Some(Tok::Thm) => {
                self.bump();
                self.theorem()
            }
            Some(Tok::Inj) => {
                self.bump();
                self.declaration(DeclKind::Injective)
            }
            Some(Tok::DefAc) => {
                self.bump();
                self.defac(false)
            }
            Some(Tok::DefAcU) => {
                self.bump();
                self.defac(true)
            }
            Some(Tok::LSquare) | Some(Tok::LBrace) => Ok(Entry::Rules(self.rules()?)),
            Some(Tok::Command(_)) => self.command(),
            Some(Tok::Ident(_)) => self.declaration(DeclKind::Static),
            _ => self.unexpected("a top-level entry (declaration, def, thm, rule, or #command)"),
        }
    }

    /// `name params : ty .` (the `injective`/AC keyword, if any, is already
    /// consumed; `kind` says which).
    fn declaration(&mut self, kind: DeclKind) -> R<Entry> {
        let name = self.ident()?;
        let params = self.params()?;
        self.expect(&Tok::Colon, "`:` before the declared type")?;
        let ty = self.term()?;
        self.expect(&Tok::Dot, "`.` to end the declaration")?;
        Ok(Entry::Declaration(Declaration { name, params, ty, kind }))
    }

    /// `def name params [: ty] [:= body] .`
    fn definition(&mut self) -> R<Entry> {
        let name = self.ident()?;
        let params = self.params()?;
        let ty = if self.peek() == Some(&Tok::Colon) {
            self.bump();
            Some(self.term()?)
        } else {
            None
        };
        let body = if self.peek() == Some(&Tok::Assign) {
            self.bump();
            Some(self.term()?)
        } else {
            None
        };
        if ty.is_none() && body.is_none() {
            return Err(DkError::Parse {
                pos: self.pos_byte(),
                message: format!("definition `{name}` needs a type (`: ty`) or a body (`:= term`)"),
            });
        }
        self.expect(&Tok::Dot, "`.` to end the definition")?;
        Ok(Entry::Definition(Definition { name, params, ty, body }))
    }

    /// `thm name params [: ty] := body .`
    fn theorem(&mut self) -> R<Entry> {
        let name = self.ident()?;
        let params = self.params()?;
        let ty = if self.peek() == Some(&Tok::Colon) {
            self.bump();
            Some(self.term()?)
        } else {
            None
        };
        self.expect(&Tok::Assign, "`:=` before the proof term")?;
        let body = self.term()?;
        self.expect(&Tok::Dot, "`.` to end the theorem")?;
        Ok(Entry::Theorem(Theorem { name, params, ty, body }))
    }

    /// `defac name [ operand_ty ] .` / `defacu name [ operand_ty , neutral ] .`
    /// (the keyword is already consumed; `unital` selects the `defacu` form).
    fn defac(&mut self, unital: bool) -> R<Entry> {
        let name = self.ident()?;
        self.expect(&Tok::LSquare, "`[` before the AC operand type")?;
        let ty = self.term()?;
        let kind = if unital {
            self.expect(&Tok::Comma, "`,` before the neutral element")?;
            let neutral = self.term()?;
            DeclKind::AcU(Box::new(neutral))
        } else {
            DeclKind::Ac
        };
        self.expect(&Tok::RSquare, "`]` after the AC declaration")?;
        self.expect(&Tok::Dot, "`.` to end the declaration")?;
        Ok(Entry::Declaration(Declaration { name, params: Vec::new(), ty, kind }))
    }

    /// Zero or more `(name : ty)` parameters.
    fn params(&mut self) -> R<Vec<Param>> {
        let mut v = Vec::new();
        while self.peek() == Some(&Tok::LParen) {
            self.bump();
            let name = self.ident()?;
            self.expect(&Tok::Colon, "`:` in a parameter")?;
            let ty = self.term()?;
            self.expect(&Tok::RParen, "`)` to close a parameter")?;
            v.push(Param { name, ty });
        }
        Ok(v)
    }

    /// One or more rewrite rules sharing a terminating `.`.
    fn rules(&mut self) -> R<Vec<RewriteRule>> {
        let mut rules = Vec::new();
        loop {
            let name = if self.peek() == Some(&Tok::LBrace) {
                self.bump();
                let r = self.ref_ident()?;
                self.expect(&Tok::RBrace, "`}` to close the rule name")?;
                Some(r)
            } else {
                None
            };
            self.expect(&Tok::LSquare, "`[` to open the rule context")?;
            let context = self.context()?;
            self.expect(&Tok::RSquare, "`]` to close the rule context")?;
            self.allow_bracket = true;
            let lhs = self.term()?;
            self.allow_bracket = false;
            self.expect(&Tok::LongArrow, "`-->` in a rewrite rule")?;
            let rhs = self.term()?;
            rules.push(RewriteRule { name, context, lhs, rhs });
            match self.peek() {
                Some(Tok::LBrace) | Some(Tok::LSquare) => continue,
                Some(Tok::Dot) => {
                    self.bump();
                    return Ok(rules);
                }
                _ => return self.unexpected("`.` or the next rewrite rule"),
            }
        }
    }

    /// A rewrite-rule context: comma-separated `name` or `name : ty`.
    fn context(&mut self) -> R<Vec<ContextVar>> {
        let mut v = Vec::new();
        if self.peek() == Some(&Tok::RSquare) {
            return Ok(v);
        }
        loop {
            let name = self.ident()?;
            let ty = if self.peek() == Some(&Tok::Colon) {
                self.bump();
                Some(self.term()?)
            } else {
                None
            };
            v.push(ContextVar { name, ty });
            if self.peek() == Some(&Tok::Comma) {
                self.bump();
                continue;
            }
            return Ok(v);
        }
    }

    // --- commands ---

    fn command(&mut self) -> R<Entry> {
        let name = match self.bump().unwrap().tok {
            Tok::Command(s) => s,
            _ => unreachable!(),
        };
        let cmd = match name.as_str() {
            "NAME" => {
                let m = self.module_name()?;
                Command::Name(m)
            }
            "REQUIRE" => {
                let m = self.module_name()?;
                Command::Require(m)
            }
            "EVAL" => {
                let config = self.eval_config()?;
                let term = self.term()?;
                Command::Eval { config, term }
            }
            "INFER" => {
                let config = self.eval_config()?;
                let term = self.term()?;
                Command::Infer { config, term }
            }
            "CHECK" | "CHECKNOT" | "ASSERT" | "ASSERTNOT" => {
                let assert = name.starts_with("ASSERT");
                let negated = name.ends_with("NOT");
                let left = self.aterm()?;
                let claim = match self.peek() {
                    Some(Tok::Colon) => {
                        self.bump();
                        Claim::HasType(left, self.term()?)
                    }
                    Some(Tok::Equal) => {
                        self.bump();
                        Claim::Convertible(left, self.term()?)
                    }
                    _ => return self.unexpected("`:` or `==` in a check"),
                };
                Command::Check { assert, negated, claim }
            }
            "PRINT" => match self.peek() {
                Some(Tok::Str(_)) => match self.bump().unwrap().tok {
                    Tok::Str(s) => Command::Print(s),
                    _ => unreachable!(),
                },
                _ => return self.unexpected("a string literal"),
            },
            "GDT" => Command::Gdt(self.ref_ident()?),
            _ => {
                // Unknown / future directive: skip its arguments up to the `.`.
                while !matches!(self.peek(), Some(Tok::Dot) | None) {
                    self.bump();
                }
                Command::Other(name)
            }
        };
        self.expect(&Tok::Dot, "`.` to end the command")?;
        Ok(Entry::Command(cmd))
    }

    /// An optional `[config]` after `#EVAL`/`#INFER`, captured raw.
    fn eval_config(&mut self) -> R<Option<String>> {
        if self.peek() != Some(&Tok::LSquare) {
            return Ok(None);
        }
        let lo = self.bump().unwrap().end; // just past `[`
        while !matches!(self.peek(), Some(Tok::RSquare) | None) {
            self.bump();
        }
        let hi = match self.toks.get(self.pos) {
            Some(s) => s.start, // just before `]`
            None => return Err(DkError::UnexpectedEof { expected: "`]`".into() }),
        };
        self.bump(); // `]`
        Ok(Some(self.src[lo..hi].trim().to_string()))
    }

    // --- terms ---

    /// A full term: a binder (`pid : dom -> cod`, `pid : dom => body`,
    /// `pid => body`) or an application optionally followed by `-> codomain`.
    fn term(&mut self) -> R<Term> {
        // Binder lookahead: a bare identifier followed by `=>` or `:`.
        if matches!(self.peek(), Some(Tok::Ident(_))) {
            match self.peek_at(1) {
                Some(Tok::FatArrow) => {
                    let b = self.ident()?;
                    self.bump(); // `=>`
                    let body = self.term()?;
                    return Ok(Term::abs(Some(b), None, body));
                }
                Some(Tok::Colon) => {
                    let b = self.ident()?;
                    self.bump(); // `:`
                    let dom = self.aterm()?;
                    match self.peek() {
                        Some(Tok::Arrow) => {
                            self.bump();
                            let cod = self.term()?;
                            return Ok(Term::pi(Some(b), dom, cod));
                        }
                        Some(Tok::FatArrow) => {
                            self.bump();
                            let body = self.term()?;
                            return Ok(Term::abs(Some(b), Some(dom), body));
                        }
                        _ => return self.unexpected("`->` or `=>` after a typed binder"),
                    }
                }
                _ => {}
            }
        }

        let head = self.aterm()?;
        if self.peek() == Some(&Tok::Arrow) {
            self.bump();
            let cod = self.term()?;
            Ok(Term::pi(None, head, cod))
        } else {
            Ok(head)
        }
    }

    /// An application: one or more atomic terms, left-associated.
    fn aterm(&mut self) -> R<Term> {
        let mut t = self.sterm()?;
        while self.starts_sterm() {
            let a = self.sterm()?;
            t = Term::app(t, a);
        }
        Ok(t)
    }

    fn starts_sterm(&self) -> bool {
        match self.peek() {
            Some(Tok::Type | Tok::Ident(_) | Tok::Qid(..) | Tok::LParen) => true,
            Some(Tok::LBrace) => self.allow_bracket,
            _ => false,
        }
    }

    /// An atomic term: `Type`, an identifier, `( term )`, or `{ term }`.
    fn sterm(&mut self) -> R<Term> {
        match self.peek() {
            Some(Tok::Type) => {
                self.bump();
                Ok(Term::Type)
            }
            Some(Tok::Ident(_)) | Some(Tok::Qid(..)) => Ok(Term::Ref(self.ref_ident()?)),
            Some(Tok::LParen) => {
                self.bump();
                let t = self.term()?;
                self.expect(&Tok::RParen, "`)` to close a parenthesised term")?;
                Ok(t)
            }
            Some(Tok::LBrace) if self.allow_bracket => {
                self.bump();
                // Brackets nest a full term; their content is an ordinary term,
                // not itself a pattern, so suspend bracket mode inside.
                let saved = self.allow_bracket;
                self.allow_bracket = false;
                let t = self.term()?;
                self.allow_bracket = saved;
                self.expect(&Tok::RBrace, "`}` to close a bracketed pattern")?;
                Ok(Term::Bracket(Box::new(t)))
            }
            _ => self.unexpected("a term"),
        }
    }
}
