//! SpecTec parser.
//!
//! Style: hand-rolled combinator style. Each sub-parser is a pure
//! function `fn(&mut &[Spanned]) -> Result<T, Diagnostic>` — input
//! slice goes in, residual slice comes out via the `&mut`. No traits,
//! no interior mutability, no `unsafe`. Designed to mirror the textbook
//! parser-combinator shape `Tokens → Result<(T, Tokens), Err>`, which
//! ports cleanly to a kernel-verifiable function later.
//!
//! Top-level forms covered structurally:
//!
//! - `syntax NAME[/profile][(params)] [hint(...)]* [= variant|record|alias]`
//! - `def $NAME[(arg_tys)] : ret_ty [hint(...)]*` (signature, args optional)
//! - `def $NAME[(pats)] = rhs [-- premise]*` (clause)
//! - `var NAME : type [hints*]`
//! - `relation NAME: <mixfix-template> [hints*]`
//! - `rule NAME[/case]: <conclusion> [-- premise]* [hints*]`
//! - `grammar NAME[/case][(params)] : ret [hints*] [= productions]`
//!
//! BinderHint bodies are kept as opaque `TokenRun`s here; the elaborator in
//! [`crate::elab`] further structures rule bodies, expression
//! positions, and constructor applications using the mixfix `OpTable`
//! built from `relation` and `syntax`-variant declarations.

use crate::cst::{
    Alt, DefClause, DefSig, GrammarDecl, HintAtom, Ident, RecordField, RecordSlot, RelationDecl,
    RuleDecl, SyntaxBody, SyntaxDecl, TokenRun, Top, VarDecl,
};
use crate::source::{Diagnostic, FileId, Span};
use crate::token::{Spanned, Token};

/// Parse a full token stream into top-level forms.
pub fn parse(file: FileId, tokens: Vec<Spanned>) -> Result<Vec<Top>, Diagnostic> {
    let mut input: &[Spanned] = &tokens;
    let mut tops = Vec::new();
    while !input.is_empty() {
        let top = parse_top(file, &mut input)?;
        tops.push(top);
    }
    Ok(tops)
}

// ---------- core helpers ----------

/// Look at the next token without consuming.
fn peek(input: &[Spanned]) -> Option<&Spanned> {
    input.first()
}

/// Construct a diagnostic at the end of `file`.
fn eof_diag(file: FileId, msg: impl Into<String>) -> Diagnostic {
    Diagnostic::error(Span::new(file, u32::MAX, u32::MAX), msg)
}

/// Consume the next token if it equals `expected`. Returns its span.
fn eat(input: &mut &[Spanned], expected: &Token) -> Option<Span> {
    match input.first() {
        Some(s) if &s.token == expected => {
            let span = s.span;
            *input = &input[1..];
            Some(span)
        }
        _ => None,
    }
}

/// Consume the next token if it equals `expected`, otherwise diagnose.
fn expect(input: &mut &[Spanned], file: FileId, expected: &Token) -> Result<Span, Diagnostic> {
    match input.first() {
        Some(s) if &s.token == expected => {
            let span = s.span;
            *input = &input[1..];
            Ok(span)
        }
        Some(s) => Err(Diagnostic::error(
            s.span,
            format!(
                "expected {}, found {}",
                expected.describe(),
                s.token.describe()
            ),
        )),
        None => Err(eof_diag(file, format!("expected {}", expected.describe()))),
    }
}

/// Consume an identifier OR a keyword used in identifier position.
///
/// SpecTec lets reserved words appear as names after `$` and a handful of
/// other contexts (`def $var(...)` is common in the spec's notation
/// chapter). A leading backtick also escapes a reserved word into a name
/// (e.g. `` syntax `syntax = () ``). Accept any token whose textual
/// representation works as an identifier.
fn parse_ident_or_keyword(input: &mut &[Spanned], file: FileId) -> Result<Ident, Diagnostic> {
    // Backtick escape: `` ` `` followed by an identifier, a keyword, or
    // certain punctuation tokens like `...` (`` `... `` is a real
    // identifier in `X.1-notation.syntax.spectec` line 18).
    if let Some(Spanned {
        token: Token::Backtick,
        span: bt_span,
    }) = input.first()
    {
        let bt_span = *bt_span;
        // First check special-case escapes that aren't idents/keywords.
        if let Some(Spanned {
            token: Token::DotDotDot,
            span: tail,
        }) = input.get(1)
        {
            let span = bt_span.join(*tail);
            *input = &input[2..];
            return Ok(Ident {
                span,
                text: "`...".to_string(),
            });
        }
        let saved = *input;
        *input = &input[1..];
        match parse_ident_or_keyword(input, file) {
            Ok(inner) => {
                let span = bt_span.join(inner.span);
                let text = format!("`{}", inner.text);
                return Ok(Ident { span, text });
            }
            Err(_) => {
                // Restore: this backtick wasn't escaping a name.
                *input = saved;
            }
        }
    }
    let (text, span) = match input.first() {
        Some(Spanned {
            token: Token::Ident(t),
            span,
        }) => (t.clone(), *span),
        Some(Spanned {
            token: Token::Syntax,
            span,
        }) => ("syntax".to_string(), *span),
        Some(Spanned {
            token: Token::Def,
            span,
        }) => ("def".to_string(), *span),
        Some(Spanned {
            token: Token::Relation,
            span,
        }) => ("relation".to_string(), *span),
        Some(Spanned {
            token: Token::Rule,
            span,
        }) => ("rule".to_string(), *span),
        Some(Spanned {
            token: Token::Var,
            span,
        }) => ("var".to_string(), *span),
        Some(Spanned {
            token: Token::Grammar,
            span,
        }) => ("grammar".to_string(), *span),
        Some(Spanned {
            token: Token::BinderHint,
            span,
        }) => ("hint".to_string(), *span),
        Some(Spanned {
            token: Token::If,
            span,
        }) => ("if".to_string(), *span),
        Some(Spanned {
            token: Token::Let,
            span,
        }) => ("let".to_string(), *span),
        Some(Spanned {
            token: Token::Else,
            span,
        }) => ("else".to_string(), *span),
        Some(Spanned {
            token: Token::Otherwise,
            span,
        }) => ("otherwise".to_string(), *span),
        Some(Spanned {
            token: Token::Eps,
            span,
        }) => ("eps".to_string(), *span),
        Some(s) => {
            return Err(Diagnostic::error(
                s.span,
                format!("expected identifier, found {}", s.token.describe()),
            ));
        }
        None => return Err(eof_diag(file, "expected identifier")),
    };
    *input = &input[1..];
    Ok(Ident { span, text })
}

/// Consume a profile label after `syntax NAME/`. SpecTec profiles are
/// usually identifiers (`syn`, `sem`) but can also be numbers
/// (`symsplit/1`, `symsplit/2`).
fn parse_profile_label(input: &mut &[Spanned], file: FileId) -> Result<Ident, Diagnostic> {
    match input.first() {
        Some(Spanned {
            token: Token::Ident(t),
            span,
        }) => {
            let id = Ident {
                span: *span,
                text: t.clone(),
            };
            *input = &input[1..];
            Ok(id)
        }
        Some(Spanned {
            token: Token::Nat(n),
            span,
        }) => {
            let id = Ident {
                span: *span,
                text: n.to_string(),
            };
            *input = &input[1..];
            Ok(id)
        }
        Some(s) => Err(Diagnostic::error(
            s.span,
            format!(
                "expected profile label (identifier or number) after `/`, found {}",
                s.token.describe()
            ),
        )),
        None => Err(eof_diag(file, "expected profile label after `/`")),
    }
}

/// True if `tok` would begin a new top-level form (`syntax`, `def`, etc.).
fn is_top_level_keyword(tok: &Token) -> bool {
    matches!(
        tok,
        Token::Syntax | Token::Def | Token::Relation | Token::Rule | Token::Var | Token::Grammar
    )
}

/// True if the token at position `i` in `tokens` is preceded by `/` or
/// `$`. We use this to recognise that the next token is part of an
/// identifier path (`Heaptype_sub/def`) or a function call (`$var(...)`)
/// rather than the start of a fresh top-level form.
fn preceded_by_slash(tokens: &[Spanned], i: usize) -> bool {
    i > 0 && matches!(tokens[i - 1].token, Token::Slash | Token::Dollar)
}

// ---------- top-level dispatch ----------

fn parse_top(file: FileId, input: &mut &[Spanned]) -> Result<Top, Diagnostic> {
    let first = peek(input).expect("caller ensures non-empty");
    match first.token {
        Token::Syntax => parse_syntax(file, input).map(Top::Syntax),
        Token::Def => parse_def(file, input),
        Token::Var => parse_var(file, input).map(Top::Var),
        Token::Relation => parse_relation(file, input).map(Top::Relation),
        Token::Rule => parse_rule(file, input).map(Top::Rule),
        Token::Grammar => parse_grammar(file, input).map(Top::Grammar),
        _ => Err(Diagnostic::error(
            first.span,
            format!(
                "expected `syntax`, `def`, `relation`, `rule`, `var`, or `grammar`, found {}",
                first.token.describe()
            ),
        )),
    }
}

// ---------- var ----------

/// `var NAME : type [hints*]`
fn parse_var(file: FileId, input: &mut &[Spanned]) -> Result<VarDecl, Diagnostic> {
    let kw_span = expect(input, file, &Token::Var)?;
    let name = parse_ident_or_keyword(input, file)?;
    expect(input, file, &Token::Colon)?;
    let ty = take_until_top_level(input, |t| matches!(t, Token::BinderHint));
    let hints = parse_hints(input)?;
    let mut span = kw_span.join(name.span);
    span = span.join(ty.span);
    for h in &hints {
        span = span.join(h.span);
    }
    Ok(VarDecl {
        span,
        name,
        ty,
        hints,
    })
}

// ---------- relation ----------

/// `relation NAME: <mixfix-template> [hints*]`
fn parse_relation(file: FileId, input: &mut &[Spanned]) -> Result<RelationDecl, Diagnostic> {
    let kw_span = expect(input, file, &Token::Relation)?;
    let name = parse_ident_or_keyword(input, file)?;
    expect(input, file, &Token::Colon)?;
    let template = take_until_top_level(input, |t| matches!(t, Token::BinderHint));
    let hints = parse_hints(input)?;
    let mut span = kw_span.join(name.span);
    span = span.join(template.span);
    for h in &hints {
        span = span.join(h.span);
    }
    Ok(RelationDecl {
        span,
        name,
        template,
        hints,
    })
}

// ---------- rule ----------

/// `rule NAME[/case]: <conclusion> [-- premise]* [hints*]`
///
/// Rule case names allow hyphens (`eq-any`, `i31-eq`) and may contain
/// further slashes (`Foo/bar/baz`). We collect after `/` up to `:` as a
/// joined text identifier.
fn parse_rule(file: FileId, input: &mut &[Spanned]) -> Result<RuleDecl, Diagnostic> {
    let kw_span = expect(input, file, &Token::Rule)?;
    let name = parse_ident_or_keyword(input, file)?;
    let case = if eat(input, &Token::Slash).is_some() {
        Some(parse_case_path(input, file)?)
    } else {
        None
    };
    expect(input, file, &Token::Colon)?;
    let (conclusion, premises) = take_def_clause_rhs_and_premises(input);
    // Hints (rare on rules but allowed) come after premises. The
    // `take_def_clause_rhs_and_premises` helper already stops premises at
    // top-level boundaries, so any remaining `hint(...)` runs are ours.
    let hints = parse_hints(input)?;

    let mut span = kw_span.join(name.span);
    if let Some(c) = &case {
        span = span.join(c.span);
    }
    span = span.join(conclusion.span);
    for p in &premises {
        span = span.join(p.span);
    }
    for h in &hints {
        span = span.join(h.span);
    }
    Ok(RuleDecl {
        span,
        name,
        case,
        conclusion,
        premises,
        hints,
    })
}

/// After `/`, collect a case path: a sequence of name-like tokens joined
/// by `-`, `/`, or `.` (so cases like `eq-any`, `ref.struct`, `i32.add`,
/// `Foo/bar`, and `Heaptype_sub/def` all parse — keywords like `def`,
/// `var`, `if` are accepted as path segments). Stops at any other token.
fn parse_case_path(input: &mut &[Spanned], file: FileId) -> Result<Ident, Diagnostic> {
    let mut text = String::new();
    let mut span: Option<Span> = None;
    loop {
        let (segment, sp) = match peek(input) {
            Some(Spanned {
                token: Token::Ident(t),
                span: sp,
            }) => (t.clone(), *sp),
            Some(Spanned {
                token: Token::Nat(n),
                span: sp,
            }) => (n.to_string(), *sp),
            Some(Spanned {
                token: Token::Minus,
                span: sp,
            }) => ("-".to_string(), *sp),
            Some(Spanned {
                token: Token::Slash,
                span: sp,
            }) => ("/".to_string(), *sp),
            Some(Spanned {
                token: Token::Dot,
                span: sp,
            }) => (".".to_string(), *sp),
            // Allow reserved keywords as path segments (`Heaptype_sub/def`).
            Some(Spanned {
                token: Token::Syntax,
                span: sp,
            }) => ("syntax".into(), *sp),
            Some(Spanned {
                token: Token::Def,
                span: sp,
            }) => ("def".into(), *sp),
            Some(Spanned {
                token: Token::Relation,
                span: sp,
            }) => ("relation".into(), *sp),
            Some(Spanned {
                token: Token::Rule,
                span: sp,
            }) => ("rule".into(), *sp),
            Some(Spanned {
                token: Token::Var,
                span: sp,
            }) => ("var".into(), *sp),
            Some(Spanned {
                token: Token::Grammar,
                span: sp,
            }) => ("grammar".into(), *sp),
            Some(Spanned {
                token: Token::BinderHint,
                span: sp,
            }) => ("hint".into(), *sp),
            Some(Spanned {
                token: Token::If,
                span: sp,
            }) => ("if".into(), *sp),
            Some(Spanned {
                token: Token::Let,
                span: sp,
            }) => ("let".into(), *sp),
            Some(Spanned {
                token: Token::Else,
                span: sp,
            }) => ("else".into(), *sp),
            Some(Spanned {
                token: Token::Otherwise,
                span: sp,
            }) => ("otherwise".into(), *sp),
            Some(Spanned {
                token: Token::Eps,
                span: sp,
            }) => ("eps".into(), *sp),
            _ => break,
        };
        text.push_str(&segment);
        span = Some(span.map_or(sp, |s| s.join(sp)));
        *input = &input[1..];
    }
    let span = span.ok_or_else(|| eof_diag(file, "expected case path after `/`"))?;
    if text.is_empty() {
        return Err(Diagnostic::error(span, "empty case path after `/`"));
    }
    Ok(Ident { span, text })
}

// ---------- grammar ----------

/// `grammar NAME [(params)] [/case] [(params)] [: ret] [hints*] [= productions]`
///
/// The `/case` suffix and the parenthesised `(params)` group can appear
/// in either order (`Tsymsplit/1`, `Treftype_(I)/base`). Both are
/// optional. `: ret` is also optional (some grammars omit it, e.g.
/// `grammar Tsource = ...`). The `= productions` body is optional too
/// (forward declarations).
fn parse_grammar(file: FileId, input: &mut &[Spanned]) -> Result<GrammarDecl, Diagnostic> {
    let kw_span = expect(input, file, &Token::Grammar)?;
    let name = parse_ident_or_keyword(input, file)?;

    // Allow `(params)` before OR after `/case`. Accept both orderings.
    let mut params = parse_optional_paren_params(input);
    let case = if eat(input, &Token::Slash).is_some() {
        Some(parse_case_path(input, file)?)
    } else {
        None
    };
    if params.is_empty() {
        params = parse_optional_paren_params(input);
    }

    let ret = if eat(input, &Token::Colon).is_some() {
        take_until_top_level(input, |t| matches!(t, Token::BinderHint | Token::Eq))
    } else {
        // No `:` — fabricate an empty TokenRun at the current position.
        empty_run_here(input, name.span)
    };
    let hints = parse_hints(input)?;
    let productions = if eat(input, &Token::Eq).is_some() {
        Some(take_until_top_level(input, |_| false))
    } else {
        None
    };

    let mut span = kw_span.join(name.span);
    if let Some(c) = &case {
        span = span.join(c.span);
    }
    for p in &params {
        span = span.join(p.span);
    }
    if !ret.tokens.is_empty() {
        span = span.join(ret.span);
    }
    for h in &hints {
        span = span.join(h.span);
    }
    if let Some(p) = &productions {
        span = span.join(p.span);
    }
    Ok(GrammarDecl {
        span,
        name,
        case,
        params,
        ret,
        hints,
        productions,
    })
}

/// Synthesise an empty `TokenRun` for places where an optional section
/// is absent (e.g. a missing return type). The span is a zero-length
/// span at the start of the cursor position, falling back to `fallback`
/// if at EOF.
fn empty_run_here(input: &[Spanned], fallback: Span) -> TokenRun {
    let span = input
        .first()
        .map(|s| Span::new(s.span.file, s.span.start, s.span.start))
        .unwrap_or_else(|| Span::new(fallback.file, fallback.end, fallback.end));
    TokenRun {
        span,
        tokens: Vec::new(),
    }
}

/// Take tokens from the start of input up to (but not including) the next
/// top-level boundary, or end-of-input.
///
/// A top-level boundary is a top-level keyword token at paren-depth 0
/// that is *not* preceded by `/` (so `Heaptype_sub/def` is not split).
/// The very first token is always taken even if it would otherwise be a
/// boundary — this lets [`parse_top`] start a `Top::Other` form with the
/// keyword (`relation`/`rule`/etc.) that triggered the dispatch.
fn take_until_next_top(input: &mut &[Spanned]) -> TokenRun {
    let mut out: Vec<Spanned> = Vec::new();
    let mut span: Option<Span> = None;
    let mut cursor: &[Spanned] = input;
    let mut depth: i32 = 0;
    let mut first = true;
    while let Some(s) = cursor.first() {
        if !first
            && depth == 0
            && is_top_level_keyword(&s.token)
            && !preceded_by_slash(&out, out.len())
        {
            break;
        }
        depth += s.bracket_delta();
        out.push(s.clone());
        span = Some(match span {
            None => s.span,
            Some(sp) => sp.join(s.span),
        });
        cursor = &cursor[1..];
        first = false;
    }
    *input = cursor;
    TokenRun {
        span: span.unwrap_or_else(|| {
            cursor
                .first()
                .map(|s| Span::new(s.span.file, s.span.start, s.span.start))
                .unwrap_or_else(|| Span::new(FileId::new(0), 0, 0))
        }),
        tokens: out,
    }
}

// ---------- syntax declarations ----------

/// `syntax NAME[/profile][(params)] [hint(...)]* [= body]`
fn parse_syntax(file: FileId, input: &mut &[Spanned]) -> Result<SyntaxDecl, Diagnostic> {
    let kw_span = expect(input, file, &Token::Syntax)?;
    let name = parse_ident_or_keyword(input, file)?;
    let profile = if eat(input, &Token::Slash).is_some() {
        Some(parse_profile_label(input, file)?)
    } else {
        None
    };
    let params = parse_optional_paren_params(input);
    let hints = parse_hints(input)?;
    let body = if eat(input, &Token::Eq).is_some() {
        Some(parse_syntax_body(file, input)?)
    } else {
        None
    };

    // Span: from `syntax` keyword to the end of whatever we consumed.
    // We extend conservatively using the last absorbed token.
    let mut span = kw_span;
    span = span.join(name.span);
    if let Some(p) = &profile {
        span = span.join(p.span);
    }
    for tr in &params {
        span = span.join(tr.span);
    }
    for h in &hints {
        span = span.join(h.span);
    }
    if let Some(b) = &body {
        span = span.join(body_span(b));
    }

    Ok(SyntaxDecl {
        span,
        name,
        profile,
        params,
        hints,
        body,
    })
}

fn body_span(b: &SyntaxBody) -> Span {
    match b {
        SyntaxBody::Variant(alts) => alts
            .iter()
            .map(|a| a.span)
            .reduce(Span::join)
            .expect("variant has at least one alt"),
        SyntaxBody::Record(fields) => fields
            .iter()
            .filter_map(|f| match f {
                RecordSlot::Real(rf) => Some(rf.span),
                RecordSlot::Placeholder => None,
            })
            .reduce(Span::join)
            .expect("record has at least one field"),
        SyntaxBody::Alias(tr) => tr.span,
    }
}

/// After `syntax NAME =`, parse the body. Three shapes:
/// - `{ ... }` (record) — peek for `LBrace`
/// - `| ALT | ALT | ...` (variant) — peek for `Pipe`
/// - anything else (alias) — collect a token run until next top-level
///
/// Note SpecTec lets you write `syntax foo = ALT_1 | ALT_2` *without* a
/// leading pipe (e.g. `syntax addrtype = | I32 | I64` vs
/// `syntax numtype = I32 | I64`). We handle both: if we see `Pipe` first
/// it's a variant; if the leading body contains an unparenthesised
/// top-level `Pipe` later, we treat it as variant too.
fn parse_syntax_body(file: FileId, input: &mut &[Spanned]) -> Result<SyntaxBody, Diagnostic> {
    if let Some(Spanned {
        token: Token::LBrace,
        ..
    }) = peek(input)
    {
        return parse_record_body(file, input);
    }

    // Variant or alias? Take everything up to the next top-level keyword,
    // then look for `Pipe` at depth 0. A body that starts with a
    // case-head ident (uppercase / underscore-prefixed) and has no
    // top-level pipe is a single-case variant (e.g.
    // `syntax callframe = FRAME_ n {frame}`).
    let body_run = take_until_next_top(input);
    if contains_top_level_pipe(&body_run.tokens) {
        Ok(SyntaxBody::Variant(split_alts(&body_run)?))
    } else if body_starts_with_case_head(&body_run.tokens)
        || body_looks_like_variant(&body_run.tokens)
        || body_is_single_nat_literal(&body_run.tokens)
    {
        // Reuse split_alts so the trailing `hint(...)` clauses get
        // peeled off the body just like the multi-alt case.
        Ok(SyntaxBody::Variant(split_alts(&body_run)?))
    } else {
        Ok(SyntaxBody::Alias(body_run))
    }
}

/// True when the entire body is a single bare numeric literal (e.g.
/// `syntax symdots = 0`). OCaml elaborates this to a one-alt pattern-
/// literal variant, so we route it through the variant path.
fn body_is_single_nat_literal(toks: &[Spanned]) -> bool {
    toks.len() == 1 && matches!(toks[0].token, Token::Nat(_))
}

/// True when the body looks like a (single-case) variant rather than
/// a bare type expression. Three flavours qualify:
///
/// 1. Top-level "literal marks" — `` ` ``, `;`, `->` — that don't
///    appear in pure type expressions.
///
/// 2. Two or more juxtaposed sub-elements at depth 0. A bare type
///    expression is one ident (`tagtype = typeuse`), one parametric
///    `Ident(args)`, or one parenthesised type, optionally with
///    iter postfixes. Anything with multiple top-level chunks
///    (`globaltype = mut? valtype`, `memtype = addrtype limits PAGE`)
///    is a headless single-case variant whose binds are those chunks.
///
/// 3. Single bare numeric literal (handled by
///    [`body_is_single_nat_literal`], called separately at the
///    `parse_syntax_body` call site).
fn body_looks_like_variant(toks: &[Spanned]) -> bool {
    let mut depth: i32 = 0;
    let mut top_idents: usize = 0;
    for t in toks {
        if depth == 0 {
            match &t.token {
                Token::Backtick | Token::Semi | Token::Arrow => return true,
                Token::Ident(_) | Token::Nat(_) | Token::Text(_) => top_idents += 1,
                _ => {}
            }
        }
        depth += t.bracket_delta();
    }
    top_idents >= 2
}

/// True when the first token is an `Ident` whose name looks like a
/// case-head (uppercase / leading-underscore). Mirrors the heuristic
/// in `crate::elab::is_case_head`.
fn body_starts_with_case_head(toks: &[Spanned]) -> bool {
    let Some(Spanned {
        token: Token::Ident(n),
        ..
    }) = toks.first()
    else {
        return false;
    };
    if n.len() < 2 {
        return false;
    }
    let first = n.as_bytes()[0];
    if !(first.is_ascii_uppercase() || first == b'_') {
        return false;
    }
    n.bytes()
        .all(|b| !b.is_ascii_alphabetic() || b.is_ascii_uppercase())
}

/// Parse a record body `{ FIELD ty [hints*], FIELD ty [hints*], ... }`.
/// Phase 1: store each field's type as a raw `TokenRun`.
fn parse_record_body(file: FileId, input: &mut &[Spanned]) -> Result<SyntaxBody, Diagnostic> {
    let lbrace_span = expect(input, file, &Token::LBrace)?;
    let mut fields: Vec<RecordSlot> = Vec::new();

    // Handle empty record `{}`.
    if eat(input, &Token::RBrace).is_some() {
        return Ok(SyntaxBody::Record(fields));
    }

    loop {
        if eat(input, &Token::DotDotDot).is_some() {
            fields.push(RecordSlot::Placeholder);
        } else {
            let name = parse_ident_or_keyword(input, file)?;
            let ty = take_field_ty(input);
            let hints = parse_hints(input)?;
            let mut span = name.span;
            span = span.join(ty.span);
            for h in &hints {
                span = span.join(h.span);
            }
            fields.push(RecordSlot::Real(RecordField {
                span,
                name,
                ty,
                hints,
            }));
        }

        match peek(input) {
            Some(Spanned {
                token: Token::Comma,
                ..
            }) => {
                *input = &input[1..];
                continue;
            }
            Some(Spanned {
                token: Token::RBrace,
                ..
            }) => {
                *input = &input[1..];
                let _ = lbrace_span; // captured for completeness
                return Ok(SyntaxBody::Record(fields));
            }
            Some(s) => {
                return Err(Diagnostic::error(
                    s.span,
                    format!(
                        "expected `,` or `}}` in record body, found {}",
                        s.token.describe()
                    ),
                ));
            }
            None => return Err(eof_diag(file, "unterminated record body")),
        }
    }
}

/// Take tokens for a record field's type, stopping at the next top-level
/// `,`, top-level `}`, or the start of a `hint(...)` clause.
fn take_field_ty(input: &mut &[Spanned]) -> TokenRun {
    let mut tokens = Vec::new();
    let mut depth: i32 = 0;
    let mut span: Option<Span> = None;
    let mut cursor: &[Spanned] = input;
    while let Some(s) = cursor.first() {
        match &s.token {
            Token::LParen | Token::LBracket | Token::LBrace => depth += 1,
            Token::RParen | Token::RBracket => depth -= 1,
            Token::RBrace if depth == 0 => break,
            Token::Comma if depth == 0 => break,
            Token::BinderHint if depth == 0 => break,
            _ => {}
        }
        if depth < 0 {
            break;
        }
        tokens.push(s.clone());
        span = Some(match span {
            None => s.span,
            Some(sp) => sp.join(s.span),
        });
        cursor = &cursor[1..];
    }
    *input = cursor;
    TokenRun {
        span: span.unwrap_or_else(|| {
            // Empty type — synthesise a zero-length span at the cursor.
            cursor
                .first()
                .map(|s| Span::new(s.span.file, s.span.start, s.span.start))
                .unwrap_or_else(|| Span::new(FileId::new(0), 0, 0))
        }),
        tokens,
    }
}

/// Does the token run contain a `|` at top-level (depth 0 with respect to
/// parens/brackets)? Used to distinguish `syntax X = A | B` from
/// `syntax X = some_alias(A | B)`.
fn contains_top_level_pipe(tokens: &[Spanned]) -> bool {
    let mut depth: i32 = 0;
    for t in tokens {
        if depth == 0 && matches!(t.token, Token::Pipe) {
            return true;
        }
        depth += t.bracket_delta();
    }
    false
}

/// Split a variant body (post-`=`) into alternatives separated by `|`.
/// Trims a leading `|` if present and an optional leading `...`.
/// Hints attached to each alternative go in the `Alt.hints` field.
fn split_alts(run: &TokenRun) -> Result<Vec<Alt>, Diagnostic> {
    let mut alts = Vec::new();
    let mut depth: i32 = 0;
    let mut start = 0usize;

    // Skip a leading `|`.
    if matches!(run.tokens.first().map(|s| &s.token), Some(Token::Pipe)) {
        start = 1;
    }

    let mut cur = start;
    let mut chunk_start = start;

    while cur < run.tokens.len() {
        let t = &run.tokens[cur];
        if depth == 0 && matches!(t.token, Token::Pipe) {
            push_alt(&run.tokens[chunk_start..cur], &mut alts)?;
            chunk_start = cur + 1;
        }
        depth += t.bracket_delta();
        cur += 1;
    }
    push_alt(&run.tokens[chunk_start..], &mut alts)?;
    Ok(alts)
}

fn push_alt(slice: &[Spanned], alts: &mut Vec<Alt>) -> Result<(), Diagnostic> {
    // Trim trailing hints off the body and into `Alt.hints`.
    let (body_slice, hints) = extract_trailing_hints(slice)?;
    if body_slice.is_empty() && hints.is_empty() {
        // empty alt — skip
        return Ok(());
    }
    let body_span = body_slice
        .iter()
        .map(|s| s.span)
        .reduce(Span::join)
        .unwrap_or_else(|| {
            // No body tokens but we have hints — span the hints.
            hints
                .iter()
                .map(|h| h.span)
                .reduce(Span::join)
                .expect("at least one hint or body")
        });
    let mut full_span = body_span;
    for h in &hints {
        full_span = full_span.join(h.span);
    }
    alts.push(Alt {
        span: full_span,
        body: TokenRun {
            span: body_span,
            tokens: body_slice.to_vec(),
        },
        hints,
    });
    Ok(())
}

/// Given the tokens for one alternative, peel any trailing `hint(...)`
/// clauses off the end and return `(body_slice, hints)`.
fn extract_trailing_hints(slice: &[Spanned]) -> Result<(&[Spanned], Vec<HintAtom>), Diagnostic> {
    // Walk from the end: a hint clause is `hint ( ... )` taking up
    // contiguous tokens including the keyword. We scan from the right
    // looking for `BinderHint LParen ... RParen` runs.
    //
    // Simpler approach: scan from the left, collect a prefix until we hit
    // a `hint` token at depth 0, then everything from there is a hint
    // sequence. Reasoning: hints always come at the end of an alternative
    // in well-formed SpecTec, never in the middle.
    let mut depth: i32 = 0;
    let mut first_hint: Option<usize> = None;
    for (i, t) in slice.iter().enumerate() {
        if depth == 0 && matches!(t.token, Token::BinderHint) {
            first_hint = Some(i);
            break;
        }
        depth += t.bracket_delta();
    }
    let body = &slice[..first_hint.unwrap_or(slice.len())];
    let mut hint_input: &[Spanned] = &slice[first_hint.unwrap_or(slice.len())..];
    let hints = parse_hints(&mut hint_input)?;
    Ok((body, hints))
}

// ---------- def signatures and clauses ----------

/// `def $NAME[(arg_tys)] : ret_ty [hints*]`  (signature, args optional)
/// `def $NAME[(pats)] = rhs [-- premise]*`   (clause, args optional)
/// `def $NAME [hints*]`                       (forward / builtin hint decl)
///
/// Distinguished by whether the post-args separator is `:` (signature),
/// `=` (clause), or absent / immediately a `hint(...)` (forward decl).
/// Names may be reserved keywords (`def $var(...)`).
fn parse_def(file: FileId, input: &mut &[Spanned]) -> Result<Top, Diagnostic> {
    let kw_span = expect(input, file, &Token::Def)?;
    expect(input, file, &Token::Dollar)?;
    let name = parse_ident_or_keyword(input, file)?;
    let args = if matches!(peek(input).map(|s| &s.token), Some(Token::LParen)) {
        parse_paren_comma_list(file, input)?
    } else {
        Vec::new()
    };

    match peek(input) {
        Some(Spanned {
            token: Token::Colon,
            ..
        }) => {
            *input = &input[1..];
            let ret_ty = take_def_ret_ty(input);
            let hints = parse_hints(input)?;
            let mut span = kw_span.join(name.span);
            for a in &args {
                span = span.join(a.span);
            }
            span = span.join(ret_ty.span);
            for h in &hints {
                span = span.join(h.span);
            }
            Ok(Top::DefSig(DefSig {
                span,
                name,
                arg_tys: args,
                ret_ty,
                hints,
            }))
        }
        Some(Spanned {
            token: Token::Eq, ..
        }) => {
            *input = &input[1..];
            let (rhs, premises) = take_def_clause_rhs_and_premises(input);
            let mut span = kw_span.join(name.span);
            for a in &args {
                span = span.join(a.span);
            }
            span = span.join(rhs.span);
            for p in &premises {
                span = span.join(p.span);
            }
            Ok(Top::DefClause(DefClause {
                span,
                name,
                arg_pats: args,
                rhs,
                premises,
            }))
        }
        // Forward declaration: `def $NAME [hint(...)]*` followed by another
        // top-level form or end-of-input. Treated as a signature with no
        // return type (empty TokenRun).
        Some(Spanned {
            token: Token::BinderHint,
            ..
        })
        | None => {
            let hints = parse_hints(input)?;
            // Sanity: we should now be at EOF or a top-level keyword.
            if let Some(s) = peek(input)
                && !is_top_level_keyword(&s.token)
            {
                return Err(Diagnostic::error(
                    s.span,
                    format!(
                        "expected `:`, `=`, `hint(...)`, or next top-level form after `def $NAME`, found {}",
                        s.token.describe()
                    ),
                ));
            }
            let mut span = kw_span.join(name.span);
            for a in &args {
                span = span.join(a.span);
            }
            for h in &hints {
                span = span.join(h.span);
            }
            // Use an empty TokenRun for the return type; Phase 2 elaboration
            // will recognise the absent type from `ret_ty.tokens.is_empty()`.
            let ret_ty = TokenRun {
                span: Span::new(name.span.file, name.span.end, name.span.end),
                tokens: Vec::new(),
            };
            Ok(Top::DefSig(DefSig {
                span,
                name,
                arg_tys: args,
                ret_ty,
                hints,
            }))
        }
        Some(s) if is_top_level_keyword(&s.token) => {
            // No `:` / `=` / `hint` — declaration with no body at all.
            let mut span = kw_span.join(name.span);
            for a in &args {
                span = span.join(a.span);
            }
            let ret_ty = TokenRun {
                span: Span::new(name.span.file, name.span.end, name.span.end),
                tokens: Vec::new(),
            };
            Ok(Top::DefSig(DefSig {
                span,
                name,
                arg_tys: args,
                ret_ty,
                hints: Vec::new(),
            }))
        }
        Some(s) => Err(Diagnostic::error(
            s.span,
            format!(
                "expected `:` (signature), `=` (clause), or `hint(...)` after `def $NAME(...)`, found {}",
                s.token.describe()
            ),
        )),
    }
}

/// Parse `( T_1, T_2, ... )` into a list of `TokenRun`s, one per
/// comma-separated entry. The outer parens are consumed.
///
/// Argument-list entries may contain `syntax X` type-parameters and any
/// other syntactic form — top-level keywords inside this paren group are
/// not boundaries.
fn parse_paren_comma_list(
    file: FileId,
    input: &mut &[Spanned],
) -> Result<Vec<TokenRun>, Diagnostic> {
    expect(input, file, &Token::LParen)?;
    let mut out = Vec::new();
    if eat(input, &Token::RParen).is_some() {
        return Ok(out);
    }
    loop {
        let tr = take_until_paren_balanced(input, |t| matches!(t, Token::Comma | Token::RParen));
        out.push(tr);
        match peek(input) {
            Some(Spanned {
                token: Token::Comma,
                ..
            }) => {
                *input = &input[1..];
            }
            Some(Spanned {
                token: Token::RParen,
                ..
            }) => {
                *input = &input[1..];
                return Ok(out);
            }
            Some(s) => {
                return Err(Diagnostic::error(
                    s.span,
                    format!(
                        "expected `,` or `)` in argument list, found {}",
                        s.token.describe()
                    ),
                ));
            }
            None => return Err(eof_diag(file, "unterminated argument list")),
        }
    }
}

/// Like [`take_until_top_level`] but does NOT stop at top-level keywords;
/// only the `stop` predicate (at depth 0) terminates. Used for collecting
/// argument-list entries, which can contain `syntax X` and similar.
fn take_until_paren_balanced(input: &mut &[Spanned], stop: impl Fn(&Token) -> bool) -> TokenRun {
    let mut depth: i32 = 0;
    let mut span: Option<Span> = None;
    let mut tokens = Vec::new();
    let mut cursor: &[Spanned] = input;
    while let Some(s) = cursor.first() {
        if depth == 0 && stop(&s.token) {
            break;
        }
        depth += s.bracket_delta();
        tokens.push(s.clone());
        span = Some(match span {
            None => s.span,
            Some(sp) => sp.join(s.span),
        });
        cursor = &cursor[1..];
    }
    *input = cursor;
    TokenRun {
        span: span.unwrap_or_else(|| {
            cursor
                .first()
                .map(|s| Span::new(s.span.file, s.span.start, s.span.start))
                .unwrap_or_else(|| Span::new(FileId::new(0), 0, 0))
        }),
        tokens,
    }
}

/// After `def $NAME(args) :`, take the return type. Stops at `hint` or at
/// the next top-level keyword.
fn take_def_ret_ty(input: &mut &[Spanned]) -> TokenRun {
    take_until_top_level(input, |t| matches!(t, Token::BinderHint)).and_join_top_keyword_stop(input)
}

/// After `def $NAME(args) =`, the RHS continues until either `--` (a
/// premise) or the next top-level keyword. Following `--` tokens up to
/// either another `--` or a top-level keyword form a premise.
fn take_def_clause_rhs_and_premises(input: &mut &[Spanned]) -> (TokenRun, Vec<TokenRun>) {
    let rhs = take_until_top_level(input, |t| matches!(t, Token::DashDash))
        .and_join_top_keyword_stop(input);
    let mut premises = Vec::new();
    while let Some(Spanned {
        token: Token::DashDash,
        ..
    }) = peek(input)
    {
        *input = &input[1..];
        let prem = take_until_top_level(input, |t| matches!(t, Token::DashDash))
            .and_join_top_keyword_stop(input);
        premises.push(prem);
    }
    (rhs, premises)
}

/// Collect tokens until `stop(token)` returns true at paren-depth 0, or
/// until we hit a top-level keyword that would start a new form (also at
/// depth 0, and not preceded by `/`).
fn take_until_top_level(input: &mut &[Spanned], stop: impl Fn(&Token) -> bool) -> TokenRun {
    let mut depth: i32 = 0;
    let mut span: Option<Span> = None;
    let mut tokens = Vec::new();
    let mut cursor: &[Spanned] = input;
    while let Some(s) = cursor.first() {
        if depth == 0 {
            if stop(&s.token) {
                break;
            }
            if is_top_level_keyword(&s.token) && !preceded_by_slash(&tokens, tokens.len()) {
                break;
            }
        }
        depth += s.bracket_delta();
        tokens.push(s.clone());
        span = Some(match span {
            None => s.span,
            Some(sp) => sp.join(s.span),
        });
        cursor = &cursor[1..];
    }
    *input = cursor;
    TokenRun {
        span: span.unwrap_or_else(|| {
            cursor
                .first()
                .map(|s| Span::new(s.span.file, s.span.start, s.span.start))
                .unwrap_or_else(|| Span::new(FileId::new(0), 0, 0))
        }),
        tokens,
    }
}

trait TokenRunExt: Sized {
    /// Pass-through: this combinator is a placeholder for the older API
    /// where we needed to chain. With the new implementation
    /// `take_until_top_level` already stops at top-level keywords, so this
    /// is a no-op kept for call-site clarity.
    fn and_join_top_keyword_stop(self, _input: &mut &[Spanned]) -> Self;
}

impl TokenRunExt for TokenRun {
    fn and_join_top_keyword_stop(self, _input: &mut &[Spanned]) -> Self {
        self
    }
}

// ---------- hints ----------

fn parse_hints(input: &mut &[Spanned]) -> Result<Vec<HintAtom>, Diagnostic> {
    let mut out = Vec::new();
    while let Some(Spanned {
        token: Token::BinderHint,
        ..
    }) = peek(input)
    {
        out.push(parse_hint(input)?);
    }
    Ok(out)
}

fn parse_hint(input: &mut &[Spanned]) -> Result<HintAtom, Diagnostic> {
    let hint_span = match input.first() {
        Some(Spanned {
            token: Token::BinderHint,
            span,
        }) => {
            let sp = *span;
            *input = &input[1..];
            sp
        }
        _ => unreachable!("caller checks first token is `hint`"),
    };
    let file = hint_span.file;
    let lparen_span = expect(input, file, &Token::LParen)?;
    let body = take_balanced_to_rparen(input);
    let rparen_span = expect(input, file, &Token::RParen)?;
    let _ = lparen_span;
    Ok(HintAtom {
        span: hint_span.join(rparen_span),
        body,
    })
}

/// Collect tokens until a matching `RParen` at depth 0. The `RParen`
/// itself is NOT consumed.
fn take_balanced_to_rparen(input: &mut &[Spanned]) -> TokenRun {
    let mut depth: i32 = 0;
    let mut span: Option<Span> = None;
    let mut tokens = Vec::new();
    let mut cursor: &[Spanned] = input;
    while let Some(s) = cursor.first() {
        if depth == 0 && matches!(s.token, Token::RParen) {
            break;
        }
        depth += s.bracket_delta();
        tokens.push(s.clone());
        span = Some(match span {
            None => s.span,
            Some(sp) => sp.join(s.span),
        });
        cursor = &cursor[1..];
    }
    *input = cursor;
    TokenRun {
        span: span.unwrap_or_else(|| {
            cursor
                .first()
                .map(|s| Span::new(s.span.file, s.span.start, s.span.start))
                .unwrap_or_else(|| Span::new(FileId::new(0), 0, 0))
        }),
        tokens,
    }
}

// ---------- optional parameter list `(...)` after a name ----------

/// If the next token is `LParen`, consume a single balanced
/// parenthesised group as a `TokenRun` and return it as a one-element
/// `params` list. SpecTec's `syntax foo(N)`, `syntax list(syntax X)`,
/// `def $sum(nat*)`, etc. all take a single `(...)` group. Phase 1
/// stores it raw.
fn parse_optional_paren_params(input: &mut &[Spanned]) -> Vec<TokenRun> {
    let mut out = Vec::new();
    if matches!(peek(input).map(|s| &s.token), Some(Token::LParen)) {
        // Take from `(` through the matching `)`.
        let start_span = input.first().expect("checked").span;
        let mut depth: i32 = 0;
        let mut tokens = Vec::new();
        let mut span = start_span;
        let mut cursor: &[Spanned] = input;
        while let Some(s) = cursor.first() {
            match &s.token {
                Token::LParen => depth += 1,
                Token::RParen => depth -= 1,
                _ => {}
            }
            tokens.push(s.clone());
            span = span.join(s.span);
            cursor = &cursor[1..];
            if depth == 0 {
                break;
            }
        }
        *input = cursor;
        out.push(TokenRun { span, tokens });
    }
    out
}

// ---------- unit tests ----------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lex::lex;
    use crate::source::SourceMap;

    fn parse_str(src: &str) -> Result<Vec<Top>, Diagnostic> {
        let mut map = SourceMap::new();
        let id = map.add("<test>", src);
        let tokens = lex(id, src)?;
        parse(id, tokens)
    }

    #[test]
    fn empty_input() {
        let tops = parse_str("").unwrap();
        assert!(tops.is_empty());
    }

    #[test]
    fn syntax_alias() {
        let tops = parse_str("syntax u8 = uN(`8)").unwrap();
        assert_eq!(tops.len(), 1);
        let Top::Syntax(s) = &tops[0] else {
            panic!("expected Top::Syntax");
        };
        assert_eq!(s.name.text, "u8");
        assert!(s.profile.is_none());
        assert!(s.params.is_empty());
        assert!(matches!(s.body, Some(SyntaxBody::Alias(_))));
    }

    #[test]
    fn syntax_variant_with_and_without_leading_pipe() {
        let with_pipe = parse_str("syntax addrtype = | I32 | I64").unwrap();
        let Top::Syntax(s) = &with_pipe[0] else {
            panic!()
        };
        let Some(SyntaxBody::Variant(alts)) = &s.body else {
            panic!()
        };
        assert_eq!(alts.len(), 2);

        let without_pipe = parse_str("syntax numtype = I32 | I64 | F32 | F64").unwrap();
        let Top::Syntax(s) = &without_pipe[0] else {
            panic!()
        };
        let Some(SyntaxBody::Variant(alts)) = &s.body else {
            panic!()
        };
        assert_eq!(alts.len(), 4);
    }

    #[test]
    fn syntax_record() {
        let src = r#"syntax point = { X nat, Y nat }"#;
        let tops = parse_str(src).unwrap();
        let Top::Syntax(s) = &tops[0] else { panic!() };
        let Some(SyntaxBody::Record(fields)) = &s.body else {
            panic!()
        };
        assert_eq!(fields.len(), 2);
        let RecordSlot::Real(f0) = &fields[0] else {
            panic!()
        };
        let RecordSlot::Real(f1) = &fields[1] else {
            panic!()
        };
        assert_eq!(f0.name.text, "X");
        assert_eq!(f1.name.text, "Y");
    }

    #[test]
    fn syntax_record_with_extension_dots() {
        let src = r#"syntax context/sem = { ..., RECS subtype* }"#;
        let tops = parse_str(src).unwrap();
        let Top::Syntax(s) = &tops[0] else { panic!() };
        assert_eq!(s.profile.as_ref().unwrap().text, "sem");
        let Some(SyntaxBody::Record(fields)) = &s.body else {
            panic!()
        };
        // Two slots: the `...` Placeholder, then RECS.
        assert_eq!(fields.len(), 2);
        assert!(matches!(fields[0], RecordSlot::Placeholder));
        let RecordSlot::Real(f1) = &fields[1] else {
            panic!()
        };
        assert_eq!(f1.name.text, "RECS");
    }

    #[test]
    fn syntax_with_profile_and_params() {
        let src = "syntax fN(N) = | POS fNmag(N) | NEG fNmag(N)";
        let tops = parse_str(src).unwrap();
        let Top::Syntax(s) = &tops[0] else { panic!() };
        assert_eq!(s.name.text, "fN");
        assert_eq!(s.params.len(), 1);
        let Some(SyntaxBody::Variant(alts)) = &s.body else {
            panic!()
        };
        assert_eq!(alts.len(), 2);
    }

    #[test]
    fn syntax_with_hints() {
        let src = r#"syntax bit hint(desc "bit") = 0 | 1"#;
        let tops = parse_str(src).unwrap();
        let Top::Syntax(s) = &tops[0] else { panic!() };
        assert_eq!(s.hints.len(), 1);
        let Some(SyntaxBody::Variant(alts)) = &s.body else {
            panic!()
        };
        assert_eq!(alts.len(), 2);
    }

    #[test]
    fn syntax_alternative_hints_attach_to_alt() {
        let src = r#"syntax x =
            | POS fNmag(N) hint(show $(+%))
            | NEG fNmag(N) hint(show $(-%))"#;
        let tops = parse_str(src).unwrap();
        let Top::Syntax(s) = &tops[0] else { panic!() };
        let Some(SyntaxBody::Variant(alts)) = &s.body else {
            panic!()
        };
        assert_eq!(alts.len(), 2);
        assert_eq!(alts[0].hints.len(), 1);
        assert_eq!(alts[1].hints.len(), 1);
    }

    #[test]
    fn syntax_forward_decl_no_body() {
        let tops = parse_str(r#"syntax rectype hint(desc "recursive type")"#).unwrap();
        let Top::Syntax(s) = &tops[0] else { panic!() };
        assert!(s.body.is_none());
        assert_eq!(s.hints.len(), 1);
    }

    #[test]
    fn def_signature() {
        let tops = parse_str("def $min(nat, nat) : nat").unwrap();
        let Top::DefSig(d) = &tops[0] else {
            panic!("expected DefSig, got {:?}", tops[0]);
        };
        assert_eq!(d.name.text, "min");
        assert_eq!(d.arg_tys.len(), 2);
    }

    #[test]
    fn def_signature_with_hint() {
        let tops = parse_str(r#"def $sum(nat*) : nat  hint(show (+) %) hint(macro none)"#).unwrap();
        let Top::DefSig(d) = &tops[0] else { panic!() };
        assert_eq!(d.hints.len(), 2);
    }

    #[test]
    fn def_clause_no_premise() {
        let tops = parse_str("def $sum(eps) = 0").unwrap();
        let Top::DefClause(d) = &tops[0] else {
            panic!()
        };
        assert_eq!(d.name.text, "sum");
        assert_eq!(d.arg_pats.len(), 1);
        assert!(d.premises.is_empty());
        // RHS just contains `0`.
        assert_eq!(d.rhs.tokens.len(), 1);
        assert!(matches!(&d.rhs.tokens[0].token, Token::Nat(n) if n.is_zero()));
    }

    #[test]
    fn def_clause_with_premises() {
        let src = r#"def $min(i, j) = i  -- if $(i <= j)"#;
        let tops = parse_str(src).unwrap();
        let Top::DefClause(d) = &tops[0] else {
            panic!()
        };
        assert_eq!(d.premises.len(), 1);
    }

    #[test]
    fn def_clause_with_otherwise() {
        let src = r#"def $min(i, j) = j  -- otherwise"#;
        let tops = parse_str(src).unwrap();
        let Top::DefClause(d) = &tops[0] else {
            panic!()
        };
        assert_eq!(d.premises.len(), 1);
    }

    #[test]
    fn multiple_top_level_forms() {
        let src = r#"
            def $min(nat, nat) : nat
            def $min(i, j) = i  -- if $(i <= j)
            def $min(i, j) = j  -- otherwise
        "#;
        let tops = parse_str(src).unwrap();
        assert_eq!(tops.len(), 3);
        assert!(matches!(tops[0], Top::DefSig(_)));
        assert!(matches!(tops[1], Top::DefClause(_)));
        assert!(matches!(tops[2], Top::DefClause(_)));
    }

    #[test]
    fn var_simple() {
        let tops = parse_str("var n : nat").unwrap();
        let Top::Var(v) = &tops[0] else { panic!() };
        assert_eq!(v.name.text, "n");
        assert!(!v.ty.tokens.is_empty());
        assert!(v.hints.is_empty());
    }

    #[test]
    fn var_with_hint() {
        let tops = parse_str(r#"var lct : localtype  hint(show lt)"#).unwrap();
        let Top::Var(v) = &tops[0] else { panic!() };
        assert_eq!(v.name.text, "lct");
        assert_eq!(v.hints.len(), 1);
    }

    #[test]
    fn relation_with_template_and_hints() {
        let src = r#"relation Numtype_sub: context |- numtype <: numtype  hint(name "S-num")"#;
        let tops = parse_str(src).unwrap();
        let Top::Relation(r) = &tops[0] else { panic!() };
        assert_eq!(r.name.text, "Numtype_sub");
        // Template tokens: context |- numtype <: numtype = 5 tokens
        assert_eq!(r.template.tokens.len(), 5);
        assert_eq!(r.hints.len(), 1);
    }

    #[test]
    fn rule_simple_no_case() {
        let tops = parse_str(r#"rule Numtype_sub: C |- numtype <: numtype"#).unwrap();
        let Top::Rule(r) = &tops[0] else { panic!() };
        assert_eq!(r.name.text, "Numtype_sub");
        assert!(r.case.is_none());
        assert!(r.premises.is_empty());
    }

    #[test]
    fn rule_with_case_and_hyphen() {
        let tops = parse_str(r#"rule Heaptype_sub/eq-any: C |- EQ <: ANY"#).unwrap();
        let Top::Rule(r) = &tops[0] else { panic!() };
        assert_eq!(r.name.text, "Heaptype_sub");
        assert_eq!(r.case.as_ref().unwrap().text, "eq-any");
    }

    #[test]
    fn rule_with_premises() {
        let src = r#"rule Heaptype_sub/trans:
            C |- heaptype_1 <: heaptype_2
            -- Heaptype_ok: C |- heaptype' : OK
            -- Heaptype_sub: C |- heaptype_1 <: heaptype'
            -- Heaptype_sub: C |- heaptype' <: heaptype_2"#;
        let tops = parse_str(src).unwrap();
        let Top::Rule(r) = &tops[0] else { panic!() };
        assert_eq!(r.case.as_ref().unwrap().text, "trans");
        assert_eq!(r.premises.len(), 3);
    }

    #[test]
    fn grammar_inline() {
        let tops = parse_str(r#"grammar Bbyte : byte = 0x00 | ... | 0xFF"#).unwrap();
        let Top::Grammar(g) = &tops[0] else { panic!() };
        assert_eq!(g.name.text, "Bbyte");
        assert!(g.case.is_none());
        assert!(g.params.is_empty());
        assert!(g.productions.is_some());
    }

    #[test]
    fn grammar_with_params_and_case() {
        let src = r#"grammar Tsymsplit/1 : () hint(show Tsym) hint(macro none) = Tvar(B_1) | ..."#;
        let tops = parse_str(src).unwrap();
        let Top::Grammar(g) = &tops[0] else { panic!() };
        assert_eq!(g.name.text, "Tsymsplit");
        assert_eq!(g.case.as_ref().unwrap().text, "1");
        assert_eq!(g.hints.len(), 2);
        assert!(g.productions.is_some());
    }

    #[test]
    fn grammar_forward_decl_no_body() {
        let src = r#"grammar Bu32 : u32"#;
        let tops = parse_str(src).unwrap();
        let Top::Grammar(g) = &tops[0] else { panic!() };
        assert!(g.productions.is_none());
    }

    #[test]
    fn mixed_top_forms() {
        let src = r#"
            syntax foo = nat
            var n : nat
            relation R: nat |- nat
            rule R: 0 |- 0
            def $f(nat) : nat
            def $f(0) = 0
            grammar G : nat = 0
        "#;
        let tops = parse_str(src).unwrap();
        assert_eq!(tops.len(), 7);
        assert!(matches!(tops[0], Top::Syntax(_)));
        assert!(matches!(tops[1], Top::Var(_)));
        assert!(matches!(tops[2], Top::Relation(_)));
        assert!(matches!(tops[3], Top::Rule(_)));
        assert!(matches!(tops[4], Top::DefSig(_)));
        assert!(matches!(tops[5], Top::DefClause(_)));
        assert!(matches!(tops[6], Top::Grammar(_)));
    }

    #[test]
    fn syntax_extension_alts_with_dotdotdot() {
        // `syntax absheaptype/sem = | ... | BOT` — `...` is an alternative.
        let src = r#"syntax absheaptype/sem = | ... | BOT"#;
        let tops = parse_str(src).unwrap();
        let Top::Syntax(s) = &tops[0] else { panic!() };
        let Some(SyntaxBody::Variant(alts)) = &s.body else {
            panic!()
        };
        // Two alts: `...` and `BOT`.
        assert_eq!(alts.len(), 2);
    }
}
