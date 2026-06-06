//! SpecTec parser (Phase 1: structurally parses `syntax` and `def`).
//!
//! Style: hand-rolled combinator style. Each sub-parser is a pure
//! function `fn(&mut &[Spanned]) -> Result<T, Diagnostic>` — input slice
//! goes in, residual slice comes out via the `&mut`. No traits, no
//! interior mutability, no `unsafe`. Designed to mirror the textbook
//! parser-combinator shape `Tokens → Result<(T, Tokens), Err>`, which
//! ports cleanly to a kernel-verifiable function later.
//!
//! What Phase 1 covers structurally:
//!
//! - `syntax NAME[/profile][(params)] [hint(...)]* [= variant|record|alias]`
//! - `def $NAME(arg_tys) : ret_ty [hint(...)]*` (signature)
//! - `def $NAME(pats) = rhs [-- premise]*` (clause)
//!
//! Other top-level forms (`relation`, `rule`, `var`, `grammar`) are
//! collected into [`Top::Other`] as raw token runs. Phase 2 structures
//! them.

use crate::cst::{
    Alt, DefClause, DefSig, HintAtom, Ident, RecordField, SyntaxBody, SyntaxDecl, Top, TokenRun,
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
fn peek<'a>(input: &'a [Spanned]) -> Option<&'a Spanned> {
    input.first()
}

/// Construct a diagnostic at the end of `file`.
fn eof_diag(file: FileId, msg: impl Into<String>) -> Diagnostic {
    Diagnostic::error(Span::new(file, u32::MAX, u32::MAX), msg)
}

/// Consume the next token if it equals `expected`. Returns its span.
fn eat<'a>(input: &mut &'a [Spanned], expected: &Token) -> Option<Span> {
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
fn expect<'a>(
    input: &mut &'a [Spanned],
    file: FileId,
    expected: &Token,
) -> Result<Span, Diagnostic> {
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
fn parse_ident_or_keyword<'a>(
    input: &mut &'a [Spanned],
    file: FileId,
) -> Result<Ident, Diagnostic> {
    // Backtick escape: `` ` `` followed by an identifier, a keyword, or
    // certain punctuation tokens like `...` (`` `... `` is a real
    // identifier in `X.1-notation.syntax.spectec` line 18).
    if let Some(Spanned { token: Token::Backtick, span: bt_span }) = input.first() {
        let bt_span = *bt_span;
        // First check special-case escapes that aren't idents/keywords.
        if let Some(Spanned { token: Token::DotDotDot, span: tail }) = input.get(1) {
            let span = bt_span.join(*tail);
            *input = &input[2..];
            return Ok(Ident { span, text: "`...".to_string() });
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
        Some(Spanned { token: Token::Ident(t), span }) => (t.clone(), *span),
        Some(Spanned { token: Token::Syntax, span }) => ("syntax".to_string(), *span),
        Some(Spanned { token: Token::Def, span }) => ("def".to_string(), *span),
        Some(Spanned { token: Token::Relation, span }) => ("relation".to_string(), *span),
        Some(Spanned { token: Token::Rule, span }) => ("rule".to_string(), *span),
        Some(Spanned { token: Token::Var, span }) => ("var".to_string(), *span),
        Some(Spanned { token: Token::Grammar, span }) => ("grammar".to_string(), *span),
        Some(Spanned { token: Token::Hint, span }) => ("hint".to_string(), *span),
        Some(Spanned { token: Token::If, span }) => ("if".to_string(), *span),
        Some(Spanned { token: Token::Let, span }) => ("let".to_string(), *span),
        Some(Spanned { token: Token::Else, span }) => ("else".to_string(), *span),
        Some(Spanned { token: Token::Otherwise, span }) => ("otherwise".to_string(), *span),
        Some(Spanned { token: Token::Eps, span }) => ("eps".to_string(), *span),
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
fn parse_profile_label<'a>(
    input: &mut &'a [Spanned],
    file: FileId,
) -> Result<Ident, Diagnostic> {
    match input.first() {
        Some(Spanned { token: Token::Ident(t), span }) => {
            let id = Ident { span: *span, text: t.clone() };
            *input = &input[1..];
            Ok(id)
        }
        Some(Spanned { token: Token::Nat(n), span }) => {
            let id = Ident { span: *span, text: n.to_string() };
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
        Token::Syntax
            | Token::Def
            | Token::Relation
            | Token::Rule
            | Token::Var
            | Token::Grammar
    )
}

/// True if `tok` at index `i` of `tokens` is preceded by a slash (`/`).
/// We use this to recognise paths like `Heaptype_sub/def` where `def`
/// is part of the identifier path, not a fresh top-level keyword.
fn preceded_by_slash(tokens: &[Spanned], i: usize) -> bool {
    i > 0 && matches!(tokens[i - 1].token, Token::Slash)
}

// ---------- top-level dispatch ----------

fn parse_top(file: FileId, input: &mut &[Spanned]) -> Result<Top, Diagnostic> {
    let first = peek(input).expect("caller ensures non-empty");
    match first.token {
        Token::Syntax => parse_syntax(file, input).map(Top::Syntax),
        Token::Def => parse_def(file, input),
        Token::Relation | Token::Rule | Token::Var | Token::Grammar => {
            Ok(Top::Other(take_until_next_top(input)))
        }
        _ => Err(Diagnostic::error(
            first.span,
            format!(
                "expected `syntax`, `def`, `relation`, `rule`, `var`, or `grammar`, found {}",
                first.token.describe()
            ),
        )),
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
        match &s.token {
            Token::LParen | Token::LBracket | Token::LBrace => depth += 1,
            Token::RParen | Token::RBracket | Token::RBrace => depth -= 1,
            _ => {}
        }
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
            .map(|f| f.span)
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
    if let Some(Spanned { token: Token::LBrace, .. }) = peek(input) {
        return parse_record_body(file, input);
    }

    // Variant or alias? Take everything up to the next top-level keyword,
    // then look for `Pipe` at depth 0.
    let body_run = take_until_next_top(input);
    if contains_top_level_pipe(&body_run.tokens) {
        Ok(SyntaxBody::Variant(split_alts(&body_run)?))
    } else {
        Ok(SyntaxBody::Alias(body_run))
    }
}

/// Parse a record body `{ FIELD ty [hints*], FIELD ty [hints*], ... }`.
/// Phase 1: store each field's type as a raw `TokenRun`.
fn parse_record_body(file: FileId, input: &mut &[Spanned]) -> Result<SyntaxBody, Diagnostic> {
    let lbrace_span = expect(input, file, &Token::LBrace)?;
    let mut fields = Vec::new();

    // Handle empty record `{}`.
    if eat(input, &Token::RBrace).is_some() {
        return Ok(SyntaxBody::Record(fields));
    }

    loop {
        // Skip a leading `...` in the field list (used for forward extension).
        if eat(input, &Token::DotDotDot).is_some() {
            // No structured representation in Phase 1; ignore.
        } else {
            let name = parse_ident_or_keyword(input, file)?;
            let ty = take_field_ty(input);
            let hints = parse_hints(input)?;
            let mut span = name.span;
            span = span.join(ty.span);
            for h in &hints {
                span = span.join(h.span);
            }
            fields.push(RecordField {
                span,
                name,
                ty,
                hints,
            });
        }

        match peek(input) {
            Some(Spanned { token: Token::Comma, .. }) => {
                *input = &input[1..];
                continue;
            }
            Some(Spanned { token: Token::RBrace, .. }) => {
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
            Token::Hint if depth == 0 => break,
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
        match &t.token {
            Token::LParen | Token::LBracket | Token::LBrace => depth += 1,
            Token::RParen | Token::RBracket | Token::RBrace => depth -= 1,
            Token::Pipe if depth == 0 => return true,
            _ => {}
        }
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
        match &t.token {
            Token::LParen | Token::LBracket | Token::LBrace => depth += 1,
            Token::RParen | Token::RBracket | Token::RBrace => depth -= 1,
            Token::Pipe if depth == 0 => {
                push_alt(&run.tokens[chunk_start..cur], &mut alts)?;
                chunk_start = cur + 1;
            }
            _ => {}
        }
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
fn extract_trailing_hints(
    slice: &[Spanned],
) -> Result<(&[Spanned], Vec<HintAtom>), Diagnostic> {
    // Walk from the end: a hint clause is `hint ( ... )` taking up
    // contiguous tokens including the keyword. We scan from the right
    // looking for `Hint LParen ... RParen` runs.
    //
    // Simpler approach: scan from the left, collect a prefix until we hit
    // a `hint` token at depth 0, then everything from there is a hint
    // sequence. Reasoning: hints always come at the end of an alternative
    // in well-formed SpecTec, never in the middle.
    let mut depth: i32 = 0;
    let mut first_hint: Option<usize> = None;
    for (i, t) in slice.iter().enumerate() {
        match &t.token {
            Token::LParen | Token::LBracket | Token::LBrace => depth += 1,
            Token::RParen | Token::RBracket | Token::RBrace => depth -= 1,
            Token::Hint if depth == 0 => {
                first_hint = Some(i);
                break;
            }
            _ => {}
        }
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
        Some(Spanned { token: Token::Colon, .. }) => {
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
        Some(Spanned { token: Token::Eq, .. }) => {
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
        Some(Spanned { token: Token::Hint, .. }) | None => {
            let hints = parse_hints(input)?;
            // Sanity: we should now be at EOF or a top-level keyword.
            if let Some(s) = peek(input) {
                if !is_top_level_keyword(&s.token) {
                    return Err(Diagnostic::error(
                        s.span,
                        format!(
                            "expected `:`, `=`, `hint(...)`, or next top-level form after `def $NAME`, found {}",
                            s.token.describe()
                        ),
                    ));
                }
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
        let tr = take_until_paren_balanced(input, |t| {
            matches!(t, Token::Comma | Token::RParen)
        });
        out.push(tr);
        match peek(input) {
            Some(Spanned { token: Token::Comma, .. }) => {
                *input = &input[1..];
            }
            Some(Spanned { token: Token::RParen, .. }) => {
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
fn take_until_paren_balanced(
    input: &mut &[Spanned],
    stop: impl Fn(&Token) -> bool,
) -> TokenRun {
    let mut depth: i32 = 0;
    let mut span: Option<Span> = None;
    let mut tokens = Vec::new();
    let mut cursor: &[Spanned] = input;
    while let Some(s) = cursor.first() {
        if depth == 0 && stop(&s.token) {
            break;
        }
        match &s.token {
            Token::LParen | Token::LBracket | Token::LBrace => depth += 1,
            Token::RParen | Token::RBracket | Token::RBrace => depth -= 1,
            _ => {}
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
    take_until_top_level(input, |t| matches!(t, Token::Hint))
        .and_join_top_keyword_stop(input)
}

/// After `def $NAME(args) =`, the RHS continues until either `--` (a
/// premise) or the next top-level keyword. Following `--` tokens up to
/// either another `--` or a top-level keyword form a premise.
fn take_def_clause_rhs_and_premises(input: &mut &[Spanned]) -> (TokenRun, Vec<TokenRun>) {
    let rhs = take_until_top_level(input, |t| matches!(t, Token::DashDash))
        .and_join_top_keyword_stop(input);
    let mut premises = Vec::new();
    while let Some(Spanned { token: Token::DashDash, .. }) = peek(input) {
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
fn take_until_top_level(
    input: &mut &[Spanned],
    stop: impl Fn(&Token) -> bool,
) -> TokenRun {
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
        match &s.token {
            Token::LParen | Token::LBracket | Token::LBrace => depth += 1,
            Token::RParen | Token::RBracket | Token::RBrace => depth -= 1,
            _ => {}
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
    while let Some(Spanned { token: Token::Hint, .. }) = peek(input) {
        out.push(parse_hint(input)?);
    }
    Ok(out)
}

fn parse_hint(input: &mut &[Spanned]) -> Result<HintAtom, Diagnostic> {
    let hint_span = match input.first() {
        Some(Spanned { token: Token::Hint, span }) => {
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
        match &s.token {
            Token::RParen if depth == 0 => break,
            Token::LParen | Token::LBracket | Token::LBrace => depth += 1,
            Token::RParen | Token::RBracket | Token::RBrace => depth -= 1,
            _ => {}
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
        let Top::Syntax(s) = &with_pipe[0] else { panic!() };
        let Some(SyntaxBody::Variant(alts)) = &s.body else { panic!() };
        assert_eq!(alts.len(), 2);

        let without_pipe = parse_str("syntax numtype = I32 | I64 | F32 | F64").unwrap();
        let Top::Syntax(s) = &without_pipe[0] else { panic!() };
        let Some(SyntaxBody::Variant(alts)) = &s.body else { panic!() };
        assert_eq!(alts.len(), 4);
    }

    #[test]
    fn syntax_record() {
        let src = r#"syntax point = { X nat, Y nat }"#;
        let tops = parse_str(src).unwrap();
        let Top::Syntax(s) = &tops[0] else { panic!() };
        let Some(SyntaxBody::Record(fields)) = &s.body else { panic!() };
        assert_eq!(fields.len(), 2);
        assert_eq!(fields[0].name.text, "X");
        assert_eq!(fields[1].name.text, "Y");
    }

    #[test]
    fn syntax_record_with_extension_dots() {
        let src = r#"syntax context/sem = { ..., RECS subtype* }"#;
        let tops = parse_str(src).unwrap();
        let Top::Syntax(s) = &tops[0] else { panic!() };
        assert_eq!(s.profile.as_ref().unwrap().text, "sem");
        let Some(SyntaxBody::Record(fields)) = &s.body else { panic!() };
        // The `...` is skipped; only `RECS subtype*` becomes a structured field.
        assert_eq!(fields.len(), 1);
        assert_eq!(fields[0].name.text, "RECS");
    }

    #[test]
    fn syntax_with_profile_and_params() {
        let src = "syntax fN(N) = | POS fNmag(N) | NEG fNmag(N)";
        let tops = parse_str(src).unwrap();
        let Top::Syntax(s) = &tops[0] else { panic!() };
        assert_eq!(s.name.text, "fN");
        assert_eq!(s.params.len(), 1);
        let Some(SyntaxBody::Variant(alts)) = &s.body else { panic!() };
        assert_eq!(alts.len(), 2);
    }

    #[test]
    fn syntax_with_hints() {
        let src = r#"syntax bit hint(desc "bit") = 0 | 1"#;
        let tops = parse_str(src).unwrap();
        let Top::Syntax(s) = &tops[0] else { panic!() };
        assert_eq!(s.hints.len(), 1);
        let Some(SyntaxBody::Variant(alts)) = &s.body else { panic!() };
        assert_eq!(alts.len(), 2);
    }

    #[test]
    fn syntax_alternative_hints_attach_to_alt() {
        let src = r#"syntax x =
            | POS fNmag(N) hint(show $(+%))
            | NEG fNmag(N) hint(show $(-%))"#;
        let tops = parse_str(src).unwrap();
        let Top::Syntax(s) = &tops[0] else { panic!() };
        let Some(SyntaxBody::Variant(alts)) = &s.body else { panic!() };
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
        let Top::DefClause(d) = &tops[0] else { panic!() };
        assert_eq!(d.name.text, "sum");
        assert_eq!(d.arg_pats.len(), 1);
        assert!(d.premises.is_empty());
        // RHS just contains `0`.
        assert_eq!(d.rhs.tokens.len(), 1);
        assert!(matches!(d.rhs.tokens[0].token, Token::Nat(0)));
    }

    #[test]
    fn def_clause_with_premises() {
        let src = r#"def $min(i, j) = i  -- if $(i <= j)"#;
        let tops = parse_str(src).unwrap();
        let Top::DefClause(d) = &tops[0] else { panic!() };
        assert_eq!(d.premises.len(), 1);
    }

    #[test]
    fn def_clause_with_otherwise() {
        let src = r#"def $min(i, j) = j  -- otherwise"#;
        let tops = parse_str(src).unwrap();
        let Top::DefClause(d) = &tops[0] else { panic!() };
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
    fn relation_folds_to_other() {
        let src = r#"
            relation Foo: nat |- nat
            syntax x = nat
        "#;
        let tops = parse_str(src).unwrap();
        assert_eq!(tops.len(), 2);
        assert!(matches!(tops[0], Top::Other(_)));
        assert!(matches!(tops[1], Top::Syntax(_)));
    }

    #[test]
    fn rule_var_grammar_fold_to_other() {
        let src = r#"
            rule Foo/bar: x
            var n : nat
            grammar G : nat = 0
        "#;
        let tops = parse_str(src).unwrap();
        assert_eq!(tops.len(), 3);
        assert!(tops.iter().all(|t| matches!(t, Top::Other(_))));
    }

    #[test]
    fn syntax_extension_alts_with_dotdotdot() {
        // `syntax absheaptype/sem = | ... | BOT` — `...` is an alternative.
        let src = r#"syntax absheaptype/sem = | ... | BOT"#;
        let tops = parse_str(src).unwrap();
        let Top::Syntax(s) = &tops[0] else { panic!() };
        let Some(SyntaxBody::Variant(alts)) = &s.body else { panic!() };
        // Two alts: `...` and `BOT`.
        assert_eq!(alts.len(), 2);
    }
}
