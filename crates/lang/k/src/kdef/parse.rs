//! A [`winnow`]-based parser for the **`.k` source** grammar fragment
//! ([`crate::kdef::ast`]).
//!
//! Scope: enough of K's outer syntax to read the *grammar* of a simple
//! tutorial language — `requires`, `module`/`endmodule`, `imports`, and
//! `syntax Sort ::= …` productions (terminals, non-terminals with optional
//! `name:` labels, `|` alternatives, `>` priority blocks, block-level
//! `left:`/`right:`/`non-assoc:` tags, `[attr]` lists, `List{S,"sep"}` /
//! `NeList{…}` sugar). Non-`syntax` sentences (`rule`/`context`/
//! `configuration`/`claim`) and out-of-line `syntax priority`/`syntax left`
//! declarations are **skipped** (scanned to the next sentence boundary) and
//! counted — this frontend reads grammar, not semantics.
//!
//! The grammar surface is sourced + verified in `notes/vibes/k/research/`; the
//! load-bearing facts: `>` separates priority blocks (leftmost binds tightest),
//! terminals are double-quoted, non-terminals are bare sort names, a lone
//! non-terminal RHS is a subsort/injection.
//!
//! We build on `winnow` (via its workspace wrapper `covalence_parse::winnow`)
//! rather than a hand-rolled scanner so the parser can grow toward a larger
//! subset of K — see `SKELETONS.md` for what is deferred.

use covalence_parse::winnow::{
    ModalResult, Parser,
    combinator::{alt, eof, opt, separated},
    error::{ContextError, ParseError as WinnowParseError, StrContext, StrContextValue},
    token::{literal, one_of, take_while},
};
use smol_str::SmolStr;

use crate::kdef::ast::{
    Assoc, Attr, Import, KDefinition, KModule, KRule, ListDecl, PriorityBlock, ProdItem,
    Production, RuleTerm, Sort, SyntaxDecl,
};

/// A parse error with a byte offset into the `.k` source.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("k-definition parse error at byte {offset}: {message}")]
pub struct ParseError {
    pub offset: usize,
    pub message: String,
}

/// Map a byte `offset` into `src` to a 1-based `(line, column)` pair.
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

/// Parse a whole `.k` file into a [`KDefinition`] (grammar fragment only).
pub fn parse_definition(src: &str) -> Result<KDefinition, ParseError> {
    definition
        .parse(src)
        .map_err(|e: WinnowParseError<&str, ContextError>| ParseError {
            offset: e.offset(),
            message: describe(e.inner()),
        })
}

fn describe(err: &ContextError) -> String {
    let ctx: Vec<String> = err.context().map(|c| c.to_string()).collect();
    if ctx.is_empty() {
        "unexpected input".to_string()
    } else {
        ctx.join("; ")
    }
}

// ---------------------------------------------------------------------------
// Trivia (whitespace + // line and /* block */ comments)
// ---------------------------------------------------------------------------

/// Return `s` with leading whitespace and comments removed — the pure
/// look-ahead helper the token parsers and boundary checks share.
fn strip_trivia(mut s: &str) -> &str {
    loop {
        let before = s;
        s = s.trim_start();
        if let Some(rest) = s.strip_prefix("//") {
            s = rest.find('\n').map_or("", |i| &rest[i..]);
        } else if let Some(rest) = s.strip_prefix("/*") {
            s = rest.find("*/").map_or("", |i| &rest[i + 2..]);
        }
        if s == before {
            return s;
        }
    }
}

/// Consume leading trivia from the stream.
fn trivia(input: &mut &str) -> ModalResult<()> {
    let stripped = strip_trivia(input);
    let n = input.len() - stripped.len();
    *input = &input[n..];
    Ok(())
}

// ---------------------------------------------------------------------------
// Tokens (each consumes leading trivia first)
// ---------------------------------------------------------------------------

fn is_ident_start(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_' || c == '#'
}
fn is_ident_continue(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_' || c == '-'
}

/// An identifier / sort / module / attribute-key token (`[A-Za-z_#][\w-]*`).
fn ident<'a>(input: &mut &'a str) -> ModalResult<&'a str> {
    trivia(input)?;
    (one_of(is_ident_start), take_while(0.., is_ident_continue))
        .take()
        .parse_next(input)
}

/// Match the exact keyword `word` (a whole identifier equal to it).
fn keyword<'a>(word: &'static str) -> impl Fn(&mut &'a str) -> ModalResult<()> {
    move |input: &mut &'a str| {
        ident
            .verify(|s: &&str| *s == word)
            .void()
            .context(StrContext::Expected(StrContextValue::StringLiteral(word)))
            .parse_next(input)
    }
}

/// Match a punctuation symbol (after trivia).
fn sym<'a>(s: &'static str) -> impl Fn(&mut &'a str) -> ModalResult<()> {
    move |input: &mut &'a str| {
        trivia(input)?;
        literal(s)
            .void()
            .context(StrContext::Expected(StrContextValue::StringLiteral(s)))
            .parse_next(input)
    }
}

/// A double-quoted terminal string with `\" \\ \n \t \r` escapes; returns the
/// decoded contents (without the quotes).
fn string_lit(input: &mut &str) -> ModalResult<String> {
    trivia(input)?;
    literal("\"")
        .context(StrContext::Expected(StrContextValue::Description(
            "double-quoted terminal",
        )))
        .parse_next(input)?;
    let mut out = String::new();
    loop {
        let mut chars = input.chars();
        let Some(c) = chars.next() else {
            return Err(fail("unterminated string terminal"));
        };
        let rest = chars.as_str();
        match c {
            '"' => {
                *input = rest;
                return Ok(out);
            }
            '\\' => {
                let Some(e) = rest.chars().next() else {
                    return Err(fail("unterminated escape in string terminal"));
                };
                let after = &rest[e.len_utf8()..];
                match e {
                    'n' => out.push('\n'),
                    't' => out.push('\t'),
                    'r' => out.push('\r'),
                    '"' => out.push('"'),
                    '\\' => out.push('\\'),
                    other => {
                        // Preserve unknown escapes verbatim (permissive).
                        out.push('\\');
                        out.push(other);
                    }
                }
                *input = after;
            }
            other => {
                out.push(other);
                *input = rest;
            }
        }
    }
}

/// A hard, non-backtracking failure carrying a message (as a context label).
fn fail(msg: &'static str) -> covalence_parse::winnow::error::ErrMode<ContextError> {
    let mut e = ContextError::new();
    e.extend([StrContext::Label(msg)]);
    covalence_parse::winnow::error::ErrMode::Cut(e)
}

// ---------------------------------------------------------------------------
// Sentence-boundary keywords
// ---------------------------------------------------------------------------

const TOP_KEYWORDS: &[&str] = &[
    "syntax",
    "rule",
    "context",
    "configuration",
    "claim",
    "imports",
    "import",
    "endmodule",
    "module",
    "requires",
    "require",
];

/// The leading identifier at `s` (after trivia), if any — used for look-ahead.
fn peek_ident(s: &str) -> Option<&str> {
    let s = strip_trivia(s);
    let mut it = s.char_indices();
    let (_, first) = it.next()?;
    if !is_ident_start(first) {
        return None;
    }
    let end = it
        .find(|(_, c)| !is_ident_continue(*c))
        .map_or(s.len(), |(i, _)| i);
    Some(&s[..end])
}

/// Whether the stream is at a sentence boundary (next top-level keyword, or eof).
fn at_sentence_boundary(s: &str) -> bool {
    let s = strip_trivia(s);
    s.is_empty() || peek_ident(s).is_some_and(|w| TOP_KEYWORDS.contains(&w))
}

// ---------------------------------------------------------------------------
// Grammar
// ---------------------------------------------------------------------------

fn definition(input: &mut &str) -> ModalResult<KDefinition> {
    let mut requires = Vec::new();
    let mut modules = Vec::new();
    loop {
        trivia(input)?;
        if input.is_empty() {
            break;
        }
        match peek_ident(input) {
            Some("requires" | "require") => {
                ident(input)?; // consume keyword
                requires.push(string_lit(input)?);
            }
            Some("module") => modules.push(module(input)?),
            _ => {
                return Err(fail("expected `requires` or `module` at top level"));
            }
        }
    }
    let _: () = eof.void().parse_next(input)?;
    Ok(KDefinition { requires, modules })
}

fn module(input: &mut &str) -> ModalResult<KModule> {
    keyword("module")(input)?;
    let name = SmolStr::new(ident(input)?);
    let attrs = opt(attr_list).parse_next(input)?.unwrap_or_default();

    let mut imports = Vec::new();
    let mut syntax = Vec::new();
    let mut rules = Vec::new();
    let mut skipped_sentences = 0usize;

    loop {
        trivia(input)?;
        match peek_ident(input) {
            Some("endmodule") => {
                keyword("endmodule")(input)?;
                break;
            }
            None if input.is_empty() => {
                return Err(fail(
                    "unexpected end of input inside module (missing `endmodule`)",
                ));
            }
            Some("imports" | "import") => imports.push(import(input)?),
            Some("syntax") => {
                // Lenient: a production we can't parse (K's unquoted-terminal /
                // mixfix forms beyond our grammar fragment) is skipped, not fatal,
                // so a real `.k` still yields its rules. A parse that stops
                // *mid-sentence* (partial success, e.g. `separated` giving up at a
                // `|` before an unparseable alternative) is also treated as a skip.
                let mut probe = *input;
                match syntax_sentence(&mut probe) {
                    Ok(decl) if at_sentence_boundary(probe) => {
                        *input = probe;
                        match decl {
                            Some(d) => syntax.push(d),
                            None => skipped_sentences += 1,
                        }
                    }
                    _ => {
                        skip_sentence(input)?;
                        skipped_sentences += 1;
                    }
                }
            }
            Some("rule") => {
                // Lenient likewise: rules outside the prefix fragment (cells,
                // `~>`, nested `=>`) are skipped rather than fatal.
                let mut probe = *input;
                match rule_sentence(&mut probe) {
                    Ok(r) => {
                        *input = probe;
                        rules.push(r);
                    }
                    Err(_) => {
                        skip_sentence(input)?;
                        skipped_sentences += 1;
                    }
                }
            }
            Some("context" | "configuration" | "claim") => {
                skip_sentence(input)?;
                skipped_sentences += 1;
            }
            _ => return Err(fail("expected a sentence keyword or `endmodule`")),
        }
    }

    Ok(KModule {
        name,
        attrs,
        imports,
        syntax,
        rules,
        skipped_sentences,
    })
}

/// Parse a standalone **program term** in the prefix fragment (a whole
/// `sym(args…)` / variable term) — the reader for programs a `KSession` reduces.
pub fn parse_term(src: &str) -> Result<RuleTerm, ParseError> {
    let mut p = src;
    let t = rule_term(&mut p)
        .and_then(|t| {
            trivia(&mut p)?;
            if p.is_empty() {
                Ok(t)
            } else {
                Err(fail("unexpected trailing input after term"))
            }
        })
        .map_err(|e: covalence_parse::winnow::error::ErrMode<ContextError>| {
            let offset = src.len() - p.len();
            ParseError {
                offset,
                message: match e {
                    covalence_parse::winnow::error::ErrMode::Backtrack(c)
                    | covalence_parse::winnow::error::ErrMode::Cut(c) => describe(&c),
                    _ => "incomplete input".to_string(),
                },
            }
        })?;
    Ok(t)
}

/// Parse a `rule` sentence in the prefix-term fragment:
/// `rule LHS => RHS [requires REQ] [ATTRS]`. Errors (→ the caller skips it) on
/// anything outside the fragment: cells `<k>`, `~>`, nested/local `=>`.
fn rule_sentence(input: &mut &str) -> ModalResult<KRule> {
    keyword("rule")(input)?;
    // Optional `[label]:` prefix.
    if strip_trivia(input).starts_with('[') {
        let mut probe = *input;
        if attr_list(&mut probe).is_ok() && strip_trivia(probe).starts_with(':') {
            *input = probe;
            sym(":")(input)?;
        }
    }
    let lhs = rule_term(input)?;
    sym("=>")(input)?;
    let rhs = rule_term(input)?;
    // Reject a second (nested/sequenced) `=>` — outside the fragment.
    if strip_trivia(input).starts_with("=>") {
        return Err(fail(
            "nested/multiple `=>` not supported (prefix fragment only)",
        ));
    }
    let requires = if peek_ident(input) == Some("requires") {
        keyword("requires")(input)?;
        Some(rule_term(input)?)
    } else {
        None
    };
    // Ignore `ensures` (post-condition) if present.
    if peek_ident(input) == Some("ensures") {
        keyword("ensures")(input)?;
        let _ = rule_term(input)?;
    }
    let attrs = opt(attr_list).parse_next(input)?.unwrap_or_default();
    // The rule must end at a sentence boundary; otherwise it used syntax we
    // don't model — bail so the caller skips it.
    if !at_sentence_boundary(input) {
        return Err(fail(
            "trailing rule syntax not supported (prefix fragment only)",
        ));
    }
    Ok(KRule {
        lhs,
        rhs,
        requires,
        attrs,
    })
}

/// A prefix rule/program term: `sym(args…)` (constructor application, nullary
/// written `sym()`), or a bare `name[:Sort]` (variable). Cells, `~>`, operators,
/// and `[…]`/`{…}` collection syntax are rejected (→ caller skips the rule).
fn rule_term(input: &mut &str) -> ModalResult<RuleTerm> {
    let name = SmolStr::new(ident(input)?);
    trivia(input)?;
    if strip_trivia(input).starts_with('(') {
        sym("(")(input)?;
        let args: Vec<RuleTerm> = if strip_trivia(input).starts_with(')') {
            Vec::new()
        } else {
            separated(1.., rule_term, sym(",")).parse_next(input)?
        };
        sym(")")(input)?;
        Ok(RuleTerm::App { sym: name, args })
    } else if strip_trivia(input).starts_with(':') {
        sym(":")(input)?;
        let sort = parse_sort(input)?;
        Ok(RuleTerm::Var {
            name,
            sort: Some(sort),
        })
    } else {
        Ok(RuleTerm::Var { name, sort: None })
    }
}

fn import(input: &mut &str) -> ModalResult<Import> {
    alt((keyword("imports"), keyword("import"))).parse_next(input)?;
    let public = match peek_ident(input) {
        Some("public") => {
            ident(input)?;
            Some(true)
        }
        Some("private") => {
            ident(input)?;
            Some(false)
        }
        _ => None,
    };
    let name = SmolStr::new(ident(input)?);
    Ok(Import { name, public })
}

/// Parse a `syntax …` sentence. Returns `None` if it was an out-of-line form
/// (`syntax priority`/`syntax left …`/`syntax lexical …`) that we skip.
fn syntax_sentence(input: &mut &str) -> ModalResult<Option<SyntaxDecl>> {
    keyword("syntax")(input)?;
    // Out-of-line priority / associativity / lexical declarations: skip.
    if let Some("priority" | "priorities" | "left" | "right" | "non-assoc" | "lexical") =
        peek_ident(input)
    {
        skip_sentence(input)?;
        return Ok(None);
    }

    let sort = parse_sort(input)?;
    trivia(input)?;
    if opt(sym("::=")).parse_next(input)?.is_none() {
        // Bare sort declaration: `syntax Foo [attrs]`.
        let attrs = opt(attr_list).parse_next(input)?.unwrap_or_default();
        return Ok(Some(SyntaxDecl {
            sort,
            blocks: Vec::new(),
            list: None,
            attrs,
        }));
    }

    // `List{Elem,"sep"}` / `NeList{Elem,"sep"}` sugar?
    if let Some(w @ ("List" | "NeList")) = peek_ident(input) {
        let list = list_decl(input, w == "NeList")?;
        return Ok(Some(SyntaxDecl {
            sort,
            blocks: Vec::new(),
            list: Some(list),
            attrs: Vec::new(),
        }));
    }

    // Priority blocks, `>`-separated (leftmost binds tightest).
    let blocks: Vec<PriorityBlock> = separated(1.., priority_block, sym(">")).parse_next(input)?;
    Ok(Some(SyntaxDecl {
        sort,
        blocks,
        list: None,
        attrs: Vec::new(),
    }))
}

fn list_decl(input: &mut &str, non_empty: bool) -> ModalResult<ListDecl> {
    ident(input)?; // List | NeList
    sym("{")(input)?;
    let elem = parse_sort(input)?;
    sym(",")(input)?;
    let sep = string_lit(input)?;
    sym("}")(input)?;
    let attrs = opt(attr_list).parse_next(input)?.unwrap_or_default();
    Ok(ListDecl {
        non_empty,
        elem,
        sep,
        attrs,
    })
}

fn priority_block(input: &mut &str) -> ModalResult<PriorityBlock> {
    let assoc = opt(assoc_tag).parse_next(input)?;
    let prods: Vec<Production> = separated(1.., production, sym("|")).parse_next(input)?;
    Ok(PriorityBlock { assoc, prods })
}

/// A block-leading `left:` / `right:` / `non-assoc:` tag (only matches when the
/// keyword is immediately followed by a single `:`).
fn assoc_tag(input: &mut &str) -> ModalResult<Assoc> {
    let a = match peek_ident(input) {
        Some("left") => Assoc::Left,
        Some("right") => Assoc::Right,
        Some("non-assoc") => Assoc::NonAssoc,
        _ => return Err(backtrack()),
    };
    // Require a following single colon (not `::=`); otherwise this is a
    // production, not an assoc tag.
    let after_kw = strip_trivia(&input[input.len() - strip_trivia(input).len()..]);
    let _ = after_kw;
    // Look ahead on a copy: ident then ':' but not "::=".
    let mut probe = *input;
    ident(&mut probe)?;
    let p = strip_trivia(probe);
    if !p.starts_with(':') || p.starts_with("::=") {
        return Err(backtrack());
    }
    // Commit.
    ident(input)?;
    sym(":")(input)?;
    Ok(a)
}

fn production(input: &mut &str) -> ModalResult<Production> {
    let mut items = Vec::new();
    loop {
        trivia(input)?;
        if production_ends(input) {
            break;
        }
        items.push(prod_item(input)?);
    }
    if items.is_empty() {
        return Err(fail(
            "empty production (expected a terminal or non-terminal)",
        ));
    }
    let attrs = opt(attr_list).parse_next(input)?.unwrap_or_default();
    Ok(Production { items, attrs })
}

/// Whether the current position ends a production: an attribute list `[`, an
/// alternative `|`, a priority drop `>`, or a sentence boundary.
fn production_ends(s: &str) -> bool {
    let s = strip_trivia(s);
    s.starts_with('[') || s.starts_with('|') || s.starts_with('>') || at_sentence_boundary(s)
}

fn prod_item(input: &mut &str) -> ModalResult<ProdItem> {
    trivia(input)?;
    if input.starts_with('"') {
        return Ok(ProdItem::Terminal(string_lit(input)?));
    }
    if input.starts_with("r\"") {
        return Err(fail(
            "regex/token production items (r\"…\") are not supported yet",
        ));
    }
    // A non-terminal: optional `label:` then a sort.
    let first = SmolStr::new(ident(input)?);
    // Distinguish `label: Sort` from a bare `Sort`.
    let p = strip_trivia(input);
    if p.starts_with(':') && !p.starts_with("::=") {
        sym(":")(input)?;
        let sort = parse_sort(input)?;
        Ok(ProdItem::NonTerminal {
            label: Some(first),
            sort,
        })
    } else {
        let params = opt(sort_params).parse_next(input)?.unwrap_or_default();
        Ok(ProdItem::NonTerminal {
            label: None,
            sort: Sort {
                name: first,
                params,
            },
        })
    }
}

fn parse_sort(input: &mut &str) -> ModalResult<Sort> {
    let name = SmolStr::new(
        ident
            .context(StrContext::Expected(StrContextValue::Description(
                "a sort name",
            )))
            .parse_next(input)?,
    );
    let params = opt(sort_params).parse_next(input)?.unwrap_or_default();
    Ok(Sort { name, params })
}

fn sort_params(input: &mut &str) -> ModalResult<Vec<Sort>> {
    trivia(input)?;
    if !strip_trivia(input).starts_with('{') {
        return Err(backtrack());
    }
    sym("{")(input)?;
    let params: Vec<Sort> = separated(1.., parse_sort, sym(",")).parse_next(input)?;
    sym("}")(input)?;
    Ok(params)
}

// ---------------------------------------------------------------------------
// Attributes
// ---------------------------------------------------------------------------

fn attr_list(input: &mut &str) -> ModalResult<Vec<Attr>> {
    sym("[")(input)?;
    let attrs: Vec<Attr> = separated(0.., attr, sym(",")).parse_next(input)?;
    sym("]")(input)?;
    Ok(attrs)
}

fn attr(input: &mut &str) -> ModalResult<Attr> {
    let key = SmolStr::new(ident(input)?);
    let arg = opt(attr_arg).parse_next(input)?;
    Ok(Attr { key, arg })
}

/// `( … )` attribute argument: raw text with balanced parentheses.
fn attr_arg(input: &mut &str) -> ModalResult<String> {
    trivia(input)?;
    if !input.starts_with('(') {
        return Err(backtrack());
    }
    *input = &input[1..];
    let mut depth = 1usize;
    let mut out = String::new();
    let mut chars = input.char_indices();
    let mut consumed = 0;
    for (i, c) in chars.by_ref() {
        match c {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    consumed = i + 1;
                    break;
                }
            }
            _ => {}
        }
        out.push(c);
    }
    if depth != 0 {
        return Err(fail("unterminated attribute argument `(`"));
    }
    *input = &input[consumed..];
    Ok(out.trim().to_string())
}

// ---------------------------------------------------------------------------
// Skipping non-grammar sentences
// ---------------------------------------------------------------------------

/// Skip a whole sentence: consume tokens (tracking `[](){}` depth, skipping
/// string literals) until the next top-level sentence boundary at depth 0.
fn skip_sentence(input: &mut &str) -> ModalResult<()> {
    // Consume the leading keyword itself first so we don't immediately stop.
    ident(input)?;
    let mut depth = 0i32;
    loop {
        trivia(input)?;
        if input.is_empty() {
            return Ok(());
        }
        if depth == 0 && at_sentence_boundary(input) {
            return Ok(());
        }
        let c = input.chars().next().unwrap();
        match c {
            '"' => {
                let _ = string_lit(input)?;
            }
            '[' | '(' | '{' => {
                depth += 1;
                *input = &input[1..];
            }
            ']' | ')' | '}' => {
                depth -= 1;
                *input = &input[1..];
            }
            _ if is_ident_start(c) => {
                let _ = ident(input)?;
            }
            _ => {
                *input = &input[c.len_utf8()..];
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Error helpers
// ---------------------------------------------------------------------------

/// A recoverable (backtracking) error for `opt`/`alt`.
fn backtrack() -> covalence_parse::winnow::error::ErrMode<ContextError> {
    covalence_parse::winnow::error::ErrMode::Backtrack(ContextError::new())
}
