//! SpecTec elaboration — building mixfix operator tables from the CST.
//!
//! Phase 2c slice: this module converts a `Vec<Top>` into an
//! [`ElabContext`] holding a [`mixfix::OpTable`] populated from `relation`
//! templates (and, later, from `syntax` variant constructors). No
//! re-parsing of rule bodies, variant alternatives, or expression
//! positions yet — those use the table in subsequent slices.
//!
//! The construction is two-pass:
//!
//! 1. Gather declared **type names** from `Top::Syntax` (including
//!    profiled and parametric declarations). These determine which
//!    template-tokens count as **holes**.
//!
//! 2. For each `Top::Relation`, convert its `template` TokenRun into a
//!    `Vec<Fragment>`: type-name idents (with their trailing
//!    iteration/parameter suffix) become `Fragment::Hole`s; everything
//!    else becomes `Fragment::Lit`.
//!
//! Style: pure functions, no globals, no `unsafe`.

use std::collections::HashSet;

use crate::cst::{Alt, RuleDecl, SyntaxBody, Top, TokenRun};
use crate::mixfix::{Fragment, OpId, OpTable, Precedence};
use crate::source::{Diagnostic, Span};
use crate::token::{Spanned, Token};

/// Default precedence for relation holes. SpecTec's surface language
/// has no explicit per-operator precedence — relations all sit at the
/// bottom of the binding tower. Higher precedences come into play with
/// syntax-constructor and arithmetic operators (added later).
pub const REL_HOLE_PREC: Precedence = 0;

/// Default precedence for syntax-variant constructor arg holes.
/// Constructors bind tighter than relations (so `C |- (BLOCK x y) : t`
/// associates the way you'd expect), so we use a high precedence here.
pub const CTOR_HOLE_PREC: Precedence = 100;

/// Result of running [`build_table`].
#[derive(Debug, Default)]
pub struct ElabContext {
    pub op_table: OpTable,
    /// All declared `syntax` names (irrespective of profile or
    /// arity). Used by the template-to-fragments pass to recognise hole
    /// positions.
    pub type_names: HashSet<String>,
}

/// Build an [`ElabContext`] from parsed top-level forms.
///
/// Returns Ok even if individual relation templates fail — those errors
/// are collected and returned in the `Err` variant so the caller can
/// surface them all at once.
pub fn build_table(tops: &[Top]) -> Result<ElabContext, Vec<Diagnostic>> {
    let mut diags = Vec::new();

    // Pass 1: gather syntax type names. We also include `nat`, `int`,
    // `text`, `bool` as built-in atomic types so they're treated as
    // holes when they appear in relation templates.
    let mut type_names: HashSet<String> = ["nat", "int", "text", "bool", "rat", "real"]
        .iter()
        .map(|s| s.to_string())
        .collect();
    for top in tops {
        if let Top::Syntax(s) = top {
            type_names.insert(s.name.text.clone());
        }
    }

    // Pass 2: extract operators.
    //   - Each `Top::Relation` template becomes one Op (relation-level
    //     precedence, holes interspersed with literals).
    //   - Each `SyntaxBody::Variant` alternative whose head looks like a
    //     case constructor becomes one Op (high precedence, with the
    //     head as a leading Lit and remaining type expressions as Holes).
    let mut op_table = OpTable::new();
    for top in tops {
        match top {
            Top::Relation(r) => {
                match template_to_fragments(&r.template, &type_names) {
                    Ok(frags) => {
                        op_table.add(r.name.text.clone(), frags);
                    }
                    Err(d) => diags.push(d),
                }
            }
            Top::Syntax(s) => {
                if let Some(SyntaxBody::Variant(alts)) = &s.body {
                    for alt in alts {
                        if let Some((name, frags)) = alt_to_constructor(alt, &type_names) {
                            op_table.add(name, frags);
                        }
                    }
                }
            }
            _ => {}
        }
    }

    if diags.is_empty() {
        Ok(ElabContext {
            op_table,
            type_names,
        })
    } else {
        Err(diags)
    }
}

/// Convert a relation `template` token run into mixfix fragments.
///
/// The rule:
///
/// - A type-name `Ident` introduces a `Hole`. Any immediately following
///   type-suffix tokens (`*`, `?`, `+`, or a balanced `(...)` group)
///   are also absorbed into the same hole — they describe the hole's
///   type, not separate template literals.
/// - A bare `(` not preceded by a type-name Ident also begins a hole
///   (treated as a parenthesised type expression).
/// - Any other token becomes a `Lit`.
pub fn template_to_fragments(
    template: &TokenRun,
    type_names: &HashSet<String>,
) -> Result<Vec<Fragment>, Diagnostic> {
    let mut out = Vec::new();
    let mut i = 0;
    let toks = &template.tokens;
    while i < toks.len() {
        let t = &toks[i];
        match &t.token {
            Token::Ident(name) if type_names.contains(name) => {
                out.push(Fragment::Hole(REL_HOLE_PREC));
                i += 1;
                i += skip_type_suffix(&toks[i..]);
            }
            Token::LParen => {
                // Standalone parenthesised type expression as a hole.
                out.push(Fragment::Hole(REL_HOLE_PREC));
                i += skip_balanced(&toks[i..]);
                i += skip_type_suffix(&toks[i..]);
            }
            _ => {
                out.push(Fragment::Lit(t.token.clone()));
                i += 1;
            }
        }
    }
    Ok(out)
}

/// Count how many trailing type-suffix tokens follow at position 0:
/// `*`, `?`, `+`, or balanced `(...)` groups, in any combination.
fn skip_type_suffix(toks: &[Spanned]) -> usize {
    let mut i = 0;
    while i < toks.len() {
        match &toks[i].token {
            Token::Star | Token::Question | Token::Plus => {
                i += 1;
            }
            Token::Caret => {
                // `^N` style — exponent on iteration count. Consume `^`
                // plus the next atomic token (Ident, Nat, or paren group).
                i += 1;
                if let Some(s) = toks.get(i) {
                    match &s.token {
                        Token::LParen => i += skip_balanced(&toks[i..]),
                        Token::Ident(_) | Token::Nat(_) => i += 1,
                        _ => {} // give up, let outer pass handle
                    }
                }
            }
            Token::LParen => {
                // `foo(args)` — parametric type argument list.
                i += skip_balanced(&toks[i..]);
            }
            _ => break,
        }
    }
    i
}

/// Try to extract a constructor operator from a variant alternative.
///
/// Returns `Some((name, fragments))` if the alt looks like a case
/// constructor (head is a SpecTec-convention case name like `NOP`,
/// `BLOCK`, `I32`, `_IDX`). Returns `None` for type-inclusion alts like
/// `| numtype | reftype` and other shapes we don't yet recognise.
///
/// Fragments: `[Lit(head_ident_token)] ++ <type-fragments of remaining tokens>`,
/// where type-fragments are produced by walking the remaining tokens
/// with the same logic that `template_to_fragments` uses for relation
/// holes (declared type names become `Hole`s; literals stay literals).
pub fn alt_to_constructor(
    alt: &Alt,
    type_names: &HashSet<String>,
) -> Option<(String, Vec<Fragment>)> {
    let toks = &alt.body.tokens;
    let head_tok = toks.first()?;
    let head_name = match &head_tok.token {
        Token::Ident(n) if is_case_head(n) => n.clone(),
        _ => return None,
    };
    let rest = &toks[1..];
    let mut frags = vec![Fragment::Lit(head_tok.token.clone())];
    let mut i = 0;
    while i < rest.len() {
        match &rest[i].token {
            Token::Ident(name) if type_names.contains(name) => {
                frags.push(Fragment::Hole(CTOR_HOLE_PREC));
                i += 1 + skip_type_suffix(&rest[i + 1..]);
            }
            Token::LParen => {
                frags.push(Fragment::Hole(CTOR_HOLE_PREC));
                let consumed = skip_balanced(&rest[i..]);
                i += consumed;
                i += skip_type_suffix(&rest[i..]);
            }
            _ => {
                frags.push(Fragment::Lit(rest[i].token.clone()));
                i += 1;
            }
        }
    }
    Some((head_name, frags))
}

// ---------- minimal Expr AST + conclusion elaboration ----------

/// Minimal expression AST. Phase 2c-ii covers what shows up in simple
/// rule conclusions: variables, numbers, parenthesised tuples, and
/// arbitrary "case-application" of an uppercase or `_PREFIXED` name to
/// arguments. Operands that fall outside this subset are kept as
/// `Raw(TokenRun)` so we can grow the structured cases incrementally
/// without losing source coverage.
///
/// Spans are carried so downstream consumers can attach diagnostics.
#[derive(Clone, Debug)]
pub enum Expr {
    Var { span: Span, name: String },
    Num { span: Span, value: u64 },
    Text { span: Span, value: String },
    /// Parenthesised sequence — `()` is the empty tuple, `(x)` is a
    /// grouping (semantically equivalent to `x`), `(x, y)` is a 2-tuple.
    /// We preserve the surface distinction by always producing a tuple
    /// node, even when there's just one element; downstream passes can
    /// flatten singleton tuples if they need to.
    Tup { span: Span, items: Vec<Expr> },
    /// `NAME` or `NAME e_1 e_2 ...` — constructor / case application.
    /// The "case-like" head is any identifier whose first character is
    /// uppercase, or that begins with an underscore. This matches
    /// SpecTec's convention (`I32`, `BLOCK`, `_IDX`, `_DEF`, ...).
    Case {
        span: Span,
        head: String,
        args: Vec<Expr>,
    },
    /// `eps` — the empty sequence literal.
    Eps { span: Span },
    /// Fallback: an unanalysed token run. Used when the expression
    /// shape isn't yet supported by the structured cases.
    Raw(TokenRun),
}

impl Expr {
    pub fn span(&self) -> Span {
        match self {
            Expr::Var { span, .. }
            | Expr::Num { span, .. }
            | Expr::Text { span, .. }
            | Expr::Tup { span, .. }
            | Expr::Case { span, .. }
            | Expr::Eps { span } => *span,
            Expr::Raw(tr) => tr.span,
        }
    }
}

/// Result of elaborating one `rule`: the relation it belongs to, the
/// operand expressions extracted from its conclusion, and the rule's
/// premises (each elaborated to its kind).
#[derive(Clone, Debug)]
pub struct ElabRuleConclusion {
    pub rule_name: String,
    pub case: Option<String>,
    pub op: OpId,
    pub operands: Vec<Expr>,
    pub premises: Vec<ElabPremise>,
}

/// An elaborated premise.
#[derive(Clone, Debug)]
pub enum ElabPremise {
    /// `RelName: <args>` — a relation premise.
    Rule {
        rel_name: String,
        op: OpId,
        operands: Vec<Expr>,
    },
    /// `if <expr>` — a boolean side condition.
    If(Expr),
    /// `let <lhs> = <rhs>` — a binding side condition.
    Let { lhs: Expr, rhs: Expr },
    /// `otherwise` / `else` — residual catch-all marker.
    Else,
    /// `(P)<iter>` — replicated premise. `inner` is the elaborated body;
    /// `kind` describes the iteration shape. Iteration *binder*
    /// inference (linking inner variables to their `*`-suffixed sources)
    /// is deferred to a later slice; the `bindings` field holds the raw
    /// `(x* y* ...)` body of `^(...)` counts for now.
    Iter {
        inner: Box<ElabPremise>,
        kind: IterKind,
    },
    /// Anything not yet structurally recognised, kept as a raw run.
    Raw(TokenRun),
}

/// Iteration shape attached to a premise.
#[derive(Clone, Debug)]
pub enum IterKind {
    /// `(P)?`
    Opt,
    /// `(P)*`
    Star,
    /// `(P)+`
    Plus,
    /// `(P)^<count-expr>` — fixed-length iteration with an explicit count.
    /// The count expression is kept as a raw token run for now.
    Length(TokenRun),
}

/// Elaborate one rule's conclusion against the operator table.
///
/// Looks up the rule's relation by name in `ctx.op_table`, walks the
/// operator's `Fragment` template, matches literals against the
/// conclusion's tokens, and parses the holes as expressions.
pub fn elab_rule_conclusion(
    rule: &RuleDecl,
    ctx: &ElabContext,
) -> Result<ElabRuleConclusion, Diagnostic> {
    let op = ctx
        .op_table
        .iter()
        .find(|o| o.name == rule.name.text)
        .ok_or_else(|| {
            Diagnostic::error(
                rule.name.span,
                format!(
                    "rule references unknown relation `{}`",
                    rule.name.text
                ),
            )
        })?;
    let op_id = op.id;
    let fragments = op.fragments.clone();

    let mut input: &[Spanned] = &rule.conclusion.tokens;
    let mut operands = Vec::new();

    for (i, frag) in fragments.iter().enumerate() {
        match frag {
            Fragment::Lit(expected) => {
                expect_token_in_conclusion(&mut input, expected, &rule.name.text)?;
            }
            Fragment::Hole(_) => {
                // Each hole runs up to the next literal in the template
                // (if any) or to the end of input. We compute that
                // stopping set lazily by scanning ahead.
                let stop = next_lit_after(&fragments, i + 1);
                let expr = parse_expression_until(&mut input, stop.as_ref())?;
                operands.push(expr);
            }
        }
    }

    if !input.is_empty() {
        return Err(Diagnostic::error(
            input.first().unwrap().span,
            format!(
                "rule `{}` conclusion has {} leftover token(s) after matching template",
                rule.name.text,
                input.len()
            ),
        ));
    }

    let premises = rule
        .premises
        .iter()
        .map(|p| elab_premise(p, ctx))
        .collect::<Result<Vec<_>, _>>()?;

    Ok(ElabRuleConclusion {
        rule_name: rule.name.text.clone(),
        case: rule.case.as_ref().map(|c| c.text.clone()),
        op: op_id,
        operands,
        premises,
    })
}

/// Elaborate a single premise from its raw token run.
///
/// Detects the premise form from the leading token: `if`, `let`,
/// `else`/`otherwise`, an iteration group `(...)`, or otherwise a
/// `RelName: <args>` relation reference.
pub fn elab_premise(
    prem: &TokenRun,
    ctx: &ElabContext,
) -> Result<ElabPremise, Diagnostic> {
    let toks = &prem.tokens;
    match toks.first().map(|s| &s.token) {
        Some(Token::If) => {
            // `if <expr>` — entire remainder is the expression.
            let span = prem.span;
            if toks.len() == 1 {
                return Err(Diagnostic::error(
                    span,
                    "`if` premise needs a condition expression",
                ));
            }
            let body = &toks[1..];
            let body_span = body
                .iter()
                .map(|s| s.span)
                .reduce(Span::join)
                .unwrap_or(span);
            let cond = classify_simple_expression(body, body_span)?;
            Ok(ElabPremise::If(cond))
        }
        Some(Token::Let) => {
            // `let <lhs> = <rhs>` — find top-level `=` split.
            let body = &toks[1..];
            let eq_idx = top_level_index_of(body, |t| matches!(t, Token::Eq))
                .ok_or_else(|| {
                    Diagnostic::error(
                        prem.span,
                        "`let` premise has no top-level `=` splitting lhs from rhs",
                    )
                })?;
            let lhs_slice = &body[..eq_idx];
            let rhs_slice = &body[eq_idx + 1..];
            if lhs_slice.is_empty() || rhs_slice.is_empty() {
                return Err(Diagnostic::error(
                    prem.span,
                    "`let` premise has empty lhs or rhs",
                ));
            }
            let lhs_span = lhs_slice.iter().map(|s| s.span).reduce(Span::join).unwrap();
            let rhs_span = rhs_slice.iter().map(|s| s.span).reduce(Span::join).unwrap();
            let lhs = classify_simple_expression(lhs_slice, lhs_span)?;
            let rhs = classify_simple_expression(rhs_slice, rhs_span)?;
            Ok(ElabPremise::Let { lhs, rhs })
        }
        Some(Token::Else) | Some(Token::Otherwise) => Ok(ElabPremise::Else),
        Some(Token::LParen) => elab_iter_premise(prem, ctx),
        Some(Token::Ident(name)) => {
            // `RelName: <args>` — relation premise.
            let rel_name = name.clone();
            let Some(op) = ctx.op_table.iter().find(|o| o.name == rel_name) else {
                return Ok(ElabPremise::Raw(prem.clone()));
            };
            let op_id = op.id;
            let fragments = op.fragments.clone();
            // Expect a `:` right after the relation name.
            if !matches!(toks.get(1).map(|s| &s.token), Some(Token::Colon)) {
                return Ok(ElabPremise::Raw(prem.clone()));
            }
            let mut input: &[Spanned] = &toks[2..];
            let mut operands = Vec::new();
            for (i, frag) in fragments.iter().enumerate() {
                match frag {
                    Fragment::Lit(expected) => {
                        // Use a soft error here: fall back to Raw if a
                        // literal doesn't match (premise might have
                        // optional extras we don't model yet).
                        match input.first() {
                            Some(s) if &s.token == expected => {
                                input = &input[1..];
                            }
                            _ => return Ok(ElabPremise::Raw(prem.clone())),
                        }
                    }
                    Fragment::Hole(_) => {
                        let stop = next_lit_after(&fragments, i + 1);
                        match parse_expression_until(&mut input, stop.as_ref()) {
                            Ok(e) => operands.push(e),
                            Err(_) => return Ok(ElabPremise::Raw(prem.clone())),
                        }
                    }
                }
            }
            if !input.is_empty() {
                return Ok(ElabPremise::Raw(prem.clone()));
            }
            Ok(ElabPremise::Rule {
                rel_name,
                op: op_id,
                operands,
            })
        }
        _ => Ok(ElabPremise::Raw(prem.clone())),
    }
}

/// Recognise an iteration premise: `( <inner-premise> ) <iter-suffix>`.
/// The matching `)` must be at paren depth 0 of the inner body and
/// must leave at least one trailing token (the iter suffix).
fn elab_iter_premise(
    prem: &TokenRun,
    ctx: &ElabContext,
) -> Result<ElabPremise, Diagnostic> {
    let toks = &prem.tokens;
    // toks[0] is `(`. Find the matching `)` (depth 0 again).
    let close_idx = matching_rparen(toks).ok_or_else(|| {
        Diagnostic::error(prem.span, "iteration premise: no matching `)`")
    })?;
    let inner_toks = &toks[1..close_idx];
    let trailing = &toks[close_idx + 1..];
    if inner_toks.is_empty() {
        return Ok(ElabPremise::Raw(prem.clone()));
    }
    if trailing.is_empty() {
        // Just a parenthesised premise with no iter suffix — pass-through.
        let inner_span = inner_toks
            .iter()
            .map(|s| s.span)
            .reduce(Span::join)
            .expect("non-empty");
        let inner_prem = TokenRun {
            span: inner_span,
            tokens: inner_toks.to_vec(),
        };
        return elab_premise(&inner_prem, ctx);
    }
    // Recognise the iter suffix.
    let kind = match &trailing[0].token {
        Token::Question if trailing.len() == 1 => IterKind::Opt,
        Token::Star if trailing.len() == 1 => IterKind::Star,
        Token::Plus if trailing.len() == 1 => IterKind::Plus,
        Token::Caret => {
            // `^<count-expr>` — count is the rest of trailing.
            let count_toks = &trailing[1..];
            if count_toks.is_empty() {
                return Ok(ElabPremise::Raw(prem.clone()));
            }
            let count_span = count_toks
                .iter()
                .map(|s| s.span)
                .reduce(Span::join)
                .expect("non-empty");
            IterKind::Length(TokenRun {
                span: count_span,
                tokens: count_toks.to_vec(),
            })
        }
        _ => return Ok(ElabPremise::Raw(prem.clone())),
    };
    // Recursively elaborate the inner premise.
    let inner_span = inner_toks
        .iter()
        .map(|s| s.span)
        .reduce(Span::join)
        .expect("non-empty");
    let inner_prem = TokenRun {
        span: inner_span,
        tokens: inner_toks.to_vec(),
    };
    let inner_elab = elab_premise(&inner_prem, ctx)?;
    Ok(ElabPremise::Iter {
        inner: Box::new(inner_elab),
        kind,
    })
}

/// Given `toks[0]` is `LParen`, return the index of the matching `RParen`
/// at depth 0 (relative to that opening paren).
fn matching_rparen(toks: &[Spanned]) -> Option<usize> {
    let mut depth: i32 = 0;
    for (i, t) in toks.iter().enumerate() {
        match &t.token {
            Token::LParen | Token::LBracket | Token::LBrace => depth += 1,
            Token::RParen | Token::RBracket | Token::RBrace => {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
            }
            _ => {}
        }
    }
    None
}

/// Index of the first token (at paren depth 0) for which `pred` is true.
fn top_level_index_of(toks: &[Spanned], pred: impl Fn(&Token) -> bool) -> Option<usize> {
    let mut depth: i32 = 0;
    for (i, t) in toks.iter().enumerate() {
        match &t.token {
            Token::LParen | Token::LBracket | Token::LBrace => depth += 1,
            Token::RParen | Token::RBracket | Token::RBrace => depth -= 1,
            _ => {}
        }
        if depth == 0 && pred(&t.token) {
            return Some(i);
        }
    }
    None
}

/// Find the next `Lit` token in the fragment list starting at `from`.
fn next_lit_after(frags: &[Fragment], from: usize) -> Option<Token> {
    for f in &frags[from..] {
        if let Fragment::Lit(t) = f {
            return Some(t.clone());
        }
    }
    None
}

fn expect_token_in_conclusion(
    input: &mut &[Spanned],
    expected: &Token,
    rule_name: &str,
) -> Result<(), Diagnostic> {
    match input.first() {
        Some(s) if &s.token == expected => {
            *input = &input[1..];
            Ok(())
        }
        Some(s) => Err(Diagnostic::error(
            s.span,
            format!(
                "rule `{}` conclusion does not match relation template: expected {}, found {}",
                rule_name,
                expected.describe(),
                s.token.describe()
            ),
        )),
        None => Err(Diagnostic::error(
            Span::new(crate::source::FileId::new(0), u32::MAX, u32::MAX),
            format!(
                "rule `{}` conclusion ends before template literal {}",
                rule_name,
                expected.describe()
            ),
        )),
    }
}

/// Parse an expression from `input`, stopping when the next top-level
/// token equals `stop_lit` (or, if `stop_lit` is None, when input is
/// empty). The stop sentinel is NOT consumed.
fn parse_expression_until(
    input: &mut &[Spanned],
    stop_lit: Option<&Token>,
) -> Result<Expr, Diagnostic> {
    // Collect tokens up to the stop sentinel at depth 0.
    let mut depth: i32 = 0;
    let mut taken: Vec<Spanned> = Vec::new();
    while let Some(s) = input.first() {
        if depth == 0
            && stop_lit.map(|t| t == &s.token).unwrap_or(false)
        {
            break;
        }
        match &s.token {
            Token::LParen | Token::LBracket | Token::LBrace => depth += 1,
            Token::RParen | Token::RBracket | Token::RBrace => depth -= 1,
            _ => {}
        }
        taken.push(s.clone());
        *input = &input[1..];
    }
    if taken.is_empty() {
        return Err(Diagnostic::error(
            input
                .first()
                .map(|s| s.span)
                .unwrap_or_else(|| Span::new(crate::source::FileId::new(0), u32::MAX, u32::MAX)),
            "empty expression in rule conclusion hole",
        ));
    }
    let span = taken
        .iter()
        .map(|s| s.span)
        .reduce(Span::join)
        .expect("non-empty by check above");
    classify_simple_expression(&taken, span)
}

/// Try to recognise a "simple" expression from a slice of tokens. Falls
/// back to `Expr::Raw` if we can't structure it.
fn classify_simple_expression(toks: &[Spanned], span: Span) -> Result<Expr, Diagnostic> {
    // Singletons: Var, Num, Text, Eps, or a zero-arg Case for uppercase
    // / underscore-prefixed names.
    if toks.len() == 1 {
        return Ok(match &toks[0].token {
            Token::Ident(name) if is_case_head(name) => Expr::Case {
                span,
                head: name.clone(),
                args: Vec::new(),
            },
            Token::Ident(name) => Expr::Var {
                span,
                name: name.clone(),
            },
            Token::Nat(n) => Expr::Num { span, value: *n },
            Token::Text(t) => Expr::Text {
                span,
                value: t.clone(),
            },
            Token::Eps => Expr::Eps { span },
            _ => Expr::Raw(TokenRun {
                span,
                tokens: toks.to_vec(),
            }),
        });
    }

    // Parenthesised: `( ... )` — split inner on top-level commas.
    if matches!(toks.first().map(|s| &s.token), Some(Token::LParen))
        && matches!(toks.last().map(|s| &s.token), Some(Token::RParen))
    {
        let inner = &toks[1..toks.len() - 1];
        if depth_balanced(inner) {
            return classify_tuple_inner(inner, span);
        }
    }

    // Case application: `HEAD arg1 arg2 ...` where HEAD is uppercase or
    // begins with `_`.
    if let Some(Spanned { token: Token::Ident(head), .. }) = toks.first() {
        if is_case_head(head) {
            // Args are the rest of the token slice, split on... actually
            // for now treat the rest as a single Raw run. Tighter
            // splitting belongs to the next slice.
            let head_name = head.clone();
            if toks.len() == 1 {
                return Ok(Expr::Case {
                    span,
                    head: head_name,
                    args: Vec::new(),
                });
            }
            let args_slice = &toks[1..];
            let arg_span = args_slice
                .iter()
                .map(|s| s.span)
                .reduce(Span::join)
                .expect("non-empty");
            let args = vec![Expr::Raw(TokenRun {
                span: arg_span,
                tokens: args_slice.to_vec(),
            })];
            return Ok(Expr::Case {
                span,
                head: head_name,
                args,
            });
        }
    }

    Ok(Expr::Raw(TokenRun {
        span,
        tokens: toks.to_vec(),
    }))
}

/// True if `name` looks like a SpecTec case constructor.
///
/// Heuristic: at least 2 characters AND every alphabetic character is
/// uppercase. This catches `NOP`, `BLOCK`, `I32`, `UNREACHABLE`, `_IDX`,
/// `_DEF`, and rejects single-letter metavariables (`C`, `X`, `N`),
/// lowercase identifiers (`numtype`), and mixed-case names (`Foo`).
///
/// The proper distinction between metavariables and constructors comes
/// from `var` and `syntax`-variant declarations; this heuristic stands
/// in until the elaborator threads those through. See [[phase-p-parallel-types]]
/// for the broader pattern of letting parallel structures coexist while
/// the elaborator catches up.
fn is_case_head(name: &str) -> bool {
    if name.len() < 2 {
        return false;
    }
    let mut bytes = name.bytes();
    match bytes.next() {
        Some(b) if b.is_ascii_uppercase() => {}
        Some(b'_') => {}
        _ => return false,
    }
    let mut saw_letter = false;
    for b in name.bytes() {
        if b.is_ascii_alphabetic() {
            saw_letter = true;
            if b.is_ascii_lowercase() {
                return false;
            }
        }
    }
    saw_letter
}

fn depth_balanced(toks: &[Spanned]) -> bool {
    let mut depth: i32 = 0;
    for t in toks {
        match &t.token {
            Token::LParen | Token::LBracket | Token::LBrace => depth += 1,
            Token::RParen | Token::RBracket | Token::RBrace => {
                depth -= 1;
                if depth < 0 {
                    return false;
                }
            }
            _ => {}
        }
    }
    depth == 0
}

fn classify_tuple_inner(inner: &[Spanned], span: Span) -> Result<Expr, Diagnostic> {
    // Empty: `()`.
    if inner.is_empty() {
        return Ok(Expr::Tup {
            span,
            items: Vec::new(),
        });
    }
    // Split on top-level commas.
    let mut items: Vec<Expr> = Vec::new();
    let mut depth: i32 = 0;
    let mut chunk_start = 0;
    for (i, t) in inner.iter().enumerate() {
        match &t.token {
            Token::LParen | Token::LBracket | Token::LBrace => depth += 1,
            Token::RParen | Token::RBracket | Token::RBrace => depth -= 1,
            Token::Comma if depth == 0 => {
                let chunk = &inner[chunk_start..i];
                let cspan = chunk
                    .iter()
                    .map(|s| s.span)
                    .reduce(Span::join)
                    .expect("non-empty chunk");
                items.push(classify_simple_expression(chunk, cspan)?);
                chunk_start = i + 1;
            }
            _ => {}
        }
    }
    let chunk = &inner[chunk_start..];
    let cspan = chunk
        .iter()
        .map(|s| s.span)
        .reduce(Span::join)
        .expect("non-empty chunk");
    items.push(classify_simple_expression(chunk, cspan)?);

    // Singleton: `(x)` — grouping. Return inner expression directly.
    if items.len() == 1 {
        return Ok(items.into_iter().next().unwrap());
    }
    Ok(Expr::Tup { span, items })
}

/// Given `toks[0]` IS an opening bracket, return the number of tokens
/// from `toks[0]` up to AND INCLUDING the matching close bracket. If
/// brackets are unbalanced, returns the remaining length.
fn skip_balanced(toks: &[Spanned]) -> usize {
    let mut depth: i32 = 0;
    let mut i = 0;
    while i < toks.len() {
        match &toks[i].token {
            Token::LParen | Token::LBracket | Token::LBrace => depth += 1,
            Token::RParen | Token::RBracket | Token::RBrace => {
                depth -= 1;
                if depth == 0 {
                    return i + 1;
                }
            }
            _ => {}
        }
        i += 1;
    }
    toks.len()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lex::lex;
    use crate::parse::parse;
    use crate::source::SourceMap;

    fn build_from_str(src: &str) -> ElabContext {
        let mut map = SourceMap::new();
        let id = map.add("<test>", src);
        let tokens = lex(id, src).unwrap();
        let tops = parse(id, tokens).unwrap();
        build_table(&tops).unwrap()
    }

    /// Format an op's fragments compactly for tests: `H` for hole, `<token>` for lit.
    fn fmt_op(op: &crate::mixfix::Op) -> String {
        let parts: Vec<String> = op
            .fragments
            .iter()
            .map(|f| match f {
                Fragment::Hole(_) => "%".to_string(),
                Fragment::Lit(t) => format!("{:?}", t),
            })
            .collect();
        format!("{}: {}", op.name, parts.join(" "))
    }

    #[test]
    fn type_names_include_builtins() {
        let ctx = build_from_str("");
        assert!(ctx.type_names.contains("nat"));
        assert!(ctx.type_names.contains("int"));
        assert!(ctx.type_names.contains("bool"));
        assert!(ctx.type_names.contains("text"));
    }

    #[test]
    fn type_names_from_syntax_decls() {
        let src = r#"
            syntax foo = nat
            syntax bar(N) = nat
            syntax baz/syn = nat
        "#;
        let ctx = build_from_str(src);
        assert!(ctx.type_names.contains("foo"));
        assert!(ctx.type_names.contains("bar"));
        assert!(ctx.type_names.contains("baz"));
    }

    #[test]
    fn relation_with_simple_template() {
        let src = r#"
            syntax context = nat
            syntax numtype = nat
            relation Numtype_sub: context |- numtype <: numtype
        "#;
        let ctx = build_from_str(src);
        let op = ctx.op_table.iter().find(|o| o.name == "Numtype_sub").unwrap();
        // % |- % <: %
        assert_eq!(op.fragments.len(), 5);
        assert!(matches!(op.fragments[0], Fragment::Hole(_)));
        assert!(matches!(op.fragments[1], Fragment::Lit(Token::Turnstile)));
        assert!(matches!(op.fragments[2], Fragment::Hole(_)));
        assert!(matches!(op.fragments[3], Fragment::Lit(Token::Subtype)));
        assert!(matches!(op.fragments[4], Fragment::Hole(_)));
    }

    #[test]
    fn relation_with_iter_suffix_in_hole() {
        // `context |- type : deftype*` — the trailing `*` should be
        // absorbed into the last hole, not become a separate Lit.
        let src = r#"
            syntax context = nat
            syntax type = nat
            syntax deftype = nat
            relation Type_ok: context |- type : deftype*
        "#;
        let ctx = build_from_str(src);
        let op = ctx.op_table.iter().find(|o| o.name == "Type_ok").unwrap();
        // % |- % : %    (3 holes, 2 lits — `*` absorbed)
        assert_eq!(op.fragments.len(), 5);
        assert!(matches!(op.fragments[0], Fragment::Hole(_)));
        assert!(matches!(op.fragments[1], Fragment::Lit(Token::Turnstile)));
        assert!(matches!(op.fragments[2], Fragment::Hole(_)));
        assert!(matches!(op.fragments[3], Fragment::Lit(Token::Colon)));
        assert!(matches!(op.fragments[4], Fragment::Hole(_)));
    }

    #[test]
    fn relation_with_optional_and_plus_suffixes() {
        let src = r#"
            syntax foo = nat
            syntax bar = nat
            syntax baz = nat
            relation R: foo? |- bar+ <: baz*
        "#;
        let ctx = build_from_str(src);
        let op = ctx.op_table.iter().find(|o| o.name == "R").unwrap();
        // 3 holes, 2 lits
        assert_eq!(op.fragments.len(), 5);
        assert_eq!(
            op.fragments.iter().filter(|f| matches!(f, Fragment::Hole(_))).count(),
            3
        );
    }

    #[test]
    fn relation_starts_with_literal() {
        // `|- valtype DEFAULTABLE` — starts with `|-` literal, then a hole,
        // then a `DEFAULTABLE` literal that's NOT a declared type name.
        let src = r#"
            syntax valtype = nat
            relation Defaultable: |- valtype DEFAULTABLE
        "#;
        let ctx = build_from_str(src);
        let op = ctx.op_table.iter().find(|o| o.name == "Defaultable").unwrap();
        // Lit Hole Lit
        assert_eq!(op.fragments.len(), 3);
        assert!(matches!(op.fragments[0], Fragment::Lit(Token::Turnstile)));
        assert!(matches!(op.fragments[1], Fragment::Hole(_)));
        assert!(matches!(op.fragments[2], Fragment::Lit(Token::Ident(ref s)) if s == "DEFAULTABLE"));
    }

    #[test]
    fn relation_with_parametric_type_in_hole() {
        // `relation R: foo(N) |- bar` — the `(N)` is part of the first
        // hole's type, not separate template tokens.
        let src = r#"
            syntax foo(N) = nat
            syntax bar = nat
            relation R: foo(N) |- bar
        "#;
        let ctx = build_from_str(src);
        let op = ctx.op_table.iter().find(|o| o.name == "R").unwrap();
        // Hole Lit Hole
        assert_eq!(op.fragments.len(), 3);
    }

    #[test]
    fn multiple_relations_extracted() {
        let src = r#"
            syntax t = nat
            relation A: t |- t
            relation B: t |- t : t
            relation C: t ~> t
        "#;
        let ctx = build_from_str(src);
        let names: Vec<_> = ctx.op_table.iter().map(|o| o.name.clone()).collect();
        assert!(names.contains(&"A".to_string()));
        assert!(names.contains(&"B".to_string()));
        assert!(names.contains(&"C".to_string()));
    }

    #[test]
    fn empty_input_gives_empty_table() {
        let ctx = build_from_str("");
        assert_eq!(ctx.op_table.iter().count(), 0);
    }

    #[test]
    fn variant_constructors_become_ops() {
        let src = r#"
            syntax numtype = | I32 | I64 | F32 | F64
        "#;
        let ctx = build_from_str(src);
        for name in &["I32", "I64", "F32", "F64"] {
            assert!(
                ctx.op_table.iter().any(|o| o.name == *name),
                "expected op for `{name}`"
            );
        }
    }

    #[test]
    fn variant_constructors_with_args() {
        let src = r#"
            syntax heaptype = nat
            syntax null = NULL
            syntax reftype = | REF null? heaptype
        "#;
        let ctx = build_from_str(src);
        let op = ctx.op_table.iter().find(|o| o.name == "REF").unwrap();
        // Lit(REF), Hole (null?), Hole (heaptype) — but only if both
        // null and heaptype are declared as syntax. `null` is declared.
        assert!(matches!(op.fragments[0], Fragment::Lit(_)));
        let hole_count = op
            .fragments
            .iter()
            .filter(|f| matches!(f, Fragment::Hole(_)))
            .count();
        assert_eq!(hole_count, 2, "expected REF to have 2 args");
    }

    #[test]
    fn type_inclusion_alt_does_not_become_constructor() {
        // `syntax valtype = | numtype | reftype` — these aren't case
        // constructors, they're type inclusions. No ops added for them.
        let src = r#"
            syntax numtype = nat
            syntax reftype = nat
            syntax valtype = | numtype | reftype
        "#;
        let ctx = build_from_str(src);
        let names: Vec<_> = ctx.op_table.iter().map(|o| o.name.clone()).collect();
        // No op named "numtype" or "reftype" should be in the table.
        assert!(!names.contains(&"numtype".to_string()));
        assert!(!names.contains(&"reftype".to_string()));
    }

    #[test]
    fn nullary_constructors_have_just_a_lit() {
        let src = r#"
            syntax instr = | NOP | UNREACHABLE
        "#;
        let ctx = build_from_str(src);
        let nop = ctx.op_table.iter().find(|o| o.name == "NOP").unwrap();
        assert_eq!(nop.fragments.len(), 1);
        assert!(matches!(nop.fragments[0], Fragment::Lit(_)));
    }

    #[test]
    fn nonexistent_type_in_template_is_lit() {
        // `Foobar` isn't declared as a syntax — treated as a literal token.
        let src = r#"
            syntax foo = nat
            relation R: foo |- Foobar
        "#;
        let ctx = build_from_str(src);
        let op = ctx.op_table.iter().find(|o| o.name == "R").unwrap();
        // Hole Lit Lit
        assert_eq!(op.fragments.len(), 3);
        assert!(matches!(op.fragments[0], Fragment::Hole(_)));
        assert!(matches!(op.fragments[1], Fragment::Lit(Token::Turnstile)));
        assert!(matches!(op.fragments[2], Fragment::Lit(Token::Ident(ref s)) if s == "Foobar"));
    }

    // Used only when debugging; kept for future iteration.
    #[allow(dead_code)]
    fn debug_table(ctx: &ElabContext) {
        for op in ctx.op_table.iter() {
            eprintln!("  {}", fmt_op(op));
        }
    }

    // ---------- conclusion elaboration ----------

    fn elab_first_rule(src: &str) -> ElabRuleConclusion {
        let mut map = SourceMap::new();
        let id = map.add("<test>", src);
        let tokens = lex(id, src).unwrap();
        let tops = parse(id, tokens).unwrap();
        let ctx = build_table(&tops).unwrap();
        let rule = tops
            .iter()
            .find_map(|t| if let Top::Rule(r) = t { Some(r) } else { None })
            .expect("no rule in input");
        elab_rule_conclusion(rule, &ctx).expect("elab failed")
    }

    #[test]
    fn elab_subtype_rule_three_vars() {
        let src = r#"
            syntax context = nat
            syntax numtype = nat
            relation Numtype_sub: context |- numtype <: numtype
            rule Numtype_sub:
              C |- numtype <: numtype
        "#;
        let elab = elab_first_rule(src);
        assert_eq!(elab.rule_name, "Numtype_sub");
        assert!(elab.case.is_none());
        assert_eq!(elab.operands.len(), 3);
        for op in &elab.operands {
            match op {
                Expr::Var { name, .. } => {
                    assert!(matches!(name.as_str(), "C" | "numtype"));
                }
                other => panic!("expected Var, got {other:?}"),
            }
        }
    }

    #[test]
    fn elab_rule_with_case_path() {
        let src = r#"
            syntax context = nat
            syntax heaptype = nat
            relation Heaptype_sub: context |- heaptype <: heaptype
            rule Heaptype_sub/refl:
              C |- heaptype <: heaptype
        "#;
        let elab = elab_first_rule(src);
        assert_eq!(elab.case.as_deref(), Some("refl"));
        assert_eq!(elab.operands.len(), 3);
    }

    #[test]
    fn elab_constant_constructors() {
        let src = r#"
            syntax instr = nat
            relation Step_pure: instr ~> instr
            rule Step_pure/unreachable:
              UNREACHABLE ~> TRAP
        "#;
        let elab = elab_first_rule(src);
        assert_eq!(elab.operands.len(), 2);
        let (lhs, rhs) = (&elab.operands[0], &elab.operands[1]);
        assert!(
            matches!(lhs, Expr::Case { head, args, .. } if head == "UNREACHABLE" && args.is_empty())
        );
        assert!(
            matches!(rhs, Expr::Case { head, args, .. } if head == "TRAP" && args.is_empty())
        );
    }

    #[test]
    fn elab_eps_as_eps_node() {
        let src = r#"
            syntax instr = nat
            relation Step_pure: instr ~> instr
            rule Step_pure/nop:
              NOP ~> eps
        "#;
        let elab = elab_first_rule(src);
        assert_eq!(elab.operands.len(), 2);
        assert!(matches!(&elab.operands[0], Expr::Case { head, .. } if head == "NOP"));
        assert!(matches!(&elab.operands[1], Expr::Eps { .. }));
    }

    #[test]
    fn elab_parenthesised_tuple() {
        let src = r#"
            syntax context = nat
            syntax t = nat
            relation R: context |- t : t
            rule R:
              (C) |- (a, b) : c
        "#;
        let elab = elab_first_rule(src);
        assert_eq!(elab.operands.len(), 3);
        // First operand is `(C)` — singleton parens collapse to Var(C).
        assert!(matches!(&elab.operands[0], Expr::Var { name, .. } if name == "C"));
        // Second is `(a, b)` — 2-tuple.
        let Expr::Tup { items, .. } = &elab.operands[1] else {
            panic!("expected Tup, got {:?}", elab.operands[1]);
        };
        assert_eq!(items.len(), 2);
        // Third is `c` — Var.
        assert!(matches!(&elab.operands[2], Expr::Var { name, .. } if name == "c"));
    }

    #[test]
    fn elab_unknown_relation_errors() {
        // Rule references a relation that doesn't exist.
        let src = r#"
            syntax t = nat
            relation A: t |- t
            rule UnknownRelation:
              x |- y
        "#;
        let mut map = SourceMap::new();
        let id = map.add("<test>", src);
        let tokens = lex(id, src).unwrap();
        let tops = parse(id, tokens).unwrap();
        let ctx = build_table(&tops).unwrap();
        let rule = tops
            .iter()
            .find_map(|t| if let Top::Rule(r) = t { Some(r) } else { None })
            .unwrap();
        assert!(elab_rule_conclusion(rule, &ctx).is_err());
    }

    #[test]
    fn elab_template_mismatch_errors() {
        // Rule conclusion missing the `<:` from the template.
        let src = r#"
            syntax t = nat
            relation R: t |- t <: t
            rule R:
              a |- b c
        "#;
        let mut map = SourceMap::new();
        let id = map.add("<test>", src);
        let tokens = lex(id, src).unwrap();
        let tops = parse(id, tokens).unwrap();
        let ctx = build_table(&tops).unwrap();
        let rule = tops
            .iter()
            .find_map(|t| if let Top::Rule(r) = t { Some(r) } else { None })
            .unwrap();
        assert!(elab_rule_conclusion(rule, &ctx).is_err());
    }

    // ---------- premise elaboration ----------

    #[test]
    fn elab_premise_if_guard() {
        let src = r#"
            syntax context = nat
            syntax t = nat
            relation R: context |- t : t
            rule R:
              C |- a : b
              -- if a
        "#;
        let elab = elab_first_rule(src);
        assert_eq!(elab.premises.len(), 1);
        assert!(matches!(&elab.premises[0], ElabPremise::If(Expr::Var { name, .. }) if name == "a"));
    }

    #[test]
    fn elab_premise_let_binding() {
        let src = r#"
            syntax context = nat
            syntax t = nat
            relation R: context |- t : t
            rule R:
              C |- x : y
              -- let p = q
        "#;
        let elab = elab_first_rule(src);
        assert_eq!(elab.premises.len(), 1);
        let ElabPremise::Let { lhs, rhs } = &elab.premises[0] else {
            panic!("expected Let, got {:?}", elab.premises[0]);
        };
        assert!(matches!(lhs, Expr::Var { name, .. } if name == "p"));
        assert!(matches!(rhs, Expr::Var { name, .. } if name == "q"));
    }

    #[test]
    fn elab_premise_else_marker() {
        let src = r#"
            syntax context = nat
            syntax t = nat
            relation R: context |- t : t
            rule R:
              C |- x : y
              -- otherwise
        "#;
        let elab = elab_first_rule(src);
        assert!(matches!(&elab.premises[0], ElabPremise::Else));
    }

    #[test]
    fn elab_premise_relation_reference() {
        let src = r#"
            syntax context = nat
            syntax t = nat
            relation OK: context |- t : t
            relation Sub: context |- t <: t
            rule Sub:
              C |- x <: y
              -- OK: C |- z : z
        "#;
        let elab = elab_first_rule(src);
        assert_eq!(elab.premises.len(), 1);
        let ElabPremise::Rule { rel_name, operands, .. } = &elab.premises[0] else {
            panic!("expected Rule premise, got {:?}", elab.premises[0]);
        };
        assert_eq!(rel_name, "OK");
        assert_eq!(operands.len(), 3);
    }

    #[test]
    fn elab_premise_unknown_relation_falls_back_to_raw() {
        let src = r#"
            syntax context = nat
            syntax t = nat
            relation R: context |- t : t
            rule R:
              C |- x : y
              -- Unknown_rel: C |- z : z
        "#;
        let elab = elab_first_rule(src);
        assert!(matches!(&elab.premises[0], ElabPremise::Raw(_)));
    }

    #[test]
    fn elab_premise_iter_star() {
        let src = r#"
            syntax context = nat
            syntax t = nat
            relation Sub: context |- t <: t
            rule Sub:
              C |- x <: y
              -- (Sub: C |- a <: b)*
        "#;
        let elab = elab_first_rule(src);
        assert_eq!(elab.premises.len(), 1);
        let ElabPremise::Iter { inner, kind } = &elab.premises[0] else {
            panic!("expected Iter, got {:?}", elab.premises[0]);
        };
        assert!(matches!(kind, IterKind::Star));
        assert!(matches!(inner.as_ref(), ElabPremise::Rule { rel_name, .. } if rel_name == "Sub"));
    }

    #[test]
    fn elab_premise_iter_opt() {
        let src = r#"
            syntax context = nat
            syntax t = nat
            relation R: context |- t : t
            rule R:
              C |- x : y
              -- (R: C |- a : b)?
        "#;
        let elab = elab_first_rule(src);
        let ElabPremise::Iter { kind, .. } = &elab.premises[0] else {
            panic!("expected Iter")
        };
        assert!(matches!(kind, IterKind::Opt));
    }

    #[test]
    fn elab_premise_iter_plus() {
        let src = r#"
            syntax context = nat
            syntax t = nat
            relation R: context |- t : t
            rule R:
              C |- x : y
              -- (R: C |- a : b)+
        "#;
        let elab = elab_first_rule(src);
        let ElabPremise::Iter { kind, .. } = &elab.premises[0] else {
            panic!("expected Iter")
        };
        assert!(matches!(kind, IterKind::Plus));
    }

    #[test]
    fn elab_premise_iter_caret_length() {
        let src = r#"
            syntax context = nat
            syntax t = nat
            relation R: context |- t : t
            rule R:
              C |- x : y
              -- (R: C |- a : b)^n
        "#;
        let elab = elab_first_rule(src);
        let ElabPremise::Iter { kind, .. } = &elab.premises[0] else {
            panic!("expected Iter")
        };
        assert!(matches!(kind, IterKind::Length(_)));
    }

    #[test]
    fn elab_multiple_premises() {
        let src = r#"
            syntax context = nat
            syntax t = nat
            relation Wf: context |- t : t
            relation Sub: context |- t <: t
            rule Sub:
              C |- x <: z
              -- Wf: C |- y : y
              -- Sub: C |- x <: y
              -- Sub: C |- y <: z
        "#;
        let elab = elab_first_rule(src);
        assert_eq!(elab.premises.len(), 3);
        for p in &elab.premises {
            assert!(matches!(p, ElabPremise::Rule { .. }));
        }
    }

    #[test]
    fn is_case_head_classification() {
        assert!(is_case_head("I32"));
        assert!(is_case_head("NOP"));
        assert!(is_case_head("BLOCK"));
        assert!(is_case_head("UNREACHABLE"));
        assert!(is_case_head("_IDX"));
        assert!(is_case_head("_DEF"));
        assert!(!is_case_head("instr"));
        assert!(!is_case_head("t_1"));
        assert!(!is_case_head("_"));
        assert!(!is_case_head(""));
        // Single-letter uppercase metavariables are NOT case heads.
        assert!(!is_case_head("C"));
        assert!(!is_case_head("X"));
        assert!(!is_case_head("N"));
        // Mixed case is not a case head.
        assert!(!is_case_head("Foo"));
        assert!(!is_case_head("Numtype_sub"));
    }
}
