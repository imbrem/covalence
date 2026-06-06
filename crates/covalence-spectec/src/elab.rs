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

use crate::cst::{Top, TokenRun};
use crate::mixfix::{Fragment, OpTable, Precedence};
use crate::source::Diagnostic;
use crate::token::{Spanned, Token};

/// Default precedence for relation holes. SpecTec's surface language
/// has no explicit per-operator precedence — relations all sit at the
/// bottom of the binding tower. Higher precedences come into play with
/// syntax-constructor and arithmetic operators (added later).
pub const REL_HOLE_PREC: Precedence = 0;

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

    // Pass 2: extract operators from relation templates.
    let mut op_table = OpTable::new();
    for top in tops {
        if let Top::Relation(r) = top {
            match template_to_fragments(&r.template, &type_names) {
                Ok(frags) => {
                    op_table.add(r.name.text.clone(), frags);
                }
                Err(d) => diags.push(d),
            }
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
}
