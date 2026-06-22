//! Parse SpecTec AST fragments straight from their **S-expression** form —
//! the textual encoding the upstream OCaml SpecTec compiler emits.
//!
//! [`crate::wasm`] / [`crate::ast::parse_spectec_stream`] already parse a whole
//! *stream* of top-level definitions. This module adds the missing small
//! pieces: parsing a single [`ast::SpecTecSym`] (grammar symbol) or
//! [`ast::SpecTecDef`] (definition) from a string, so grammars — and the tests
//! over them — can be written inline as readable S-expressions like
//! `(seq (iter (num 0x80) list) (num 0x0B))` instead of constructing the AST
//! by hand.
//!
//! It is a thin layer over the same machinery `parse_spectec_stream` uses:
//! [`sexpr_parse`] tokenises the S-expression into [`sexpr_parse::SExprItem`]s
//! and the derived [`decode::Decode`] impl turns those into the typed AST.

use crate::ast;
use crate::decode::Decode;

/// An error parsing a SpecTec AST fragment from S-expression text.
#[derive(Debug, Clone, thiserror::Error)]
pub enum ParseError {
    /// The input was not well-formed S-expression syntax.
    #[error("s-expression syntax error: {0}")]
    Sexpr(String),
    /// The S-expression did not decode into the requested AST node.
    #[error("decode error: {0}")]
    Decode(String),
    /// The input held no top-level S-expression at all.
    #[error("expected one s-expression, found none")]
    Empty,
    /// More than one top-level S-expression where exactly one was expected.
    #[error("expected a single s-expression, found trailing input")]
    Trailing,
}

/// Parse exactly one value of a [`Decode`] type `T` from an S-expression.
fn parse_one<T: Decode>(input: &str) -> Result<T, ParseError> {
    let items =
        sexpr_parse::parse_sexpr_stream(input).map_err(|e| ParseError::Sexpr(e.to_string()))?;
    let mut it = items.iter().peekable();
    if it.peek().is_none() {
        return Err(ParseError::Empty);
    }
    let value = T::decode(&mut it).map_err(|e| ParseError::Decode(e.to_string()))?;
    if it.peek().is_some() {
        return Err(ParseError::Trailing);
    }
    Ok(value)
}

/// Parse a single grammar symbol, e.g. `(num 0x0B)`,
/// `(alt (num 0x61) (num 0x62))`, or `(seq (iter (num 0x80) list) (num 0x0B))`.
pub fn parse_sym(input: &str) -> Result<ast::SpecTecSym, ParseError> {
    parse_one(input)
}

/// Parse a single top-level definition, e.g. a `(gram …)`.
pub fn parse_def(input: &str) -> Result<ast::SpecTecDef, ParseError> {
    parse_one(input)
}

/// Parse a whole stream of top-level definitions (re-exposes
/// [`ast::parse_spectec_stream`] with this module's error type).
pub fn parse_defs(input: &str) -> Result<Vec<ast::SpecTecDef>, ParseError> {
    ast::parse_spectec_stream(input).map_err(|e| ParseError::Decode(e.to_string()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{SpecTecIter, SpecTecSym};

    #[test]
    fn parse_num_and_text() {
        assert_eq!(parse_sym("(num 0x0B)").unwrap(), SpecTecSym::Num { n: 0x0B });
        assert_eq!(
            parse_sym(r#"(text "abc")"#).unwrap(),
            SpecTecSym::Text { t: "abc".into() },
        );
        // The bare `eps` atom only ever appears *nested* (the S-expression
        // stream parser requires every top-level item to be a `(…)` node), so
        // exercise it inside a `seq`.
        assert_eq!(
            parse_sym("(seq eps (num 0x0B))").unwrap(),
            SpecTecSym::Seq {
                gs: vec![SpecTecSym::Eps, SpecTecSym::Num { n: 0x0B }],
            },
        );
    }

    #[test]
    fn parse_nested_symbol() {
        // `0x80* 0x0B`
        let sym = parse_sym("(seq (iter (num 0x80) list) (num 0x0B))").unwrap();
        assert_eq!(
            sym,
            SpecTecSym::Seq {
                gs: vec![
                    SpecTecSym::Iter {
                        g1: Box::new(SpecTecSym::Num { n: 0x80 }),
                        it: SpecTecIter::List,
                        xes: vec![],
                    },
                    SpecTecSym::Num { n: 0x0B },
                ],
            },
        );
    }

    #[test]
    fn errors_are_typed_not_panics() {
        assert!(matches!(parse_sym(""), Err(ParseError::Empty)));
        assert!(parse_sym("(num").is_err());
        assert!(matches!(
            parse_sym("(num 0x0B) (num 0x0C)"),
            Err(ParseError::Trailing),
        ));
    }
}
