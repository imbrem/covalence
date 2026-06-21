//! The `SExpr` encoding of Metamath expressions.
//!
//! A Metamath expression is a typecode followed by a flat sequence of math
//! symbols. We encode it as a flat [`SExpr`] **list** whose every element is a
//! [`Atom::Symbol`]: `[typecode, sym, sym, ...]`. See the crate-level docs for
//! why this *faithful-flat-sequence* encoding is preferred over a structured
//! tree.
//!
//! Whether a given symbol is a *variable* (substitutable) or a *constant* is
//! not stored in the expression — it is a property of the surrounding
//! [`crate::metamath::Database`]. The expression layer is purely syntactic.

use covalence_sexp::{SExp, SExpr};

/// A Metamath expression: an `SExpr` list `[typecode, sym, sym, ...]`.
///
/// This is a transparent alias for [`SExpr`]; we keep the alias to document
/// intent at call sites. All elements are expected to be [`Atom::Symbol`]s; the
/// helpers below tolerate malformed input by returning `None`.
pub type Expr = SExpr;

/// The position of the typecode within an expression list (the head).
pub const TYPECODE_POS: usize = 0;

/// Build an expression from a typecode and a sequence of symbol names.
pub fn make_expr<'a>(typecode: &str, body: impl IntoIterator<Item = &'a str>) -> Expr {
    let mut elems = Vec::new();
    elems.push(SExp::symbol(typecode));
    for s in body {
        elems.push(SExp::symbol(s));
    }
    SExp::List(elems)
}

/// Build an expression from a flat list of symbol names where the first is the
/// typecode. Returns `None` if `symbols` is empty.
pub fn from_symbols<'a>(symbols: impl IntoIterator<Item = &'a str>) -> Option<Expr> {
    let elems: Vec<SExpr> = symbols.into_iter().map(SExp::symbol).collect();
    if elems.is_empty() {
        return None;
    }
    Some(SExp::List(elems))
}

/// The typecode (head symbol) of an expression, if well-formed.
pub fn typecode_of(e: &Expr) -> Option<&str> {
    e.as_list()?.get(TYPECODE_POS)?.as_symbol()
}

/// The body (everything after the typecode) of an expression as an `SExpr`
/// slice, if well-formed.
pub fn body_of(e: &Expr) -> Option<&[SExpr]> {
    let list = e.as_list()?;
    list.get(TYPECODE_POS + 1..)
}

/// All symbol names in an expression (typecode included), in order. Returns
/// `None` if any element is not a plain symbol.
pub fn expr_symbols(e: &Expr) -> Option<Vec<&str>> {
    e.as_list()?
        .iter()
        .map(SExp::as_symbol)
        .collect::<Option<Vec<_>>>()
}

/// Render an expression back to its flat Metamath surface form
/// (`typecode sym sym ...`), for diagnostics.
pub fn render(e: &Expr) -> String {
    match expr_symbols(e) {
        Some(syms) => syms.join(" "),
        None => format!("{e:?}"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn roundtrip() {
        let e = make_expr("wff", ["(", "ph", "->", "ps", ")"]);
        assert_eq!(typecode_of(&e), Some("wff"));
        let body: Vec<&str> = body_of(&e).unwrap().iter().map(|s| s.as_symbol().unwrap()).collect();
        assert_eq!(body, ["(", "ph", "->", "ps", ")"]);
        assert_eq!(render(&e), "wff ( ph -> ps )");
    }

    #[test]
    fn from_symbols_empty_is_none() {
        assert!(from_symbols(std::iter::empty()).is_none());
    }

    #[test]
    fn symbols_all() {
        let e = make_expr("term", ["0"]);
        assert_eq!(expr_symbols(&e), Some(vec!["term", "0"]));
    }
}
