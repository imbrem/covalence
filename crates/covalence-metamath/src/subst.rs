//! The substitution engine — the heart of "Metamath-style rewrite".
//!
//! A Metamath substitution maps each variable to a sequence of math symbols
//! (the *body* of an expression of the variable's typecode). Applying a
//! substitution to a schema walks its symbol sequence and, for every symbol
//! that is a substituted variable, **splices** the replacement body in place.
//! Constants and unmapped symbols pass through unchanged.
//!
//! On our flat-list [`Expr`] encoding this is a single pass that preserves the
//! `[typecode, ...body]` shape: the typecode is a constant (never a variable),
//! so it is always copied, and the body symbols are spliced.

use std::collections::BTreeMap;

use covalence_sexp::{Atom, SExp, SExpr};

use crate::expr::Expr;

/// A variable substitution: variable name → replacement body (a sequence of
/// math-symbol `SExpr`s, i.e. an expression with its typecode stripped).
///
/// We use a `BTreeMap` for deterministic iteration in diagnostics.
pub type Subst = BTreeMap<String, Vec<SExpr>>;

/// Apply a substitution to a schema expression, splicing each substituted
/// variable's replacement body in place.
///
/// Non-list inputs and non-symbol elements pass through structurally
/// unchanged (the encoding is flat, so this only matters for robustness).
pub fn apply_subst(schema: &Expr, subst: &Subst) -> Expr {
    match schema {
        SExp::List(elems) => {
            let mut out = Vec::with_capacity(elems.len());
            for e in elems {
                splice_into(e, subst, &mut out);
            }
            SExp::List(out)
        }
        // A bare atom (no list wrapper): substitute if it is a mapped variable.
        atom => {
            let mut out = Vec::new();
            splice_into(atom, subst, &mut out);
            if out.len() == 1 {
                out.into_iter().next().unwrap()
            } else {
                SExp::List(out)
            }
        }
    }
}

/// Push the substitution image of a single schema element into `out`. A mapped
/// variable splices its (possibly multi-symbol) replacement; everything else is
/// copied verbatim.
fn splice_into(e: &SExpr, subst: &Subst, out: &mut Vec<SExpr>) {
    if let SExp::Atom(Atom::Symbol(name)) = e
        && let Some(replacement) = subst.get(name.as_str())
    {
        out.extend(replacement.iter().cloned());
        return;
    }
    out.push(e.clone());
}

/// Collect the distinct variable names appearing in a substituted body, given
/// the set of names that are variables. Used for $d checking: a $d on
/// `(a, b)` requires that the variables occurring in `subst(a)` and `subst(b)`
/// are disjoint.
pub fn vars_in_body<'a>(body: &'a [SExpr], is_variable: &impl Fn(&str) -> bool) -> Vec<&'a str> {
    let mut seen = Vec::new();
    for e in body {
        if let SExp::Atom(Atom::Symbol(name)) = e {
            let n = name.as_str();
            if is_variable(n) && !seen.contains(&n) {
                seen.push(n);
            }
        }
    }
    seen
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::{make_expr, render};

    fn subst(pairs: &[(&str, Expr)]) -> Subst {
        pairs
            .iter()
            .map(|(v, e)| {
                let body = e.as_list().unwrap()[1..].to_vec();
                (v.to_string(), body)
            })
            .collect()
    }

    #[test]
    fn splice_single_variable() {
        // schema: wff ( ph -> ps ) ; ph := ( ph -> ps ), ps := ch
        let schema = make_expr("wff", ["(", "ph", "->", "ps", ")"]);
        let s = subst(&[
            ("ph", make_expr("wff", ["(", "ph", "->", "ps", ")"])),
            ("ps", make_expr("wff", ["ch"])),
        ]);
        let r = apply_subst(&schema, &s);
        assert_eq!(render(&r), "wff ( ( ph -> ps ) -> ch )");
    }

    #[test]
    fn typecode_preserved() {
        // The head typecode is a constant and is never substituted.
        let schema = make_expr("term", ["t"]);
        let s = subst(&[("t", make_expr("term", ["(", "x", "+", "y", ")"]))]);
        let r = apply_subst(&schema, &s);
        assert_eq!(render(&r), "term ( x + y )");
    }

    #[test]
    fn unmapped_symbols_passthrough() {
        let schema = make_expr("wff", ["0", "=", "0"]);
        let s = subst(&[]);
        assert_eq!(render(&apply_subst(&schema, &s)), "wff 0 = 0");
    }

    #[test]
    fn vars_collected() {
        let body = make_expr("_", ["(", "x", "+", "y", ")"]).as_list().unwrap()[1..].to_vec();
        let is_var = |s: &str| matches!(s, "x" | "y");
        assert_eq!(vars_in_body(&body, &is_var), vec!["x", "y"]);
    }
}
