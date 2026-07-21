//! Shared analysis of nested Lisp quasiquotation.
//!
//! @covalence-api {"id":"A0028","title":"Lisp quasiquote templates","status":"experimental","dependsOn":["A0015","A0022"]}

use covalence_sexp::SExpr;

/// A quasiquote template after quote-depth and splice-position validation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Quasiquote<'a> {
    Literal(&'a SExpr),
    Evaluate(&'a SExpr),
    Syntax {
        name: &'static str,
        operand: Box<Self>,
    },
    List(Vec<QuasiquoteItem<'a>>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum QuasiquoteItem<'a> {
    Value(Quasiquote<'a>),
    Splice(&'a SExpr),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum QuasiquoteError {
    Arity { form: &'static str },
    SpliceOutsideList,
}

/// Analyze one template, retaining evaluation forms as untrusted syntax.
pub fn analyze(template: &SExpr) -> Result<Quasiquote<'_>, QuasiquoteError> {
    analyze_at(template, 1, false)
}

fn analyze_at(
    template: &SExpr,
    depth: usize,
    splice_position: bool,
) -> Result<Quasiquote<'_>, QuasiquoteError> {
    let Some(items) = template.as_list() else {
        return Ok(Quasiquote::Literal(template));
    };
    if let Some(name @ ("unquote" | "unquote-splicing" | "quasiquote")) =
        items.first().and_then(SExpr::as_symbol)
    {
        let name = match name {
            "unquote" => "unquote",
            "unquote-splicing" => "unquote-splicing",
            "quasiquote" => "quasiquote",
            _ => unreachable!(),
        };
        if items.len() != 2 {
            return Err(QuasiquoteError::Arity { form: name });
        }
        match name {
            "unquote" if depth == 1 => return Ok(Quasiquote::Evaluate(&items[1])),
            "unquote-splicing" if depth == 1 && splice_position => {
                return Ok(Quasiquote::Evaluate(&items[1]));
            }
            "unquote-splicing" if depth == 1 => {
                return Err(QuasiquoteError::SpliceOutsideList);
            }
            "quasiquote" => {
                return Ok(Quasiquote::Syntax {
                    name: "quasiquote",
                    operand: Box::new(analyze_at(&items[1], depth + 1, false)?),
                });
            }
            "unquote" | "unquote-splicing" => {
                return Ok(Quasiquote::Syntax {
                    name: if name == "unquote" {
                        "unquote"
                    } else {
                        "unquote-splicing"
                    },
                    operand: Box::new(analyze_at(&items[1], depth - 1, false)?),
                });
            }
            _ => unreachable!(),
        }
    }

    items
        .iter()
        .map(|item| {
            let splice = item.as_list().is_some_and(|form| {
                form.first().and_then(SExpr::as_symbol) == Some("unquote-splicing")
            });
            if splice && depth == 1 {
                match analyze_at(item, depth, true)? {
                    Quasiquote::Evaluate(expression) => Ok(QuasiquoteItem::Splice(expression)),
                    _ => unreachable!("active splice analyzes as evaluation"),
                }
            } else {
                Ok(QuasiquoteItem::Value(analyze_at(item, depth, false)?))
            }
        })
        .collect::<Result<Vec<_>, _>>()
        .map(Quasiquote::List)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn nesting_delays_unquote_and_active_splicing_is_explicit() {
        let template = covalence_sexp::parse(
            "(outer (quasiquote ((unquote x))) (unquote y) (unquote-splicing zs))",
        )
        .unwrap()
        .pop()
        .unwrap();
        let Quasiquote::List(items) = analyze(&template).unwrap() else {
            panic!("expected list plan")
        };
        assert!(matches!(
            items[1],
            QuasiquoteItem::Value(Quasiquote::Syntax { .. })
        ));
        assert!(matches!(
            items[2],
            QuasiquoteItem::Value(Quasiquote::Evaluate(_))
        ));
        assert!(matches!(items[3], QuasiquoteItem::Splice(_)));
    }
}
