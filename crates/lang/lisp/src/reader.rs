//! The reader — a thin wrapper over [`covalence_sexp::parse`].
//!
//! Materializes the [`SExpr`] tree (the simplest correct thing). The
//! event-driven fold-to-`Term` path (`SExpBuilder` / `TreeBuilder`) is a
//! future allocation optimization; see the generated open-work index.

use covalence_sexp::{ParseError, SExpr, parse};
use covalence_sexpr_api::SExprSyntax;

/// Fold the parser's proper-list surface tree into an abstract S-expression
/// representation.
///
/// This adapter lives in the language layer so the low-level parser never
/// depends on `covalence-sexpr-api`. `atom` selects the dialect's payload
/// interpretation; list structure is lowered solely through the abstract
/// `nil`/`cons` capabilities.
pub fn lower_with<A>(
    api: &A,
    sexpr: &SExpr,
    atom: &impl Fn(&covalence_sexp::Atom) -> Result<A::Payload, A::Error>,
) -> Result<A::Value, A::Error>
where
    A: SExprSyntax + ?Sized,
{
    match sexpr {
        SExpr::Atom(value) => api.atom(atom(value)?),
        SExpr::List(items) => {
            let mut result = api.nil();
            for item in items.iter().rev() {
                let head = lower_with(api, item, atom)?;
                result = api.cons(head, result)?;
            }
            Ok(result)
        }
    }
}

/// Parse `src` into a sequence of top-level S-expressions.
pub fn read(src: &str) -> Result<Vec<SExpr>, ParseError> {
    parse(src)
}

/// Parse an **ACL2 book source** into its top-level forms. Books use
/// single-`;` line comments (and `"..."` strings), which is the SMT-LIB
/// trivia dialect — the REPL's [`read`]/[`read_one`] (Covalence dialect,
/// `;;` comments) are unchanged. No `'x` reader macro and no `#|…|#` block
/// comments — see `notes/vibes/lisp/acl2-book-frontend.md` §2.
pub fn read_book(src: &str) -> Result<Vec<SExpr>, ParseError> {
    covalence_sexp::parse_smt(src)
}

/// Parse `src` expecting exactly one top-level S-expression (one REPL cell).
pub fn read_one(src: &str) -> Result<SExpr, ReadError> {
    let mut forms = parse(src).map_err(ReadError::Parse)?;
    match forms.len() {
        1 => Ok(forms.pop().expect("len checked")),
        n => Err(ReadError::Arity(n)),
    }
}

/// A single-form read error.
#[derive(Debug, thiserror::Error)]
pub enum ReadError {
    /// The S-expression parser failed.
    #[error(transparent)]
    Parse(ParseError),
    /// Expected exactly one top-level form, found `n`.
    #[error("expected exactly one top-level form, found {0}")]
    Arity(usize),
}

#[cfg(test)]
mod tests {
    use covalence_sexpr_api::{Free, FreeSExpr};

    use super::*;

    #[test]
    fn parsed_proper_lists_lower_through_the_abstract_api() {
        let parsed = read_one("(a (b))").unwrap();
        let lowered = lower_with(&Free::<String>::new(), &parsed, &|atom| match atom {
            covalence_sexp::Atom::Symbol(value) => Ok(value.to_string()),
            covalence_sexp::Atom::Str { .. } => unreachable!(),
        })
        .unwrap();

        assert_eq!(
            lowered,
            FreeSExpr::Cons(
                Box::new(FreeSExpr::Atom("a".into())),
                Box::new(FreeSExpr::Cons(
                    Box::new(FreeSExpr::Cons(
                        Box::new(FreeSExpr::Atom("b".into())),
                        Box::new(FreeSExpr::Nil),
                    )),
                    Box::new(FreeSExpr::Nil),
                )),
            )
        );
    }
}
