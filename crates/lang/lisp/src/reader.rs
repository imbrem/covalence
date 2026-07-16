//! The reader — a thin wrapper over [`covalence_sexp::parse`].
//!
//! Materializes the [`SExpr`] tree (the simplest correct thing). The
//! event-driven fold-to-`Term` path (`SExpBuilder` / `TreeBuilder`) is a
//! future allocation optimization; see `SKELETONS.md`.

use covalence_sexp::{ParseError, SExpr, parse};

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
