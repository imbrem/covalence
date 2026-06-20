//! A parser for the *uncompressed* `.mm` subset.
//!
//! Supports the keyword set `$c $v $f $e $d $a $p $.`, scoping `${ ... $}`, and
//! comments `$( ... $)`. The **compressed** proof format and `$[ ... $]` file
//! inclusion are north stars — see this crate's `SKELETONS.md`.
//!
//! Metamath tokenisation is simply whitespace-separated tokens (the language
//! has no string literals or nested delimiters at the token level), so the
//! lexer is a hand-rolled scanner; `covalence-parse` is a declared dependency
//! for the day we need its combinators for richer surface syntax.

use covalence_sexp::SExpr;

use crate::database::{Database, FloatHyp, Hypothesis};
use crate::error::MmError;
use crate::expr::from_symbols;

/// Parse an uncompressed `.mm` source string into a [`Database`].
pub fn parse(input: &str) -> Result<Database, MmError> {
    let tokens = tokenize(input)?;
    let mut p = Parser {
        toks: &tokens,
        pos: 0,
    };
    let mut db = Database::new();
    p.parse_block(&mut db, true)?;
    db.finish()
}

/// Whitespace-tokenise, stripping `$( ... $)` comments.
fn tokenize(input: &str) -> Result<Vec<String>, MmError> {
    let mut out = Vec::new();
    let mut raw = input.split_ascii_whitespace().peekable();
    while let Some(tok) = raw.next() {
        if tok == "$(" {
            // Consume to matching `$)`.
            let mut closed = false;
            for t in raw.by_ref() {
                if t == "$)" {
                    closed = true;
                    break;
                }
            }
            if !closed {
                return Err(MmError::Parse("unterminated comment `$(`".into()));
            }
            continue;
        }
        if tok == "$)" {
            return Err(MmError::Parse("unmatched `$)`".into()));
        }
        out.push(tok.to_string());
    }
    Ok(out)
}

struct Parser<'a> {
    toks: &'a [String],
    pos: usize,
}

impl<'a> Parser<'a> {
    fn peek(&self) -> Option<&'a str> {
        self.toks.get(self.pos).map(String::as_str)
    }

    fn next(&mut self) -> Option<&'a str> {
        let t = self.toks.get(self.pos).map(String::as_str);
        if t.is_some() {
            self.pos += 1;
        }
        t
    }

    /// Parse statements until end of input or a closing `$}`. `top_level` is
    /// true for the outermost block; a `$}` there is an unmatched-scope error.
    fn parse_block(&mut self, db: &mut Database, top_level: bool) -> Result<(), MmError> {
        while let Some(tok) = self.peek() {
            match tok {
                "$}" if top_level => {
                    return Err(MmError::Parse("unmatched `$}`".into()));
                }
                "$}" => return Ok(()),
                "${" => {
                    self.next();
                    db.push_scope();
                    self.parse_block(db, false)?;
                    match self.next() {
                        Some("$}") => db.pop_scope()?,
                        _ => return Err(MmError::Parse("unclosed `${`".into())),
                    }
                }
                "$c" => {
                    self.next();
                    let syms = self.read_until_dot("$c")?;
                    db.declare_constants(syms)?;
                }
                "$v" => {
                    self.next();
                    let syms = self.read_until_dot("$v")?;
                    db.declare_variables(syms)?;
                }
                "$d" => {
                    self.next();
                    let syms = self.read_until_dot("$d")?;
                    db.add_disjoint(syms)?;
                }
                kw if kw.starts_with('$') => {
                    return Err(MmError::Parse(format!(
                        "unexpected keyword `{kw}` (expected a label or `$c/$v/$d/${{/$}}`)"
                    )));
                }
                _ => {
                    // A label introduces a $f/$e/$a/$p statement.
                    let label = self.next().unwrap().to_string();
                    let kw = self.next().ok_or_else(|| {
                        MmError::Parse(format!("expected keyword after label `{label}`"))
                    })?;
                    match kw {
                        "$f" => self.parse_float(db, label)?,
                        "$e" => self.parse_essential(db, label)?,
                        "$a" => self.parse_assert(db, label, false)?,
                        "$p" => self.parse_assert(db, label, true)?,
                        other => {
                            return Err(MmError::Parse(format!(
                                "unexpected keyword `{other}` after label `{label}`"
                            )));
                        }
                    }
                }
            }
        }
        Ok(())
    }

    /// Read tokens up to and consuming `$.`.
    fn read_until_dot(&mut self, ctx: &str) -> Result<Vec<String>, MmError> {
        let mut out = Vec::new();
        loop {
            match self.next() {
                Some("$.") => return Ok(out),
                Some(t) if t.starts_with('$') => {
                    return Err(MmError::Parse(format!(
                        "unexpected `{t}` in {ctx} (expected `$.`)"
                    )));
                }
                Some(t) => out.push(t.to_string()),
                None => return Err(MmError::Parse(format!("unterminated {ctx}"))),
            }
        }
    }

    fn parse_float(&mut self, db: &mut Database, label: String) -> Result<(), MmError> {
        let body = self.read_until_dot("$f")?;
        if body.len() != 2 {
            return Err(MmError::Parse(format!(
                "`{label}` $f must be `typecode var`, got {body:?}"
            )));
        }
        db.add_float(FloatHyp {
            label,
            typecode: body[0].clone(),
            var: body[1].clone(),
        })
    }

    fn parse_essential(&mut self, db: &mut Database, label: String) -> Result<(), MmError> {
        let syms = self.read_until_dot("$e")?;
        let expr = self.make_expr(&label, &syms)?;
        db.add_essential(Hypothesis { label, expr })
    }

    fn parse_assert(
        &mut self,
        db: &mut Database,
        label: String,
        provable: bool,
    ) -> Result<(), MmError> {
        // Read the conclusion symbols up to `$.` (axiom) or `$=` (theorem).
        let mut syms = Vec::new();
        let proof: Option<Vec<String>> = loop {
            match self.next() {
                Some("$.") => break None,
                Some("$=") if provable => {
                    break Some(self.read_proof(&label)?);
                }
                Some("$=") => {
                    return Err(MmError::Parse(format!(
                        "`{label}` is a `$a` axiom and cannot have a proof (`$=`)"
                    )));
                }
                Some(t) if t.starts_with('$') => {
                    return Err(MmError::Parse(format!("unexpected `{t}` in `{label}`")));
                }
                Some(t) => syms.push(t.to_string()),
                None => return Err(MmError::Parse(format!("unterminated `{label}`"))),
            }
        };
        if provable && proof.is_none() {
            return Err(MmError::Parse(format!(
                "`{label}` $p has no proof (missing `$=`)"
            )));
        }
        let conclusion = self.make_expr(&label, &syms)?;
        db.add_assertion(label, conclusion, proof)
    }

    /// Read an (uncompressed) proof: labels up to `$.`. Rejects the compressed
    /// format (`( ... ) letters`) with a clear message.
    fn read_proof(&mut self, label: &str) -> Result<Vec<String>, MmError> {
        if self.peek() == Some("(") {
            return Err(MmError::Parse(format!(
                "`{label}` uses the compressed proof format, which is not yet supported \
                 (see SKELETONS.md)"
            )));
        }
        let mut labels = Vec::new();
        loop {
            match self.next() {
                Some("$.") => return Ok(labels),
                Some("?") => {
                    return Err(MmError::Parse(format!(
                        "`{label}` contains an incomplete-proof placeholder `?`"
                    )));
                }
                Some(t) if t.starts_with('$') => {
                    return Err(MmError::Parse(format!(
                        "unexpected `{t}` in proof of `{label}`"
                    )));
                }
                Some(t) => labels.push(t.to_string()),
                None => return Err(MmError::Parse(format!("unterminated proof of `{label}`"))),
            }
        }
    }

    /// Build an `SExpr` expression from a symbol list (the first being the
    /// typecode), validating it is non-empty.
    fn make_expr(&self, label: &str, syms: &[String]) -> Result<SExpr, MmError> {
        from_symbols(syms.iter().map(String::as_str)).ok_or_else(|| MmError::MalformedExpr {
            label: label.to_string(),
            message: "expression is empty (needs at least a typecode)".into(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::{render, typecode_of};

    #[test]
    fn parse_constants_and_vars() {
        let db = parse("$c wff |- $. $v ph $.").unwrap();
        assert!(db.is_symbol("wff"));
        assert!(!db.is_variable("wff"));
        assert!(db.is_variable("ph"));
    }

    #[test]
    fn comments_skipped() {
        let db = parse("$( hello $) $c a $.").unwrap();
        assert!(db.is_symbol("a"));
    }

    #[test]
    fn float_parsed() {
        let db = parse("$c wff $. $v ph $. wph $f wff ph $.").unwrap();
        let stmt = db.statement_by_label("wph").unwrap();
        assert!(matches!(stmt, crate::database::Statement::Float(_)));
    }

    #[test]
    fn axiom_conclusion_is_sexpr() {
        let db = parse("$c term 0 $. tze $a term 0 $.").unwrap();
        let a = db.assertions().next().unwrap();
        assert_eq!(typecode_of(&a.conclusion), Some("term"));
        assert_eq!(render(&a.conclusion), "term 0");
    }

    #[test]
    fn unterminated_comment_errors() {
        assert!(parse("$( oops").is_err());
    }

    #[test]
    fn compressed_proof_rejected_clearly() {
        let src = "$c term 0 $. tze $a term 0 $. th $p term 0 $= ( tze ) A $.";
        let err = parse(src).unwrap_err();
        assert!(format!("{err}").contains("compressed"));
    }

    #[test]
    fn duplicate_label_rejected() {
        let src = "$c term $. $v t $. tt $f term t $. tt $f term t $.";
        assert!(matches!(parse(src), Err(MmError::DuplicateLabel(_))));
    }

    #[test]
    fn unmatched_scope_close_errors() {
        assert!(parse("$c a $. $}").is_err());
    }
}
