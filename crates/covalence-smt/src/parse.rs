use covalence_sexp::{SExp, SExpr};

use crate::alethe::{AletheCommand, AletheProof};
use crate::error::AletheError;
use crate::problem::SmtProblem;

/// Parse an Alethe proof from its textual representation.
///
/// Uses the SMT-LIB S-expression dialect, then interprets each top-level
/// list as an Alethe command (`assume`, `step`, `anchor`, `define-fun`).
pub fn parse_alethe(input: &str) -> Result<AletheProof, AletheError> {
    let sexps = covalence_sexp::parse_smt(input)?;
    let mut commands = Vec::new();
    for sexp in sexps {
        commands.push(parse_command(sexp)?);
    }
    Ok(AletheProof::new(commands))
}

fn parse_command(sexp: SExpr) -> Result<AletheCommand, AletheError> {
    let items = match sexp {
        SExp::List(items) => items,
        SExp::Atom(_) => return Err(AletheError::ExpectedList),
    };

    let head = items
        .first()
        .and_then(|s| s.as_symbol())
        .ok_or(AletheError::MissingField("command name"))?;

    match head {
        "assume" => parse_assume(&items),
        "step" => parse_step(&items),
        "anchor" => parse_anchor(&items),
        "define-fun" => parse_define_fun(&items),
        other => Err(AletheError::UnrecognizedCommand(other.to_string())),
    }
}

/// `(assume <id> <formula>)`
fn parse_assume(items: &[SExpr]) -> Result<AletheCommand, AletheError> {
    let id = items
        .get(1)
        .and_then(|s| s.as_symbol())
        .ok_or(AletheError::MissingField("assume id"))?
        .to_string();
    let term = items
        .get(2)
        .ok_or(AletheError::MissingField("assume term"))?
        .clone();
    Ok(AletheCommand::Assume { id, term })
}

/// `(step <id> (cl ...) :rule <name> [:premises (...)] [:args (...)] [:discharge (...)])`
fn parse_step(items: &[SExpr]) -> Result<AletheCommand, AletheError> {
    let id = items
        .get(1)
        .and_then(|s| s.as_symbol())
        .ok_or(AletheError::MissingField("step id"))?
        .to_string();

    let clause_list = items
        .get(2)
        .ok_or(AletheError::MissingField("step clause"))?;
    let clause = parse_clause(clause_list)?;

    let mut rule = String::new();
    let mut premises = Vec::new();
    let mut args = Vec::new();
    let mut discharge = Vec::new();

    // Scan keyword attributes starting at index 3
    let mut i = 3;
    while i < items.len() {
        if let Some(kw) = items[i].as_symbol() {
            match kw {
                ":rule" => {
                    i += 1;
                    rule = items
                        .get(i)
                        .and_then(|s| s.as_symbol())
                        .ok_or(AletheError::MissingField("step rule value"))?
                        .to_string();
                }
                ":premises" => {
                    i += 1;
                    premises = extract_symbol_list(
                        items
                            .get(i)
                            .ok_or(AletheError::MissingField("step premises value"))?,
                    )?;
                }
                ":args" => {
                    i += 1;
                    args = extract_sexp_list(
                        items
                            .get(i)
                            .ok_or(AletheError::MissingField("step args value"))?,
                    )?;
                }
                ":discharge" => {
                    i += 1;
                    discharge = extract_symbol_list(
                        items
                            .get(i)
                            .ok_or(AletheError::MissingField("step discharge value"))?,
                    )?;
                }
                _ => {}
            }
        }
        i += 1;
    }

    if rule.is_empty() {
        return Err(AletheError::MissingField("step :rule"));
    }

    Ok(AletheCommand::Step {
        id,
        clause,
        rule,
        premises,
        args,
        discharge,
    })
}

/// Parse `(cl ...)` — returns the literals (everything after the `cl` symbol).
fn parse_clause(sexp: &SExpr) -> Result<Vec<SExpr>, AletheError> {
    let items = sexp.as_list().ok_or(AletheError::ExpectedList)?;
    let head = items.first().and_then(|s| s.as_symbol());
    if head != Some("cl") {
        return Err(AletheError::MissingField("cl keyword in clause"));
    }
    Ok(items[1..].to_vec())
}

/// `(anchor :step <id> [:args (...)])`
fn parse_anchor(items: &[SExpr]) -> Result<AletheCommand, AletheError> {
    let mut step = String::new();
    let mut args = Vec::new();

    let mut i = 1;
    while i < items.len() {
        if let Some(kw) = items[i].as_symbol() {
            match kw {
                ":step" => {
                    i += 1;
                    step = items
                        .get(i)
                        .and_then(|s| s.as_symbol())
                        .ok_or(AletheError::MissingField("anchor :step value"))?
                        .to_string();
                }
                ":args" => {
                    i += 1;
                    args = extract_sexp_list(
                        items
                            .get(i)
                            .ok_or(AletheError::MissingField("anchor :args value"))?,
                    )?;
                }
                _ => {}
            }
        }
        i += 1;
    }

    if step.is_empty() {
        return Err(AletheError::MissingField("anchor :step"));
    }

    Ok(AletheCommand::Anchor { step, args })
}

/// `(define-fun <name> (<params>...) <sort> <body>)`
fn parse_define_fun(items: &[SExpr]) -> Result<AletheCommand, AletheError> {
    let name = items
        .get(1)
        .and_then(|s| s.as_symbol())
        .ok_or(AletheError::MissingField("define-fun name"))?
        .to_string();

    let params_sexp = items
        .get(2)
        .ok_or(AletheError::MissingField("define-fun params"))?;
    let params = match params_sexp {
        SExp::List(children) => children.clone(),
        SExp::Atom(_) => return Err(AletheError::ExpectedList),
    };

    let sort = items
        .get(3)
        .ok_or(AletheError::MissingField("define-fun sort"))?
        .clone();
    let body = items
        .get(4)
        .ok_or(AletheError::MissingField("define-fun body"))?
        .clone();

    Ok(AletheCommand::DefineFun {
        name,
        params,
        sort,
        body,
    })
}

/// Parse an SMT-LIB2 problem from its textual representation.
///
/// Recognizes `set-logic`, `declare-sort`, `declare-fun`, `declare-const`,
/// and `assert` commands. Metadata commands (`check-sat`, `exit`, `set-info`,
/// `set-option`, `get-proof`) are silently skipped.
/// Unknown commands produce an error.
pub fn parse_smtlib2(input: &str) -> Result<SmtProblem, AletheError> {
    let sexps = covalence_sexp::parse_smt(input)?;
    let mut problem = SmtProblem::new();
    for sexp in sexps {
        parse_smtlib2_command(sexp, &mut problem)?;
    }
    Ok(problem)
}

fn parse_smtlib2_command(sexp: SExpr, problem: &mut SmtProblem) -> Result<(), AletheError> {
    let items = match sexp {
        SExp::List(items) => items,
        SExp::Atom(_) => return Err(AletheError::ExpectedList),
    };

    let head = items
        .first()
        .and_then(|s| s.as_symbol())
        .ok_or(AletheError::MissingField("command name"))?;

    match head {
        "set-logic" => {
            let logic = items
                .get(1)
                .and_then(|s| s.as_symbol())
                .ok_or(AletheError::MissingField("set-logic name"))?;
            problem.set_logic(logic);
        }
        "declare-sort" => {
            let name = items
                .get(1)
                .and_then(|s| s.as_symbol())
                .ok_or(AletheError::MissingField("declare-sort name"))?;
            let arity_str = items
                .get(2)
                .and_then(|s| s.as_symbol())
                .ok_or(AletheError::MissingField("declare-sort arity"))?;
            let arity: u32 = arity_str
                .parse()
                .map_err(|_| AletheError::MissingField("declare-sort arity (not a number)"))?;
            problem.declare_sort(name, arity);
        }
        "declare-fun" => {
            let name = items
                .get(1)
                .and_then(|s| s.as_symbol())
                .ok_or(AletheError::MissingField("declare-fun name"))?
                .to_string();
            let params_sexp = items
                .get(2)
                .ok_or(AletheError::MissingField("declare-fun params"))?;
            let params = match params_sexp {
                SExp::List(children) => children.clone(),
                SExp::Atom(_) => return Err(AletheError::ExpectedList),
            };
            let sort = items
                .get(3)
                .ok_or(AletheError::MissingField("declare-fun sort"))?
                .clone();
            problem.declare_fun(name, params, sort);
        }
        "declare-const" => {
            let name = items
                .get(1)
                .and_then(|s| s.as_symbol())
                .ok_or(AletheError::MissingField("declare-const name"))?
                .to_string();
            let sort = items
                .get(2)
                .ok_or(AletheError::MissingField("declare-const sort"))?
                .clone();
            problem.declare_fun(name, vec![], sort);
        }
        "assert" => {
            let term = items
                .get(1)
                .ok_or(AletheError::MissingField("assert term"))?
                .clone();
            problem.assert_term(term);
        }
        // Metadata / non-semantic commands — skip silently.
        "check-sat" | "exit" | "set-info" | "set-option" | "get-proof" => {}
        other => return Err(AletheError::UnrecognizedCommand(other.to_string())),
    }

    Ok(())
}

/// Extract a list of symbol strings from a parenthesized list.
fn extract_symbol_list(sexp: &SExpr) -> Result<Vec<String>, AletheError> {
    let items = sexp.as_list().ok_or(AletheError::ExpectedList)?;
    items
        .iter()
        .map(|s| {
            s.as_symbol()
                .map(|sym| sym.to_string())
                .ok_or(AletheError::ExpectedSymbol)
        })
        .collect()
}

/// Extract the children of a parenthesized list as `Vec<SExpr>`.
fn extract_sexp_list(sexp: &SExpr) -> Result<Vec<SExpr>, AletheError> {
    let items = sexp.as_list().ok_or(AletheError::ExpectedList)?;
    Ok(items.to_vec())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_assume_command() {
        let proof = parse_alethe("(assume h1 (not x))").unwrap();
        assert_eq!(proof.len(), 1);
        match &proof.commands()[0] {
            AletheCommand::Assume { id, term } => {
                assert_eq!(id, "h1");
                assert_eq!(
                    *term,
                    SExp::List(vec![SExp::symbol("not"), SExp::symbol("x")])
                );
            }
            other => panic!("expected Assume, got {other:?}"),
        }
    }

    #[test]
    fn parse_step_command() {
        let input = "(step t1 (cl (not x) y) :rule resolution :premises (h1 h2))";
        let proof = parse_alethe(input).unwrap();
        assert_eq!(proof.len(), 1);
        match &proof.commands()[0] {
            AletheCommand::Step {
                id,
                clause,
                rule,
                premises,
                args,
                discharge,
            } => {
                assert_eq!(id, "t1");
                assert_eq!(clause.len(), 2);
                assert_eq!(rule, "resolution");
                assert_eq!(premises, &["h1", "h2"]);
                assert!(args.is_empty());
                assert!(discharge.is_empty());
            }
            other => panic!("expected Step, got {other:?}"),
        }
    }

    #[test]
    fn parse_step_with_args() {
        let input = "(step t1 (cl x) :rule inst :args ((= z a)))";
        let proof = parse_alethe(input).unwrap();
        match &proof.commands()[0] {
            AletheCommand::Step { args, .. } => {
                assert_eq!(args.len(), 1);
            }
            other => panic!("expected Step, got {other:?}"),
        }
    }

    #[test]
    fn parse_step_with_discharge() {
        let input = "(step t3 (cl (not a) b) :rule subproof :discharge (h1))";
        let proof = parse_alethe(input).unwrap();
        match &proof.commands()[0] {
            AletheCommand::Step { discharge, .. } => {
                assert_eq!(discharge, &["h1"]);
            }
            other => panic!("expected Step, got {other:?}"),
        }
    }

    #[test]
    fn parse_anchor_command() {
        let input = "(anchor :step t3 :args ((x Int)))";
        let proof = parse_alethe(input).unwrap();
        match &proof.commands()[0] {
            AletheCommand::Anchor { step, args } => {
                assert_eq!(step, "t3");
                assert_eq!(args.len(), 1);
            }
            other => panic!("expected Anchor, got {other:?}"),
        }
    }

    #[test]
    fn parse_define_fun_command() {
        let input = "(define-fun f ((x Int)) Bool (= x 0))";
        let proof = parse_alethe(input).unwrap();
        match &proof.commands()[0] {
            AletheCommand::DefineFun {
                name,
                params,
                sort,
                body,
            } => {
                assert_eq!(name, "f");
                assert_eq!(params.len(), 1);
                assert_eq!(*sort, SExp::symbol("Bool"));
                assert!(matches!(body, SExp::List(_)));
            }
            other => panic!("expected DefineFun, got {other:?}"),
        }
    }

    #[test]
    fn parse_empty_input() {
        let proof = parse_alethe("").unwrap();
        assert!(proof.is_empty());
    }

    #[test]
    fn parse_comment_only() {
        let proof = parse_alethe("; just a comment\n").unwrap();
        assert!(proof.is_empty());
    }

    #[test]
    fn error_unrecognized_command() {
        let err = parse_alethe("(foobar x y)").unwrap_err();
        assert!(matches!(err, AletheError::UnrecognizedCommand(_)));
    }

    #[test]
    fn error_missing_step_rule() {
        let err = parse_alethe("(step t1 (cl x))").unwrap_err();
        assert!(matches!(err, AletheError::MissingField(_)));
    }

    #[test]
    fn error_bare_atom() {
        let err = parse_alethe("assume").unwrap_err();
        assert!(matches!(err, AletheError::ExpectedList));
    }

    #[test]
    fn parse_empty_clause() {
        let input = "(step t1 (cl) :rule false)";
        let proof = parse_alethe(input).unwrap();
        match &proof.commands()[0] {
            AletheCommand::Step { clause, .. } => {
                assert!(clause.is_empty());
            }
            other => panic!("expected Step, got {other:?}"),
        }
    }

    #[test]
    fn parse_multiple_commands() {
        let input = "\
(assume h1 a)
(assume h2 (not a))
(step t1 (cl) :rule resolution :premises (h1 h2))";
        let proof = parse_alethe(input).unwrap();
        assert_eq!(proof.len(), 3);
        assert!(matches!(proof.commands()[0], AletheCommand::Assume { .. }));
        assert!(matches!(proof.commands()[1], AletheCommand::Assume { .. }));
        assert!(matches!(proof.commands()[2], AletheCommand::Step { .. }));
    }

    // ----------------------------------------------------------------
    // parse_smtlib2 tests
    // ----------------------------------------------------------------

    #[test]
    fn smtlib2_set_logic() {
        let p = parse_smtlib2("(set-logic QF_UF)").unwrap();
        assert_eq!(p.logic(), Some("QF_UF"));
    }

    #[test]
    fn smtlib2_declare_sort() {
        let p = parse_smtlib2("(declare-sort U 0)").unwrap();
        assert_eq!(p.sorts().len(), 1);
        assert_eq!(p.sorts()[0].name, "U");
        assert_eq!(p.sorts()[0].arity, 0);
    }

    #[test]
    fn smtlib2_declare_fun() {
        let p = parse_smtlib2("(declare-fun f (Int Int) Bool)").unwrap();
        assert_eq!(p.funs().len(), 1);
        assert_eq!(p.funs()[0].name, "f");
        assert_eq!(p.funs()[0].params.len(), 2);
        assert_eq!(p.funs()[0].sort.as_symbol(), Some("Bool"));
    }

    #[test]
    fn smtlib2_declare_const() {
        let p = parse_smtlib2("(declare-const x Int)").unwrap();
        assert_eq!(p.funs().len(), 1);
        assert_eq!(p.funs()[0].name, "x");
        assert!(p.funs()[0].params.is_empty());
        assert_eq!(p.funs()[0].sort.as_symbol(), Some("Int"));
    }

    #[test]
    fn smtlib2_assert() {
        let p = parse_smtlib2("(assert (= x 0))").unwrap();
        assert_eq!(p.assertions().len(), 1);
        assert!(p.assertions()[0].as_list().is_some());
    }

    #[test]
    fn smtlib2_skip_metadata() {
        let input =
            "(set-info :source \"test\")\n(set-option :produce-proofs true)\n(check-sat)\n(exit)";
        let p = parse_smtlib2(input).unwrap();
        assert!(p.logic().is_none());
        assert!(p.assertions().is_empty());
    }

    #[test]
    fn smtlib2_unrecognized_command() {
        let err = parse_smtlib2("(foobar x)").unwrap_err();
        assert!(matches!(err, AletheError::UnrecognizedCommand(_)));
    }

    #[test]
    fn smtlib2_full_problem() {
        let input = "\
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun p (U) Bool)
(assert (p a))
(assert (= a b))
(assert (not (p b)))
(check-sat)
(exit)";
        let p = parse_smtlib2(input).unwrap();
        assert_eq!(p.logic(), Some("QF_UF"));
        assert_eq!(p.sorts().len(), 1);
        assert_eq!(p.funs().len(), 3);
        assert_eq!(p.assertions().len(), 3);
    }
}
