use std::io;

use covalence_sexp::prettyprint;

use crate::AletheProof;
use crate::problem::SmtProblem;

/// Errors that an [`SmtSolver`] may return.
#[derive(Debug, thiserror::Error)]
pub enum SmtSolveError {
    /// The formula is satisfiable (no proof of UNSAT).
    #[error("satisfiable")]
    Sat,

    /// The solver returned unknown.
    #[error("unknown: {0}")]
    Unknown(String),

    /// The solver hit a resource limit (time, memory, …).
    #[error("resource limit: {0}")]
    ResourceLimit(String),

    /// An internal solver error.
    #[error("internal error: {0}")]
    Internal(String),
}

/// An SMT solver backend that produces Alethe proofs.
///
/// Implementations receive an [`SmtProblem`] and either return an
/// [`AletheProof`] (on UNSAT) or an [`SmtSolveError`].
pub trait SmtSolver: Send + Sync {
    /// Attempt to solve the given SMT problem.
    ///
    /// On success (UNSAT), returns the Alethe proof.
    fn solve(&self, problem: &SmtProblem) -> Result<AletheProof, SmtSolveError>;
}

/// Serialize an [`SmtProblem`] to SMT-LIB2 text format.
pub fn write_smtlib2(problem: &SmtProblem, w: &mut impl io::Write) -> io::Result<()> {
    if let Some(logic) = problem.logic() {
        writeln!(w, "(set-logic {logic})")?;
    }

    for sort in problem.sorts() {
        writeln!(w, "(declare-sort {} {})", sort.name, sort.arity)?;
    }

    for fun in problem.funs() {
        write!(w, "(declare-fun {} (", fun.name)?;
        let mut buf = Vec::new();
        prettyprint(&fun.params, &mut buf)?;
        let params_str =
            String::from_utf8(buf).map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;
        write!(w, "{}", params_str)?;
        write!(w, ") ")?;
        let mut buf = Vec::new();
        prettyprint(&[fun.sort.clone()], &mut buf)?;
        let sort_str =
            String::from_utf8(buf).map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;
        writeln!(w, "{})", sort_str)?;
    }

    for assertion in problem.assertions() {
        write!(w, "(assert ")?;
        let mut buf = Vec::new();
        prettyprint(&[assertion.clone()], &mut buf)?;
        let term_str =
            String::from_utf8(buf).map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;
        writeln!(w, "{})", term_str)?;
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use covalence_sexp::SExp;

    use super::*;

    #[test]
    fn write_empty_problem() {
        let problem = SmtProblem::new();
        let mut buf = Vec::new();
        write_smtlib2(&problem, &mut buf).unwrap();
        assert_eq!(String::from_utf8(buf).unwrap(), "");
    }

    #[test]
    fn write_full_problem() {
        let mut problem = SmtProblem::new();
        problem
            .set_logic("QF_UF")
            .declare_sort("U", 0)
            .declare_fun("a", vec![], SExp::symbol("U"))
            .declare_fun("p", vec![SExp::symbol("U")], SExp::symbol("Bool"))
            .assert_term(SExp::List(vec![SExp::symbol("p"), SExp::symbol("a")]));

        let mut buf = Vec::new();
        write_smtlib2(&problem, &mut buf).unwrap();
        let output = String::from_utf8(buf).unwrap();

        assert!(output.contains("(set-logic QF_UF)"));
        assert!(output.contains("(declare-sort U 0)"));
        assert!(output.contains("(declare-fun a ()"));
        assert!(output.contains("(declare-fun p (U)"));
        assert!(output.contains("(assert (p a))"));
    }
}
