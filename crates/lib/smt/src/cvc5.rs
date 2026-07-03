use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;

use crate::AletheProof;
use crate::parse::parse_alethe;
use crate::problem::SmtProblem;
use crate::solver::{SmtSolveError, SmtSolver, write_smtlib2};

/// SMT solver backend that shells out to the cvc5 binary.
///
/// Requires cvc5 to be installed and accessible at the configured path.
/// On UNSAT, cvc5 produces an Alethe proof via `--dump-proofs --proof-format=alethe`.
pub struct Cvc5Solver {
    path: PathBuf,
}

impl Cvc5Solver {
    /// Create a solver that uses the cvc5 binary at `path`.
    pub fn new(path: impl Into<PathBuf>) -> Self {
        Self { path: path.into() }
    }

    /// Create a solver that uses `"cvc5"` from `$PATH`.
    pub fn from_path() -> Self {
        Self::new("cvc5")
    }

    /// The path to the cvc5 binary.
    pub fn path(&self) -> &Path {
        &self.path
    }
}

impl SmtSolver for Cvc5Solver {
    fn solve(&self, problem: &SmtProblem) -> Result<AletheProof, SmtSolveError> {
        // Serialize problem + check-sat + exit
        let mut input = Vec::new();
        write_smtlib2(problem, &mut input)
            .map_err(|e| SmtSolveError::Internal(format!("serialization: {e}")))?;
        writeln!(input, "(check-sat)")
            .and_then(|_| writeln!(input, "(exit)"))
            .map_err(|e| SmtSolveError::Internal(format!("serialization: {e}")))?;

        let output = Command::new(&self.path)
            .arg("--dump-proofs")
            .arg("--proof-format=alethe")
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped())
            .spawn()
            .and_then(|mut child| child.stdin.take().unwrap().write_all(&input).map(|_| child))
            .and_then(|child| child.wait_with_output())
            .map_err(|e| SmtSolveError::Internal(format!("cvc5 execution: {e}")))?;

        let stdout = String::from_utf8(output.stdout)
            .map_err(|e| SmtSolveError::Internal(format!("cvc5 stdout: {e}")))?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            return Err(SmtSolveError::Internal(format!(
                "cvc5 exited with {}: {}",
                output.status,
                stderr.trim()
            )));
        }

        // cvc5 output: first line is "unsat", rest is proof wrapped in `(proof\n...\n)`
        let mut lines = stdout.lines();
        match lines.next().map(str::trim) {
            Some("unsat") => {}
            Some("sat") => return Err(SmtSolveError::Sat),
            Some("unknown") => {
                return Err(SmtSolveError::Unknown(lines.collect::<Vec<_>>().join("\n")));
            }
            Some(other) => {
                return Err(SmtSolveError::Internal(format!(
                    "unexpected cvc5 output: {other}"
                )));
            }
            None => {
                return Err(SmtSolveError::Internal("empty cvc5 output".into()));
            }
        }

        // Remaining output is the proof, possibly wrapped in `(proof ...)`
        let rest: String = lines.collect::<Vec<_>>().join("\n");
        let proof_text = unwrap_proof_wrapper(&rest);

        parse_alethe(proof_text).map_err(|e| SmtSolveError::Internal(format!("proof parse: {e}")))
    }
}

/// Strip cvc5's outer proof wrapper.
///
/// cvc5 wraps proofs in either `(proof ...)` or bare `(\n...\n)`.
/// In both cases we strip the outer parens to get the raw commands.
fn unwrap_proof_wrapper(text: &str) -> &str {
    let trimmed = text.trim();
    // `(proof ...)`
    if let Some(inner) = trimmed.strip_prefix("(proof") {
        if let Some(inner) = inner.strip_suffix(')') {
            return inner.trim();
        }
    }
    // Bare `(\n(assume ...)...\n)` — outer parens wrapping command lists
    if let Some(inner) = trimmed.strip_prefix('(') {
        if let Some(inner) = inner.strip_suffix(')') {
            let inner = inner.trim();
            if inner.starts_with('(') {
                return inner;
            }
        }
    }
    trimmed
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unwrap_proof_wrapper_strips() {
        let input = "(proof\n(assume h1 a)\n(step t1 (cl) :rule resolution :premises (h1))\n)";
        let result = unwrap_proof_wrapper(input);
        assert!(result.starts_with("(assume"));
        assert!(result.ends_with(")"));
        assert!(!result.contains("proof"));
    }

    #[test]
    fn unwrap_bare_parens() {
        let input = "(\n(assume h1 a)\n(step t1 (cl) :rule resolution :premises (h1))\n)";
        let result = unwrap_proof_wrapper(input);
        assert!(result.starts_with("(assume"));
        assert!(result.ends_with(")"));
    }

    #[test]
    fn unwrap_proof_wrapper_passthrough() {
        let input = "(assume h1 a)\n(step t1 (cl) :rule resolution :premises (h1))";
        let result = unwrap_proof_wrapper(input);
        assert_eq!(result, input);
    }
}
