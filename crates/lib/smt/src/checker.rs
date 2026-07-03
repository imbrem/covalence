use crate::Decision;
use crate::alethe::{AletheCommand, AletheProof};

/// Abstract Alethe proof checker.
///
/// Implementations process each command and decide whether the proof is valid.
/// Designed to be implementable both as a pure Rust checker and as a wrapper
/// over the WASM kernel engine.
pub trait AletheChecker {
    /// Process one command. Returns `true` if the command is accepted.
    fn command(&mut self, cmd: &AletheCommand) -> bool;

    /// The final decision after processing all commands.
    fn decision(&self) -> Decision;
}

/// Drive a checker through all commands of an Alethe proof.
pub fn check_alethe(checker: &mut impl AletheChecker, proof: &AletheProof) -> Decision {
    for cmd in proof.commands() {
        if !checker.command(cmd) {
            return Decision::Unsat; // rejected
        }
    }
    checker.decision()
}

/// Trivial checker that accepts every command and returns `Unknown`.
///
/// Useful as a baseline for testing that parsing succeeded.
pub struct TrivialChecker;

impl AletheChecker for TrivialChecker {
    fn command(&mut self, _cmd: &AletheCommand) -> bool {
        true
    }

    fn decision(&self) -> Decision {
        Decision::Unknown
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_sexp::SExp;

    #[test]
    fn trivial_checker_accepts_all() {
        let mut checker = TrivialChecker;
        let cmd = AletheCommand::Assume {
            id: "h1".into(),
            term: SExp::symbol("x"),
        };
        assert!(checker.command(&cmd));
        assert_eq!(checker.decision(), Decision::Unknown);
    }

    #[test]
    fn check_alethe_with_trivial() {
        let proof = AletheProof::new([
            AletheCommand::Assume {
                id: "h1".into(),
                term: SExp::symbol("a"),
            },
            AletheCommand::Step {
                id: "t1".into(),
                clause: vec![],
                rule: "resolution".into(),
                premises: vec!["h1".into()],
                args: vec![],
                discharge: vec![],
            },
        ]);
        let decision = check_alethe(&mut TrivialChecker, &proof);
        assert_eq!(decision, Decision::Unknown);
    }
}
