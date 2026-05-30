pub use covalence_types::Decision;

mod alethe;
mod checker;
mod error;
pub mod parse;
pub mod problem;
pub mod solver;

#[cfg(feature = "cvc5")]
pub mod cvc5;

pub use alethe::{AletheCommand, AletheProof};
pub use checker::{AletheChecker, TrivialChecker, check_alethe};
pub use error::AletheError;
pub use parse::{parse_alethe, parse_smtlib2};
pub use problem::{FunDecl, SmtProblem, SortDecl};
pub use solver::{SmtSolveError, SmtSolver, write_smtlib2};

#[cfg(feature = "cvc5")]
pub use cvc5::Cvc5Solver;
