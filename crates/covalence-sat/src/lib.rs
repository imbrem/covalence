pub use covalence_types::Decision;

#[cfg(feature = "wasm")]
pub mod component;
#[cfg(feature = "drat")]
mod drat;
mod formula;
#[cfg(feature = "lrat")]
mod lrat;
mod model;
pub mod parse;
mod solver;

#[cfg(feature = "drat")]
pub use drat::{
    DratChecker, DratProof, DratStep, NaiveDratChecker, WatchedDratChecker, check_proof,
};
pub use formula::{Clause, Cnf, Lit, Var};
#[cfg(feature = "lrat")]
pub use lrat::{LratChecker, LratProof, LratStep, NaiveLratChecker, check_lrat_proof};
pub use model::Model;
pub use parse::ParseError;
pub use solver::{SolveError, Solver};
