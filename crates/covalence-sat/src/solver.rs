use crate::{Cnf, Model};

/// Errors that a [`Solver`] may return.
#[derive(Debug, thiserror::Error)]
pub enum SolveError {
    /// The formula is unsatisfiable.
    #[error("unsatisfiable")]
    Unsat,

    /// The solver hit a resource limit (time, memory, conflicts, …).
    #[error("resource limit: {0}")]
    ResourceLimit(String),

    /// An internal solver error.
    #[error("internal error: {0}")]
    Internal(String),
}

/// A SAT solver backend.
///
/// Implementations receive a [`Cnf`] formula and either return a satisfying
/// [`Model`] or a [`SolveError`]. The trait is object-safe and thread-safe.
pub trait Solver: Send + Sync {
    /// Attempt to solve the given CNF formula.
    ///
    /// On success, returns a total [`Model`] that satisfies the formula.
    /// On failure, returns a [`SolveError`] explaining why.
    fn solve(&self, cnf: &Cnf) -> Result<Model, SolveError>;
}
