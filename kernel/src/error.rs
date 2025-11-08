use thiserror::Error;

use crate::fact::StoreFailure;
use crate::theorem::IdMismatch;

#[derive(Debug, Error, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum KernelError {
    /// Fact storage failure
    #[error(transparent)]
    StoreFailure(#[from] StoreFailure),
    /// Theorem belongs to a different kernel
    #[error(transparent)]
    IdMismatch(#[from] IdMismatch),
}
