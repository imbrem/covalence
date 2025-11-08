use thiserror::Error;

use crate::fact::StoreFailure;
use crate::store::{AddParentFailure, AddVarFailure};
use crate::theorem::IdMismatch;

#[derive(Debug, Error, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum KernelError {
    /// Failed to store fact
    #[error(transparent)]
    StoreFailure(#[from] StoreFailure),
    /// Failed to add parent to context
    #[error(transparent)]
    AddParentFailure(#[from] AddParentFailure),
    /// Failed to add variable to context
    #[error(transparent)]
    AddVarFailure(#[from] AddVarFailure),
    /// Theorem belongs to a different kernel
    #[error(transparent)]
    IdMismatch(#[from] IdMismatch),
    /// Would cause a cycle in the context graph
    #[error("covalence kernel error: adding this parent would cause a cycle")]
    WouldCycle,
    /// Not implemented
    #[error("covalence kernel error: not implemented")]
    NotImplemented,
}
