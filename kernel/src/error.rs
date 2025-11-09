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
    #[error("covalence kernel error: theorem belongs to a different kernel")]
    IdMismatch,
    /// Would cause a cycle in the context graph
    #[error("covalence kernel error: adding this parent would cause a cycle")]
    WouldCycle,
    /// Variable not found
    #[error("covalence kernel error: variable not found")]
    VarNotFound,
    /// Context mismatch
    #[error("covalence kernel error: context mismatch")]
    CtxMismatch,
    /// Not implemented
    #[error("covalence kernel error: not implemented")]
    NotImplemented,
}

impl From<IdMismatch> for KernelError {
    fn from(_: IdMismatch) -> Self {
        KernelError::IdMismatch
    }
}
