use thiserror::Error;

use crate::formula::StoreFailure;
use crate::store::{AddParentFailure, AddVarFailure};
use crate::theorem::{IdMismatch, rw::EqMismatch};

#[derive(Debug, Error, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum KernelError {
    /// Failed to store fact
    #[error("covalence store error: failed to store fact")]
    StoreFailure,
    /// Failed to add parent to context
    #[error("covalence store error: failed to add parent to context")]
    AddParentFailure,
    /// Failed to add variable to context
    #[error("covalence store error: failed to add variable to context")]
    AddVarFailure,
    /// Theorem belongs to a different kernel
    #[error("covalence kernel error: theorem belongs to a different kernel")]
    IdMismatch,
    /// Equality mismatch
    #[error("covalence kernel error: equality mismatch")]
    EqMismatch,
    /// Shape mismatch
    #[error("covalence kernel error: shape mismatch")]
    ShapeMismatch,
    /// Defeq required
    #[error("covalence kernel error: require definitional equality")]
    RequireDefEq,
    /// Would cause a cycle in the context graph
    #[error("covalence kernel error: adding this parent would cause a cycle")]
    WouldCycle,
    /// Variable not found
    #[error("covalence kernel error: variable not found")]
    VarNotFound,
    /// Context mismatch
    #[error("covalence kernel error: context mismatch")]
    CtxMismatch,
    /// Expected a single-variable context
    #[error("covalence kernel error: expected a single-variable context")]
    SingleVarCtxExpected,
    /// Not implemented
    #[error("covalence kernel error: not implemented")]
    NotImplemented,
}

impl From<StoreFailure> for KernelError {
    fn from(_: StoreFailure) -> Self {
        KernelError::StoreFailure
    }
}

impl From<AddParentFailure> for KernelError {
    fn from(_: AddParentFailure) -> Self {
        KernelError::AddParentFailure
    }
}

impl From<AddVarFailure> for KernelError {
    fn from(_: AddVarFailure) -> Self {
        KernelError::AddVarFailure
    }
}

impl From<IdMismatch> for KernelError {
    fn from(_: IdMismatch) -> Self {
        KernelError::IdMismatch
    }
}

impl From<EqMismatch> for KernelError {
    fn from(_: EqMismatch) -> Self {
        KernelError::EqMismatch
    }
}
