//! Re-export shim for the spec handles.
//!
//! `TypeSpec` now lives in [`crate::ty::spec`] and `TermSpec` in
//! [`crate::term::spec`] (each next to the language it defines). They
//! are re-exported here so the `defs/*` catalogue can keep importing
//! `super::spec::{TermSpec, TypeSpec}`, and `crate::defs::{TermSpec,
//! TypeSpec}` keeps resolving for downstream code.

pub use crate::term::TermSpec;
pub use crate::ty::TypeSpec;
