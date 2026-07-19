//! Grammar front ends that lower into HOL: the regex → byte-predicate compiler
//! and matching tactic, and the SpecTec grammar layer built over it.
//!
//! Distinct from the catalogue's [`crate::init::regex`] theory — these are the
//! compilers/tactics, not the type definitions.

pub mod cfg;
pub mod lexer;
pub mod regex;
pub mod spectec;
