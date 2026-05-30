//! OpenTheory article interpreter for HOL Light-style kernels.
//!
//! This crate provides an untrusted OpenTheory article stack machine that
//! programs against the abstract `HolLightKernel` trait from `covalence-hol`.

pub mod error;
pub mod interp;
pub mod machine;
pub mod name;
pub mod object;
pub mod reader;
pub mod resolve;
pub mod theory;

pub use error::OtError;
pub use interp::ArticleInterp;
pub use machine::{ArticleMachine, ArticleResult};
pub use name::{NameTable, OtName};
pub use object::OtObject;
pub use reader::read_article;
pub use resolve::{
    FileResolver, Theory, TheoryCache, TheoryResolver, check_theory, register_select,
};
pub use theory::{TheoryFile, parse_theory_file};
