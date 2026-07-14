//! OpenTheory article interpreter for HOL Light-style kernels.
//!
//! This crate provides an untrusted OpenTheory article stack machine that
//! programs against the abstract `HolLightKernel` trait from `covalence-hol`.

pub mod error;
#[cfg(feature = "fetch")]
pub mod fetch;
pub mod interp;
pub mod machine;
pub mod name;
#[cfg(feature = "native")]
pub mod native;
pub mod object;
pub mod reader;
pub mod resolve;
pub mod theory;

pub use error::OtError;
#[cfg(feature = "fetch")]
pub use fetch::{CachingUrlResolver, OPENTHEORY_REPO, UrlResolver};
pub use interp::ArticleInterp;
pub use machine::{ArticleMachine, ArticleResult};
pub use name::{NameTable, OtName};
#[cfg(feature = "native")]
pub use native::NativeOt;
pub use object::OtObject;
pub use reader::read_article;
pub use resolve::{
    FileResolver, Theory, TheoryCache, TheoryResolver, check_theory, register_select,
};
pub use theory::{TheoryBlock, TheoryFile, parse_theory_file};
