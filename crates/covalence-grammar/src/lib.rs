//! Datatypes for classes of grammar used by Covalence's untrusted kernel
//! frontend when reasoning about binary formats.
//!
//! v0 ships a single grammar class:
//!
//! - [`regex`] — *proper* (capture-free) regular expressions over a
//!   generic alphabet `A`, plus a parser for the usual surface syntax
//!   into [`Regex<char>`].
//!
//! Subsequent classes (CFGs, attribute grammars, PEGs, …) are planned but
//! not in scope here. The crate is intentionally minimal and dependency-light
//! so the entire surface compiles to `wasm32-wasip1-threads` and can later
//! be lifted into kernel-verified computations.
//!
//! Like other surface-language crates that may be lifted into the kernel,
//! `covalence-grammar` forbids `unsafe`.

#![forbid(unsafe_code)]

pub mod regex;

pub use regex::{Class, ClassRange, ParseError, Regex, RegexLetter, parse_regex, parse_regex_u8};
