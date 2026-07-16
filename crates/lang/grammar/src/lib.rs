//! Datatypes for classes of grammar used by Covalence's untrusted kernel
//! frontend when reasoning about binary formats.
//!
//! Grammar classes shipped so far:
//!
//! - [`regex`] — *proper* (capture-free) regular expressions over a
//!   generic alphabet `A`, plus a parser for the usual surface syntax
//!   into [`Regex<char>`].
//! - [`cfg`] — context-free grammars whose terminal segments are
//!   [`Regex<A>`] values, the neutral IR the SpecTec lowering targets and
//!   the kernel's CFG stratum consumes.
//! - [`numeral`] — the compositional literal grammars: a tower of families
//!   (digit classes -> `Numeral<BASE>` -> `nat_any` -> `int_any` -> `frac` ->
//!   `decimal`/`sci`) built from the regex combinators, each producing a typed
//!   `covalence-types` value and carrying a deparser (transpose) for round-trip.
//!
//! Subsequent classes (attribute grammars, PEGs, …) are planned but
//! not in scope here. The crate is intentionally minimal and dependency-light
//! so the entire surface compiles to `wasm32-wasip1-threads` and can later
//! be lifted into kernel-verified computations.
//!
//! Like other surface-language crates that may be lifted into the kernel,
//! `covalence-grammar` forbids `unsafe`.

#![forbid(unsafe_code)]

pub mod cfg;
pub mod regex;

pub use cfg::{Cfg, CfgError, NtDef, NtId, Prod, Seg};
pub use regex::{Class, ClassRange, ParseError, Regex, RegexLetter, parse_regex, parse_regex_u8};

pub mod numeral;

pub use numeral::{
    IntLit, NatBase, NatLit, Numeral, accept_digit, dec_digit_class, decimal, decimal_grammar,
    deparse_decimal, deparse_frac, deparse_int, deparse_nat, deparse_nat_in, digit_class, frac,
    frac_grammar, hex_digit_class, int_any, int_any_grammar, nat_any, nat_any_grammar,
    oct_digit_class, sci, sci_grammar,
};
