//! # covalence-metamath
//!
//! The **`.mm` format / IO frontend** for the Metamath substitution engine.
//!
//! The engine itself — the `SExpr` expression model, the substitution core, the
//! frame/database model, and the RPN proof checker — lives in
//! [`covalence_hol::metamath`], because a Metamath database *is* the substrate
//! for defining a logic (`docs/theories-models-and-logics.md` §5.6,
//! `docs/surface-compiler.md` §3.0.5). This crate is the messy reader layer on
//! top of it: tokenising `.mm` source, scoping `${ ... $}`, comments
//! `$( ... $)`, and (as north stars) compressed-proof decoding, `$[ $]` file
//! inclusion, and `set.mm` ingestion. Keeping those concerns here keeps the
//! engine in `covalence-hol` clean.
//!
//! The engine's public types are re-exported below so existing callers
//! (`covalence_metamath::{Database, parse, verify_all, ...}`) keep working.
//!
//! ## Status & north stars
//!
//! See `SKELETONS.md` (co-located) for deferrals: the compressed-proof format,
//! `set.mm` scale/performance, and `$[ ... $]` file inclusion. The engine-side
//! deferrals (structured-tree encoding, the `#logic` correspondence layer) live
//! in `covalence-hol/src/metamath/SKELETONS.md`.
//!
//! [Metamath]: https://us.metamath.org/

mod parse;

pub use parse::parse;

// Re-export the engine surface from `covalence-hol` so this crate remains the
// stable entry point for Metamath consumers.
pub use covalence_hol::metamath::{
    Assertion, Database, Expr, FloatHyp, Frame, Hypothesis, MmError, Statement, Subst,
    TYPECODE_POS, apply_subst, body_of, expr_symbols, typecode_of, verify_all, verify_assertion,
};
