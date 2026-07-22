//! Reusable Lisp frontends and proof-producing HOL realizations.
//!
//! The stable waist is [`kernel_api`]: backend-neutral syntax, definitions,
//! environments, partial CEK execution, finite `MayEval` witnesses, and
//! admission capabilities. This crate supplies concrete readers and dialects:
//!
//! - [`frontend`] lowers Scheme, Sector, and ACL2 surface forms to the common
//!   core;
//! - [`carrier`] realizes Lisp data through the shared abstract S-expression
//!   API;
//! - [`relation`] proves `Reduces input value`; its exact `int ⊕ bytes`
//!   backend is the default [`session::Lang::Lisp`];
//! - [`semantics`] retains the older equational Scheme backend for recursive
//!   definitions while partial higher-order proof semantics are developed;
//! - [`acl2`] layers checked worlds, admission, derivations, and theorem
//!   transport over the common Lisp core.
//!
//! Parsing, lowering, search, and execution may propose witnesses. Only the
//! HOL kernel can produce theorem authority, and rendered proof-mode values
//! are read from checked theorem conclusions.

#![forbid(unsafe_code)]

pub mod forsp;
pub mod frontend;
pub mod reader;
pub mod scheme_effect;

#[cfg(feature = "hol")]
pub mod hol;

#[cfg(feature = "hol")]
pub mod carrier;

#[cfg(feature = "hol")]
pub mod defs;

#[cfg(feature = "hol")]
pub mod semantics;

#[cfg(feature = "hol")]
pub mod int_backend;

#[cfg(feature = "hol")]
pub mod relation;

#[cfg(feature = "hol")]
pub mod session;

#[cfg(feature = "hol")]
pub mod acl2;

#[cfg(feature = "hol")]
pub mod acl2_api;

#[cfg(feature = "hol")]
pub mod book;

#[cfg(feature = "hol")]
pub mod progress;
pub mod quasiquote;

#[cfg(feature = "hol")]
pub mod world;

use covalence_sexp::SExpr;
use covalence_sexpr_api::SExprSyntax;

/// Stable backend-neutral Lisp capabilities used by the concrete dialects in
/// this crate.
pub use covalence_kernel_lisp as kernel_api;

/// Next-generation Lisp syntax capability, stacked directly on the abstract
/// S-expression constructors.
///
/// Evaluation and proof production are intentionally separate capabilities:
/// a parser/lowerer needs only this trait. Existing [`Lisp`] implementations
/// remain source-compatible while adapters migrate them to this narrower
/// vocabulary.
pub trait LispDatumSyntax: SExprSyntax {
    fn symbol_payload(&self, name: &str) -> Result<Self::Payload, Self::Error>;

    fn number_payload(&self, text: &str) -> Option<Result<Self::Payload, Self::Error>>;

    fn string_payload(&self, format: &str, bytes: &[u8]) -> Result<Self::Payload, Self::Error>;

    fn resolve_payload(&self, atom: &covalence_sexp::Atom) -> Result<Self::Payload, Self::Error> {
        match atom {
            covalence_sexp::Atom::Symbol(text) => match self.number_payload(text) {
                Some(result) => result,
                None => self.symbol_payload(text),
            },
            covalence_sexp::Atom::Str { format, bytes } => self.string_payload(format, bytes),
        }
    }

    fn lower_syntax(&self, sexpr: &SExpr) -> Result<Self::Value, Self::Error> {
        reader::lower_with(self, sexpr, &|atom| self.resolve_payload(atom))
    }
}
