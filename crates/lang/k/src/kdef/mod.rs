//! **The `.k` source frontend** — parse the *grammar* (the `syntax`
//! declarations) of a K definition written in K's own surface language, as
//! opposed to [`crate::ast`]/[`crate::parse`] which consume **KORE** (kompile's
//! elaborated output).
//!
//! This is the "custom frontend for a K fragment" path: rather than depend on
//! kompile, we read a `.k` file's grammar directly. The target is the basic K
//! tutorial's simple languages (LAMBDA, IMP) — enough to lift a real
//! programming-language grammar into Covalence.
//!
//! Pipeline:
//!
//! ```text
//! .k source ──(parse)──▶ KDefinition ──(sexpr)──▶ canonical S-expr IR
//!                            │
//!                            └──(cfg)──▶ covalence_grammar::Cfg ──▶ kernel CFG stratum
//! ```
//!
//! - [`ast`] — plain-data grammar AST ([`ast::KDefinition`] / [`ast::KModule`] /
//!   [`ast::SyntaxDecl`] / [`ast::Production`] / [`ast::ProdItem`]).
//! - [`parse`] — a [`winnow`](covalence_parse::winnow)-based parser
//!   ([`parse::parse_definition`]) for the grammar fragment; skips
//!   `rule`/`configuration`/… sentences.
//! - [`sexpr`] — canonical S-expression rendering of the grammar AST.
//! - [`cfg`] — lower the grammar to a [`covalence_grammar::Cfg`] (terminals →
//!   char-regexes, non-terminals → CFG references, `List{}` desugared, priority
//!   /brackets flattened) — the neutral IR the kernel CFG stratum consumes.
//!
//! Untrusted, kernel-free, `#![forbid(unsafe_code)]` — like the rest of
//! `covalence-k`. Design + roadmap: `notes/design/k-frontend.md`; deferred work:
//! `SKELETONS.md`.

pub mod ast;
pub mod cfg;
pub mod lower;
pub mod parse;
pub mod sexpr;
