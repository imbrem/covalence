//! # covalence-metamath
//!
//! A tiny, theory-agnostic [Metamath] proof checker **and** its `.mm` format
//! reader. This is the **lower, HOL-free crate**: the engine here depends only
//! on [`covalence_sexp`], so `covalence-init` depends on *this* crate (a
//! HOL-backed consumer of a Metamath [`Database`]) — not the other way around.
//!
//! Metamath is a *metalogic*: its sole proof primitive is **metavariable
//! substitution**. A database is a flat list of declarations — constants,
//! typed variables, hypotheses, and assertions (axioms `$a` / theorems `$p`).
//! An assertion is a *schema*: a list of mandatory hypotheses and a conclusion,
//! all of which may contain variables. A proof is a reverse-Polish (RPN)
//! sequence of labels; applying an assertion pops its mandatory hypotheses off
//! a stack, unifies them to compute a variable→expression substitution, checks
//! the **distinct-variable** (`$d`) side conditions, and pushes the substituted
//! conclusion. The verifier core is famously small — this crate keeps it that
//! way (see [`verify`]).
//!
//! ## Primitive expressions (the encoding decision)
//!
//! Real Metamath operates on flat *symbol strings* together with a separate
//! grammar (e.g. `set.mm`'s `wff`/`class`/`setvar` productions) that gives
//! those strings structure. The grammar is what makes parsing ambiguous and is
//! deliberately **not** part of the trusted verifier — a Metamath verifier
//! never parses the math, it only manipulates token sequences. This crate
//! mirrors that with a **dedicated primitive type** [`Expr`] = a typecode
//! [`Symbol`] plus a flat `body: Vec<Symbol>`, e.g. `( wff ( ph -> ps ) )` is
//! `typecode = "wff"`, `body = ["(", "ph", "->", "ps", ")"]` — *not* a nested
//! tree `(wff (-> ph ps))`. Substitution *splices* the body of the replacement
//! in place, exactly the string-substitution Metamath specifies — bit-for-bit
//! faithful to `set.mm` semantics, and trivially correct. A grammar pass turning
//! flat sequences into structured trees is deferred to the (untrusted) bridge
//! layer above.
//!
//! [`covalence_sexp`] remains a dependency, but only at the **boundary**:
//! [`Expr::to_sexpr`] / [`Expr::from_sexpr`] convert to and from the flat
//! `[typecode, sym, sym, ...]` `SExpr` list. The engine itself never routes
//! through `SExpr`.
//!
//! ## Module map
//!
//! * [`expr`] — the primitive [`Expr`] type, [`Symbol`], `SExpr` conversion.
//! * [`subst`] — the substitution engine (the heart of "Metamath rewrite").
//! * [`database`] — constants/variables/hypotheses/assertions + frames + `$d`,
//!   the [`Proof`] encodings, the [`DatabaseSink`] builder trait.
//! * [`verify`] — schematic rule application + the RPN proof checker (both
//!   normal and compressed proofs); a HOL-free "sanity-check" backend behind the
//!   default-on `checker` feature.
//! * [`error`] — the `MmError` type shared across the engine.
//! * [`mod@parse`] — the `.mm` source reader (tokenise, scope `${ ... $}`, comments
//!   `$( ... $)`, `$[ include $]` via [`SourceResolver`]) driving a
//!   [`DatabaseSink`].
//!
//! ## Status & north stars
//!
//! See `SKELETONS.md` (co-located) for deferrals: symbol interning for `set.mm`
//! scale/performance, the structured-tree encoding, the canonical `.mm`
//! serializer, the HOL-backed [`DatabaseSink`], and the consumer-side `#logic` /
//! `Derivable_L` correspondence layer (in `covalence-init`).
//!
//! [Metamath]: https://us.metamath.org/

pub mod axioms;
pub mod database;
pub mod emit;
pub mod error;
pub mod expr;
pub mod interpret;
pub mod parse;
pub mod subst;
pub mod typesetting;
#[cfg(feature = "checker")]
pub mod verify;

pub use axioms::{
    AxiomSet, Implication, MetaError, allow_definitions, axiom_closure, check_implication,
    derivable_from, provable_closure, same_statement, setmm_witness,
};
pub use database::{
    Assertion, Database, DatabaseSink, FloatHyp, Frame, Hypothesis, Proof, Statement, SymbolKind,
};
pub use emit::to_mm_string;
pub use error::MmError;
pub use expr::{Expr, Symbol, TYPECODE_POS, body_of, expr_symbols, typecode_of};
pub use interpret::{
    Coverage, InterpError, InterpretationCert, Renaming, TransportedTheorem, check_interpretation,
    interpretation_coverage, matching_witnesses_mod_renaming, same_statement_mod_renaming,
};
pub use parse::{
    FileResolver, MemoryResolver, SourceResolver, parse, parse_into, parse_into_with_resolver,
    parse_with_resolver,
};
pub use subst::{Subst, apply_subst};
pub use typesetting::{Typedef, parse_typesetting};
#[cfg(feature = "checker")]
pub use verify::{ProofStep, proof_steps, verify_all, verify_assertion};
