//! Covalence Pure: an Isabelle/Pure–shaped logical framework.
//!
//! See `docs/design/proposals/stacked-pure-hol/README.md` for the
//! design intent. This crate is the **trusted bottom layer** of the
//! stacked kernel design: a tiny LF with meta-implication,
//! meta-universal, and meta-equality plus a single native data
//! primitive (byte strings via `Blob`). Everything else — `bool`,
//! `int`, `nat`, HOL connectives, content hashing, S-expression
//! syntax, FFI bridges — lives in upper-layer crates.
//!
//! ## Conventions (Isabelle/Pure parity)
//!
//! - **Locally-nameless** terms: de Bruijn indices for bound
//!   variables, named free variables and constants carrying their
//!   declared type. Exactly Isabelle/Pure's `term` datatype, minus
//!   schematic `Var` (no unification in the kernel).
//! - **Intrinsic typing** via `Term::type_of`: every Free / Const
//!   carries its instance type; `Abs`/`All` carries the binder type;
//!   `App` / `Imp` / `Eq` are checked structurally. The same
//!   `TypeEnv` is shared across every term in a `Thm`, so Free /
//!   Const consistency is enforced across hyps and concl.
//! - **`BinderHint` is α-transparent.** The `BinderHint` newtype around a binder's
//!   display label has trivial `Eq`/`Hash`/`Ord`, so structural
//!   equality on `TermKind` is α-equivalence. Rules use `==` freely.
//!
//! ## Trust graph
//!
//! ```text
//!   covalence-pure                       (TCB; this crate)
//!       │
//!       ▼
//!   covalence-pure-shell                 (hashing, sexp syntax)
//!       │
//!       ▼
//!   covalence-shell, application code    (REPL, server, …)
//! ```
//!
//! ## Scope of this crate
//!
//! - Term and type representation (`term.rs`).
//! - Capture-avoiding substitution, β/η, type-variable substitution
//!   (`subst.rs`).
//! - The eight LF rules + the six equality rules + `inst_tfree`
//!   (`thm.rs`).
//!
//! ## Not in this crate (yet)
//!
//! - Local authorities and the `observe` rule.
//! - The `define` rule for introducing constants by definitional
//!   equality.
//! - Standard library loader (BLAKE3-keyed blobs).
//! - WASM-oracle adapter.
//! - Anything HOL-shaped (`bool`, `=`, `∧`, `∀`, …) — lives in
//!   `covalence-hol`.

mod builtins;
pub mod error;
pub mod subst;
pub mod term;
pub mod ctx;
pub mod thm;

pub use error::{Error, Result};
pub use term::{
    Arith, BinderHint, Def, Hint, ObsEq, ObsImp, ObsTrue, Object, Observer, Prim, Term, TermKind,
    Type, TypeKind,
};
pub use ctx::Ctx;
pub use thm::{Thm, TypeDef};
