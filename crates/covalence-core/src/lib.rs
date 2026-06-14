//! Covalence Core: the trusted kernel.
//!
//! An Isabelle/Pure–shaped logical framework (meta-implication
//! `⟹`, meta-universal `⋀`, meta-equality `≡`) plus folded-in HOL
//! primitives: the `bool` / `int` / `nat` / `bytes` types with
//! computational reduction rules, and HOL's connectives /
//! quantifiers / Hilbert choice as first-class term variants. The
//! bona-fide axioms of HOL (extensionality, choice, induction over
//! the primitive datatypes) are core kernel rules — not
//! observer-system postulates.
//!
//! See `docs/design/proposals/stacked-pure-hol/README.md` for the
//! historical design intent. Content hashing, S-expression syntax,
//! FFI bridges, and the untrusted HOL builder shell live downstream
//! in `covalence-hol`.
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
//! - **Binders are anonymous.** Bound variables are pure de Bruijn
//!   indices (printed `#i`); no display label is stored, so structural
//!   equality on `TermKind` is α-equivalence. Rules use `==` freely.
//!
//! ## Trust graph
//!
//! ```text
//!   covalence-core                       (TCB; this crate)
//!       │
//!       ▼
//!   covalence-hol                        (untrusted shell: HOL
//!       │                                 builders, hashing, sexp,
//!       │                                 init lazy statics, WASM)
//!       ▼
//!   covalence-shell, application code    (REPL, server, …)
//! ```
//!
//! ## Scope of this crate
//!
//! - Term and type representation (`term.rs`), including HOL
//!   primitives.
//! - Capture-avoiding substitution, β/η, type-variable substitution
//!   (`subst.rs`).
//! - Closed-form reduction (`builtins.rs`) — decides `Prim` and
//!   `Bool` operations on literal arguments by reflexivity.
//! - LF rules, equality rules, HOL rules, `inst_tfree`, the bona-
//!   fide HOL axioms (`thm.rs`).

mod builtins;
pub mod defs;
pub mod error;
mod hol;
pub mod subst;
pub mod term;
pub mod ty;
pub mod ctx;
pub mod thm;

pub use error::{Error, Result};
pub use term::{
    Def, Hint, IntTag, ObsEq, ObsImp, ObsTrue, Object, Observer, SmallIntLiteral, Term, TermKind,
    Type, TypeKind,
};
pub use ty::{TypeList, TypeSpec};
pub use term::TermSpec;
pub use ctx::Ctx;
pub use thm::{Thm, TypeDef};
