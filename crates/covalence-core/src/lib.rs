//! Covalence Core: the trusted kernel.
//!
//! An LCF-style **HOL Light** kernel in safe Rust. The only logical
//! primitives are `=` ([`term::TermKind::Eq`]) and `ε`
//! ([`term::TermKind::Select`]); `T`/`F` are `bool` literals and every
//! connective / quantifier (`∧ ∨ ¬ ⟹ ⟺ ∀ ∃`) is an ordinary defined
//! constant in `defs::logic`. The single opaque type is [`Thm`]; its
//! only constructors are the inference-rule methods, so soundness reduces
//! to those rules plus the kernel's commitment to its primitive types'
//! denotations (`nat` = the standard naturals, `bool` = two values, …).
//!
//! On top of HOL Light's ten primitive rules the kernel adds, with a
//! `Soundness:` docstring justifying each: the well-known derived rules
//! (`sym`, `cong_app`/`cong_abs`, `imp_intro`/`imp_elim`,
//! `all_intro`/`all_elim`, `eta_conv`) and connective rules
//! (`and_*`/`or_*`/`not_*`); three non-computational primitives
//! ([`Thm::nat_induct`], [`Thm::false_elim`], [`Thm::unit_eq`]); the
//! conservative-extension primitives ([`Thm::define`],
//! [`Thm::new_type_definition`]); the accelerated reduction rules
//! ([`Thm::reduce_prim`], [`Thm::unfold_term_spec`]); and the observer
//! rules (`obs_eq`/`obs_true`/`obs_imp`) sound under a parametric ε-model.
//!
//! Content hashing, S-expression syntax, FFI bridges, and the untrusted
//! HOL builder shell live downstream in `covalence-hol`. The canonical
//! reference is `docs/kernel-design.md`.
//!
//! ## Conventions
//!
//! - **Locally-nameless** terms: de Bruijn indices for bound variables,
//!   named free variables and constants carrying their declared type.
//! - **Intrinsic typing** via [`Term::type_of`]: every Free / Const
//!   carries its instance type and `Abs` carries the binder type; `App`
//!   and `Eq` are checked structurally. The same `TypeEnv` is shared
//!   across every term in a `Thm`, so Free consistency is enforced across
//!   hyps and conclusion.
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
//! - Term and type representation, including the `=`/`ε` primitives
//!   (`term/`, `ty/`).
//! - Capture-avoiding substitution, β/η, type-variable substitution
//!   (`subst.rs`).
//! - Closed-form reduction (`builtins.rs`) — decides catalogue ops and
//!   HOL `=` on literal arguments by reflexivity.
//! - The hypothesis context (`ctx.rs`) and HOL term builders (`hol.rs`).
//! - The inference rules (`thm/`) and the derived-type/term catalogue
//!   (`defs/`, semi-trusted — see `docs/kernel-design.md` §6).

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
