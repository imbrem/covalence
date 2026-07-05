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
//! (`and_*`/`or_*`/`not_*`); four non-computational primitives
//! ([`Thm::nat_induct`], [`Thm::false_elim`], [`Thm::unit_eq`],
//! [`Thm::lem`] — the classicality axiom); the
//! conservative-extension primitives ([`Thm::define`],
//! [`Thm::new_type_definition`]); and the accelerated reduction rules
//! ([`Thm::reduce_prim`], [`Thm::unfold_term_spec`]).
//!
//! Content hashing, S-expression syntax, FFI bridges, and the untrusted
//! HOL builder shell live downstream in `covalence-hol`. The canonical
//! reference is `notes/vibes/kernel-design.md`.
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
//!   (`defs/`, semi-trusted — see `notes/vibes/kernel-design.md` §6).
//! - The toHOL denotation ops (`tohol.rs`) and the audited core-on-pure
//!   seam surface (`seam.rs`). The untrusted reduction/reification drivers
//!   live downstream in `covalence-hol-eval`.

mod builtins;
pub mod ctx;
pub mod defs;
pub mod error;
mod hol;
pub mod seam;
pub mod subst;
pub mod term;
pub mod thm;
mod tohol;
pub mod ty;

pub use ctx::Ctx;
pub use error::{Error, Result};
pub use term::TermSpec;
pub use term::{
    Checked, Def, FreshId, FreshLeaf, FreshTyLeaf, HashCons, IntTag, SmallIntLiteral, Term,
    TermCons, TermKind, TrustedCons, TyError, Type, TypeKind, Var,
};
pub use thm::{Thm, TypeDef};
pub use ty::{TrustedTypeCons, TypeCons, TypeHashCons, TypeList, TypeSpec};
