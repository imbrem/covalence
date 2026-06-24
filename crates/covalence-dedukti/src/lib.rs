//! # covalence-dedukti
//!
//! A reader for the [Dedukti] `.dk` format: the concrete syntax of the
//! **λΠ-calculus modulo rewriting** (a.k.a. LF + user rewrite rules). This is
//! the **lower, HOL-free crate** — it depends on nothing in the kernel, so the
//! future HOL bridge in `covalence-hol` will depend on *this* crate, not the
//! other way around. The design deliberately mirrors
//! [`covalence-metamath`](../covalence_metamath): a faithful, source-level
//! syntactic image first; semantics (type checking, rewriting, kernel import)
//! layered on top by consumers.
//!
//! ## Why Dedukti
//!
//! Dedukti is a **logical framework**: many proof systems (Coq/Rocq, Matita,
//! HOL, Agda, FoCaLiZe, …) export their proofs into `.dk` files via translators
//! (Logipedia, Krajono, Holide, …). Each such export encodes its source logic
//! as a Dedukti *signature* — a set of declarations and rewrite rules — over
//! which the proof terms type-check. That makes a `.dk` file a uniform,
//! machine-checkable carrier for derivations from very different logics.
//!
//! The long-term goal (see `SKELETONS.md`) is to **internalise** these
//! signatures and derivations into Covalence's HOL kernel and then do
//! *metatheory* on them — e.g. exhibit a translation between a sufficiently
//! strong MLTT encoding and a sufficiently strong set-theory encoding as a
//! single syntactic metatheorem in HOL, the way `covalence-hol::metalogic`
//! already realises Metamath databases as `⊢ Derivable_L ⌜S⌝`.
//!
//! ## What this crate does *today*
//!
//! Lexes and parses a `.dk` source into a [`Signature`] — a faithful AST of:
//!
//! * **terms** ([`Term`]): the sort `Type`, identifier references (unresolved —
//!   variable vs. constant is not distinguished syntactically), application,
//!   λ-abstraction (`x => t`, `x : A => t`), and (dependent) products
//!   (`x : A -> B`, `A -> B`);
//! * **declarations** (`name : ty.`, `injective …`, `defac`/`defacu …`);
//! * **definitions** (`def name [: ty] [:= body].`) and **theorems** (opaque
//!   `thm name [: ty] := body.`);
//! * **rewrite rules** (`{name} [ctx] lhs --> rhs.`);
//! * **commands** (`#NAME #REQUIRE #EVAL #INFER #CHECK/#ASSERT(+NOT) #PRINT
//!   #GDT`, and a catch-all for other directives).
//!
//! It performs **no** scope resolution, type checking, or rewriting — those are
//! deferred (the `.dk` file is assumed to have been checked by Dedukti). The
//! grammar follows Dedukti's own Menhir parser; see [`parse`].
//!
//! ## Module map
//!
//! * [`term`] — the [`Term`] model and [`Ref`].
//! * [`entry`] — top-level entries ([`Entry`], [`Declaration`], [`Definition`],
//!   [`Theorem`], [`RewriteRule`], [`Command`]) and the [`Signature`] container.
//! * [`lex`] — the `.dk` tokeniser.
//! * [`parse`] — the recursive-descent parser ([`parse`](parse::parse)).
//! * [`error`] — the [`DkError`] type.
//! * `hol` (feature `hol`) — the kernel-internalisation bridge: deep-embeds
//!   Dedukti syntax into `covalence-hol` terms and realises a signature's
//!   rewrite relation as a `metalogic::RuleSet`, producing genuine
//!   `⊢ Derivable_Σ ⌜red a b⌝` theorems. This is a first, deliberately co-located
//!   step toward the metatheory goal; it will move into `covalence-hol` (next to
//!   the `metalogic::mm_*` modules) once it matures.
//!
//! [Dedukti]: https://deducteam.github.io/

pub mod entry;
pub mod error;
#[cfg(feature = "hol")]
pub mod hol;
pub mod lex;
pub mod parse;
pub mod term;

pub use entry::{
    Claim, Command, ContextVar, DeclKind, Declaration, Definition, Entry, Param, RewriteRule,
    Signature, Theorem,
};
pub use error::DkError;
pub use parse::parse;
pub use term::{Ref, Symbol, Term};
