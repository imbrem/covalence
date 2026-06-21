//! # covalence-metamath
//!
//! A tiny, theory-agnostic [Metamath] proof checker **and** its `.mm` format
//! reader. This is the **lower, HOL-free crate**: the engine here depends only
//! on [`covalence_sexp`], so `covalence-hol` depends on *this* crate (a
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
//! ## Why `SExpr`? (the encoding decision)
//!
//! Real Metamath operates on flat *symbol strings* together with a separate
//! grammar (e.g. `set.mm`'s `wff`/`class`/`setvar` productions) that gives
//! those strings structure. The grammar is what makes parsing ambiguous and is
//! deliberately **not** part of the trusted verifier — a Metamath verifier
//! never parses the math, it only manipulates token sequences. This crate
//! mirrors that: an expression is an [`covalence_sexp::SExpr`] **list whose
//! head is the typecode and whose tail is the flat symbol sequence**, e.g.
//! `( wff ( ph -> ps ) )` is the four-deep-flat list
//! `(wff "(" ph "->" ps ")")` — *not* a nested tree `(wff (-> ph ps))`.
//! Substitution *splices* the body of the replacement into the parent list,
//! exactly the string-substitution Metamath specifies — bit-for-bit faithful to
//! `set.mm` semantics, and trivially correct. A grammar pass turning flat lists
//! into structured trees is deferred to the (untrusted) bridge layer above.
//!
//! ## Module map
//!
//! * [`expr`] — the `SExpr` expression encoding + variable helpers.
//! * [`subst`] — the substitution engine (the heart of "Metamath rewrite").
//! * [`database`] — constants/variables/hypotheses/assertions + frames + `$d`.
//! * [`verify`] — schematic rule application and the RPN proof checker.
//! * [`error`] — the `MmError` type shared across the engine.
//! * [`parse`] — the `.mm` source reader (tokenise, scope `${ ... $}`, comments
//!   `$( ... $)`) constructing a [`Database`].
//!
//! ## Status & north stars
//!
//! See `SKELETONS.md` (co-located) for deferrals: the compressed-proof format,
//! `$[ ... $]` file inclusion, `set.mm` scale/performance, the structured-tree
//! encoding, and the consumer-side `#logic` / `Derivable_L` correspondence layer
//! (in `covalence-hol`).
//!
//! [Metamath]: https://us.metamath.org/

pub mod database;
pub mod error;
pub mod expr;
pub mod parse;
pub mod subst;
pub mod verify;

pub use database::{Assertion, Database, FloatHyp, Frame, Hypothesis, Statement};
pub use error::MmError;
pub use expr::{Expr, TYPECODE_POS, body_of, expr_symbols, typecode_of};
pub use parse::parse;
pub use subst::{Subst, apply_subst};
pub use verify::{verify_all, verify_assertion};
