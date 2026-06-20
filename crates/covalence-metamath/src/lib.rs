//! # covalence-metamath
//!
//! A tiny, theory-agnostic [Metamath] proof checker whose expressions are
//! represented as [`covalence_sexp::SExpr`]s.
//!
//! Metamath is a *metalogic*: its sole proof primitive is **metavariable
//! substitution**. A database is a flat list of declarations — constants,
//! typed variables, hypotheses, and assertions (axioms `$a` / theorems `$p`).
//! An assertion is a *schema*: a list of mandatory hypotheses and a conclusion,
//! all of which may contain variables. A proof is a reverse-Polish (RPN)
//! sequence of labels; applying an assertion pops its mandatory hypotheses off
//! a stack, unifies them to compute a variable→expression substitution, checks
//! the **distinct-variable** ($d) side conditions, and pushes the substituted
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
//!
//! Two encodings were available (the task asked us to pick and justify one):
//!
//! * **faithful-flat-sequence** (chosen): each Metamath expression is one
//!   `SExpr::List` of atom symbols, `[typecode, tok, tok, ...]`. Substitution
//!   *splices* the body of the replacement expression into the parent list —
//!   exactly the string-substitution Metamath specifies. This is bit-for-bit
//!   faithful to `set.mm` semantics, sidesteps grammar ambiguity (we never
//!   need to know that `(` `ph` `->` `ps` `)` parses as an implication), and
//!   keeps the substitution engine trivially correct.
//! * **structured-tree** (rejected for the core): encode `( ph -> ps )` as the
//!   recursive tree `(-> ph ps)`. Nicer for metatheory — substitution is a
//!   plain structural tree rewrite with no splicing — but *building* the tree
//!   from a token string requires the grammar, reintroducing the ambiguity
//!   Metamath was designed to avoid, and makes us *not* a Metamath verifier.
//!
//! We use `SExpr` rather than a bare `Vec<Symbol>` because it is the project's
//! canonical expression medium: a faithful flat list today is one
//! `map`/grammar pass away from the structured tree we will want when we prove
//! the **representation-equivalence metatheorem** ("Metamath-PA ≡ our PA")
//! against our locally-nameless syntax. Keeping expressions as `SExpr` from the
//! start means that bridge is a transformation on a shared type, not a reparse.
//!
//! ## Module map
//!
//! * [`expr`] — the `SExpr` expression encoding + variable helpers.
//! * [`subst`] — the substitution engine (the heart of "Metamath rewrite").
//! * [`database`] — constants/variables/hypotheses/assertions + frames + `$d`.
//! * [`verify`] — schematic rule application and the RPN proof checker.
//! * [`parse`] — a parser for the uncompressed `.mm` subset.
//!
//! ## Status & north stars
//!
//! See `SKELETONS.md` (co-located) for deferrals: compressed-proof format,
//! `set.mm` scale, and the `covalence-hol` import tactic + the
//! representation-equivalence metatheorem that makes it sound. This crate's
//! core is deliberately independent of `covalence-hol`.
//!
//! [Metamath]: https://us.metamath.org/

mod database;
mod error;
mod expr;
mod parse;
mod subst;
mod verify;

pub use database::{Assertion, Database, Frame, FloatHyp, Hypothesis, Statement};
pub use error::MmError;
pub use expr::{Expr, TYPECODE_POS, body_of, expr_symbols, typecode_of};
pub use parse::parse;
pub use subst::{Subst, apply_subst};
pub use verify::{verify_all, verify_assertion};
