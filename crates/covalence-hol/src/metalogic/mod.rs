//! # Metalogic: databases as first-class HOL data, and the relations between them
//!
//! This module realises the first cut of the **`Database` / `Derivable_L` /
//! relation-lattice** layer called for in
//! `docs/theories-models-and-logics.md` §5.6 (the "HOL type for databases, and
//! the relation lattice" paragraph) and tracked as a north star in
//! [`crate::metamath`]'s `SKELETONS.md`. The point is to do **metatheory inside
//! HOL**: to state and *prove* facts that relate one logic to another, the
//! logics themselves — at least their axiom/rule sets — must be **HOL values**
//! that HOL can quantify over.
//!
//! ## The `Database` encoding (the design choice)
//!
//! A database is reified as a **HOL predicate over encoded formulas**:
//!
//! ```text
//!   Database  :=  Φ → bool
//! ```
//!
//! where `Φ` is the reified propositional-formula carrier from
//! [`crate::init::prop`] (genuine syntactic data — `enc(A ⟹ B)` and
//! `enc(A ∧ B)` are distinct HOL terms). `db : Φ → bool` is the database's
//! **axiom set**: `db ⌜A⌝` says "`A` is an axiom of `db`". This is the
//! lightest encoding that makes the relations expressible: because a database
//! is an ordinary HOL term, HOL can `∀`-quantify over databases, compare two
//! databases ([`extends`]), and state derivability *as a function of the
//! database value* ([`derivable`]).
//!
//! We chose the **set-of-axioms-as-predicate** form over a reified *list* of
//! axiom-schemas because (a) the relations we want — extension `⊑` and
//! interpretation `⟹_σ` — are most naturally inclusions / image conditions on
//! the axiom *set*, and a predicate is exactly a set; (b) it sidesteps any
//! commitment to a particular enumeration order or finiteness, so an
//! infinite/schematic axiom set (the usual case — modus-ponens-style schemas)
//! is representable without machinery; and (c) the **structural inference
//! rules** (here modus ponens) are *shared* by every database, so they live in
//! the fixed [`derivable`] frame, not in the per-database value. A database is
//! then exactly "which formulas you may cite as axioms", which is precisely
//! what the relations range over.
//!
//! ## `Derivable_DB` connects to the impredicative engine
//!
//! Derivability is the same **impredicative Church predicate** as
//! [`crate::init::prop`]'s `Derivable_Prop` and [`crate::peano::pa`]'s
//! `Derivable_PA` — `Derivable_L A := ∀d. Closed_L d ⟹ d A` — but with the
//! axiom clauses replaced by a *single* clause that reads the axioms **off the
//! database value**:
//!
//! ```text
//!   Closed_DB db d  :=  (∀A B. d A ∧ d ⌜A ⟹ B⌝ ⟹ d B)   -- modus ponens (shared)
//!                     ∧ (∀ax. db ax ⟹ d ax)              -- db's axioms
//!   Derivable_DB db A  :=  ∀d. Closed_DB db d ⟹ d A
//! ```
//!
//! So a [`crate::init::prop`]-style fixed-axiom logic is the special case where
//! `db` is the predicate "is an instance of one of the ten Hilbert schemas",
//! and the generic [`crate::peano::pa`]-style `Derivable_L A := ∀d. Closed_L d ⟹ d A`
//! engine is recovered by `Closed_L := Closed_DB db`. The new content here is
//! that `db` is a *parameter*, ranged over by HOL — which is what lets us state
//! and prove the **relations between databases**.
//!
//! ## The relations (metatheory)
//!
//! Two foundational relations on the database type, each with its theorem:
//!
//! 1. **Extension** [`extends`]: `A ⊑ B := ∀ax. A ax ⟹ B ax` (B's axioms ⊇
//!    A's). Its theorem is **monotonicity** [`monotone`]:
//!    `⊢ A ⊑ B ⟹ Derivable_DB A S ⟹ Derivable_DB B S` — anything derivable in
//!    a database stays derivable in any extension. Proved as an honest HOL
//!    theorem (no postulates), demonstrated transporting a concrete fact across
//!    a concrete one-axiom extension ([`tests`]).
//!
//! 2. **Interpretation** under a translation `σ : Φ → Φ` ([`relations::interp`]:
//!    `A ⟹_σ B := ∀ax. A ax ⟹ Derivable_DB B (σ ax)`) — the `S`-rewrite of §5.6
//!    as a relation on the database type. Its theorem is **transport**
//!    [`relations::transport`]:
//!    `⊢ σ_hom σ ⟹ Interp A B σ ⟹ Derivable_DB A S ⟹ Derivable_DB B (σ S)`,
//!    for any `⟹`-homomorphic `σ`. Proved by rule induction (via the reusable
//!    [`relations::derivable_db_mp`] MP-closure of `Derivable_DB`), and
//!    demonstrated on the **identity translation**, which recovers monotonicity
//!    as interpretation under the identity renaming. A non-trivial structural
//!    `σ` is the next step (see [`SKELETONS.md`](./SKELETONS.md)).
//!
//! ## Relation to the Metamath substrate
//!
//! The ideal `Derivable_L A := ∃P. ValidProof(P, A, db)` grounds derivability
//! on the decidable [`crate::metamath`] verifier. Reifying that verifier *as a
//! HOL function* is heavy; this cut grounds `Derivable_DB` on the impredicative
//! engine instead (the same one [`crate::init::prop`] / [`crate::peano::pa`]
//! already prove sound), and defers the `∃ValidProof ⟺ impredicative` bridge.
//! The essential requirement — **the database is a HOL value the relations
//! range over** — is met. See [`SKELETONS.md`](./SKELETONS.md).

pub mod database;
pub mod relations;

pub use database::{derivable, derivable_db, extends, monotone};
pub use relations::{derivable_db_mp, interp, sigma_hom, transport};
