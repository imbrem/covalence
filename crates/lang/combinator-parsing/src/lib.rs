//! A general parser-combinator algebra with three interpretations that stay distinct.
//!
//! Parsing is presented here along two independent axes.
//!
//! The **capability axis** distinguishes *total*, *partial*, and *relational*
//! interpretation. A total parser always produces exactly one interpretation; a
//! partial parser may decline with a diagnostic; a relational parser enumerates
//! every interpretation it found. These are three different notions and they are
//! kept apart by unrelated traits. In particular, ordered choice (left-biased,
//! committing) and relational union (every alternative retained) are *different
//! operators with different law tables*, not two spellings of one operator.
//!
//! The **encoding axis** carries two coexisting presentations of that algebra: a
//! first-order syntax encoding whose programs are data, and a host-combinator
//! encoding whose programs are Rust values containing closures. They are related
//! by a compilation from the first to the second with no inverse.
//!
//! The relationships along the capability axis are **refinements, never
//! equalities**. Widening a total parser to a partial one is information
//! preserving; widening a partial parser to a relational one discards the
//! diagnostic and has no retraction. Ordered choice agrees with taking the first
//! union result only on the image of that widening, and diverges as soon as a
//! `bind` sits above the choice. Consequently this crate exposes no `take_first`,
//! no narrowing adapter, and no `normalize` / `to_relational` operation on
//! programs.
//!
//! Evaluation is untrusted host computation. Witnesses are data and grant no
//! theorem authority. `Err` means the *evaluator* failed; ordinary non-match is
//! never an error. Budgets are supplied by the caller at the evaluation boundary
//! and are never stored per combinator node, and value equality is always a
//! caller-supplied agreement rather than an assumed host `PartialEq`.
//!
//! # Non-goals
//!
//! 1. **No universal quantification over sources.** Every check in this crate is
//!    falsification over a finite corpus under a finite budget. Passing is
//!    *failure to falsify*; no host result confers theorem authority.
//! 2. **No completeness claim for any relational enumerator.** An empty vector
//!    proves no negative fact, so "this value is not in the union, therefore
//!    ordered choice declines" is not merely untested — it is not statable as a
//!    host test.
//! 3. **No parser equality.** Extensional equality is undecidable; only
//!    observations are compared.
//! 4. **No content addressing of programs.** Syntax programs are data, but rule
//!    references and bind continuations resolve through an environment, so
//!    hashing a program hashes the skeleton and not the parser. The environment's
//!    identity must be part of any content address, and that is the caller's
//!    responsibility.
//! 5. **No static well-formedness pass.** The value universe is single-sorted, so
//!    an ill-typed map or application surfaces as an environment error at run
//!    time rather than as a compile error.
//! 6. **No diagnostic on the relational capability, ever.** Granting one
//!    reintroduces exactly the material ordered choice needs and starts the slide
//!    toward collapse. This is a permanent commitment, not a gap. The accepted
//!    cost is real: a CFG backend read through the relational trait loses the
//!    diagnostic its own interface carries.
//!
//! @covalence-api {"id":"A0021","title":"General parser combinators","status":"experimental","dependsOn":["A0015"]}

#![forbid(unsafe_code)]

pub mod budget;
pub mod conformance;
pub mod host;
pub mod morphism;
mod sharing;
pub mod syntax;
pub mod theory;
