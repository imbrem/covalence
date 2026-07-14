//! **`covalence-numerals`** — the numeral-literal ladder behind a *swappable
//! backend*.
//!
//! Numeric literals (`2748`, `0xABC`, `-1/2`, `1.5e3`) are parsed by the
//! compositional grammars in [`covalence_grammar`] and *built* by a
//! [`NumeralBackend`]. Two seams, both traits:
//!
//! ```text
//! bytes --(LiteralGrammar::parse)--> Lit --(NumeralBackend::{nat,int,…})--> Repr
//! ```
//!
//! - [`LiteralGrammar`] — parse/deparse the surface syntax. The default
//!   [`NumeralGrammar`] wraps [`covalence_grammar`]; swap it for a different
//!   alphabet without touching any backend.
//! - [`NumeralBackend`] — turn a parsed [`Lit`] into the backend's own
//!   representation (`Repr`) and, optionally, PROVE relationships (`Thm`)
//!   between built values. This is the point of the crate.
//! - [`lower`] glues them: parse with `G`, build with `B`, generic over both.
//!
//! The default build is **kernel-independent** (only [`covalence_grammar`] +
//! [`covalence_types`]); [`RatValue`]/[`RatBackend`] is a self-contained
//! backend that evaluates literals to rationals with no proofs.
//!
//! Behind the **`hol`** feature live the kernel backends:
//!
//! - [`Symbolic`] — builds real kernel `Term`s and proves e.g. `0xABC = 2748`
//!   *structurally*: both surface forms fold (in [`covalence_types`]) to the
//!   same [`covalence_types::Nat`], hence to the **same kernel literal term**,
//!   so reflexivity closes the equation — with **no new TCB**.
//! - [`Builtin`] — the same trait, but relationships are decided by the
//!   kernel's existing `reduce` / `prove_true` CanonRule procedures (fast; and
//!   it agrees with [`Symbolic`]).
//! - `Wasm` — a verified-trace backend (**skeleton**; see `SKELETONS.md`).

#![forbid(unsafe_code)]

pub mod grammar;
pub mod lit;

pub use grammar::NumeralGrammar;
pub use lit::{FloatCert32, Lit, LiteralGrammar, NumeralBackend, Style, build, lower};

mod rat_backend;
pub use rat_backend::{RatBackend, RatValue};

#[cfg(feature = "hol")]
pub mod backend;
#[cfg(feature = "hol")]
pub use backend::{Builtin, Symbolic, Wasm};
