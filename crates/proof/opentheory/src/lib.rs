//! Verify [OpenTheory](http://www.gilith.com/opentheory/) articles — the proof
//! interchange format of HOL Light, HOL4, and ProofPower — by replaying them
//! against covalence's HOL kernel, re-checking every inference.
//!
//! # The layers, and the stable high-level API
//!
//! Everything is built to keep a small, backend-agnostic surface stable as the
//! kernel is refactored underneath — the traits are the seams, the concrete
//! types are swappable:
//!
//! - **[`ArticleInterp`]** — the article stack machine, generic over any
//!   `K: `[`HolLightKernel`](covalence_hol::traits::HolLightKernel). This trait
//!   (in `covalence-hol`) is the backend-swap seam: covalence-HOL today
//!   ([`NativeOt`]), an internal / metamath-HOL later — same interpreter, same
//!   CLI, a new impl.
//! - **[`NativeOt`]** (feature `native`) — the native backend over
//!   `covalence-core`. **Zero TCB beyond core HOL**: every rule delegates to an
//!   audited kernel operation, and `axiom` statements are *hypothesis-tracked*
//!   (`{p} ⊢ p`), never minted — so an article verifies *relative to* exactly
//!   the axioms it uses.
//! - **Package resolution** — [`check_theory`] over a [`TheoryResolver`]:
//!   offline [`FileResolver`], or network [`CachingUrlResolver`] (feature
//!   `fetch`) that versions bare names via the repo's `?pkg=` index.
//!
//! Driven by `cov hol check <files.art>` / `cov hol pkg <packages>` and the
//! `bun run opentheory` download+cache+verify-all benchmark. `cov hol pkg base`
//! re-checks the whole standard library — **1340 theorems**.
//!
//! # Checking against a *native* theory
//!
//! By default OpenTheory's axioms are assumed (tracked as hypotheses). But a
//! backend whose own logic already has the relevant structure can *discharge*
//! them — the capability is factored into two reusable pieces:
//!
//! - **[`matching`]** — recognising that an imported statement denotes the same
//!   proposition as a native theorem, and transporting proofs across the
//!   representation gap. Generic over the [`MatchLogic`] (the HOL being matched)
//!   and the [`MatchStrategy`] (`Structural` / `UpToBeta` / `UpToDelta` / …).
//! - **[`NativeOverrides`] / [`OverrideMap`]** — inject native proofs for
//!   axioms ([`prove_axiom`]) and native types/constants for OpenTheory names,
//!   consulted by [`NativeOt`]. Cannot forge: a returned theorem is a real
//!   kernel theorem, re-checked against the statement it claims.
//!
//! [`axioms::standard_axioms`] uses both to prove OpenTheory's three HOL axioms
//! (infinity over `nat`, extensionality, choice) in covalence's kernel, so
//! `cov hol pkg --native-axioms base` verifies all 1340 theorems relative to
//! **zero** axioms.
//!
//! [`prove_axiom`]: native::NativeOverrides::prove_axiom

#[cfg(feature = "native")]
pub mod axioms;
pub mod error;
#[cfg(feature = "fetch")]
pub mod fetch;
pub mod interp;
pub mod machine;
#[cfg(feature = "native")]
pub mod matching;
pub mod name;
#[cfg(feature = "native")]
pub mod native;
pub mod object;
pub mod reader;
pub mod resolve;
pub mod theory;

#[cfg(feature = "native")]
pub use axioms::{prove_choice, prove_extensionality, prove_infinity, standard_axioms};
pub use error::OtError;
#[cfg(feature = "fetch")]
pub use fetch::{CachingUrlResolver, OPENTHEORY_REPO, UrlResolver};
pub use interp::ArticleInterp;
pub use machine::{ArticleMachine, ArticleResult};
#[cfg(feature = "native")]
pub use matching::{
    HolMatch, MatchLogic, MatchStrategy, Structural, UpToBeta, UpToBetaDelta, UpToDelta,
    transport_hol,
};
pub use name::{NameTable, OtName};
#[cfg(feature = "native")]
pub use native::{NativeOt, NativeOverrides, OverrideMap};
pub use object::OtObject;
pub use reader::read_article;
pub use resolve::{
    FileResolver, Theory, TheoryCache, TheoryResolver, check_theory, register_select,
};
pub use theory::{TheoryBlock, TheoryFile, parse_theory_file};
