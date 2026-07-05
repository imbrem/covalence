//! Wrapper crate for property-based testing.
//!
//! All usage of `proptest` should go through this crate (the same
//! discipline as `covalence-rand` for `rand`). Consumers take it as a
//! **dev-dependency only** — property tests are test-harness code and
//! must never enter a shipped (non-dev) dependency edge, let alone the
//! TCB closure.
//!
//! The `proptest!` / `prop_assert*!` / `prop_oneof!` macros refer to
//! `::proptest::*` internally, so consumers use them via the re-exported
//! crate module:
//!
//! ```ignore
//! use covalence_proptest::proptest::prelude::*;
//!
//! proptest! {
//!     #[test]
//!     fn add_commutes(a in 0u32..100, b in 0u32..100) {
//!         prop_assert_eq!(a + b, b + a);
//!     }
//! }
//! ```
//!
//! (A bare `use covalence_proptest::prelude::*` also works for the
//! non-macro surface, but the macros need `proptest` resolvable as a
//! crate-like path — the `pub use proptest;` below provides it, and
//! Rust 2018+ macro paths inside `proptest!` resolve against the real
//! crate, so no extern alias is needed.)

pub use proptest;
pub use proptest::*;

/// Case count for a `ProptestConfig`: the `PROPTEST_CASES` env var if
/// set and parseable, else `default`.
///
/// **Every explicit `cases:` in a `ProptestConfig` must go through this
/// helper.** `ProptestConfig::default()` reads `PROPTEST_CASES` itself,
/// but an explicit `cases: N, ..ProptestConfig::default()` *overrides*
/// the env-derived value — so a hard-coded count silently defeats
/// `PROPTEST_CASES=…` high-count sweeps.
pub fn cases(default: u32) -> u32 {
    std::env::var("PROPTEST_CASES")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(default)
}
