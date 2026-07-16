//! Kernel [`NumeralBackend`]s (behind the `hol` feature).
//!
//! All three build real kernel `Term`s; they differ only in how they *prove*
//! relationships:
//!
//! - [`Symbolic`] — structural. `prove_eq` reduces both terms to a common
//!   kernel normal form and chains the resulting equations; because the two
//!   surface forms of a literal (`0xABC`, `2748`) fold to the *same*
//!   [`covalence_types::Nat`] and hence the same literal `Term`, the chain
//!   collapses to reflexivity. **No new TCB.**
//! - [`Builtin`] — the same relationships decided by the kernel's existing
//!   `reduce` / `prove_true` CanonRule procedures (fast). It agrees with
//!   [`Symbolic`] by construction (both bottom out in the same certificates).
//! - [`Wasm`] — a verified-trace backend (**skeleton**).
//!
//! The shared representation is [`NumeralTerm`]: a kernel `Term` tagged with the
//! rung it was built at, so the backends can pick the right relation
//! (`nat`-`lt`, `rat`-`le`, …). Proofs are hypothesis-free [`EvalThm`]s.

mod builtin;
mod symbolic;
mod wasm;

pub use builtin::Builtin;
pub use symbolic::{NumeralTerm, Rung, Symbolic};
pub use wasm::Wasm;
