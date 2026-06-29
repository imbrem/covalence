//! # `covalence-pure-trusted` — the kernel TCB
//!
//! The minimal trusted core: a small, value-directed kernel. A [`MThm<K, P>`]
//! certifies a specific statement [`Stmt<K, P>`] — a context **value** `c: K`
//! paired with a proposition **value** `p: P`. Read `K ⊢ P`. The ergonomic facade
//! (testing utilities, extension traits, future macros) lives in `covalence-pure`,
//! which re-exports this crate; **this** crate is the audit target.
//!
//! - **`K` is the TCB.** The context value names (and carries) what is trusted:
//!   a pile of assumptions, a HOL context, WASM-evaluation facts. Growing the
//!   trusted base = a richer `K` (`Hol`, `WasmEval`, `WasmTrusted`, …); the
//!   logical content lives in `P`.
//! - **`P` is the statement.** An equation, a claim about a WASM program, a
//!   `bool`. Connectives are host types over the *values*: `(P, Q)` is `P ∧ Q`,
//!   `Either<P, Q>` is `P ∨ Q`, `()` is `⊤`, and the `bool` value `false` is
//!   `⊥`.
//!
//! ## The invariant (load-bearing)
//!
//! Every type is **assumed inhabited** (HOL-style), so the *existence* of a
//! `MThm<K, P>` at the type level is **not information** — you could always
//! exhibit some `p: P`. What a theorem certifies is that *this specific* `(c, p)`
//! is derivable. `MThm<K, bool>` is not "K proves bool"; it certifies a specific
//! bool, possibly `false` (→ K is inconsistent). The types are *sorts*; the
//! **values** are the content. So the kernel is **value-directed**: no API reads
//! meaning from type-level inhabitation (no `Option<MThm>` standing for
//! "provable"); eliminators dispatch on values, and ex-falso takes the caller's
//! specific target value.
//!
//! ## Soundness
//!
//! 1. **`MThm` is an unforgeable wrapper around `Stmt`** (private field, no public
//!    constructor). The sole constructor `MThm::new` is **private to the `thm`
//!    module**, so only this crate's kernel can mint. Downstream crates — the
//!    `covalence-pure` facade, `covalence-pure-derive`, feature crates — cannot
//!    reach `MThm::new`; they only compose the public API or write `Rule`s that go
//!    through the gate. So **this crate is the entire minting TCB.** (Each
//!    downstream context's own `Rule` impls are *its* trust, not this crate's.)
//!    `Stmt` is public and freely constructible — it carries *no* claim of truth
//!    (the untrusted analogue of a theorem).
//! 2. **Minting is gated by [`Derive::derive`]** (`MThm`'s [`Derive`] impl), which
//!    runs a [`Rule`] and blesses its output. A rule's `Self` is the *output
//!    context*, so the orphan rule reserves each context's rules to its own crate
//!    — a context controls every theorem minted in it. Premises ride inside the
//!    rule `R` as real `MThm`s (unforgeable ⇒ genuine); a `Rule` invoked directly
//!    yields a raw pair, never a `MThm`. The reserved constructive structural
//!    rules (`trivial` / `zip` / `fst` / `or_inl` / `or_elim` / `false_elim` /
//!    `ctx_*`) are trusted methods.
//!
//! ## Future directions
//!
//! - **Proof recording** — since [`Derive::derive`] is the single choke point
//!   and a rule already bundles its premises, a recording container is just "a
//!   `MThm` that retains its `R`" — a different [`Derive`] impl. (Not built yet.)
//! - **In-place rewriting** — mutate a prop value in place (returning auxiliary
//!   data) for efficient large-term edits. (Not built yet.)

mod derive;
mod thm;

pub use derive::*;
pub use thm::*;
