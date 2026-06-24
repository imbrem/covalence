//! # covalence-pure — the base logic (TCB floor)
//!
//! A small, auditable, constructive first-order logic on which everything else
//! is built. The long-term aim is **one trusted logic + N trusted executors +
//! K accelerators**, with trust tracked in a *meta*-assumption set so the TCB is
//! explicit and user-controlled (see [`notes/covalence-pure.md`] and the
//! reorganization plan in [`notes/refactor-plan.md`]).
//!
//! ## Status
//!
//! **Empty scaffold.** This crate currently defines no logic — it exists so the
//! dependency edge `covalence-core → covalence-pure` is in place while the
//! concrete design (the `Prop` / `Local<T>` / `Sigma` / `Ker` trait encoding and
//! the two-assumption-set `Fact`) is authored. Nothing here is load-bearing yet.
//!
//! [`notes/covalence-pure.md`]: ../../../notes/covalence-pure.md
//! [`notes/refactor-plan.md`]: ../../../notes/refactor-plan.md
