//! # `covalence-pure-trusted` — the closed-world equality kernel (the TCB)
//!
//! A typed first-order signature + an equational rewriting calculus, where the
//! complete set of inferences a theory admits is a **closed, enumerable set of
//! rules** fixed statically (and diffable against a checked-in manifest).
//!
//! The trust surface, in order of what an auditor must scrutinize:
//!
//! 1. [`Eqn`] — the unforgeable certificate. Private fields, no public
//!    constructor; the only minting paths are this module's calculus + gated
//!    injectors. `Eqn::new` is **private to [`eqn`]**.
//! 2. [`Expr`] — **sealed**: the closed grammar of expressions
//!    ([`Val`]/[`Ref`]/[`App`]/[`True`]/[`False`]/`&A`/`Box<dyn Expr>`/tuples),
//!    each with a unique sort [`Expr::Ty`]. Compared by **stdlib [`Eq`]**
//!    (`derive(Eq)` *is* the structural equality `trans` uses).
//! 3. The **gated** minting functions [`apply`]/[`canon`] and [`Eqn::lift`] — each
//!    runtime-checks `admits`/`extends` *before* minting. ([`of_eq`], [`of_ptr_eq`],
//!    [`decide`]/[`semidecide`], the calculus, and the [`prop`] bool theory are
//!    ungated — leaf/structural equality is intrinsic to a sort.)
//! 4. [`StructuralEq`] (in [`eq`]) — the sealed "`Eq` is fully correct" claim that
//!    powers [`decide`]; the audited base-type leaves live here.
//! 5. `impl Language for ()` (in [`base`]) — the **empty** trivial base every
//!    language inherits (the equality calculus is ungated `Eqn` methods, not
//!    manifest rules), and `Bool`, the first real layer (the connectives).
//!
//! Equality is trusted via stdlib [`Eq`]: using a sort trusts its `Eq` (true ⟹
//! equal); "no `Eq`, no comparison". Everything else (the [`Language`] gates,
//! [`Op`], [`Rule`]/[`CanonRule`]) funnels through the items above.
//!
//! ## Soundness, in one line
//!
//! Every `Eqn<_, _, L>` is derivable using only the universal equality calculus +
//! rules in `tree(L)`; hence if every rule in `tree(L)` is sound, `L` is sound.
//! `Language` is parameter-free, so `impl Language for L` is crate-reserved and
//! unique ⇒ `tree(L)` is fixed by the program, and minting is gated on the runtime
//! `lang.admits(..)` check, so only `tree(L)` rules ever fire.

#![forbid(unsafe_code)]
// The type-level expression representation makes certificate signatures inherently
// rich (e.g. `Eqn<App<F, Val<F::In>>, Val<F::Out>, L>`); factoring these into
// aliases would obscure the kernel rather than clarify it.
#![allow(clippy::type_complexity)]

mod base;
mod eq;
mod eqn;
mod expr;
mod lang;
mod op;
mod prop;

pub use eq::*;
pub use eqn::*;
pub use expr::*;
pub use lang::*;
pub use op::*;
pub use prop::*;

#[cfg(test)]
mod tests;
