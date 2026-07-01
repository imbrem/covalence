//! # `covalence-pure-trusted` — the closed-world equality kernel (the TCB)
//!
//! A typed first-order signature + an equational rewriting calculus, where the
//! complete set of inferences a theory admits is a **closed, enumerable set of
//! rules** fixed statically (and diffable against a checked-in manifest).
//!
//! The trust surface, in order of what an auditor must scrutinize:
//!
//! 1. [`Eqn`] — the unforgeable certificate. Private fields, no public constructor.
//!    The sole mint is `pub(crate) Eqn::new`; audit **every** call site — they are
//!    exactly: the [`eqn`] equality calculus + gated injectors, the [`prop`] bool
//!    theory, [`eq`]'s [`decide`], and [`matching`]'s [`apply_rewrite`].
//! 2. [`Expr`] — **sealed**: the closed grammar of expressions
//!    ([`Val`]/[`Ref`]`<P: TrustedDeref>`/[`App`]/[`True`]/[`False`]/`&A`/
//!    `Box`/`Rc`/`Arc<A>`/[`Dyn`]/[`DynApp`]/tuples), each with a unique sort
//!    [`Expr::Ty`]. Compared by **stdlib [`Eq`]** (`derive(Eq)` *is* the structural
//!    equality `trans` uses; [`Dyn`] uses pointer equality).
//! 3. The **gated** minting functions [`apply`]/[`apply0`]/[`canon`]/
//!    [`apply_rewrite`] and [`Eqn::lift`] — each runtime-checks `admits`/`extends`
//!    *before* minting. ([`of_eq`]/[`of_eq_with`], [`of_ptr_eq`],
//!    [`decide`]/[`semidecide`], the calculus, and the [`prop`] bool theory are
//!    ungated — leaf/structural equality is intrinsic to a sort.)
//! 4. [`StructuralEq`] (in [`eq`]) — the sealed "`Eq` is fully correct" claim that
//!    powers [`decide`]; the audited base-type leaves live here.
//! 5. `impl Language for ()` (in [`base`]) — the **empty** trivial base every
//!    language inherits (the equality calculus is ungated `Eqn` methods, not
//!    manifest rules), and `Bool`, the first real layer (the connectives).
//!
//! Equality is trusted via stdlib [`Eq`]: using a sort trusts its `Eq` (true ⟹
//! equal); "no `Eq`, no comparison". **The trusted `Eq` must also be *stable*** —
//! a certificate is eternal, so a leaf whose equality can change over time (a type
//! with *shared* interior mutability, e.g. `Rc<Cell<_>>`) can leave a true-at-mint
//! certificate false later. The audited [`StructuralEq`] leaves are all immutable;
//! a bespoke interior-mutable leaf is a self-inflicted unsoundness (like a lying
//! `Eq`). Everything else (the [`Language`] gates, [`Op`], [`Rule`]/[`CanonRule`])
//! funnels through the items above.
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

/// The one crate-level seal: [`Expr`] (and its `MatchApp`/`DynApp` companions) are
/// sealed against this trait, so the expression grammar is closed to this crate.
/// ([`eq`] keeps its own separate seal for [`StructuralEq`].)
pub(crate) mod sealed {
    pub trait Sealed {}
}

mod base;
mod dynapp;
mod eq;
mod eqn;
mod expr;
mod lang;
mod matching;
mod op;
mod prop;

pub use dynapp::*;
pub use eq::*;
pub use eqn::*;
pub use expr::*;
pub use lang::*;
pub use matching::*;
pub use op::*;
pub use prop::*;

#[cfg(test)]
mod tests;
