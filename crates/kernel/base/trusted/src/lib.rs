//! # `covalence-pure-trusted` — the closed-world equality kernel (the TCB)
//!
//! A typed first-order signature + an equational rewriting calculus, where the
//! complete set of inferences a theory admits is a **closed, enumerable set of
//! rules** fixed statically (and diffable against a checked-in manifest).
//!
//! The trust surface, in order of what an auditor must scrutinize:
//!
//! 1. [`Thm`] — the unforgeable certificate `⊢ P` in language `L`. Private fields,
//!    no public constructor. The sole mint is `pub(crate) Thm::new`; audit **every**
//!    call site:
//!    - in `eqn` — `refl`/`sym`/`trans`/`cong_app`/`cong_pair`/`eq_mp`,
//!      `trans_ptr`, `of_ptr_eq`, `of_eq_with` (used by `of_eq`/`semidecide`),
//!      `lift`, `apply` (⇒ `apply0`), `canon`;
//!    - in `prop` — `and_intro`/`and_elim`/`or_inl`/`or_inr`/`mp`;
//!    - in `matching` — `apply_rewrite`.
//! 2. [`Expr`] — **sealed**: the closed grammar of expressions
//!    ([`Val`]/[`Ref`]`<P: TrustedDeref>`/[`App`]/[`True`]/[`False`]/[`Eqn`]/`&A`/
//!    `Box`/`Rc`/`Arc<A>`/[`Dyn`]/tuples), each with a unique sort [`Expr::Ty`].
//!    Compared by **stdlib [`Eq`]** (`derive(Eq)` *is* the structural equality
//!    `trans` uses; [`Dyn`] uses pointer equality). [`Eqn<A, B>`] is the equality
//!    *proposition* (bool-sorted, freely constructible ⇒ proves nothing).
//! 3. [`Op`] and the [`App::as_op`] downcast — `Op: Any`, so the pointer forwarding
//!    impls (`Box`/`Rc`/`Arc`/`&'static F`) make `App<Arc<dyn Op<..>>, _>` a
//!    *dynamic* application; `as_op` downcasts the **real** operator vtable (never a
//!    downstream hook) via trait-upcast to `&dyn Any`.
//! 4. The **gated** minting functions [`apply`]/[`apply0`]/[`canon`]/
//!    [`apply_rewrite`] and [`Thm::lift`] — each runtime-checks `admits`/`extends`
//!    *before* minting. ([`of_eq`]/[`of_eq_with`], [`of_ptr_eq`], [`semidecide`], the
//!    calculus, and the `prop` bool theory are ungated — leaf equality is
//!    *definitional*, see below.)
//! 5. `impl Language for ()` (in `base`) — the **empty** trivial base every
//!    language inherits (the calculus and bool theory are ungated `Thm` methods, not
//!    manifest rules).
//!
//! (There is deliberately **no disequality/decision seam** yet: proving `⊢ ¬(a = b)`
//! — and, generally, evaluating an expression to a constant `⊢ e = Val(eval(e))` — is
//! the planned `Evaluate` trait, kept out of the TCB for now because it must preserve
//! the `admits` gate on op evaluation and needs the builtin arithmetic ops. See
//! SKELETONS.)
//!
//! ## What leaf equality *means* here (the definitional framing)
//!
//! Leaf equality is **defined** by two introduction rules — it is not an external
//! fact the kernel "trusts" a sort not to violate:
//! - [`of_eq`] reads a sort's stdlib [`Eq`]: `a == b` (possible) ⟹ `⊢ Val(a) = Val(b)`;
//! - [`Thm::refl`]/[`Thm::cong_app`] use its [`Clone`]: `⊢ a = a`, built by
//!   *duplicating* the value (so `b == a.clone()` (possible) is likewise a way to
//!   have `⊢ a = b`).
//!
//! Together a sort's `Eq` and `Clone` *generate* the equality the kernel certifies;
//! the calculus (`sym`/`trans`/`cong`) is just its equivalence-and-congruence
//! closure. So a sort whose `Eq`/`Clone` are unusual simply *has* an unusual
//! equality — there is **no external truth for them to contradict**, hence nothing
//! forgeable in the base `()`. (A step that *distinguishes* two so-identified values
//! must itself be an **admitted** rule — an op's [`CanonRule`] eval, gated on
//! `admits` — so a "lying `Clone`" is inert until you vouch for a conflicting rule,
//! which is then a self-inflicted inconsistency in *that* language, like a false
//! axiom.) `Clone` is thus not a new trust obligation: it is *part of the definition*
//! of what "the same value" means at a sort.
//!
//! Note there is **no stability obligation** on this equality direction: we only ever
//! mint `⊢ a = b` from a comparison/clone that was *possible* (held at least once),
//! and equality is the closure over such facts — so even a flaky `Eq`/`Clone` only
//! ever lets you *prove more equalities*, never a false disequality. (You can only
//! prove `a == b`, never `a != b`, from this direction.) A disequality would need a
//! trusted **non-equality** seam — which is exactly the deferred `Evaluate` work
//! (evaluate the equality proposition to `false`); until it lands, the kernel proves
//! no disequalities, so nothing here is at risk.
//!
//! The framework guarantees **closure** (only `tree(L)` rules fire) and
//! **enumerability**, *not* internal consistency: a language that admits a rule
//! contradicting the ungated base is the author's problem, like a false axiom. To
//! model a quotient, introduce a *new sort* — never redefine a base type's equality.
//!
//! Everything else (the [`Language`] gates, [`Op`], [`Rule`]/[`CanonRule`]) funnels
//! through the items above.
//!
//! ## Soundness, in one line
//!
//! Every `Thm<L, _>` is derivable using only the universal equality/propositional
//! calculus + rules in `tree(L)`; hence if every rule in `tree(L)` is sound, `L` is
//! sound. `Language` is parameter-free, so `impl Language for L` is crate-reserved
//! and unique ⇒ `tree(L)` is fixed by the program, and minting is gated on the
//! runtime `lang.admits(..)` check, so only `tree(L)` rules ever fire.

#![forbid(unsafe_code)]
// The type-level expression representation makes certificate signatures inherently
// rich (e.g. `Eqn<App<F, Val<F::In>>, Val<F::Out>, L>`); factoring these into
// aliases would obscure the kernel rather than clarify it.
#![allow(clippy::type_complexity)]

/// The one crate-level seal: [`Expr`] (and its `MatchApp` companion) is sealed
/// against this trait, so the expression grammar is closed to this crate.
pub(crate) mod sealed {
    pub trait Sealed {}
}

mod base;
mod eqn;
mod expr;
mod float;
mod lang;
mod matching;
mod op;
mod prop;

pub use eqn::*;
pub use expr::*;
pub use float::*;
pub use lang::*;
pub use matching::*;
pub use op::*;
pub use prop::*;

#[cfg(test)]
mod tests;
