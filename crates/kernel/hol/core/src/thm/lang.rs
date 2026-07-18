//! The `covalence-pure` mint gate for [`Thm`](super::Thm).
//!
//! Every proven HOL sequent `Γ ⊢ φ` is carried as the SINGLE structured pure
//! proposition
//!
//! ```text
//! CoreProp = App<IsThm, (Val<Ctx>, Val<Term>)>
//! ```
//!
//! minted through the fine-grained rule catalogue in `super::rules` in the
//! language [`CoreLang`] (public via [`crate::seam`] since the toHOL slice —
//! the deliberate, one-module-to-audit widening of the core-on-pure seam).
//! `Ctx`/`Term` enter as [`Val`] leaves (O(1)
//! `Arc`-backed wraps — no deep clone, no re-inference), so `App<IsThm, (Val<Ctx>,
//! Val<Term>)>` is an `Expr<Ty = bool>` (the tuple sorts at `(Ctx, Term) =
//! IsThm::In`), satisfying the [`Rule::Concl`] / `Thm<L, P>` bound. It is a
//! STRUCTURED proposition (an [`Op`] over `Val` leaves), not an opaque blob — which
//! keeps the future native-HOL / `NatToHol` embedding seam open (see the generated open-work index).
//!
//! ## Soundness rests on `admits()` ALONE
//!
//! [`CoreLang`] admits exactly the sound `Rule<CoreLang>` ZSTs in
//! `super::rules`, one per HOL inference step. Each rule's `decide` takes its
//! premises as unforgeable `pure::Thm`s and **derives** its conclusion (it never
//! accepts a caller-supplied conclusion), so every firing on any input yields a
//! true theorem. The obtainable set of `pure::Thm<CoreLang, IsThm(Γ,φ)>` therefore
//! contains only genuinely-derivable sequents — the admits-only milestone.
//!
//! Concretely:
//! - `pure::Thm` is unforgeable (private fields, `pub(crate)` `new`; the only mint
//!   for an `IsThm`-headed prop is [`covalence_pure::apply`] gated on an admitted
//!   rule's own `TypeId`).
//! - Novel downstream `impl Rule<CoreLang> for Evil` types are inert:
//!   `core_admits(TypeId::of::<Evil>())` is `false`, so `apply` returns
//!   `NotAdmitted` before `Evil::decide` runs.
//! - [`super::rules::core_admits`] and `super::rules::CORE_MANIFEST` are emitted
//!   from ONE source list by the `core_rules!` macro, so they cannot drift.
//!
//! The inner `pure::Thm` field on [`Thm`](super::Thm) is now **hygiene-only**: it
//! keeps `pure::Thm`/`CoreLang` out of the public signature and preserves
//! `Arc`-identity, but is no longer load-bearing for soundness. What still remains
//! trusted (unchanged, documented seams): the `unfold_term_spec` definitional
//! unfolding and the per-family certificate dispatch (`super::certs` over
//! `covalence-pure-eval`).

use std::any::TypeId;

use covalence_pure::{App, Language, Manifest, Op, Val};

use crate::ctx::Ctx;
use crate::term::Term;

/// A **HOL tier**: a language a [`Thm`](super::Thm) can be minted at.
///
/// The kernel certificate is `Thm<L = CoreLang>` — generic over the tier so a
/// downstream crate owning a language that `extends` [`CoreLang`] (the planned
/// `CoreEval` in `covalence-hol-eval`) can host its own `Rule<CoreEval>` impls
/// and mint the HOL rules directly at its tier. The trait is deliberately
/// **public and implementable downstream** (it is a plain marker, not a sealed
/// gate): implementing `HolTier` for a language confers NO proving power —
/// soundness rests on `admits()` alone, exactly as for [`CoreLang`] (see the
/// module docs). A tier that admits an unsound rule is unsound *by its own
/// declaration*; `Thm<CoreLang>` remains the pure-HOL tier regardless of what
/// other tiers exist.
///
/// Supertraits: [`Language`] (the admits gate), `Default + Copy + 'static`
/// (tiers are stateless ZST languages; `Default` is how the rule glue
/// summons the language value to mint against).
pub trait HolTier: Language + Default + Copy + 'static {}

impl HolTier for CoreLang {}

/// The kernel judgement operator: `IsThm(Γ, φ) : bool` — "the sequent `Γ ⊢ φ` is
/// a theorem". A ZST; writing it is inert. Only the admitted rules in
/// `super::rules` (via the [`covalence_pure::apply`] gate) ever conclude an
/// `IsThm`-headed proposition. `pub` (re-exported through [`crate::seam`]) so
/// untrusted drivers can state and transport `IsThm`-headed propositions —
/// writing the op proves nothing.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct IsThm;

impl Op for IsThm {
    type In = (Ctx, Term);
    type Out = bool;
}

/// The structured proposition carried by a [`Thm`](super::Thm), **generalized
/// over its conclusion operand** `C`: the sequent `IsThm(Γ, φ)` where the
/// conclusion `φ : Term` is denoted by the expression `C` (`C: Expr<Ty =
/// Term>`).
///
/// The default operand `C = Val<Term>` (a *concrete* term leaf) recovers
/// [`CoreProp`]; a *symbolic* operand (e.g. `NatAddEqE` in
/// `covalence-hol-eval` — `nat.add (toHOL a) (toHOL b) = toHOL (a+b)` with
/// `Val<Nat>` bignum leaves under the uninterpreted `ToHolNat` op) lets a
/// theorem carry a `toHOL` value **without ever materializing** its
/// succ-tower. This is the literal-endgame's additive mechanism (design:
/// `notes/vibes/literal-endgame-design.md`, stage EG1): `IsThmProp<C>` is an
/// `Expr<Ty = bool>` for **every** `C: Expr<Ty = Term>` (the tuple sorts at
/// `(Ctx, Term) = IsThm::In`), so the base `eq_mp`/`trans`/`cong` calculus
/// transports it with **zero** new base machinery — the laziness *is* the
/// existing `Expr`/`Op` algebra.
pub type IsThmProp<C> = App<IsThm, (Val<Ctx>, C)>;

/// The **concrete** sequent proposition carried by an ordinary
/// [`Thm`](super::Thm) `= Thm<L>` (default operand): `IsThm(Γ, φ)` with the
/// conclusion `φ` as a `Val<Term>` leaf. The `= IsThmProp<Val<Term>>`
/// specialization — same value it always was, so every existing rule,
/// accessor, and consumer is unchanged.
pub type CoreProp = IsThmProp<Val<Term>>;

/// The core kernel's language: a stateless [`Copy`] ZST admitting EXACTLY the sound
/// rule catalogue in `super::rules`. Hypotheses live INSIDE the proposition (the
/// `Val<Ctx>` operand), not in the language value, so `union` is trivial.
///
/// Since the tower split (E2 + audit fix), `CoreLang` extends **nothing**:
/// it is the pure-HOL tier, and computation lives one tier up — `CoreEval`
/// (in `covalence-hol-eval`) extends both `CoreLang` and
/// [`covalence_pure_eval::Builtins`] directly, hosting the certificate rules
/// next to the native `CanonRule`s. `Thm<CoreLang, _>` therefore certifies
/// derivability from the 39 HOL rules alone.
#[derive(Clone, Copy, Debug, Default)]
pub struct CoreLang;

impl Language for CoreLang {
    fn admits(&self, rule: TypeId) -> bool {
        super::rules::core_admits(rule)
    }
    /// `CoreLang` extends **nothing** — the pure-HOL tier carries no
    /// computation TCB *by declaration* (audit fix: the historical
    /// `extends(Builtins)` edge from the first toHOL slice became dead once
    /// the cert rules moved to `CoreEval`, which accepts `Builtins` as a
    /// direct parent itself). Mirrored by the empty parent list in
    /// `super::rules::CORE_MANIFEST`.
    fn extends(&self, _parent: TypeId) -> bool {
        false
    }
    fn union(self, _other: Self) -> Option<Self> {
        Some(self)
    }
    const MANIFEST: Option<&'static Manifest> = Some(&super::rules::CORE_MANIFEST);
}
