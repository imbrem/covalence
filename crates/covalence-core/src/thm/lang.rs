//! The `covalence-pure` mint gate for [`Thm`](super::Thm).
//!
//! Every proven HOL sequent `Γ ⊢ φ` is carried as the SINGLE structured pure
//! proposition
//!
//! ```text
//! CoreProp = App<IsThm, (Val<Ctx>, Val<Term>)>
//! ```
//!
//! minted through one admitted [`MintRule`] in the crate-private language
//! [`CoreLang`]. `Ctx`/`Term` enter as [`Val`] leaves (O(1) `Arc`-backed wraps —
//! no deep clone, no re-inference), so `App<IsThm, (Val<Ctx>, Val<Term>)>` is an
//! `Expr<Ty = bool>` (the tuple sorts at `(Ctx, Term) = IsThm::In`), satisfying
//! the [`Rule::Concl`] / `Thm<L, P>` bound. It is a STRUCTURED proposition (an
//! [`Op`] over `Val` leaves), not an opaque blob — which keeps the future
//! native-HOL / `NatToHol` embedding seam open (see `SKELETONS.md`).
//!
//! ## What carries soundness today (be honest: NOT `admits()` alone)
//!
//! This gate is a certificate **carrier**, not yet an independent checker.
//! [`MintRule::decide`] is a **rubber-stamp** — it stamps `IsThm(Γ, φ)` for *any*
//! well-typed `(Γ, φ)` — so it is not a sound rule, and admitting it does not by
//! itself confer soundness (under admits-only semantics `pure::Thm<CoreLang,
//! IsThm(Γ,φ)>` would be derivable for *any* well-typed `(Γ,φ)`, i.e. vacuous).
//! What actually keeps `core::Thm` sound right now is:
//!
//! - core's (unchanged) ~55 rule methods on [`Thm`](super::Thm) compute genuinely
//!   derivable sequents, and [`Thm::build`]'s `is_bool` validation; **and**
//! - the **private newtype field** on [`Thm`](super::Thm): only core can call
//!   `build` / wrap a `pure::Thm<CoreLang, _>`, so no one else can reach the stamp.
//!   This is a *visibility* barrier — soundness currently rests on it, NOT on
//!   `admits()`. (Belt-and-braces: [`CoreLang`]/[`MintRule`] are `pub(crate)` in a
//!   private module and unexported, and [`CoreLang::admits`] gates EXACTLY
//!   `MintRule`'s `TypeId` so no *other* rule can fire — but neither of those is the
//!   load-bearing property here.)
//!
//! The **admits-only milestone** (soundness carried by `admits()` alone, nameability
//! irrelevant) requires replacing this catch-all stamp with the actual HOL inference
//! steps as *sound* `Rule<CoreLang>`s. See `SKELETONS.md` (Severe).

use std::any::TypeId;

use covalence_pure::Error as PureError;
use covalence_pure::{App, LangMeta, Language, Manifest, Op, Rule, RuleMeta, RuleRecord, Val};

use crate::ctx::Ctx;
use crate::term::Term;

/// The kernel judgement operator: `IsThm(Γ, φ) : bool` — "the sequent `Γ ⊢ φ` is
/// a theorem". A ZST; writing it is inert, only [`MintRule`] (via the admit gate)
/// ever concludes an `IsThm`-headed proposition.
#[derive(Clone, Copy, Debug)]
pub(crate) struct IsThm;

impl Op for IsThm {
    type In = (Ctx, Term);
    type Out = bool;
}

/// The structured proposition carried by every [`Thm`](super::Thm): the sequent
/// `(hyps, concl)` under the `IsThm` judgement.
pub(crate) type CoreProp = App<IsThm, (Val<Ctx>, Val<Term>)>;

/// The sole rule [`CoreLang`] admits. A crate-private ZST whose `decide` is a
/// rubber-stamp: it wraps the already-validated `(hyps, concl)` into the `IsThm`
/// proposition. UNTRUSTED — the gate is that `CoreLang` admits only this type's
/// `TypeId`, and both `CoreLang` and `MintRule` are unnameable downstream (private
/// module), so no other rule can be admitted or even written against `CoreLang`.
pub(crate) struct MintRule;

impl Rule<CoreLang> for MintRule {
    type Input = (Ctx, Term);
    type Concl = CoreProp;
    fn decide(self, (hyps, concl): (Ctx, Term), _lang: &CoreLang) -> Result<CoreProp, PureError> {
        Ok(App(IsThm, (Val(hyps), Val(concl))))
    }
}

/// The core kernel's language: a stateless [`Copy`] ZST admitting EXACTLY
/// [`MintRule`]. Hypotheses live INSIDE the proposition (the `Val<Ctx>` operand),
/// not in the language value, so `union`/`extends`/`lift` are never exercised by
/// core.
#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct CoreLang;

static CORE_MANIFEST: Manifest = Manifest {
    ty: TypeId::of::<CoreLang>(),
    extends: &[],
    admits: &[RuleRecord {
        ty: TypeId::of::<MintRule>(),
        metadata: RuleMeta,
    }],
    metadata: LangMeta,
};

impl Language for CoreLang {
    fn admits(&self, rule: TypeId) -> bool {
        rule == TypeId::of::<MintRule>()
    }
    fn extends(&self, _parent: TypeId) -> bool {
        false
    }
    fn union(self, _other: Self) -> Option<Self> {
        Some(self)
    }
    const MANIFEST: Option<&'static Manifest> = Some(&CORE_MANIFEST);
}
