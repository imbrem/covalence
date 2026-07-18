//! Languages (= theories = rulesets), the static `Manifest` tree, and the two
//! gated-rule traits ([`Rule`], [`CanonRule`]).

use std::any::TypeId;

use crate::eqn::Error;
use crate::expr::Expr;
use crate::op::Op;

/// A language / theory / ruleset. **PARAMETER-FREE on purpose**: the only type in
/// `impl Language for Foo` is `Foo` itself, so the orphan rule reserves the impl
/// to `Foo`'s crate and coherence makes it unique ⇒ the admissible-rule set is a
/// fixed function of the type. The *value* may carry data (hypotheses, axioms,
/// keys); `&self` is for object-safety, but the rule set is type-determined
/// (impls ignore `self`'s data in `admits`/`extends`).
pub trait Language: 'static {
    /// Membership gate for rule `rule` (a `TypeId`). **Contract** (3 parts):
    /// - MUST be `true` for every DIRECT rule (so it can be applied here);
    /// - MUST be `false` for any rule NOT in `tree(self)` — the soundness floor:
    ///   `admits(r) == true` ⟹ `r ∈ tree(self)`;
    /// - UNSPECIFIED for inherited (indirect) rules — implementor's choice
    ///   (returning `true` lets an inherited rule be applied directly here; `false`
    ///   requires the apply-in-home + [`lift`](crate::Thm::lift) composition).
    fn admits(&self, rule: TypeId) -> bool;

    /// Parent gate. Same 3-part contract: `true` for DIRECT parents, `false` for
    /// non-ancestors (`extends(p) == true` ⟹ `tree(p) ⊆ tree(self)`), free for
    /// indirect ancestors.
    fn extends(&self, parent: TypeId) -> bool;

    /// Combine two language *values* into one whose context admits **both** —
    /// e.g. the union of two hypothesis sets. `None` if they cannot be combined
    /// (incompatible contexts). Used to merge the contexts of two equations
    /// (`trans`/`cong_pair`/`and_intro`/`mp`): the result holds under the union.
    /// **Contract**: `union(a, b) == Some(c)` ⟹ everything provable under `a` *or*
    /// under `b` is provable under `c`. For a stateless (ZST) language this is
    /// trivially `Some(self)`.
    fn union(self, other: Self) -> Option<Self>
    where
        Self: Sized;

    /// **Static** TCB manifest, when the whole subtree is statically known. `None`
    /// for a future dynamic/wrapper language. **Canonical when present**: `tree(L)`
    /// is *defined* by it, and it is the source of truth `admits`/`extends` must
    /// not exceed. Identity is the `TypeId`; **no names** (those are a separate,
    /// untrusted overlay trait).
    const MANIFEST: Option<&'static Manifest>;
}

/// The TCB as raw type identities — a compile-time tree of `TypeId`s (no names).
/// `&'static` children so it lives in a `const`/`static`.
#[derive(Debug)]
pub struct Manifest {
    /// Identity of the language this manifest describes.
    pub ty: TypeId,
    /// Direct parents' manifests.
    pub extends: &'static [Manifest],
    /// Direct rules admitted by this language.
    pub admits: &'static [RuleRecord],
    /// Extension seam (minimal today).
    pub metadata: LangMeta,
}

/// A direct-rule entry in a [`Manifest`].
#[derive(Debug)]
pub struct RuleRecord {
    /// Identity of the rule — its own `TypeId` (a [`Rule`]/[`CanonRule`] type).
    pub ty: TypeId,
    /// Extension seam for polymorphic rules / `rule@type` (minimal today).
    pub metadata: RuleMeta,
}

/// Minimal language metadata (extension seam).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct LangMeta;

/// Minimal rule metadata (extension seam).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct RuleMeta;

/// A general gated rule, phrased as a **decision procedure**: given an `Input` and
/// a **read-only** view of the language, it either fails or proposes a boolean
/// conclusion `Concl`. Applying it via [`apply`](crate::apply) is gated on
/// **`Self`'s own `TypeId`** being admitted.
///
/// - `Input` is the freely-constructible thing consumed: `()` for a nullary axiom
///   (use [`apply0`](crate::apply0)); an [`Eqn`](crate::Eqn) to *validate* a
///   proposed equation; a bare expression to *rewrite*.
/// - `Concl` is the proposition concluded, bounded `: Expr<Ty = bool>`. An equality
///   rule sets `Concl = Eqn<A, B>` — which, being an `Expr<Ty = bool>`, forces `A`
///   and `B` to the same sort, so the same-sort constraint is now *internal* (no
///   separate `Lhs`/`Rhs` associated types needed).
/// - `decide` is UNTRUSTED (it only proposes); the single gated mint is in
///   [`apply`](crate::apply), which ignores this output until *after* the
///   `admits` check.
///
/// Keying the gate on `Self` (not a separate, implementor-chosen tag) is
/// **load-bearing**: the gate identity must be the very type whose `decide`
/// produces the conclusion, so a downstream crate cannot impersonate an admitted
/// rule. The orphan rule then blocks `impl Rule<L> for SomeFrameworkRule`, so an
/// admit-set entry cannot be "borrowed" by an unrelated conclusion. (A `'static`
/// bound is required for the `TypeId`; non-`'static`/borrowing rules need a
/// *sealed*, behaviour-tied identity mechanism — deferred, see source-local TODO markers.)
///
/// The language is passed by **shared reference** (`&L`): reading context is
/// enough, and it keeps the value available to mint against afterwards. A future
/// genuinely-linear/resource theory wants a by-value variant (making context
/// enrichment visible in the type) — deferred, see source-local TODO markers.
pub trait Rule<L>: 'static {
    /// The candidate / input consumed. Freely constructible.
    type Input;
    /// The boolean proposition concluded (e.g. `Eqn<A, B>` for an equality rule).
    type Concl: Expr<Ty = bool>;
    /// Inspect the input + read-only language, returning the conclusion to bless or
    /// failing.
    fn decide(self, input: Self::Input, lang: &L) -> Result<Self::Concl, Error>;
}

/// An op that is also its own canonical evaluation rule: `App<Self, Val(v)>`
/// canonically equals `Val(eval(v))`. Using it via [`canon`](crate::canon) is
/// gated on `Self`'s `TypeId` being admitted — so you may always *write*
/// `App<F, _>` (uninterpreted ⇒ sound by vacuity), but only *reduce* it where `F`
/// is in your TCB.
pub trait CanonRule: Op + 'static {
    /// Evaluate the operator on a ground input value. Returns `None` to REFUSE (the
    /// op declines on an unrepresentable input); the mint only fires on `Some`.
    fn eval(&self, arg: &Self::In) -> Option<Self::Out>;
}
