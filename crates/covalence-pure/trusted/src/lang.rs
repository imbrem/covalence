//! Languages (= theories = rulesets), the static `Manifest` tree, and the two
//! gated-rule traits ([`Rule`], [`CanonRule`]).

use std::any::TypeId;

use crate::eqn::Error;
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
    ///   requires the apply-in-home + [`lift`](crate::Eqn::lift) composition).
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
    /// Identity of the rule — its own `TypeId` (a `Rule`/`CanonRule` type, or a
    /// `TeqRule<C>` marker).
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

/// A general gated rule: its premises/data ride inside `self`, and `conclude`
/// produces the two sides of an [`Eqn`](crate::Eqn). Applying it via
/// [`apply`](crate::apply) is gated on **`Self`'s own `TypeId`** being admitted.
///
/// Keying on `Self` (not a separate, implementor-chosen tag) is **load-bearing**:
/// the gate identity must be the very type whose `conclude` produces the equation,
/// so a downstream crate cannot impersonate an admitted rule. The orphan rule then
/// blocks `impl Rule<L> for SomeFrameworkRule`, so an admit-set entry cannot be
/// "borrowed" by an unrelated conclusion. (A `'static` bound is required for the
/// `TypeId`; non-`'static`/borrowing rules need a *sealed*, behaviour-tied identity
/// mechanism — deferred, see SKELETONS.)
pub trait Rule<L>: 'static {
    /// Left side of the concluded equation.
    type Lhs;
    /// Right side of the concluded equation.
    type Rhs;
    /// Run the rule, yielding the two sides of the equation it concludes.
    fn conclude(self) -> Result<(Self::Lhs, Self::Rhs), Error>;
}

/// An op that is also its own canonical evaluation rule: `App<Self, Val(v)>`
/// canonically equals `Val(eval(v))`. Using it via [`canon`](crate::canon) is
/// gated on `Self`'s `TypeId` being admitted — so you may always *write*
/// `App<F, _>` (uninterpreted ⇒ sound by vacuity), but only *reduce* it where `F`
/// is in your TCB.
pub trait CanonRule: Op + 'static {
    /// Evaluate the operator on a ground input value.
    fn eval(&self, arg: &Self::In) -> Self::Out;
}
