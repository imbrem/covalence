//! The **theory bundle**: what a backend realizes from a spec, and the
//! contract its theorems obey.
//!
//! # The contract
//!
//! Let `spec` have constructors `C₀ … C_{n-1}` and let the bundle provide
//! the carrier `ty`, the membership predicate `mem : ty → bool`, and the
//! constructor terms `ctors[i]` (each a term of type `A₁ → … → Aₖ → ty`,
//! applied by ordinary application). Conventions:
//!
//! - **Applied form.** Wherever a statement below writes `P x` or `mem x`,
//!   the term is the *application* `P · x` — not β-reduced. Backends and
//!   consumers meet at this shape (β-massage locally as needed).
//! - **Membership relativization.** Induction and cases guard with `mem`.
//!   Exact-type backends have `mem = λt. ⊤` and supply
//!   [`InductiveFacts::mem_trivial`] to discharge guards.
//! - **Recursion is iteration** (catamorphism): the recursor takes one
//!   *step* per constructor, `stepᵢ : B₁ → … → Bₖ → β` where `Bⱼ = β` at
//!   recursive positions and the external type elsewhere; recursive
//!   arguments are *not* passed raw. (A primitive-recursion variant that
//!   also passes the raw arguments is a later, additive extension — some
//!   backends cannot deliver it.)
//! - **Observation instances.** For representation-polymorphic carriers
//!   (e.g. a Church encoding `S⟨'r⟩`), the *freeness* statements take
//!   their constructor-equation antecedent at a backend-chosen concrete
//!   **observation instance** of the carrier (the theorem displays it);
//!   exact-type backends state them at the carrier itself. Consumers that
//!   need a specific instance instantiate their equation before applying
//!   the fact.
//! - **Reserved names.** Constructor argument binder hints (from the spec)
//!   are used as free-variable names inside generated statements; motives
//!   and steps must not use them (or the bundle's internal `__`-prefixed
//!   names) as their own free variables. Violations surface as rule
//!   errors, never as unsound theorems.
//!
//! The facts:
//!
//! ```text
//! comp(steps, i)     ⊢ ∀x⃗. rec steps (Cᵢ x⃗) = stepᵢ x⃗ʳ        (x⃗ʳ = x⃗ with
//!                       recursive xⱼ replaced by rec steps xⱼ)
//! injective(i,k,x⃗,y⃗) ⊢ (Cᵢ x⃗ = Cᵢ y⃗) ⟹ xₖ = yₖ               (at the obs.
//!                       instance; may be Unsupported at Rec positions)
//! distinct(i,j,x⃗,y⃗)  ⊢ (Cᵢ x⃗ = Cⱼ y⃗) ⟹ F                     (i ≠ j)
//! induct(P, cases)   ⊢ ∀t. mem t ⟹ P t                        given, per i:
//!                       casesᵢ = ⊢ P r₁ ⟹ … ⟹ P rₘ ⟹ P (Cᵢ x⃗)  (curried
//!                       IHs for the recursive args, free x⃗ named by hints)
//! cases()            ⊢ ∀t. mem t ⟹ (D₀ ∨ (D₁ ∨ …))            with
//!                       Dᵢ = ∃x⃗. t = Cᵢ x⃗
//! mem_ctor(i,x⃗,ms)   ⊢ mem (Cᵢ x⃗)                              given
//!                       ms = the ⊢ mem xⱼ for the recursive positions
//! ```
//!
//! Theorems are behind **rule-form methods**, not eager fields: several are
//! schematic (induction takes a motive; freeness is wanted at specific
//! argument tuples — in a Metamath-style substrate a scheme is applied by
//! substitution, not ∀-instantiated), costs differ per backend, and a
//! backend can serve extra derived facts later without churn.

use crate::error::{IndResult, InductiveError};
use crate::logic::{Logic, LogicOps};
use crate::spec::InductiveSpec;

/// Honest capability flags for a realized bundle. Consumers that depend on
/// an optional capability check here (or handle
/// [`InductiveError::Unsupported`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BackendCaps {
    /// The carrier is exact: `⊢ ∀t. mem t` is available
    /// ([`InductiveFacts::mem_trivial`] returns `Some`).
    pub mem_trivial: bool,
    /// Injectivity is available at **recursive** argument positions.
    /// (Rank-1 Church/impredicative encodings cannot deliver it — the
    /// subtree-recovery wall; carved/exact representations can.)
    pub rec_injective: bool,
}

/// The theorem surface of a realized inductive type. See the [module
/// docs](self) for the exact statement contract.
pub trait InductiveFacts<L: Logic> {
    /// The recursor applied: `rec steps t` as a term. `steps` in
    /// constructor order (see the module docs for step types).
    fn rec_app(&self, steps: &[L::Term], t: &L::Term) -> IndResult<L::Term, L>;

    /// Computation law for constructor `i`:
    /// `⊢ ∀x⃗. rec steps (Cᵢ x⃗) = stepᵢ x⃗ʳ`, ∀-closed over the constructor
    /// arguments (recursive arguments appear as their `rec`-images on the
    /// right).
    fn comp(&self, steps: &[L::Term], i: usize) -> IndResult<L::Thm, L>;

    /// Injectivity of `Cᵢ` at argument position `k`:
    /// `⊢ (Cᵢ x⃗ = Cᵢ y⃗) ⟹ xₖ = yₖ`, the antecedent at the backend's
    /// observation instance. `xs`/`ys` are full argument tuples.
    ///
    /// May return [`InductiveError::Unsupported`] at `Rec` positions —
    /// check [`BackendCaps::rec_injective`].
    fn injective(&self, i: usize, k: usize, xs: &[L::Term], ys: &[L::Term])
    -> IndResult<L::Thm, L>;

    /// Distinctness: `⊢ (Cᵢ x⃗ = Cⱼ y⃗) ⟹ F` for `i ≠ j`, the antecedent at
    /// the backend's observation instance.
    fn distinct(&self, i: usize, j: usize, xs: &[L::Term], ys: &[L::Term]) -> IndResult<L::Thm, L>;

    /// Rule-form structural induction: given the motive `P : ty → bool`
    /// and one case proof per constructor (see the module docs for the
    /// exact case shape), conclude `⊢ ∀t. mem t ⟹ P t`.
    fn induct(&self, motive: &L::Term, cases: Vec<L::Thm>) -> IndResult<L::Thm, L>;

    /// Exhaustiveness: `⊢ ∀t. mem t ⟹ ⋁ᵢ ∃x⃗. t = Cᵢ x⃗` (right-nested
    /// disjunction in constructor order).
    fn cases(&self) -> IndResult<L::Thm, L>;

    /// Constructor membership: `⊢ mem (Cᵢ x⃗)` given proofs `⊢ mem xⱼ` for
    /// the recursive argument positions (in positional order). `args` is
    /// the full argument tuple.
    fn mem_ctor(&self, i: usize, args: &[L::Term], rec_mems: Vec<L::Thm>) -> IndResult<L::Thm, L>;

    /// `⊢ ∀t. mem t` — `Some` for exact-type backends, `None` for
    /// junk-carrying carriers.
    fn mem_trivial(&self) -> Option<L::Thm>;

    /// Capability flags for this bundle.
    fn caps(&self) -> BackendCaps;
}

/// What a backend realizes from a spec: the carrier, the membership
/// predicate, the constructor terms, and the theorem surface.
///
/// `ty` is **opaque** to consumers — nothing outside the backend should
/// assume what the carrier is; everything flows through `mem`, `ctors`,
/// and `facts`. That opacity is what makes backends swappable within a
/// logic.
pub struct InductiveTheory<L: Logic> {
    /// The spec this bundle realizes.
    pub spec: InductiveSpec<L::Type>,
    /// The carrier type (opaque).
    pub ty: L::Type,
    /// The membership predicate `mem : ty → bool`, as a term.
    pub mem: L::Term,
    /// The constructor terms, in spec order; `ctors[i]` has type
    /// `A₁ → … → Aₖ → ty` (a constant of type `ty` when nullary).
    pub ctors: Vec<L::Term>,
    /// The theorem surface.
    pub facts: Box<dyn InductiveFacts<L>>,
}

impl<L: Logic> InductiveTheory<L> {
    /// The constructor term for index `i`.
    pub fn ctor(&self, i: usize) -> IndResult<&L::Term, L> {
        self.ctors.get(i).ok_or(InductiveError::CtorIndex {
            index: i,
            arity: self.ctors.len(),
        })
    }

    /// `Cᵢ x⃗` — the constructor applied to an argument tuple (applied
    /// form), built through the logic's ops.
    pub fn ctor_app(&self, logic: &L, i: usize, args: &[L::Term]) -> IndResult<L::Term, L>
    where
        L: LogicOps,
    {
        let spec_arity = self
            .spec
            .ctors
            .get(i)
            .ok_or(InductiveError::CtorIndex {
                index: i,
                arity: self.spec.ctors.len(),
            })?
            .arity();
        if args.len() != spec_arity {
            return Err(InductiveError::Arity {
                what: "ctor_app arguments",
                expected: spec_arity,
                got: args.len(),
            });
        }
        let mut t = self.ctor(i)?.clone();
        for a in args {
            t = logic.app(t, a.clone())?;
        }
        Ok(t)
    }

    /// `mem t` — the membership guard applied to a term (applied form).
    pub fn mem_app(&self, logic: &L, t: &L::Term) -> IndResult<L::Term, L>
    where
        L: LogicOps,
    {
        Ok(logic.app(self.mem.clone(), t.clone())?)
    }

    /// The **case obligation** for constructor `i` under `motive`: the
    /// exact term a consumer must prove to feed
    /// [`InductiveFacts::induct`] —
    /// `motive r₁ ⟹ … ⟹ motive rₘ ⟹ motive (Cᵢ x⃗)` over free variables
    /// `x⃗` named by the spec's binder hints (recursive arguments typed at
    /// the carrier, external ones at their sort).
    pub fn case_obligation(&self, logic: &L, motive: &L::Term, i: usize) -> IndResult<L::Term, L>
    where
        L: LogicOps,
    {
        let ctor = self.spec.ctors.get(i).ok_or(InductiveError::CtorIndex {
            index: i,
            arity: self.spec.ctors.len(),
        })?;
        let args: Vec<L::Term> = ctor
            .args
            .iter()
            .map(|(n, s)| {
                let ty = match s {
                    crate::spec::ArgSort::Rec => self.ty.clone(),
                    crate::spec::ArgSort::Ext(x) => x.clone(),
                };
                logic.var(n, ty)
            })
            .collect();
        let mut goal = logic.app(motive.clone(), self.ctor_app(logic, i, &args)?)?;
        for k in ctor.rec_positions().collect::<Vec<_>>().into_iter().rev() {
            let ih = logic.app(motive.clone(), args[k].clone())?;
            goal = logic.imp(ih, goal)?;
        }
        Ok(goal)
    }
}
