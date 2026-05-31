//! Proof-object layer: `Context`, `Prop`, and `Thm`.
//!
//! - `Prop` is the data of an asserted proposition — a context and a
//!   conclusion term. Anyone can construct a `Prop`; it carries no
//!   guarantee of truth.
//! - `Thm` wraps a `Prop` with a marker that the kernel has verified
//!   it via one of the inference-rule constructors. External code
//!   cannot construct a `Thm` directly — only by calling
//!   `Thm::refl` / `Thm::assume` / future rules.
//! - `Context` is a linked chain of assumption `Prop`s. New
//!   assumptions stack on top via `Context::extend`; the chain is
//!   shared across `Arc` so multiple `Thm`s can refer to the same
//!   context cheaply.
//!
//! Soundness story:
//! - Each inference rule's constructor on `Thm` is a trusted unit.
//!   The rule's body proves that the resulting `Prop` follows from
//!   the kernel's logic.
//! - `Thm`s aren't pinned to an `Arc<Arena>`; they hold a `TermId`
//!   that's interpreted against whatever arena the caller pairs
//!   them with. The caller must use the same arena that the `Thm`
//!   was built against — using a different arena risks meaning
//!   drift (since `rewrite` can change a term's structural form).

use std::sync::Arc;

use crate::arena::Arena;
use crate::id::{StrId, TermId};
use crate::primop::{PrimOp1, PrimOp2};
use crate::reduce;
use crate::term::{TermDef, TermRef};
use crate::ty::TypeRef;

// ---------------------------------------------------------------------------
// Context
// ---------------------------------------------------------------------------

/// A chain of assumptions. New assumptions stack via
/// [`Context::extend`]; older ones live in `parent`. Sharing via
/// `Arc` is cheap.
#[derive(Debug)]
pub struct Context {
    /// Assumptions added at this level (oldest first). The parent's
    /// assumptions chain through `parent`.
    locals: Vec<Arc<Prop>>,
    /// Parent context (or `None` if this is the root).
    parent: Option<Arc<Context>>,
}

impl Context {
    /// The empty (root) context — no assumptions.
    pub fn empty() -> Arc<Self> {
        Arc::new(Self {
            locals: Vec::new(),
            parent: None,
        })
    }

    /// Extend a context with an additional assumption.
    pub fn extend(parent: Arc<Self>, assumption: Arc<Prop>) -> Arc<Self> {
        Arc::new(Self {
            locals: vec![assumption],
            parent: Some(parent),
        })
    }

    /// Total number of assumptions including ancestors.
    pub fn len(&self) -> usize {
        self.parent.as_ref().map_or(0, |p| p.len()) + self.locals.len()
    }

    /// True iff no assumptions are in scope.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Get the i-th assumption (0-indexed, oldest first). Walks the
    /// chain through `parent`.
    pub fn assumption(&self, i: usize) -> Option<&Arc<Prop>> {
        let parent_len = self.parent.as_ref().map_or(0, |p| p.len());
        if i < parent_len {
            self.parent.as_ref().unwrap().assumption(i)
        } else {
            self.locals.get(i - parent_len)
        }
    }

    /// The parent context, or `None` at the root.
    pub fn parent(&self) -> Option<&Arc<Context>> {
        self.parent.as_ref()
    }

    /// Does this context contain the given `Prop` (by `Arc::ptr_eq`
    /// identity) anywhere in its chain?
    pub fn contains_prop(&self, p: &Arc<Prop>) -> bool {
        if self.locals.iter().any(|a| Arc::ptr_eq(a, p)) {
            return true;
        }
        if let Some(parent) = &self.parent {
            return parent.contains_prop(p);
        }
        false
    }
}

// ---------------------------------------------------------------------------
// Prop
// ---------------------------------------------------------------------------

/// An *unverified* proposition — a context plus a conclusion term.
/// Anyone may construct a `Prop`; the kernel makes no claim about
/// truth.
///
/// Verified propositions are [`Thm`]s, which wrap a `Prop` with a
/// kernel-only constructor.
#[derive(Debug, Clone)]
pub struct Prop {
    pub context: Arc<Context>,
    pub concl: TermId,
}

impl Prop {
    /// Build a `Prop` from a context and conclusion. **No checks** —
    /// the conclusion isn't required to be a `bool`-typed term.
    /// Lifting to `Thm` (which is what enforces correctness) is the
    /// validation step.
    pub fn new(context: Arc<Context>, concl: TermId) -> Self {
        Self { context, concl }
    }
}

// ---------------------------------------------------------------------------
// Thm — kernel-verified proposition
// ---------------------------------------------------------------------------

/// A kernel-verified `Prop`. Constructible only via the inference-
/// rule methods below (or future rules); cannot be built by external
/// code from a bare `Prop`.
#[derive(Debug, Clone)]
pub struct Thm {
    prop: Prop,
}

impl Thm {
    /// Read-only access to the wrapped `Prop`.
    pub fn prop(&self) -> &Prop {
        &self.prop
    }

    /// The proof's context.
    pub fn context(&self) -> &Arc<Context> {
        &self.prop.context
    }

    /// The proof's conclusion `TermId`.
    pub fn concl(&self) -> TermId {
        self.prop.concl
    }

    // ---- inference rules ---------------------------------------------------

    /// **Reflexivity.** Build the `Thm` `ctx ⊢ t = t` for any
    /// well-typed term `t`. Allocates `Eq(t, t)` in the arena.
    pub fn refl(arena: &mut Arena, ctx: Arc<Context>, t: TermId) -> Result<Self, ProofError> {
        if !arena.is_well_typed(t) {
            return Err(ProofError::IllTypedInput);
        }
        let eq = arena.alloc_term(TermDef::Eq(TermRef::local(t), TermRef::local(t)));
        Ok(Self {
            prop: Prop::new(ctx, eq),
        })
    }

    /// **Assumption rule.** If `assumption` is a well-typed `Prop`
    /// in `ctx`, derive the `Thm` `ctx ⊢ assumption.concl`.
    pub fn assume(
        arena: &Arena,
        ctx: Arc<Context>,
        assumption: Arc<Prop>,
    ) -> Result<Self, ProofError> {
        if !ctx.contains_prop(&assumption) {
            return Err(ProofError::AssumptionNotInContext);
        }
        if !arena.is_well_typed(assumption.concl) {
            return Err(ProofError::IllTypedInput);
        }
        Ok(Self {
            prop: Prop::new(ctx, assumption.concl),
        })
    }

    /// **Weakening / add-assumption.** Take a Thm `ctx ⊢ q` and a
    /// well-typed `Prop` `p`; produce `ctx, p ⊢ q`.
    pub fn add_assumption(
        self,
        arena: &Arena,
        new_assumption: Arc<Prop>,
    ) -> Result<Self, ProofError> {
        if !arena.is_well_typed(new_assumption.concl) {
            return Err(ProofError::IllTypedInput);
        }
        let new_ctx = Context::extend(self.prop.context, new_assumption);
        Ok(Self {
            prop: Prop::new(new_ctx, self.prop.concl),
        })
    }

    /// **Ex falso → negation.** From a Thm `ctx ⊢ False` and a
    /// well-typed proposition `p`, derive `ctx ⊢ ¬p`.
    pub fn not_from_false(
        arena: &mut Arena,
        thm_false: Thm,
        p: TermId,
    ) -> Result<Self, ProofError> {
        if !arena.is_well_typed(p) {
            return Err(ProofError::IllTypedInput);
        }
        if !matches!(arena.term_def(thm_false.prop.concl), TermDef::False) {
            return Err(ProofError::ConclusionNotFalse);
        }
        let not_p = arena.alloc_term(TermDef::Op1(PrimOp1::LogicalNot, TermRef::local(p)));
        Ok(Self {
            prop: Prop::new(thm_false.prop.context, not_p),
        })
    }

    /// **Symmetry of equality.** From `ctx ⊢ a = b`, derive
    /// `ctx ⊢ b = a`.
    pub fn sym(arena: &mut Arena, thm: Thm) -> Result<Self, ProofError> {
        if !arena.is_well_typed(thm.prop.concl) {
            return Err(ProofError::IllTypedInput);
        }
        let (a, b) = match *arena.term_def(thm.prop.concl) {
            TermDef::Eq(a, b) => (a, b),
            _ => return Err(ProofError::ExpectedEquality),
        };
        let flipped = arena.alloc_term(TermDef::Eq(b, a));
        Ok(Self {
            prop: Prop::new(thm.prop.context, flipped),
        })
    }

    /// **Transitivity of equality.** From `ctx ⊢ a = b` and
    /// `ctx ⊢ b' = c` where `b ≡ b'` at UF level 0, derive
    /// `ctx ⊢ a = c`. Contexts must match.
    pub fn trans(arena: &mut Arena, ab: Thm, bc: Thm) -> Result<Self, ProofError> {
        if !arena.is_well_typed(ab.prop.concl) || !arena.is_well_typed(bc.prop.concl) {
            return Err(ProofError::IllTypedInput);
        }
        if !Arc::ptr_eq(&ab.prop.context, &bc.prop.context) {
            return Err(ProofError::ContextMismatch);
        }
        let (a, b1) = match *arena.term_def(ab.prop.concl) {
            TermDef::Eq(l, r) => (l, r),
            _ => return Err(ProofError::ExpectedEquality),
        };
        let (b2, c) = match *arena.term_def(bc.prop.concl) {
            TermDef::Eq(l, r) => (l, r),
            _ => return Err(ProofError::ExpectedEquality),
        };
        if !arena.eq_at_level_0(b1, b2) {
            return Err(ProofError::MidpointMismatch);
        }
        let ac = arena.alloc_term(TermDef::Eq(a, c));
        Ok(Self {
            prop: Prop::new(ab.prop.context, ac),
        })
    }

    /// **Equality modus ponens.** From `ctx ⊢ p = q` and `ctx ⊢ p'`
    /// where `p ≡ p'` at UF level 0, derive `ctx ⊢ q`.
    pub fn eq_mp(arena: &mut Arena, pq: Thm, p_thm: Thm) -> Result<Self, ProofError> {
        if !arena.is_well_typed(pq.prop.concl) || !arena.is_well_typed(p_thm.prop.concl) {
            return Err(ProofError::IllTypedInput);
        }
        if !Arc::ptr_eq(&pq.prop.context, &p_thm.prop.context) {
            return Err(ProofError::ContextMismatch);
        }
        let (p, q) = match *arena.term_def(pq.prop.concl) {
            TermDef::Eq(l, r) => (l, r),
            _ => return Err(ProofError::ExpectedEquality),
        };
        if !arena.eq_at_level_0(p, TermRef::local(p_thm.prop.concl)) {
            return Err(ProofError::LhsMismatch);
        }
        let q_id = q.as_local().ok_or(ProofError::ForeignConclusion)?;
        Ok(Self {
            prop: Prop::new(pq.prop.context, q_id),
        })
    }

    /// **Modus ponens.** From `ctx ⊢ Imp(p, q)` and `ctx ⊢ p'` where
    /// `p ≡ p'` at UF level 0, derive `ctx ⊢ q`.
    pub fn mp(arena: &mut Arena, imp: Thm, ant: Thm) -> Result<Self, ProofError> {
        if !arena.is_well_typed(imp.prop.concl) || !arena.is_well_typed(ant.prop.concl) {
            return Err(ProofError::IllTypedInput);
        }
        if !Arc::ptr_eq(&imp.prop.context, &ant.prop.context) {
            return Err(ProofError::ContextMismatch);
        }
        let (p, q) = match *arena.term_def(imp.prop.concl) {
            TermDef::Op2(PrimOp2::LogicalImp, p, q) => (p, q),
            _ => return Err(ProofError::ExpectedImplication),
        };
        if !arena.eq_at_level_0(p, TermRef::local(ant.prop.concl)) {
            return Err(ProofError::LhsMismatch);
        }
        let q_id = q.as_local().ok_or(ProofError::ForeignConclusion)?;
        Ok(Self {
            prop: Prop::new(imp.prop.context, q_id),
        })
    }

    /// **General congruence.** If `a` and `b` are structurally
    /// congruent walking children to depth `depth` (i.e.
    /// [`Arena::eq_at_level`] returns true), derive
    /// `ctx ⊢ a = b`.
    ///
    /// This is the kernel's *only* rule exempt from the well-typed
    /// input invariant — congruence reasons about the term shape
    /// alone, not its type. `MK_COMB` (the classical HOL rule) is
    /// the special case `depth = 1` applied to two `Comb` shells:
    /// it falls out of this rule with no extra primitive.
    pub fn cong(
        arena: &mut Arena,
        ctx: Arc<Context>,
        a: TermRef,
        b: TermRef,
        depth: u32,
    ) -> Result<Self, ProofError> {
        if !arena.eq_at_level(a, b, depth) {
            return Err(ProofError::NotCongruent);
        }
        let eq = arena.alloc_term(TermDef::Eq(a, b));
        Ok(Self {
            prop: Prop::new(ctx, eq),
        })
    }

    /// **β-reduction.** Given a well-typed redex
    /// `comb = Comb(Abs(α, body), arg)`, derive
    /// `ctx ⊢ comb = body[Bound(0) := arg]`.
    pub fn beta(
        arena: &mut Arena,
        ctx: Arc<Context>,
        comb: TermId,
    ) -> Result<Self, ProofError> {
        if !arena.is_well_typed(comb) {
            return Err(ProofError::IllTypedInput);
        }
        let (abs_ref, arg_ref) = match *arena.term_def(comb) {
            TermDef::Comb(f, x) => (f, x),
            _ => return Err(ProofError::ExpectedBetaRedex),
        };
        let abs_id = abs_ref.as_local().ok_or(ProofError::ExpectedBetaRedex)?;
        let body_ref = match *arena.term_def(abs_id) {
            TermDef::Abs(_, body) => body,
            _ => return Err(ProofError::ExpectedBetaRedex),
        };
        let reduced = arena.subst(body_ref, 0, arg_ref);
        let eq = arena.alloc_term(TermDef::Eq(TermRef::local(comb), reduced));
        Ok(Self {
            prop: Prop::new(ctx, eq),
        })
    }

    /// **Abstraction (`ABS`).** From `ctx ⊢ s = t`, derive
    /// `ctx ⊢ (λ(name: ty). s) = (λ(name: ty). t)` — i.e. bind the
    /// free variable `Free(name, ty)` in both sides under a fresh
    /// `Abs(ty, _)`.
    ///
    /// The classical side condition: `Free(name, ty)` must **not**
    /// appear free in any assumption of `ctx`. Otherwise the binder
    /// would capture the assumption's variable, breaking
    /// substitutivity. Returns
    /// [`ProofError::VariableEscapesAssumption`] if violated.
    pub fn abs(
        arena: &mut Arena,
        thm: Thm,
        name: StrId,
        ty: TypeRef,
    ) -> Result<Self, ProofError> {
        if !arena.is_well_typed(thm.prop.concl) {
            return Err(ProofError::IllTypedInput);
        }
        let (s, t) = match *arena.term_def(thm.prop.concl) {
            TermDef::Eq(l, r) => (l, r),
            _ => return Err(ProofError::ExpectedEquality),
        };
        let ctx = thm.prop.context.clone();
        for i in 0..ctx.len() {
            let assum = ctx.assumption(i).expect("len/index invariant");
            if arena.contains_free(TermRef::local(assum.concl), name, ty) {
                return Err(ProofError::VariableEscapesAssumption);
            }
        }
        let s_body = arena.abstract_over(s, name, ty, 0);
        let t_body = arena.abstract_over(t, name, ty, 0);
        let s_abs = arena.alloc_term(TermDef::Abs(ty, s_body));
        let t_abs = arena.alloc_term(TermDef::Abs(ty, t_body));
        let eq = arena.alloc_term(TermDef::Eq(TermRef::local(s_abs), TermRef::local(t_abs)));
        Ok(Self {
            prop: Prop::new(thm.prop.context, eq),
        })
    }

    /// **Top-level reduction.** Apply one rule from the §10 catalog
    /// (literal-arg evaluation, numeral normalisation, `Comb(Id, _)`,
    /// `Comb(Ite(lit, _), _)`, …) to `t` and derive
    /// `ctx ⊢ t = reduce::step(t)`.
    ///
    /// Returns [`ProofError::NotReducible`] if no rule fires.
    /// Requires `t` to be well-typed — like every non-congruence
    /// rule.
    pub fn reduce(
        arena: &mut Arena,
        ctx: Arc<Context>,
        t: TermId,
    ) -> Result<Self, ProofError> {
        if !arena.is_well_typed(t) {
            return Err(ProofError::IllTypedInput);
        }
        let reduced = reduce::step(arena, TermRef::local(t)).ok_or(ProofError::NotReducible)?;
        let eq = arena.alloc_term(TermDef::Eq(TermRef::local(t), reduced));
        Ok(Self {
            prop: Prop::new(ctx, eq),
        })
    }
}

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

/// Errors returned by the inference rules.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProofError {
    /// The assumption Prop isn't in the context chain.
    AssumptionNotInContext,
    /// `not_from_false` requires the Thm's conclusion to be the
    /// literal `False`.
    ConclusionNotFalse,
    /// A rule expected the Thm's conclusion to be an `Eq` shape.
    ExpectedEquality,
    /// `trans` / `eq_mp`: the two Thms have different contexts.
    /// Use `add_assumption` to align them first.
    ContextMismatch,
    /// `trans`: the two equalities' midpoint terms aren't equal at
    /// UF level 0.
    MidpointMismatch,
    /// `eq_mp`: the equality's LHS doesn't match the second Thm's
    /// conclusion at UF level 0.
    LhsMismatch,
    /// `eq_mp`: the equality's RHS is a foreign ref. The kernel
    /// can't yet record a foreign conclusion as a Thm.
    ForeignConclusion,
    /// `mp`: the Thm's conclusion isn't an `Op2(LogicalImp, _, _)`.
    ExpectedImplication,
    /// `beta`: the term isn't a `Comb(Abs(_, _), _)` shape.
    ExpectedBetaRedex,
    /// One of the Thm rule's term inputs isn't well-typed
    /// (`TypeInfo::Typed`). Congruence (`cong`) is the only rule
    /// exempt; all others require their inputs to type-check.
    IllTypedInput,
    /// `cong`: the two terms aren't congruent at the requested depth.
    NotCongruent,
    /// `reduce`: no §10 rule fires on the given term.
    NotReducible,
    /// `abs`: the variable being abstracted occurs free in one of
    /// the context's assumptions — would be captured by the binder.
    VariableEscapesAssumption,
}

impl std::fmt::Display for ProofError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProofError::AssumptionNotInContext => {
                write!(f, "assumption is not in the supplied context")
            }
            ProofError::ConclusionNotFalse => {
                write!(f, "expected the Thm's conclusion to be False")
            }
            ProofError::ExpectedEquality => write!(f, "expected an Eq conclusion"),
            ProofError::ContextMismatch => write!(f, "contexts do not match"),
            ProofError::MidpointMismatch => write!(f, "equalities do not chain"),
            ProofError::LhsMismatch => write!(f, "equality LHS does not match Thm conclusion"),
            ProofError::ForeignConclusion => {
                write!(f, "equality RHS is a foreign ref; cannot record as Thm conclusion")
            }
            ProofError::ExpectedImplication => write!(f, "expected an Imp conclusion"),
            ProofError::ExpectedBetaRedex => write!(f, "expected a Comb(Abs(_, _), _) redex"),
            ProofError::IllTypedInput => write!(f, "rule input is not well-typed"),
            ProofError::NotCongruent => write!(f, "terms are not congruent at the requested depth"),
            ProofError::NotReducible => write!(f, "no reduction rule fires on this term"),
            ProofError::VariableEscapesAssumption => {
                write!(f, "abstraction variable occurs free in an assumption")
            }
        }
    }
}

impl std::error::Error for ProofError {}
