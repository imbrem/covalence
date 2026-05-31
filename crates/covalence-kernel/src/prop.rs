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
use crate::id::TermId;
use crate::primop::PrimOp1;
use crate::term::{TermDef, TermRef};

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

    /// **Reflexivity.** Build the `Thm` `ctx ⊢ t = t` for any term `t`.
    ///
    /// Internally allocates the `Eq(t, t)` term in the arena. The
    /// resulting `Thm`'s conclusion is the `TermId` of that fresh
    /// equality.
    pub fn refl(arena: &mut Arena, ctx: Arc<Context>, t: TermId) -> Self {
        let eq = arena.alloc_term(TermDef::Eq(TermRef::local(t), TermRef::local(t)));
        Self {
            prop: Prop::new(ctx, eq),
        }
    }

    /// **Assumption rule.** If `assumption` is a `Prop` in `ctx`,
    /// derive the `Thm` `ctx ⊢ assumption.concl`.
    ///
    /// Returns `Err(ProofError::AssumptionNotInContext)` if the
    /// `Prop` isn't part of the supplied context (by `Arc::ptr_eq`
    /// identity).
    pub fn assume(ctx: Arc<Context>, assumption: Arc<Prop>) -> Result<Self, ProofError> {
        if !ctx.contains_prop(&assumption) {
            return Err(ProofError::AssumptionNotInContext);
        }
        Ok(Self {
            prop: Prop::new(ctx, assumption.concl),
        })
    }

    /// **Weakening / add-assumption.** Take a Thm `ctx ⊢ q` and a
    /// fresh `Prop` `p`; produce `ctx, p ⊢ q`. The new assumption is
    /// stacked on top of the old context.
    ///
    /// Always succeeds — adding an assumption never invalidates a
    /// proof.
    pub fn add_assumption(self, new_assumption: Arc<Prop>) -> Self {
        let new_ctx = Context::extend(self.prop.context, new_assumption);
        Self {
            prop: Prop::new(new_ctx, self.prop.concl),
        }
    }

    /// **Ex falso → negation.** From a Thm `ctx ⊢ False`, derive
    /// `ctx ⊢ ¬p` for an arbitrary proposition `p`. The new
    /// conclusion is `Op1(LogicalNot, p)`, allocated in the arena.
    ///
    /// Soundness: anything follows from False, including `¬p`.
    ///
    /// Returns `Err(ProofError::ConclusionNotFalse)` if `thm`'s
    /// conclusion isn't the literal `False`.
    pub fn not_from_false(
        arena: &mut Arena,
        thm_false: Thm,
        p: TermId,
    ) -> Result<Self, ProofError> {
        if !matches!(arena.term_def(thm_false.prop.concl), TermDef::False) {
            return Err(ProofError::ConclusionNotFalse);
        }
        let not_p = arena.alloc_term(TermDef::Op1(PrimOp1::LogicalNot, TermRef::local(p)));
        Ok(Self {
            prop: Prop::new(thm_false.prop.context, not_p),
        })
    }

    /// **Symmetry of equality.** From `ctx ⊢ a = b`, derive
    /// `ctx ⊢ b = a`. The new equality is allocated in the arena.
    ///
    /// Returns `ProofError::ExpectedEquality` if `thm`'s conclusion
    /// isn't an `Eq` shape.
    pub fn sym(arena: &mut Arena, thm: Thm) -> Result<Self, ProofError> {
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
    /// `ctx ⊢ a = c`.
    ///
    /// Both Thms must share the same context (by `Arc::ptr_eq`).
    /// Combining different contexts requires explicit `add_assumption`
    /// to align them first.
    pub fn trans(arena: &mut Arena, ab: Thm, bc: Thm) -> Result<Self, ProofError> {
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

    /// **Equality modus ponens.** From `ctx ⊢ p = q` and
    /// `ctx ⊢ p'` where `p ≡ p'` at UF level 0, derive `ctx ⊢ q`.
    ///
    /// `q` must be a local term (the kernel can't store a foreign
    /// ref as a Thm conclusion directly).
    pub fn eq_mp(arena: &mut Arena, pq: Thm, p_thm: Thm) -> Result<Self, ProofError> {
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
        }
    }
}

impl std::error::Error for ProofError {}
