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
use crate::term::{TermDef, TermRef};
use crate::ty::{TypeKind, TypeRef};
use crate::uf::TermUf;

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

    /// Build a flat root-level context from a list of assumptions.
    /// Equivalent to `extend`-ing each assumption onto `empty()` but
    /// avoids the per-assumption Arc chain.
    pub fn flat(assumptions: Vec<Arc<Prop>>) -> Arc<Self> {
        Arc::new(Self {
            locals: assumptions,
            parent: None,
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
///
/// **Phase P migration.** The `precondition` field is the new
/// per-Prop assumption link (a singly-linked chain via `Arc<Prop>`).
/// It coexists with the legacy `context: Arc<Context>` during the
/// transition; new rules populate it, old rules ignore it. Once
/// every rule maintains the chain (Phase P3) the legacy `context`
/// will be removed (Phase P5).
#[derive(Debug, Clone)]
pub struct Prop {
    pub context: Arc<Context>,
    pub concl: TermId,
    /// Single chained precondition. `None` for unconditional Props.
    /// A chain `P_n ← P_{n-1} ← … ← None` encodes the assumption set
    /// `{P_1.concl, …, P_{n-1}.concl}` for `P_n`.
    pub precondition: Option<Arc<Prop>>,
}

impl Prop {
    /// Build a `Prop` from a context and conclusion. **No checks** —
    /// the conclusion isn't required to be a `bool`-typed term.
    /// Lifting to `Thm` (which is what enforces correctness) is the
    /// validation step.
    ///
    /// The new precondition chain is left empty; use
    /// [`with_precondition`](Self::with_precondition) to push one on.
    pub fn new(context: Arc<Context>, concl: TermId) -> Self {
        Self { context, concl, precondition: None }
    }

    /// Set this Prop's immediate precondition. Older Props in the
    /// chain remain shared via `Arc`.
    pub fn with_precondition(mut self, pre: Arc<Prop>) -> Self {
        self.precondition = Some(pre);
        self
    }

    /// Walk the precondition chain into a `Vec` (innermost first).
    /// Used by the new rule shape; the legacy `context` field is the
    /// authoritative assumption set during the Phase P migration.
    pub fn precondition_chain(&self) -> Vec<Arc<Prop>> {
        let mut out = Vec::new();
        let mut cur = self.precondition.clone();
        while let Some(p) = cur {
            cur = p.precondition.clone();
            out.push(p);
        }
        out
    }

    /// BLAKE3 content hash of this Prop against its arena. See
    /// [`crate::hash::prop`].
    pub fn hash(&self, arena: &Arena) -> covalence_hash::O256 {
        crate::hash::prop(self, arena.hash())
    }
}

// ---------------------------------------------------------------------------
// Thm — kernel-verified proposition
// ---------------------------------------------------------------------------

/// A kernel-verified `Prop`. Constructible only via the inference-
/// rule methods below (or future rules); cannot be built by external
/// code from a bare `Prop`.
///
/// ## ⚠️ Experimental kernel — not the final version
///
/// This whole kernel is staging code. Several inference rules
/// have known soundness-affecting holes and the eventual rewrite
/// will change their signatures. In particular [`Thm::abs_unchecked`]
/// skips a soundness check. See the [crate-level docs](crate) for
/// the full list of caveats.
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

    /// **Tautology introduction.** `ctx ⊢ t` if `t` is a propositional
    /// tautology — every truth assignment to its free Bool variables
    /// evaluates `t` to `True` under the kernel's truth-table semantics for
    /// the boolean primops (`LogicalNot`/`And`/`Or`/`Imp`/`Xor`/`Nand`/`Nor`)
    /// + `Eq` over Booleans + `Bool(_)` literals.
    ///
    /// Implementation is a deliberately-naive 2^n truth-table check; the
    /// kernel's only soundness assumption beyond the existing reduction
    /// rules is that the boolean primops are correctly characterised by
    /// their truth tables (which is already a kernel invariant — see
    /// `prover-primops.md` §1).
    ///
    /// Fails with `IllTypedInput` if `t` is not a Bool, or if any subterm
    /// outside the supported propositional fragment is encountered.
    pub fn tautology_intro(
        arena: &mut Arena,
        ctx: Arc<Context>,
        t: TermId,
    ) -> Result<Self, ProofError> {
        if !arena.is_well_typed(t) {
            return Err(ProofError::IllTypedInput);
        }
        let bool_ty = TypeRef::builtin(crate::ty::BuiltinTy::Bool);
        if arena.infer(t).as_type() != Some(bool_ty) {
            return Err(ProofError::IllTypedInput);
        }
        let t_ref = TermRef::local(t);

        // Collect Bool "atoms" — Bool subterms that aren't in the
        // propositional fragment. These are what we truth-assign over.
        // Includes free Bool vars (`Free(_, Bool)`) AND opaque Bool
        // expressions like `Eq(int_term, int_term)`.
        let mut atoms: Vec<TermRef> = Vec::new();
        collect_bool_atoms(arena, t_ref, bool_ty, &mut atoms);

        if atoms.len() > 24 {
            // 2^24 ≈ 16M is the soft ceiling; cvc5 clauses don't come close.
            return Err(ProofError::Unsupported);
        }

        // Exhaustive truth-table check.
        let n = atoms.len();
        for mask in 0..(1u32 << n) {
            match evaluate_with_assignment(arena, t_ref, &atoms, mask) {
                Some(true) => continue,
                Some(false) => return Err(ProofError::NotATautology),
                None => return Err(ProofError::IllTypedInput),
            }
        }

        Ok(Self {
            prop: Prop::new(ctx, t),
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

    /// **Type-variable instantiation (`INST_TYPE`).** From `Γ ⊢ p`
    /// substitute every occurrence of the type variable `name` with
    /// `replacement` in `p` and in every assumption of `Γ`. Returns
    /// the new Thm with the substituted context + conclusion.
    ///
    /// The kernel doesn't yet have a polymorphic `TypeSubst`
    /// application path; this is the single-variable version that
    /// callers iterate for parallel substitutions.
    pub fn inst_type(
        arena: &mut Arena,
        thm: Thm,
        name: StrId,
        replacement: TypeRef,
    ) -> Result<Self, ProofError> {
        let concl_ref = arena.subst_tyvar_in_term(
            TermRef::local(thm.prop.concl),
            name,
            replacement,
        );
        let new_concl = concl_ref.as_local().ok_or(ProofError::ForeignConclusion)?;
        let old_ctx = thm.prop.context.clone();
        let mut new_assumptions = Vec::with_capacity(old_ctx.len());
        for i in 0..old_ctx.len() {
            let assum = old_ctx.assumption(i).expect("len/index invariant");
            let new_ref = arena.subst_tyvar_in_term(
                TermRef::local(assum.concl),
                name,
                replacement,
            );
            let new_id = new_ref.as_local().ok_or(ProofError::ForeignConclusion)?;
            new_assumptions.push(Arc::new(Prop::new(assum.context.clone(), new_id)));
        }
        let new_ctx = Context::flat(new_assumptions);
        Ok(Self {
            prop: Prop::new(new_ctx, new_concl),
        })
    }

    /// **Replace the Thm's context with `target_ctx`.**
    ///
    /// Soundness check: every `Arc<Prop>` in the current context
    /// must also appear (by `Arc::ptr_eq`) somewhere in
    /// `target_ctx`'s chain. The conclusion is unchanged.
    ///
    /// This is the building block bridges use to align two Thms
    /// onto a common context before applying `Arc::ptr_eq`-strict
    /// rules like [`Self::trans`] / [`Self::eq_mp`]: compute the
    /// union of Props from both inputs, build a single
    /// `Context::flat` over it, then `with_context` each input
    /// onto that shared `Arc`.
    pub fn with_context(
        self,
        target_ctx: Arc<Context>,
    ) -> Result<Self, ProofError> {
        for i in 0..self.prop.context.len() {
            let p = self.prop.context.assumption(i).expect("len/index invariant");
            if !target_ctx.contains_prop(p) {
                return Err(ProofError::AssumptionNotInContext);
            }
        }
        Ok(Self {
            prop: Prop::new(target_ctx, self.prop.concl),
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
        if !matches!(arena.term_def(thm_false.prop.concl), TermDef::Bool(false)) {
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
    pub fn trans(arena: &mut Arena, uf: &TermUf, ab: Thm, bc: Thm) -> Result<Self, ProofError> {
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
        if !uf.eq_at_level_0(b1, b2) {
            return Err(ProofError::MidpointMismatch);
        }
        let ac = arena.alloc_term(TermDef::Eq(a, c));
        Ok(Self {
            prop: Prop::new(ab.prop.context, ac),
        })
    }

    /// **Equality modus ponens.** From `ctx ⊢ p = q` and `ctx ⊢ p'`
    /// where `p ≡ p'` at UF level 0, derive `ctx ⊢ q`.
    pub fn eq_mp(arena: &mut Arena, uf: &TermUf, pq: Thm, p_thm: Thm) -> Result<Self, ProofError> {
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
        if !uf.eq_at_level_0(p, TermRef::local(p_thm.prop.concl)) {
            return Err(ProofError::LhsMismatch);
        }
        let q_id = q.as_local().ok_or(ProofError::ForeignConclusion)?;
        Ok(Self {
            prop: Prop::new(pq.prop.context, q_id),
        })
    }

    /// **Modus ponens.** From `ctx ⊢ Imp(p, q)` and `ctx ⊢ p'` where
    /// `p ≡ p'` at UF level 0, derive `ctx ⊢ q`.
    pub fn mp(arena: &mut Arena, uf: &TermUf, imp: Thm, ant: Thm) -> Result<Self, ProofError> {
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
        if !uf.eq_at_level_0(p, TermRef::local(ant.prop.concl)) {
            return Err(ProofError::LhsMismatch);
        }
        let q_id = q.as_local().ok_or(ProofError::ForeignConclusion)?;
        Ok(Self {
            prop: Prop::new(imp.prop.context, q_id),
        })
    }

    /// **HOL Light's `MK_COMB` rule.** From `Γ ⊢ f = g` and
    /// `Γ ⊢ x = y` derive `Γ ⊢ f x = g y`.
    ///
    /// Direct primitive — no UF wiring required. The two inputs
    /// must share the same context (`Arc::ptr_eq`); bridges use
    /// [`Self::with_context`] to align them first.
    pub fn mk_comb(arena: &mut Arena, fg: Thm, xy: Thm) -> Result<Self, ProofError> {
        if !Arc::ptr_eq(&fg.prop.context, &xy.prop.context) {
            return Err(ProofError::ContextMismatch);
        }
        if !arena.is_well_typed(fg.prop.concl) || !arena.is_well_typed(xy.prop.concl) {
            return Err(ProofError::IllTypedInput);
        }
        let (f, g) = match *arena.term_def(fg.prop.concl) {
            TermDef::Eq(l, r) => (l, r),
            _ => return Err(ProofError::ExpectedEquality),
        };
        let (x, y) = match *arena.term_def(xy.prop.concl) {
            TermDef::Eq(l, r) => (l, r),
            _ => return Err(ProofError::ExpectedEquality),
        };
        let fx = arena.alloc_term(TermDef::Comb(f, x));
        let _ = arena.infer(fx);
        let gy = arena.alloc_term(TermDef::Comb(g, y));
        let _ = arena.infer(gy);
        if !arena.is_well_typed(fx) || !arena.is_well_typed(gy) {
            return Err(ProofError::IllTypedInput);
        }
        let eq = arena.alloc_term(TermDef::Eq(TermRef::local(fx), TermRef::local(gy)));
        Ok(Self {
            prop: Prop::new(fg.prop.context, eq),
        })
    }

    /// **General congruence.** If `a` and `b` are structurally
    /// congruent walking children to depth `depth` (i.e.
    /// [`TermUf::eq_at_level`] returns true), derive
    /// `ctx ⊢ a = b`.
    ///
    /// This is the kernel's *only* rule exempt from the well-typed
    /// input invariant — congruence reasons about the term shape
    /// alone, not its type. `MK_COMB` (the classical HOL rule) is
    /// the special case `depth = 1` applied to two `Comb` shells:
    /// it falls out of this rule with no extra primitive.
    pub fn cong(
        arena: &mut Arena,
        uf: &TermUf,
        ctx: Arc<Context>,
        a: TermRef,
        b: TermRef,
        depth: u32,
    ) -> Result<Self, ProofError> {
        if !uf.eq_at_level(arena, a, b, depth) {
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
            TermDef::Lam(_, body) => body,
            _ => return Err(ProofError::ExpectedBetaRedex),
        };
        let reduced = arena.subst(body_ref, 0, arg_ref);
        let eq = arena.alloc_term(TermDef::Eq(TermRef::local(comb), reduced));
        // Force re-inference on the resulting Eq. `alloc_term`'s
        // `compute_term_props` only inspects children's *cached*
        // info — if any child's cache is stale (e.g. an inner Lam
        // whose Typed entry was computed in a different binder
        // context), the Eq can be cached as ILL_TYPED even when
        // the term structurally type-checks. Re-walking with
        // `infer` produces the right Typed result.
        let _ = arena.infer(eq);
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
        let s_abs = arena.alloc_term(TermDef::Lam(ty, s_body));
        let t_abs = arena.alloc_term(TermDef::Lam(ty, t_body));
        let eq = arena.alloc_term(TermDef::Eq(TermRef::local(s_abs), TermRef::local(t_abs)));
        Ok(Self {
            prop: Prop::new(thm.prop.context, eq),
        })
    }

    /// **Variant of [`Self::abs`] that skips the
    /// VariableEscapesAssumption check.** From `Γ ⊢ s = t`, derive
    /// `Γ ⊢ (λname:ty. s) = (λname:ty. t)` without verifying that
    /// `Free(name, ty)` doesn't appear in any assumption of `Γ`.
    ///
    /// **Soundness obligation on the caller**: every assumption in
    /// `Γ` that contains `Free(name, ty)` must be a globally true
    /// axiom (i.e. derivable in the empty context). HOL Light
    /// stores axioms outside the hypothesis set so its `abs` rule's
    /// check naturally excludes them; bridges that funnel axioms
    /// *through* the context (e.g. `HolPrim::new_axiom`) call this
    /// variant after externally checking the obligation.
    pub fn abs_unchecked(
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
        let s_body = arena.abstract_over(s, name, ty, 0);
        let t_body = arena.abstract_over(t, name, ty, 0);
        let s_abs = arena.alloc_term(TermDef::Lam(ty, s_body));
        let t_abs = arena.alloc_term(TermDef::Lam(ty, t_body));
        let _ = arena.infer(s_abs);
        let _ = arena.infer(t_abs);
        let eq = arena.alloc_term(TermDef::Eq(TermRef::local(s_abs), TermRef::local(t_abs)));
        let _ = arena.infer(eq);
        Ok(Self {
            prop: Prop::new(thm.prop.context, eq),
        })
    }

    /// **Term instantiation (`INST`).** From `ctx ⊢ p`, derive
    /// `ctx[name := replacement] ⊢ p[name := replacement]` — replace
    /// every `Free(name, ty)` in both the context's assumptions and
    /// the conclusion with `replacement`.
    ///
    /// `replacement` must be well-typed and its type must match `ty`
    /// — otherwise the resulting term would be ill-typed at the
    /// substituted sites.
    pub fn inst(
        arena: &mut Arena,
        thm: Thm,
        name: StrId,
        ty: TypeRef,
        replacement: TermRef,
    ) -> Result<Self, ProofError> {
        if !arena.is_well_typed(thm.prop.concl) {
            return Err(ProofError::IllTypedInput);
        }
        let rep_id = replacement.as_local().ok_or(ProofError::ForeignConclusion)?;
        if !arena.is_well_typed(rep_id) {
            return Err(ProofError::IllTypedInput);
        }
        let rep_ty = arena.infer(rep_id).as_type().ok_or(ProofError::IllTypedInput)?;
        if rep_ty != ty {
            return Err(ProofError::TypeMismatch);
        }
        // Substitute in every assumption to build the new context.
        let old_ctx = thm.prop.context.clone();
        let mut new_assumptions = Vec::with_capacity(old_ctx.len());
        for i in 0..old_ctx.len() {
            let assum = old_ctx.assumption(i).expect("len/index invariant");
            let new_concl_ref = arena.subst_free(
                TermRef::local(assum.concl),
                name,
                ty,
                replacement,
            );
            let new_concl = new_concl_ref.as_local().ok_or(ProofError::ForeignConclusion)?;
            new_assumptions.push(std::sync::Arc::new(Prop::new(
                assum.context.clone(),
                new_concl,
            )));
        }
        let new_ctx = Context::flat(new_assumptions);
        // Substitute in the conclusion.
        let new_concl_ref = arena.subst_free(TermRef::local(thm.prop.concl), name, ty, replacement);
        let new_concl = new_concl_ref.as_local().ok_or(ProofError::ForeignConclusion)?;
        Ok(Self {
            prop: Prop::new(new_ctx, new_concl),
        })
    }

    /// **Deduction theorem (`DEDUCT_ANTISYM_RULE`).** From
    /// `A₁ ⊢ p` and `A₂ ⊢ q`, derive
    /// `(A₁ \ {q}) ∪ (A₂ \ {p}) ⊢ p = q`.
    ///
    /// Both Thms' conclusions must be well-typed and share a type
    /// (otherwise the resulting `Eq` is ill-typed). Assumptions are
    /// matched by canonical (UF level 0) equality and the union is
    /// deduplicated by canonical concl.
    pub fn deduct_antisym_rule(
        arena: &mut Arena,
        uf: &TermUf,
        thm_p: Thm,
        thm_q: Thm,
    ) -> Result<Self, ProofError> {
        if !arena.is_well_typed(thm_p.prop.concl) || !arena.is_well_typed(thm_q.prop.concl) {
            return Err(ProofError::IllTypedInput);
        }
        let p_ty = arena.infer(thm_p.prop.concl).as_type().ok_or(ProofError::IllTypedInput)?;
        let q_ty = arena.infer(thm_q.prop.concl).as_type().ok_or(ProofError::IllTypedInput)?;
        if p_ty != q_ty {
            return Err(ProofError::TypeMismatch);
        }
        let p_ref = TermRef::local(thm_p.prop.concl);
        let q_ref = TermRef::local(thm_q.prop.concl);

        let mut assumptions: Vec<Arc<Prop>> = Vec::new();
        let mut seen: Vec<TermRef> = Vec::new();
        let push = |uf: &TermUf,
                        assum: Arc<Prop>,
                        exclude: TermRef,
                        assumptions: &mut Vec<Arc<Prop>>,
                        seen: &mut Vec<TermRef>| {
            let concl_ref = TermRef::local(assum.concl);
            if uf.eq_at_level_0(concl_ref, exclude) {
                return;
            }
            let canon = uf.canonical_local(concl_ref);
            if seen.iter().any(|s| *s == canon) {
                return;
            }
            seen.push(canon);
            assumptions.push(assum);
        };
        let ctx1 = thm_p.prop.context.clone();
        for i in 0..ctx1.len() {
            let assum = ctx1.assumption(i).expect("len/index invariant").clone();
            push(uf, assum, q_ref, &mut assumptions, &mut seen);
        }
        let ctx2 = thm_q.prop.context.clone();
        for i in 0..ctx2.len() {
            let assum = ctx2.assumption(i).expect("len/index invariant").clone();
            push(uf, assum, p_ref, &mut assumptions, &mut seen);
        }
        let new_ctx = Context::flat(assumptions);
        let eq = arena.alloc_term(TermDef::Eq(p_ref, q_ref));
        Ok(Self {
            prop: Prop::new(new_ctx, eq),
        })
    }

    /// **Subset-type axioms (Phase G2).** Given a subset type
    /// `σ = Subset(α, P)`, build the two HOL axioms and register them
    /// as known-true by unioning each conclusion term with `Bool(true)`
    /// in the supplied [`TermUf`]. Returns the two Thms:
    ///
    ///   1. `⊢ ∀ a:σ. abs(rep a) = a`
    ///   2. `⊢ ∀ x:α. (rep(abs x) = x) ⇔ (P x ∨ ¬∃y:α. P y)`
    ///
    /// The disjunct on axiom 2 is what makes the kernel free to
    /// introduce subset types unconditionally: when the predicate is
    /// inhabited the disjunct's RHS contains `P x`, recovering the
    /// usual HOL Light biconditional; when the predicate is empty
    /// (`¬∃y. P y` is true) the biconditional collapses to `rep(abs x)
    /// = x ⇔ true`, which is trivially consistent.
    ///
    /// Returns [`ProofError::ExpectedSubsetType`] when `subset_ty`
    /// isn't a [`crate::ty::TypeKind::Subset`].
    pub fn subset_axioms(
        arena: &mut Arena,
        uf: &mut TermUf,
        ctx: Arc<Context>,
        subset_ty: TypeRef,
    ) -> Result<(Self, Self), ProofError> {
        let (alpha, p_id) = match arena.type_ref_kind(subset_ty) {
            Some(TypeKind::Subset(alpha, p)) => (alpha, p),
            _ => return Err(ProofError::ExpectedSubsetType),
        };

        // abs : α → σ and rep : σ → α.
        let abs_fn = arena.alloc_term(TermDef::Abs(subset_ty));
        let rep_fn = arena.alloc_term(TermDef::Rep(subset_ty));
        let abs_ref = TermRef::local(abs_fn);
        let rep_ref = TermRef::local(rep_fn);
        let p_ref = TermRef::local(p_id);

        // --- Axiom 1: ∀ a:σ. abs(rep a) = a ----------------------------
        let bound0_t1 = arena.alloc_term(TermDef::Bound(0));
        let rep_b0 =
            arena.alloc_term(TermDef::Comb(rep_ref, TermRef::local(bound0_t1)));
        let abs_rep_b0 =
            arena.alloc_term(TermDef::Comb(abs_ref, TermRef::local(rep_b0)));
        let eq1 = arena.alloc_term(TermDef::Eq(
            TermRef::local(abs_rep_b0),
            TermRef::local(bound0_t1),
        ));
        let lam1 = arena.alloc_term(TermDef::Lam(subset_ty, TermRef::local(eq1)));
        let axiom1 = arena.alloc_term(TermDef::Forall(TermRef::local(lam1)));

        // --- Axiom 2: ∀ x:α. (rep(abs x) = x) ⇔ (P x ∨ ¬∃y:α. P y) -----
        // Build under one binder (the outer ∀x), so Bound(0) refers to x.
        let bound0_t2 = arena.alloc_term(TermDef::Bound(0));
        let abs_x =
            arena.alloc_term(TermDef::Comb(abs_ref, TermRef::local(bound0_t2)));
        let rep_abs_x =
            arena.alloc_term(TermDef::Comb(rep_ref, TermRef::local(abs_x)));
        let lhs = arena.alloc_term(TermDef::Eq(
            TermRef::local(rep_abs_x),
            TermRef::local(bound0_t2),
        ));

        // P x — `Comb(P, Bound(0))` with x at the outer binder.
        let p_x = arena.alloc_term(TermDef::Comb(p_ref, TermRef::local(bound0_t2)));

        // ∃ y:α. P y — under the inner ∃, the bound variable is
        // Bound(0); P was closed pre-allocation so it carries no
        // surviving De-Bruijn indices.
        let bound0_inner = arena.alloc_term(TermDef::Bound(0));
        let p_y =
            arena.alloc_term(TermDef::Comb(p_ref, TermRef::local(bound0_inner)));
        let lam_p_y = arena.alloc_term(TermDef::Lam(alpha, TermRef::local(p_y)));
        let exists_p =
            arena.alloc_term(TermDef::Exists(TermRef::local(lam_p_y)));
        let not_exists_p =
            arena.alloc_term(TermDef::Op1(PrimOp1::LogicalNot, TermRef::local(exists_p)));

        let rhs = arena.alloc_term(TermDef::Op2(
            PrimOp2::LogicalOr,
            TermRef::local(p_x),
            TermRef::local(not_exists_p),
        ));

        // Iff is Eq on bool.
        let iff = arena.alloc_term(TermDef::Eq(
            TermRef::local(lhs),
            TermRef::local(rhs),
        ));
        let lam2 = arena.alloc_term(TermDef::Lam(alpha, TermRef::local(iff)));
        let axiom2 = arena.alloc_term(TermDef::Forall(TermRef::local(lam2)));

        // Register both axioms as known-true by union with Bool(true)
        // in the UF.
        let truth = arena.alloc_term(TermDef::Bool(true));
        let truth_ref = TermRef::local(truth);
        // BothForeign is unreachable: each axiom term and `truth` are
        // fresh local allocations.
        let _ = uf.union(TermRef::local(axiom1), truth_ref);
        let _ = uf.union(TermRef::local(axiom2), truth_ref);

        let thm1 = Self {
            prop: Prop::new(ctx.clone(), axiom1),
        };
        let thm2 = Self {
            prop: Prop::new(ctx, axiom2),
        };
        Ok((thm1, thm2))
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
        let reduced = arena
            .reduce_primop(TermRef::local(t))
            .ok_or(ProofError::NotReducible)?;
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
    /// `inst`: replacement term's type doesn't match the variable's
    /// declared type.
    TypeMismatch,
    /// `subset_axioms`: the type argument isn't a Subset(α, P).
    ExpectedSubsetType,
    /// `tautology_intro`: the given Boolean term is not a tautology — at
    /// least one truth assignment to its free Bool variables evaluates the
    /// term to `False`.
    NotATautology,
    /// `tautology_intro`: the input has more free Bool variables than the
    /// truth-table check supports (current ceiling: 24).
    Unsupported,
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
            ProofError::TypeMismatch => write!(f, "replacement type doesn't match variable type"),
            ProofError::ExpectedSubsetType => write!(f, "expected a subset type"),
            ProofError::NotATautology => write!(f, "not a propositional tautology"),
            ProofError::Unsupported => write!(f, "unsupported operation"),
        }
    }
}

impl std::error::Error for ProofError {}

// =====================================================================
// Helpers for tautology_intro
// =====================================================================

/// Is `t` a propositional connective node? — i.e., a node whose value
/// can be computed from the (Boolean) values of its direct children.
fn is_prop_connective(arena: &mut Arena, t: TermRef, bool_ty: TypeRef) -> bool {
    let Some(id) = t.as_local() else { return false };
    let def = *arena.term_def(id);
    match def {
        TermDef::Bool(_) => true,
        TermDef::Op1(PrimOp1::LogicalNot, _) => true,
        TermDef::Op2(
            PrimOp2::LogicalAnd
            | PrimOp2::LogicalOr
            | PrimOp2::LogicalImp
            | PrimOp2::LogicalXor
            | PrimOp2::LogicalNand
            | PrimOp2::LogicalNor,
            _,
            _,
        ) => true,
        // Bool↔Bool equality is iff at the meta level — fold it into the
        // propositional fragment when both sides are Bool-typed.
        TermDef::Eq(a, _) => arena
            .infer(a.as_local().unwrap_or(crate::id::TermId(0)))
            .as_type()
            == Some(bool_ty),
        _ => false,
    }
}

/// Walk `t` and collect Bool subterms that are NOT propositional
/// connectives. These are the "atoms" of the propositional view: free
/// Bool vars, but also expressions like `Eq(int_term, int_term)`,
/// `Comb(p_const, x_const)` returning Bool, etc.
///
/// Dedupes by structural identity of `TermRef` (each distinct ref appears
/// once even if it occurs multiple times in the term).
fn collect_bool_atoms(
    arena: &mut Arena,
    t: TermRef,
    bool_ty: TypeRef,
    acc: &mut Vec<TermRef>,
) {
    let Some(id) = t.as_local() else { return };
    // If t is Bool-typed and NOT a propositional connective, it's an atom.
    if arena.infer(id).as_type() == Some(bool_ty) && !is_prop_connective(arena, t, bool_ty)
    {
        if !acc.iter().any(|a| *a == t) {
            acc.push(t);
        }
        return;
    }
    // Otherwise (it IS a connective), descend into deps.
    let def = *arena.term_def(id);
    match def.deps() {
        crate::term::Deps::None => {}
        crate::term::Deps::One(c) => collect_bool_atoms(arena, c, bool_ty, acc),
        crate::term::Deps::Two(a, b) => {
            collect_bool_atoms(arena, a, bool_ty, acc);
            collect_bool_atoms(arena, b, bool_ty, acc);
        }
    }
}

/// Evaluate `t` under the truth assignment `mask` for the atom list.
/// Bit `i` of `mask` is the value of `atoms[i]`.
///
/// Returns `Some(value)` if every subterm is either a propositional
/// connective or one of the listed atoms; `None` if some out-of-fragment
/// node is encountered (signalling kernel-level malformedness).
fn evaluate_with_assignment(
    arena: &Arena,
    t: TermRef,
    atoms: &[TermRef],
    mask: u32,
) -> Option<bool> {
    // Atom lookup — by structural ref identity.
    if let Some(i) = atoms.iter().position(|a| *a == t) {
        return Some((mask >> i) & 1 == 1);
    }
    let id = t.as_local()?;
    let def = *arena.term_def(id);
    match def {
        TermDef::Bool(b) => Some(b),
        TermDef::Op1(PrimOp1::LogicalNot, x) => {
            Some(!evaluate_with_assignment(arena, x, atoms, mask)?)
        }
        TermDef::Op2(op, a, b) => {
            let av = evaluate_with_assignment(arena, a, atoms, mask)?;
            let bv = evaluate_with_assignment(arena, b, atoms, mask)?;
            Some(match op {
                PrimOp2::LogicalAnd => av && bv,
                PrimOp2::LogicalOr => av || bv,
                PrimOp2::LogicalImp => !av || bv,
                PrimOp2::LogicalXor => av != bv,
                PrimOp2::LogicalNand => !(av && bv),
                PrimOp2::LogicalNor => !(av || bv),
                _ => return None,
            })
        }
        TermDef::Eq(a, b) => {
            // Bool↔Bool iff. If either side is non-Bool we shouldn't be
            // here (collect_bool_atoms would have flagged the whole Eq
            // as an atom).
            let av = evaluate_with_assignment(arena, a, atoms, mask)?;
            let bv = evaluate_with_assignment(arena, b, atoms, mask)?;
            Some(av == bv)
        }
        _ => None,
    }
}
