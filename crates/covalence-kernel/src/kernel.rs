//! Ergonomic facade over [`Arena`] + [`Thm`] for building terms and
//! composing proofs.
//!
//! Wraps an `Arena` plus a current `Context`, exposes term
//! constructors that take `&str` and return `TermRef`, and forwards
//! every inference rule with the kernel's well-typed-input checks
//! intact. Designed for end-to-end tests and small driver code —
//! anything that wants the raw API can still hit `arena_mut()`.

use std::sync::Arc;

use crate::arena::Arena;
use crate::egraph::Egraph;
use crate::id::StrId;
use crate::primop::{PrimOp1, PrimOp2};
use crate::prop::{Context, Prop, ProofError, Thm};
use crate::term::{TermDef, TermKind, TermRef};
use crate::ty::{TypeDef, TypeRef};
use crate::uf::TermUf;

/// High-level kernel facade: E-graph + current context +
/// ergonomic constructors. See module docs.
pub struct Kernel {
    egraph: Egraph,
    ctx: Arc<Context>,
}

impl Kernel {
    pub fn new() -> Self {
        Self {
            egraph: Egraph::new(),
            ctx: Context::empty(),
        }
    }

    pub fn egraph(&self) -> &Egraph {
        &self.egraph
    }

    pub fn egraph_mut(&mut self) -> &mut Egraph {
        &mut self.egraph
    }

    pub fn arena(&self) -> &Arena {
        &self.egraph.arena
    }

    pub fn arena_mut(&mut self) -> &mut Arena {
        &mut self.egraph.arena
    }

    pub fn uf(&self) -> &TermUf {
        &self.egraph.uf
    }

    pub fn uf_mut(&mut self) -> &mut TermUf {
        &mut self.egraph.uf
    }

    pub fn context(&self) -> &Arc<Context> {
        &self.ctx
    }

    /// Replace the current context. Returns the old one so callers
    /// can restore later.
    pub fn set_context(&mut self, ctx: Arc<Context>) -> Arc<Context> {
        std::mem::replace(&mut self.ctx, ctx)
    }

    /// Push an assumption onto the current context, returning the
    /// `Arc<Prop>` so the caller can use it with [`Self::assume`].
    pub fn push_assumption(&mut self, p: TermRef) -> Arc<Prop> {
        let id = p.as_local().expect("push_assumption: foreign concl");
        let prop = Arc::new(Prop::new(self.ctx.clone(), id));
        self.ctx = Context::extend(self.ctx.clone(), prop.clone());
        prop
    }

    // ---- type constructors -------------------------------------------------

    pub fn bool_ty(&self) -> TypeRef { self.egraph.arena.bool_ty() }
    pub fn nat_ty(&self) -> TypeRef { self.egraph.arena.nat_ty() }
    pub fn int_ty(&self) -> TypeRef { self.egraph.arena.int_ty() }
    pub fn bytes_ty(&self) -> TypeRef { self.egraph.arena.bytes_ty() }

    pub fn fun_ty(&mut self, dom: TypeRef, cod: TypeRef) -> TypeRef {
        self.egraph.arena.alloc_type(TypeDef::Fun(dom, cod))
    }

    // ---- term constructors -------------------------------------------------

    fn alloc(&mut self, def: TermDef) -> TermRef {
        TermRef::local(self.egraph.arena.alloc_term(def))
    }

    fn intern(&mut self, s: &str) -> StrId {
        self.egraph.arena.intern_string(s.into())
    }

    pub fn true_(&mut self) -> TermRef { self.alloc(TermDef::Bool(true)) }
    pub fn false_(&mut self) -> TermRef { self.alloc(TermDef::Bool(false)) }

    pub fn nat(&mut self, n: u64) -> TermRef { self.alloc(TermDef::nat_inline(n)) }
    pub fn int(&mut self, n: i64) -> TermRef { self.alloc(TermDef::int_inline(n)) }

    pub fn free(&mut self, name: &str, ty: TypeRef) -> TermRef {
        let n = self.intern(name);
        self.alloc(TermDef::Free(n, ty))
    }

    pub fn const_(&mut self, name: &str, ty: TypeRef) -> TermRef {
        let n = self.intern(name);
        self.alloc(TermDef::Const(n, ty))
    }

    pub fn eq(&mut self, a: TermRef, b: TermRef) -> TermRef { self.alloc(TermDef::Eq(a, b)) }

    /// Build `a ≠ b` as `Not(Eq(a, b))`. `Ne` is no longer a kernel
    /// primitive — the builder constructs the derived form.
    pub fn ne(&mut self, a: TermRef, b: TermRef) -> TermRef {
        let eq = self.alloc(TermDef::Eq(a, b));
        self.alloc(TermDef::Op1(PrimOp1::LogicalNot, eq))
    }

    pub fn comb(&mut self, f: TermRef, x: TermRef) -> TermRef { self.alloc(TermDef::Comb(f, x)) }
    pub fn op1(&mut self, op: PrimOp1, x: TermRef) -> TermRef { self.alloc(TermDef::Op1(op, x)) }
    pub fn op2(&mut self, op: PrimOp2, a: TermRef, b: TermRef) -> TermRef {
        self.alloc(TermDef::Op2(op, a, b))
    }

    /// Build `λname:ty. body` from an open body that mentions
    /// `Free(name, ty)`. Closes over the free var via
    /// [`Arena::abstract_over`] and wraps in `Abs`.
    pub fn lam(&mut self, name: &str, ty: TypeRef, body: TermRef) -> TermRef {
        let n = self.intern(name);
        let abstracted = self.egraph.arena.abstract_over(body, n, ty, 0);
        self.alloc(TermDef::Lam(ty, abstracted))
    }

    // ---- inspection --------------------------------------------------------

    pub fn kind(&self, t: TermRef) -> Option<TermKind> {
        t.as_local().map(|id| self.egraph.arena.kind(id))
    }

    pub fn def(&self, t: TermRef) -> Option<TermDef> {
        t.as_local().map(|id| *self.egraph.arena.term_def(id))
    }

    /// Apply canonical equality at level 0 via the session's UF.
    pub fn eq_at_level_0(&self, a: TermRef, b: TermRef) -> bool {
        self.egraph.uf.eq_at_level_0(a, b)
    }

    /// Record an equality in the session's UF.
    pub fn union(&mut self, a: TermRef, b: TermRef) -> Result<(), crate::arena::UnionError> {
        self.egraph.uf.union(a, b)
    }

    // ---- inference rules ---------------------------------------------------

    fn as_id(t: TermRef) -> Result<crate::id::TermId, ProofError> {
        t.as_local().ok_or(ProofError::ForeignConclusion)
    }

    pub fn refl(&mut self, t: TermRef) -> Result<Thm, ProofError> {
        Thm::refl(&mut self.egraph.arena, self.ctx.clone(), Self::as_id(t)?)
    }

    pub fn assume(&mut self, assumption: Arc<Prop>) -> Result<Thm, ProofError> {
        Thm::assume(&self.egraph.arena, self.ctx.clone(), assumption)
    }

    pub fn add_assumption(&mut self, thm: Thm, new_assum: Arc<Prop>) -> Result<Thm, ProofError> {
        thm.add_assumption(&self.egraph.arena, new_assum)
    }

    pub fn not_from_false(&mut self, thm_false: Thm, p: TermRef) -> Result<Thm, ProofError> {
        Thm::not_from_false(&mut self.egraph.arena, thm_false, Self::as_id(p)?)
    }

    pub fn sym(&mut self, thm: Thm) -> Result<Thm, ProofError> {
        Thm::sym(&mut self.egraph.arena, thm)
    }

    pub fn trans(&mut self, ab: Thm, bc: Thm) -> Result<Thm, ProofError> {
        Thm::trans(&mut self.egraph.arena, &self.egraph.uf, ab, bc)
    }

    pub fn eq_mp(&mut self, pq: Thm, p_thm: Thm) -> Result<Thm, ProofError> {
        Thm::eq_mp(&mut self.egraph.arena, &self.egraph.uf, pq, p_thm)
    }

    pub fn mp(&mut self, imp: Thm, ant: Thm) -> Result<Thm, ProofError> {
        Thm::mp(&mut self.egraph.arena, &self.egraph.uf, imp, ant)
    }

    pub fn cong(&mut self, a: TermRef, b: TermRef, depth: u32) -> Result<Thm, ProofError> {
        Thm::cong(&mut self.egraph.arena, &self.egraph.uf, self.ctx.clone(), a, b, depth)
    }

    pub fn beta(&mut self, comb: TermRef) -> Result<Thm, ProofError> {
        Thm::beta(&mut self.egraph.arena, self.ctx.clone(), Self::as_id(comb)?)
    }

    pub fn abs(&mut self, thm: Thm, name: &str, ty: TypeRef) -> Result<Thm, ProofError> {
        let n = self.intern(name);
        Thm::abs(&mut self.egraph.arena, thm, n, ty)
    }

    pub fn inst(
        &mut self,
        thm: Thm,
        name: &str,
        ty: TypeRef,
        replacement: TermRef,
    ) -> Result<Thm, ProofError> {
        let n = self.intern(name);
        Thm::inst(&mut self.egraph.arena, thm, n, ty, replacement)
    }

    pub fn reduce(&mut self, t: TermRef) -> Result<Thm, ProofError> {
        Thm::reduce(&mut self.egraph.arena, self.ctx.clone(), Self::as_id(t)?)
    }

    pub fn deduct_antisym_rule(&mut self, thm_p: Thm, thm_q: Thm) -> Result<Thm, ProofError> {
        Thm::deduct_antisym_rule(&mut self.egraph.arena, &self.egraph.uf, thm_p, thm_q)
    }
}

impl Default for Kernel {
    fn default() -> Self {
        Self::new()
    }
}
