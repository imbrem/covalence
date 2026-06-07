//! `Prover` impl for [`covalence_kernel::Kernel`].
//!
//! Lowers the high-level trait onto the kernel facade. Anything the facade
//! doesn't expose directly (e.g. `tyapp`) goes through `arena_mut()`.
//!
//! Stays narrow on purpose: this is the *only* file in the shell that knows
//! about the kernel's `TermRef`/`TypeRef`/`Prop`/`Thm` types directly. When
//! the kernel is rewritten, this file is the surface area that has to move.

use std::sync::Arc;

use covalence_kernel::primop::{PrimOp1, PrimOp2};
use covalence_kernel::term::{TermDef, TermKind};
use covalence_kernel::{Kernel, Prop, TermRef, Thm, TypeRef};

use crate::prover::{Prover, ProverError};

impl Prover for Kernel {
    type Type = TypeRef;
    type Term = TermRef;
    type Prop = Arc<Prop>;
    type Thm = Thm;

    // ------------------------------------------------------------------
    // Types
    // ------------------------------------------------------------------

    fn bool_ty(&self) -> Result<TypeRef, ProverError> {
        Ok(Kernel::bool_ty(self))
    }

    fn int_ty(&self) -> Result<TypeRef, ProverError> {
        Ok(Kernel::int_ty(self))
    }

    fn nat_ty(&self) -> Result<TypeRef, ProverError> {
        Ok(Kernel::nat_ty(self))
    }

    fn bytes_ty(&self) -> Result<TypeRef, ProverError> {
        Ok(Kernel::bytes_ty(self))
    }

    fn fun_ty(&mut self, dom: TypeRef, cod: TypeRef) -> Result<TypeRef, ProverError> {
        Ok(Kernel::fun_ty(self, dom, cod))
    }

    fn tyapp(&mut self, name: &str, args: &[TypeRef]) -> Result<TypeRef, ProverError> {
        let arena = self.arena_mut();
        let name_id = arena.intern_string(name.into());
        let args_id = arena.intern_tyargs(args.to_vec());
        Ok(arena.alloc_tyapp(name_id, args_id))
    }

    fn tyvar(&mut self, name: &str) -> Result<TypeRef, ProverError> {
        let arena = self.arena_mut();
        let name_id = arena.intern_string(name.into());
        Ok(arena.alloc_tvar(name_id))
    }

    // ------------------------------------------------------------------
    // Terms
    // ------------------------------------------------------------------

    fn truth(&mut self) -> Result<TermRef, ProverError> {
        Ok(Kernel::true_(self))
    }

    fn falsity(&mut self) -> Result<TermRef, ProverError> {
        Ok(Kernel::false_(self))
    }

    fn int_lit(&mut self, n: i64) -> Result<TermRef, ProverError> {
        Ok(Kernel::int(self, n))
    }

    fn nat_lit(&mut self, n: u64) -> Result<TermRef, ProverError> {
        Ok(Kernel::nat(self, n))
    }

    fn free_var(&mut self, name: &str, ty: TypeRef) -> Result<TermRef, ProverError> {
        Ok(Kernel::free(self, name, ty))
    }

    fn const_term(&mut self, name: &str, ty: TypeRef) -> Result<TermRef, ProverError> {
        Ok(Kernel::const_(self, name, ty))
    }

    fn comb(&mut self, f: TermRef, x: TermRef) -> Result<TermRef, ProverError> {
        Ok(Kernel::comb(self, f, x))
    }

    fn eq(&mut self, a: TermRef, b: TermRef) -> Result<TermRef, ProverError> {
        Ok(Kernel::eq(self, a, b))
    }

    fn lam(&mut self, name: &str, ty: TypeRef, body: TermRef) -> Result<TermRef, ProverError> {
        Ok(Kernel::lam(self, name, ty, body))
    }

    fn op1(&mut self, op: PrimOp1, x: TermRef) -> Result<TermRef, ProverError> {
        Ok(Kernel::op1(self, op, x))
    }

    fn op2(&mut self, op: PrimOp2, a: TermRef, b: TermRef) -> Result<TermRef, ProverError> {
        Ok(Kernel::op2(self, op, a, b))
    }

    // ------------------------------------------------------------------
    // Inspection
    // ------------------------------------------------------------------

    fn conclusion(&self, th: &Thm) -> Result<TermRef, ProverError> {
        Ok(TermRef::local(th.prop().concl))
    }

    fn dest_eq(&self, t: TermRef) -> Option<(TermRef, TermRef)> {
        match self.kind(t)? {
            TermKind::Eq(a, b) => Some((a, b)),
            _ => None,
        }
    }

    // ------------------------------------------------------------------
    // Trust-injection
    // ------------------------------------------------------------------

    fn union(&mut self, a: TermRef, b: TermRef) -> Result<(), ProverError> {
        Ok(Kernel::union(self, a, b)?)
    }

    // ------------------------------------------------------------------
    // Context
    // ------------------------------------------------------------------

    fn push_assumption(&mut self, t: TermRef) -> Result<Arc<Prop>, ProverError> {
        // `Kernel::push_assumption` panics on a foreign concl; guard so the
        // trait surface stays Result-clean.
        if t.as_local().is_none() {
            return Err(ProverError::Other("foreign term in push_assumption".into()));
        }
        Ok(Kernel::push_assumption(self, t))
    }

    // ------------------------------------------------------------------
    // Proof rules
    // ------------------------------------------------------------------

    fn assume(&mut self, p: Arc<Prop>) -> Result<Thm, ProverError> {
        Ok(Kernel::assume(self, p)?)
    }

    fn refl(&mut self, t: TermRef) -> Result<Thm, ProverError> {
        Ok(Kernel::refl(self, t)?)
    }

    fn sym(&mut self, th: Thm) -> Result<Thm, ProverError> {
        Ok(Kernel::sym(self, th)?)
    }

    fn trans(&mut self, ab: Thm, bc: Thm) -> Result<Thm, ProverError> {
        Ok(Kernel::trans(self, ab, bc)?)
    }

    fn eq_mp(&mut self, pq: Thm, p_thm: Thm) -> Result<Thm, ProverError> {
        Ok(Kernel::eq_mp(self, pq, p_thm)?)
    }

    fn mp(&mut self, imp: Thm, ant: Thm) -> Result<Thm, ProverError> {
        Ok(Kernel::mp(self, imp, ant)?)
    }

    fn cong(&mut self, a: TermRef, b: TermRef, depth: u32) -> Result<Thm, ProverError> {
        Ok(Kernel::cong(self, a, b, depth)?)
    }

    fn beta(&mut self, t: TermRef) -> Result<Thm, ProverError> {
        Ok(Kernel::beta(self, t)?)
    }

    fn abs(&mut self, th: Thm, name: &str, ty: TypeRef) -> Result<Thm, ProverError> {
        Ok(Kernel::abs(self, th, name, ty)?)
    }

    fn inst(
        &mut self,
        th: Thm,
        name: &str,
        ty: TypeRef,
        replacement: TermRef,
    ) -> Result<Thm, ProverError> {
        Ok(Kernel::inst(self, th, name, ty, replacement)?)
    }

    fn deduct_antisym(&mut self, p_thm: Thm, q_thm: Thm) -> Result<Thm, ProverError> {
        Ok(Kernel::deduct_antisym_rule(self, p_thm, q_thm)?)
    }

    fn reduce(&mut self, t: TermRef) -> Result<Thm, ProverError> {
        Ok(Kernel::reduce(self, t)?)
    }

    // ------------------------------------------------------------------
    // Boolean reasoning
    // ------------------------------------------------------------------

    fn tautology_intro(&mut self, t: TermRef) -> Result<Thm, ProverError> {
        Ok(Kernel::tautology_intro(self, t)?)
    }
}

// Re-export `TermDef` so the trait is usable without pulling `covalence_kernel`
// into every consumer (e.g. for inspection in the bridge crate).
//
// Currently unused inside this file; placed here so the re-export stays
// adjacent to the impl that justifies it.
#[allow(unused_imports)]
use TermDef as _;
