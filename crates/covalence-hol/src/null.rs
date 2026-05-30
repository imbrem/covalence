//! Null kernel — term operations work, theorem operations always fail.
//!
//! Provides a base-case implementation of the HOL Light traits where the
//! type and term layers work normally but all inference rules return
//! `Err(HolError::Unsupported(...))`.

use crate::arena::{self, HolArena};
use crate::traits::*;
use crate::types::*;

/// An uninhabited theorem type — no theorems can ever be constructed.
#[derive(Debug, Clone, Copy)]
pub enum NullThm {}

/// A null kernel that supports type/term construction but no theorem proving.
pub struct NullKernel {
    arena: HolArena,
    fun_id: NameId,
    bool_id: NameId,
    eq_id: NameId,
}

impl NullKernel {
    pub fn new(fun_id: NameId, bool_id: NameId, eq_id: NameId) -> Self {
        NullKernel {
            arena: HolArena::new(),
            fun_id,
            bool_id,
            eq_id,
        }
    }
}

fn unsupported(op: &str) -> HolError {
    HolError::Unsupported(op.into())
}

impl HolLightTypes for NullKernel {
    type Type = TypeId;

    fn fun_id(&self) -> NameId {
        self.fun_id
    }

    fn bool_id(&self) -> NameId {
        self.bool_id
    }

    fn mk_tyvar(&mut self, name: NameId) -> TypeId {
        self.arena.alloc_type(HolTypeDef::Tyvar(name))
    }

    fn mk_tyapp(&mut self, name: NameId, args: Vec<TypeId>) -> TypeId {
        self.arena.alloc_type(HolTypeDef::Tyapp(name, args))
    }

    fn bool_type(&mut self) -> TypeId {
        arena::mk_bool_type(&mut self.arena, self.bool_id)
    }

    fn fun_type(&mut self, a: TypeId, b: TypeId) -> TypeId {
        arena::mk_fun_type(&mut self.arena, self.fun_id, a, b)
    }

    fn dest_tyvar(&self, ty: TypeId) -> Option<NameId> {
        match self.arena.get_type(ty) {
            HolTypeDef::Tyvar(n) => Some(n),
            _ => None,
        }
    }

    fn dest_tyapp(&self, ty: TypeId) -> Option<(NameId, Vec<TypeId>)> {
        match self.arena.get_type(ty) {
            HolTypeDef::Tyapp(n, args) => Some((n, args)),
            _ => None,
        }
    }

    fn type_eq(&self, a: TypeId, b: TypeId) -> bool {
        arena::types_eq(&self.arena, a, b)
    }

    fn tyvars(&self, ty: TypeId) -> Vec<NameId> {
        arena::tyvars(&self.arena, ty)
    }

    fn type_inst(&mut self, ty: TypeId, pairs: &[(TypeId, NameId)]) -> TypeId {
        arena::type_inst(&mut self.arena, ty, pairs)
    }
}

impl HolLightTerms for NullKernel {
    type Term = TermId;

    fn eq_id(&self) -> NameId {
        self.eq_id
    }

    fn mk_var(&mut self, name: NameId, ty: TypeId) -> TermId {
        self.arena.alloc_term(TermDef::Var(name, ty))
    }

    fn mk_const(&mut self, name: NameId, ty: TypeId) -> TermId {
        self.arena.alloc_term(TermDef::Const(name, ty))
    }

    fn mk_comb(&mut self, f: TermId, x: TermId) -> TermId {
        self.arena.alloc_term(TermDef::Comb(f, x))
    }

    fn mk_abs(&mut self, var: TermId, body: TermId) -> TermId {
        self.arena.alloc_term(TermDef::Abs(var, body))
    }

    fn mk_eq(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        arena::mk_eq_term(
            &mut self.arena,
            self.eq_id,
            self.fun_id,
            self.bool_id,
            lhs,
            rhs,
        )
    }

    fn dest_var(&self, tm: TermId) -> Option<(NameId, TypeId)> {
        match self.arena.get_term(tm) {
            TermDef::Var(n, ty) => Some((n, ty)),
            _ => None,
        }
    }

    fn dest_const(&self, tm: TermId) -> Option<(NameId, TypeId)> {
        match self.arena.get_term(tm) {
            TermDef::Const(n, ty) => Some((n, ty)),
            _ => None,
        }
    }

    fn dest_comb(&self, tm: TermId) -> Option<(TermId, TermId)> {
        match self.arena.get_term(tm) {
            TermDef::Comb(f, x) => Some((f, x)),
            _ => None,
        }
    }

    fn dest_abs(&self, tm: TermId) -> Option<(TermId, TermId)> {
        match self.arena.get_term(tm) {
            TermDef::Abs(v, b) => Some((v, b)),
            _ => None,
        }
    }

    fn dest_eq(&self, tm: TermId) -> Option<(TermId, TermId)> {
        arena::dest_eq(&self.arena, self.eq_id, tm)
    }

    fn type_of(&mut self, tm: TermId) -> TypeId {
        arena::type_of(&mut self.arena, tm)
    }

    fn term_eq(&self, a: TermId, b: TermId) -> bool {
        arena::terms_eq(&self.arena, a, b)
    }

    fn aconv(&self, a: TermId, b: TermId) -> bool {
        arena::aconv(&self.arena, a, b)
    }

    fn frees(&self, tm: TermId) -> Vec<TermId> {
        arena::frees(&self.arena, tm)
    }

    fn vfree_in(&self, var: TermId, tm: TermId) -> bool {
        arena::vfree_in(&self.arena, var, tm)
    }

    fn vsubst(&mut self, tm: TermId, pairs: &[(TermId, TermId)]) -> Result<TermId, HolError> {
        arena::vsubst(&mut self.arena, tm, pairs)
    }

    fn inst_term(&mut self, tm: TermId, pairs: &[(TypeId, NameId)]) -> TermId {
        arena::inst_term(&mut self.arena, tm, pairs)
    }
}

impl HolLightKernel for NullKernel {
    type Thm = NullThm;

    fn hyps(&self, th: NullThm) -> Vec<TermId> {
        match th {}
    }

    fn concl(&self, th: NullThm) -> TermId {
        match th {}
    }

    fn refl(&mut self, _tm: TermId) -> Result<NullThm, HolError> {
        Err(unsupported("refl"))
    }

    fn trans(&mut self, _th1: NullThm, _th2: NullThm) -> Result<NullThm, HolError> {
        Err(unsupported("trans"))
    }

    fn mk_comb_rule(&mut self, _th1: NullThm, _th2: NullThm) -> Result<NullThm, HolError> {
        Err(unsupported("mk_comb_rule"))
    }

    fn abs_rule(&mut self, _var: TermId, _th: NullThm) -> Result<NullThm, HolError> {
        Err(unsupported("abs_rule"))
    }

    fn beta_conv(&mut self, _tm: TermId) -> Result<NullThm, HolError> {
        Err(unsupported("beta_conv"))
    }

    fn assume_rule(&mut self, _tm: TermId) -> Result<NullThm, HolError> {
        Err(unsupported("assume_rule"))
    }

    fn eq_mp(&mut self, _th1: NullThm, _th2: NullThm) -> Result<NullThm, HolError> {
        Err(unsupported("eq_mp"))
    }

    fn deduct_antisym(&mut self, _th1: NullThm, _th2: NullThm) -> Result<NullThm, HolError> {
        Err(unsupported("deduct_antisym"))
    }

    fn inst_rule(
        &mut self,
        _pairs: &[(TermId, TermId)],
        _th: NullThm,
    ) -> Result<NullThm, HolError> {
        Err(unsupported("inst_rule"))
    }

    fn inst_type_rule(
        &mut self,
        _pairs: &[(TypeId, NameId)],
        _th: NullThm,
    ) -> Result<NullThm, HolError> {
        Err(unsupported("inst_type_rule"))
    }

    fn new_axiom(&mut self, _tm: TermId) -> Result<NullThm, HolError> {
        Err(unsupported("new_axiom"))
    }

    fn new_basic_definition(&mut self, _tm: TermId) -> Result<NullThm, HolError> {
        Err(unsupported("new_basic_definition"))
    }

    fn new_basic_type_definition(
        &mut self,
        _tyname: NameId,
        _abs_name: NameId,
        _rep_name: NameId,
        _abs_var_name: NameId,
        _rep_var_name: NameId,
        _th: NullThm,
    ) -> Result<(NullThm, NullThm), HolError> {
        Err(unsupported("new_basic_type_definition"))
    }

    fn new_type(&mut self, _name: NameId, _arity: usize) -> Result<(), HolError> {
        Err(unsupported("new_type"))
    }

    fn new_constant(&mut self, _name: NameId, _ty: TypeId) -> Result<(), HolError> {
        Err(unsupported("new_constant"))
    }

    fn get_axioms(&self) -> Vec<NullThm> {
        vec![]
    }

    fn mk_type_validated(&mut self, _name: NameId, _args: Vec<TypeId>) -> Result<TypeId, HolError> {
        Err(unsupported("mk_type_validated"))
    }

    fn mk_const_validated(&mut self, _name: NameId, _ty: TypeId) -> Result<TermId, HolError> {
        Err(unsupported("mk_const_validated"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn mk_null() -> NullKernel {
        NullKernel::new(FUN_TYCON_ID, BOOL_TYCON_ID, EQ_CONST_ID)
    }

    #[test]
    fn test_null_types() {
        let mut k = mk_null();
        let b = k.bool_type();
        let f = k.fun_type(b, b);
        assert!(k.dest_tyapp(f).is_some());
        let (name, args) = k.dest_tyapp(f).unwrap();
        assert_eq!(name, FUN_TYCON_ID);
        assert_eq!(args.len(), 2);
        assert!(k.type_eq(args[0], b));
    }

    #[test]
    fn test_null_terms() {
        let mut k = mk_null();
        let b = k.bool_type();
        let x = k.mk_var(10, b);
        let y = k.mk_var(11, b);
        let app = k.mk_comb(x, y);
        assert!(k.dest_comb(app).is_some());
        let abs = k.mk_abs(x, y);
        assert!(k.dest_abs(abs).is_some());
    }

    #[test]
    fn test_null_mk_eq() {
        let mut k = mk_null();
        let b = k.bool_type();
        let x = k.mk_var(10, b);
        let eq = k.mk_eq(x, x);
        assert!(k.dest_eq(eq).is_some());
    }

    #[test]
    fn test_null_inference_rules_fail() {
        let mut k = mk_null();
        let b = k.bool_type();
        let x = k.mk_var(10, b);
        assert!(HolLightKernel::refl(&mut k, x).is_err());
        assert!(k.beta_conv(x).is_err());
        assert!(k.assume_rule(x).is_err());
        assert!(HolLightKernel::new_axiom(&mut k, x).is_err());
    }

    #[test]
    fn test_null_aconv() {
        let mut k = mk_null();
        let ty = k.mk_tyvar(10);
        let v1 = k.mk_var(1, ty);
        let v2 = k.mk_var(2, ty);
        let abs1 = k.mk_abs(v1, v1);
        let abs2 = k.mk_abs(v2, v2);
        assert!(k.aconv(abs1, abs2));
    }
}
