//! Null kernel — type/term operations work, theorem operations always fail.
//!
//! Provides a base-case implementation of the Isabelle traits where the
//! type and term layers work normally but all inference rules return
//! `Err(PureError::Unsupported(...))`.

use smol_str::SmolStr;

use crate::arena::{self, PureArena};
use crate::traits::*;
use crate::types::*;

/// An uninhabited theorem type — no theorems can ever be constructed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum NullThm {}

/// A null kernel that supports type/term construction but no theorem proving.
pub struct NullKernel {
    arena: PureArena,
    fun_id: NameId,
    prop_id: NameId,
    imp_id: NameId,
    all_id: NameId,
    eq_id: NameId,
}

impl NullKernel {
    pub fn new() -> Self {
        NullKernel {
            arena: PureArena::new(),
            fun_id: FUN_TYCON_ID,
            prop_id: PROP_TYCON_ID,
            imp_id: IMP_CONST_ID,
            all_id: ALL_CONST_ID,
            eq_id: EQ_CONST_ID,
        }
    }

    /// Access the underlying arena.
    pub fn arena(&self) -> &PureArena {
        &self.arena
    }
}

fn unsupported(op: &str) -> PureError {
    PureError::Unsupported(op.into())
}

impl IsabelleTypes for NullKernel {
    type Type = TypId;

    fn fun_id(&self) -> NameId {
        self.fun_id
    }

    fn prop_id(&self) -> NameId {
        self.prop_id
    }

    fn mk_tfree(&mut self, name: NameId, sort: Sort) -> Self::Type {
        self.arena.alloc_type(TypDef::TFree(name, sort))
    }

    fn mk_tvar(&mut self, name: IndexName, sort: Sort) -> Self::Type {
        self.arena.alloc_type(TypDef::TVar(name, sort))
    }

    fn mk_type(&mut self, name: NameId, args: Vec<Self::Type>) -> Self::Type {
        self.arena.alloc_type(TypDef::Type(name, args))
    }

    fn prop_type(&mut self) -> Self::Type {
        self.arena.alloc_type(TypDef::Type(self.prop_id, vec![]))
    }

    fn fun_type(&mut self, a: Self::Type, b: Self::Type) -> Self::Type {
        self.arena.alloc_type(TypDef::Type(self.fun_id, vec![a, b]))
    }

    fn dest_tfree(&self, ty: Self::Type) -> Option<(NameId, Sort)> {
        match self.arena.get_type(ty) {
            TypDef::TFree(n, s) => Some((n, s)),
            _ => None,
        }
    }

    fn dest_tvar(&self, ty: Self::Type) -> Option<(IndexName, Sort)> {
        match self.arena.get_type(ty) {
            TypDef::TVar(ix, s) => Some((ix, s)),
            _ => None,
        }
    }

    fn dest_type(&self, ty: Self::Type) -> Option<(NameId, Vec<Self::Type>)> {
        match self.arena.get_type(ty) {
            TypDef::Type(n, args) => Some((n, args)),
            _ => None,
        }
    }

    fn type_eq(&self, a: Self::Type, b: Self::Type) -> bool {
        arena::types_eq(&self.arena, a, b)
    }

    fn tyfrees(&self, ty: Self::Type) -> Vec<(NameId, Sort)> {
        arena::tyfrees(&self.arena, ty)
    }

    fn tyvars(&self, ty: Self::Type) -> Vec<(IndexName, Sort)> {
        arena::tyvars(&self.arena, ty)
    }

    fn instantiate_typ(&mut self, ty: Self::Type, pairs: &[(Self::Type, IndexName)]) -> Self::Type {
        arena::instantiate_typ(&mut self.arena, ty, pairs)
    }
}

impl IsabelleTerms for NullKernel {
    type Term = TermId;

    fn imp_id(&self) -> NameId {
        self.imp_id
    }

    fn all_id(&self) -> NameId {
        self.all_id
    }

    fn eq_id(&self) -> NameId {
        self.eq_id
    }

    fn mk_bound(&mut self, i: u32) -> Self::Term {
        self.arena.alloc_term(TermDef::Bound(i))
    }

    fn mk_free(&mut self, name: NameId, ty: Self::Type) -> Self::Term {
        self.arena.alloc_term(TermDef::Free(name, ty))
    }

    fn mk_var(&mut self, name: IndexName, ty: Self::Type) -> Self::Term {
        self.arena.alloc_term(TermDef::Var(name, ty))
    }

    fn mk_const(&mut self, name: NameId, ty: Self::Type) -> Self::Term {
        self.arena.alloc_term(TermDef::Const(name, ty))
    }

    fn mk_app(&mut self, f: Self::Term, x: Self::Term) -> Self::Term {
        self.arena.alloc_term(TermDef::App(f, x))
    }

    fn mk_abs(&mut self, hint: NameId, ty: Self::Type, body: Self::Term) -> Self::Term {
        self.arena.alloc_term(TermDef::Abs(hint, ty, body))
    }

    fn mk_imp(&mut self, a: Self::Term, b: Self::Term) -> Self::Term {
        let prop = self.arena.alloc_type(TypDef::Type(self.prop_id, vec![]));
        let pp = self
            .arena
            .alloc_type(TypDef::Type(self.fun_id, vec![prop, prop]));
        let imp_ty = self
            .arena
            .alloc_type(TypDef::Type(self.fun_id, vec![prop, pp]));
        let imp = self.arena.alloc_term(TermDef::Const(self.imp_id, imp_ty));
        let imp_a = self.arena.alloc_term(TermDef::App(imp, a));
        self.arena.alloc_term(TermDef::App(imp_a, b))
    }

    fn mk_all(&mut self, hint: NameId, ty: Self::Type, body: Self::Term) -> Self::Term {
        let prop = self.arena.alloc_type(TypDef::Type(self.prop_id, vec![]));
        let ty_to_prop = self
            .arena
            .alloc_type(TypDef::Type(self.fun_id, vec![ty, prop]));
        let all_ty = self
            .arena
            .alloc_type(TypDef::Type(self.fun_id, vec![ty_to_prop, prop]));
        let all = self.arena.alloc_term(TermDef::Const(self.all_id, all_ty));
        let abs = self.arena.alloc_term(TermDef::Abs(hint, ty, body));
        self.arena.alloc_term(TermDef::App(all, abs))
    }

    fn mk_eq(&mut self, a: Self::Term, b: Self::Term) -> Self::Term {
        let ty = arena::type_of(&mut self.arena, a, self.fun_id);
        let prop = self.arena.alloc_type(TypDef::Type(self.prop_id, vec![]));
        let ty_to_prop = self
            .arena
            .alloc_type(TypDef::Type(self.fun_id, vec![ty, prop]));
        let eq_ty = self
            .arena
            .alloc_type(TypDef::Type(self.fun_id, vec![ty, ty_to_prop]));
        let eq = self.arena.alloc_term(TermDef::Const(self.eq_id, eq_ty));
        let eq_a = self.arena.alloc_term(TermDef::App(eq, a));
        self.arena.alloc_term(TermDef::App(eq_a, b))
    }

    fn dest_bound(&self, tm: Self::Term) -> Option<u32> {
        match self.arena.get_term(tm) {
            TermDef::Bound(i) => Some(i),
            _ => None,
        }
    }

    fn dest_free(&self, tm: Self::Term) -> Option<(NameId, Self::Type)> {
        match self.arena.get_term(tm) {
            TermDef::Free(n, ty) => Some((n, ty)),
            _ => None,
        }
    }

    fn dest_var(&self, tm: Self::Term) -> Option<(IndexName, Self::Type)> {
        match self.arena.get_term(tm) {
            TermDef::Var(ix, ty) => Some((ix, ty)),
            _ => None,
        }
    }

    fn dest_const(&self, tm: Self::Term) -> Option<(NameId, Self::Type)> {
        match self.arena.get_term(tm) {
            TermDef::Const(n, ty) => Some((n, ty)),
            _ => None,
        }
    }

    fn dest_app(&self, tm: Self::Term) -> Option<(Self::Term, Self::Term)> {
        match self.arena.get_term(tm) {
            TermDef::App(f, x) => Some((f, x)),
            _ => None,
        }
    }

    fn dest_abs(&self, tm: Self::Term) -> Option<(NameId, Self::Type, Self::Term)> {
        match self.arena.get_term(tm) {
            TermDef::Abs(hint, ty, body) => Some((hint, ty, body)),
            _ => None,
        }
    }

    fn dest_imp(&self, tm: Self::Term) -> Option<(Self::Term, Self::Term)> {
        if let TermDef::App(f, b) = self.arena.get_term(tm) {
            if let TermDef::App(imp, a) = self.arena.get_term(f) {
                if let TermDef::Const(n, _) = self.arena.get_term(imp) {
                    if n == self.imp_id {
                        return Some((a, b));
                    }
                }
            }
        }
        None
    }

    fn dest_all(&self, tm: Self::Term) -> Option<(NameId, Self::Type, Self::Term)> {
        if let TermDef::App(all, abs) = self.arena.get_term(tm) {
            if let TermDef::Const(n, _) = self.arena.get_term(all) {
                if n == self.all_id {
                    if let TermDef::Abs(hint, ty, body) = self.arena.get_term(abs) {
                        return Some((hint, ty, body));
                    }
                }
            }
        }
        None
    }

    fn dest_eq(&self, tm: Self::Term) -> Option<(Self::Term, Self::Term)> {
        if let TermDef::App(f, b) = self.arena.get_term(tm) {
            if let TermDef::App(eq, a) = self.arena.get_term(f) {
                if let TermDef::Const(n, _) = self.arena.get_term(eq) {
                    if n == self.eq_id {
                        return Some((a, b));
                    }
                }
            }
        }
        None
    }

    fn type_of(&mut self, tm: Self::Term) -> Self::Type {
        arena::type_of(&mut self.arena, tm, self.fun_id)
    }

    fn term_eq(&self, a: Self::Term, b: Self::Term) -> bool {
        arena::terms_eq(&self.arena, a, b)
    }

    fn frees(&self, tm: Self::Term) -> Vec<(NameId, Self::Type)> {
        arena::frees(&self.arena, tm)
    }

    fn vars(&self, tm: Self::Term) -> Vec<(IndexName, Self::Type)> {
        arena::vars(&self.arena, tm)
    }

    fn free_in(&self, name: NameId, ty: Self::Type, tm: Self::Term) -> bool {
        arena::free_in(&self.arena, name, ty, tm)
    }
}

impl IsabelleKernel for NullKernel {
    type Thm = NullThm;

    fn hyps(&self, th: Self::Thm) -> Vec<Self::Term> {
        match th {}
    }

    fn concl(&self, th: Self::Thm) -> Self::Term {
        match th {}
    }

    fn assume(&mut self, _tm: Self::Term) -> Result<Self::Thm, PureError> {
        Err(unsupported("assume"))
    }

    fn implies_intr(&mut self, _a: Self::Term, _th: Self::Thm) -> Result<Self::Thm, PureError> {
        Err(unsupported("implies_intr"))
    }

    fn implies_elim(&mut self, _th1: Self::Thm, _th2: Self::Thm) -> Result<Self::Thm, PureError> {
        Err(unsupported("implies_elim"))
    }

    fn forall_intr(
        &mut self,
        _x: NameId,
        _ty: Self::Type,
        _th: Self::Thm,
    ) -> Result<Self::Thm, PureError> {
        Err(unsupported("forall_intr"))
    }

    fn forall_elim(&mut self, _t: Self::Term, _th: Self::Thm) -> Result<Self::Thm, PureError> {
        Err(unsupported("forall_elim"))
    }

    fn reflexive(&mut self, _t: Self::Term) -> Result<Self::Thm, PureError> {
        Err(unsupported("reflexive"))
    }

    fn symmetric(&mut self, _th: Self::Thm) -> Result<Self::Thm, PureError> {
        Err(unsupported("symmetric"))
    }

    fn transitive(&mut self, _th1: Self::Thm, _th2: Self::Thm) -> Result<Self::Thm, PureError> {
        Err(unsupported("transitive"))
    }

    fn beta_conversion(&mut self, _t: Self::Term) -> Result<Self::Thm, PureError> {
        Err(unsupported("beta_conversion"))
    }

    fn combination(&mut self, _th1: Self::Thm, _th2: Self::Thm) -> Result<Self::Thm, PureError> {
        Err(unsupported("combination"))
    }

    fn abstraction(
        &mut self,
        _x: NameId,
        _ty: Self::Type,
        _th: Self::Thm,
    ) -> Result<Self::Thm, PureError> {
        Err(unsupported("abstraction"))
    }

    fn instantiate_typ_rule(
        &mut self,
        _pairs: &[(Self::Type, IndexName)],
        _th: Self::Thm,
    ) -> Result<Self::Thm, PureError> {
        Err(unsupported("instantiate_typ_rule"))
    }

    fn instantiate_rule(
        &mut self,
        _pairs: &[(Self::Term, IndexName, Self::Type)],
        _th: Self::Thm,
    ) -> Result<Self::Thm, PureError> {
        Err(unsupported("instantiate_rule"))
    }

    fn axiom(&self, name: &str) -> Result<Self::Thm, PureError> {
        Err(PureError::UnknownAxiom(name.into()))
    }

    fn add_axiom(&mut self, _name: SmolStr, _tm: Self::Term) -> Result<Self::Thm, PureError> {
        Err(unsupported("add_axiom"))
    }

    fn add_type(&mut self, _name: NameId, _arity: usize) -> Result<(), PureError> {
        Err(unsupported("add_type"))
    }

    fn add_constant(&mut self, _name: NameId, _ty: Self::Type) -> Result<(), PureError> {
        Err(unsupported("add_constant"))
    }

    fn add_class(&mut self, _class: NameId) -> Result<(), PureError> {
        Err(unsupported("add_class"))
    }

    fn add_subclass(&mut self, _sub: NameId, _sup: NameId) -> Result<(), PureError> {
        Err(unsupported("add_subclass"))
    }

    fn add_arity(
        &mut self,
        _tycon: NameId,
        _arg_sorts: Vec<Sort>,
        _class: NameId,
    ) -> Result<(), PureError> {
        Err(unsupported("add_arity"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_null_types() {
        let mut k = NullKernel::new();
        let prop = k.prop_type();
        let f = k.fun_type(prop, prop);
        assert!(k.dest_type(f).is_some());
        let (name, args) = k.dest_type(f).unwrap();
        assert_eq!(name, FUN_TYCON_ID);
        assert_eq!(args.len(), 2);
        assert!(k.type_eq(args[0], prop));
    }

    #[test]
    fn test_null_terms() {
        let mut k = NullKernel::new();
        let prop = k.prop_type();
        let x = k.mk_free(10, prop);
        let y = k.mk_free(11, prop);
        let app = k.mk_app(x, y);
        assert!(k.dest_app(app).is_some());
        let abs = k.mk_abs(99, prop, x);
        assert!(k.dest_abs(abs).is_some());
    }

    #[test]
    fn test_null_mk_eq() {
        let mut k = NullKernel::new();
        let prop = k.prop_type();
        let x = k.mk_free(10, prop);
        let eq = k.mk_eq(x, x);
        assert!(k.dest_eq(eq).is_some());
    }

    #[test]
    fn test_null_mk_imp() {
        let mut k = NullKernel::new();
        let prop = k.prop_type();
        let a = k.mk_free(10, prop);
        let b = k.mk_free(11, prop);
        let imp = k.mk_imp(a, b);
        assert!(k.dest_imp(imp).is_some());
        let (left, right) = k.dest_imp(imp).unwrap();
        assert!(k.term_eq(left, a));
        assert!(k.term_eq(right, b));
    }

    #[test]
    fn test_null_mk_all() {
        let mut k = NullKernel::new();
        let prop = k.prop_type();
        let body = k.mk_bound(0);
        let all = k.mk_all(99, prop, body);
        assert!(k.dest_all(all).is_some());
        let (hint, ty, b) = k.dest_all(all).unwrap();
        assert_eq!(hint, 99);
        assert!(k.type_eq(ty, prop));
        assert!(k.term_eq(b, body));
    }

    #[test]
    fn test_null_inference_rules_fail() {
        let mut k = NullKernel::new();
        let prop = k.prop_type();
        let x = k.mk_free(10, prop);
        assert!(IsabelleKernel::assume(&mut k, x).is_err());
        assert!(k.reflexive(x).is_err());
        assert!(k.beta_conversion(x).is_err());
        assert!(IsabelleKernel::add_axiom(&mut k, SmolStr::new("x"), x).is_err());
    }
}
