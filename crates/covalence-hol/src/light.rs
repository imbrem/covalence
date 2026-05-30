//! HOL Light kernel — 10 primitive inference rules + definitions.
//!
//! This follows HOL Light's LCF-style kernel exactly. All theorems are constructed
//! only through these primitives, ensuring soundness.
//!
//! Uses arena-allocated index handles (`TypeId`, `TermId`, `ThmId`) instead of
//! `Arc`-wrapped recursive enums.

use std::collections::HashMap;

use crate::arena::{self, HolArena};
use crate::traits::*;
use crate::types::*;

/// The HOL Light kernel state.
pub struct HolKernel {
    /// Arena storage for types, terms, and theorems.
    arena: HolArena,
    /// Type constructor name → arity.
    type_constants: HashMap<NameId, usize>,
    /// Term constant name → most-general (polymorphic) type.
    constants: HashMap<NameId, TypeId>,
    /// Axioms.
    axioms: Vec<ThmId>,
    /// Well-known name IDs.
    fun_id: NameId,
    bool_id: NameId,
    eq_id: NameId,
}

impl HolKernel {
    /// Create a new kernel with the built-in type constructors (`fun`, `bool`)
    /// and the equality constant (`=`).
    pub fn new(fun_id: NameId, bool_id: NameId, eq_id: NameId) -> Self {
        let mut arena = HolArena::new();

        let mut type_constants = HashMap::new();
        type_constants.insert(fun_id, 2);
        type_constants.insert(bool_id, 0);

        // = : A -> A -> bool  (polymorphic)
        let bool_ty_id = arena::mk_bool_type(&mut arena, bool_id);
        let a = arena.alloc_type(HolTypeDef::Tyvar(NameId::MAX));
        let a_to_bool = arena::mk_fun_type(&mut arena, fun_id, a, bool_ty_id);
        let eq_ty = arena::mk_fun_type(&mut arena, fun_id, a, a_to_bool);

        let mut constants = HashMap::new();
        constants.insert(eq_id, eq_ty);

        HolKernel {
            arena,
            type_constants,
            constants,
            axioms: Vec::new(),
            fun_id,
            bool_id,
            eq_id,
        }
    }

    // -------------------------------------------------------------------
    // Accessors
    // -------------------------------------------------------------------

    pub fn fun_id(&self) -> NameId {
        self.fun_id
    }

    pub fn bool_id(&self) -> NameId {
        self.bool_id
    }

    pub fn eq_id(&self) -> NameId {
        self.eq_id
    }

    /// Access the arena (read-only).
    pub fn arena(&self) -> &HolArena {
        &self.arena
    }

    /// All type definitions.
    pub fn types(&self) -> &[HolTypeDef] {
        self.arena.types()
    }

    /// All term definitions.
    pub fn terms(&self) -> &[TermDef] {
        self.arena.terms()
    }

    pub fn type_constants(&self) -> &HashMap<NameId, usize> {
        &self.type_constants
    }

    pub fn constants(&self) -> &HashMap<NameId, TypeId> {
        &self.constants
    }

    // -------------------------------------------------------------------
    // Helpers
    // -------------------------------------------------------------------

    fn mk_eq_term(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        arena::mk_eq_term(
            &mut self.arena,
            self.eq_id,
            self.fun_id,
            self.bool_id,
            lhs,
            rhs,
        )
    }

    fn dest_eq_term(&self, tm: TermId) -> Option<(TermId, TermId)> {
        arena::dest_eq(&self.arena, self.eq_id, tm)
    }

    fn is_bool(&self, tm: TermId) -> bool {
        arena::is_bool(&self.arena, self.bool_id, tm)
    }

    /// Merge two hypothesis lists (dedup by alpha-equivalence).
    fn merge_hyps(&self, h1: &[TermId], h2: &[TermId]) -> Vec<TermId> {
        let mut result = h1.to_vec();
        for &h in h2 {
            if !result
                .iter()
                .any(|&existing| arena::aconv(&self.arena, existing, h))
            {
                result.push(h);
            }
        }
        result
    }

    /// Remove a hypothesis (by alpha-equivalence).
    fn remove_hyp(&self, hyps: &[TermId], tm: TermId) -> Vec<TermId> {
        hyps.iter()
            .filter(|&&h| !arena::aconv(&self.arena, h, tm))
            .copied()
            .collect()
    }
}

// -------------------------------------------------------------------
// Trait implementations
// -------------------------------------------------------------------

impl HolLightTypes for HolKernel {
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

impl HolLightTerms for HolKernel {
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
        self.mk_eq_term(lhs, rhs)
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
        self.dest_eq_term(tm)
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

impl HolLightKernel for HolKernel {
    type Thm = ThmId;

    fn hyps(&self, th: ThmId) -> Vec<TermId> {
        self.arena.get_thm(th).hyps
    }

    fn concl(&self, th: ThmId) -> TermId {
        self.arena.get_thm(th).concl
    }

    fn refl(&mut self, tm: TermId) -> Result<ThmId, HolError> {
        let concl = self.mk_eq_term(tm, tm);
        Ok(self.arena.alloc_thm(ThmDef {
            hyps: vec![],
            concl,
        }))
    }

    fn trans(&mut self, th1: ThmId, th2: ThmId) -> Result<ThmId, HolError> {
        let thm1 = self.arena.get_thm(th1);
        let thm2 = self.arena.get_thm(th2);
        let (s, t1) = self
            .dest_eq_term(thm1.concl)
            .ok_or(HolError::NotAnEquation)?;
        let (t2, u) = self
            .dest_eq_term(thm2.concl)
            .ok_or(HolError::NotAnEquation)?;
        if !arena::aconv(&self.arena, t1, t2) {
            return Err(HolError::TypeMismatch(
                "TRANS: middle terms not alpha-equivalent".into(),
            ));
        }
        let hyps = self.merge_hyps(&thm1.hyps, &thm2.hyps);
        let concl = self.mk_eq_term(s, u);
        Ok(self.arena.alloc_thm(ThmDef { hyps, concl }))
    }

    fn mk_comb_rule(&mut self, th1: ThmId, th2: ThmId) -> Result<ThmId, HolError> {
        let thm1 = self.arena.get_thm(th1);
        let thm2 = self.arena.get_thm(th2);
        let (f, g) = self
            .dest_eq_term(thm1.concl)
            .ok_or(HolError::NotAnEquation)?;
        let (x, y) = self
            .dest_eq_term(thm2.concl)
            .ok_or(HolError::NotAnEquation)?;
        let f_ty = arena::type_of(&mut self.arena, f);
        match self.arena.get_type(f_ty) {
            HolTypeDef::Tyapp(n, args) if n == self.fun_id && args.len() == 2 => {
                let domain = args[0];
                let x_ty = arena::type_of(&mut self.arena, x);
                if !arena::types_eq(&self.arena, domain, x_ty) {
                    return Err(HolError::TypeMismatch(
                        "MK_COMB: domain type mismatch".into(),
                    ));
                }
            }
            _ => {
                return Err(HolError::TypeMismatch(
                    "MK_COMB: first theorem not a function equation".into(),
                ));
            }
        }
        // Re-read thm data since we may have allocated in type_of
        let thm1 = self.arena.get_thm(th1);
        let thm2 = self.arena.get_thm(th2);
        let hyps = self.merge_hyps(&thm1.hyps, &thm2.hyps);
        let fx = self.arena.alloc_term(TermDef::Comb(f, x));
        let gy = self.arena.alloc_term(TermDef::Comb(g, y));
        let concl = self.mk_eq_term(fx, gy);
        Ok(self.arena.alloc_thm(ThmDef { hyps, concl }))
    }

    fn abs_rule(&mut self, var: TermId, th: ThmId) -> Result<ThmId, HolError> {
        match self.arena.get_term(var) {
            TermDef::Var(_, _) => {}
            _ => return Err(HolError::NotAVariable),
        }
        let thm = self.arena.get_thm(th);
        let (s, t) = self
            .dest_eq_term(thm.concl)
            .ok_or(HolError::NotAnEquation)?;
        for &hyp in &thm.hyps {
            if arena::vfree_in(&self.arena, var, hyp) {
                return Err(HolError::FreeVariable);
            }
        }
        let hyps = thm.hyps.clone();
        let abs_s = self.arena.alloc_term(TermDef::Abs(var, s));
        let abs_t = self.arena.alloc_term(TermDef::Abs(var, t));
        let concl = self.mk_eq_term(abs_s, abs_t);
        Ok(self.arena.alloc_thm(ThmDef { hyps, concl }))
    }

    fn beta_conv(&mut self, tm: TermId) -> Result<ThmId, HolError> {
        if let TermDef::Comb(f, arg) = self.arena.get_term(tm) {
            if let TermDef::Abs(var, body) = self.arena.get_term(f) {
                if arena::terms_eq(&self.arena, var, arg) {
                    let concl = self.mk_eq_term(tm, body);
                    return Ok(self.arena.alloc_thm(ThmDef {
                        hyps: vec![],
                        concl,
                    }));
                }
                return Err(HolError::NotBetaRedex);
            }
        }
        Err(HolError::NotBetaRedex)
    }

    fn assume_rule(&mut self, tm: TermId) -> Result<ThmId, HolError> {
        if !self.is_bool(tm) {
            return Err(HolError::NotBoolean);
        }
        Ok(self.arena.alloc_thm(ThmDef {
            hyps: vec![tm],
            concl: tm,
        }))
    }

    fn eq_mp(&mut self, th1: ThmId, th2: ThmId) -> Result<ThmId, HolError> {
        let thm1 = self.arena.get_thm(th1);
        let thm2 = self.arena.get_thm(th2);
        let (p, q) = self
            .dest_eq_term(thm1.concl)
            .ok_or(HolError::NotAnEquation)?;
        if !arena::aconv(&self.arena, p, thm2.concl) {
            return Err(HolError::TypeMismatch(
                "EQ_MP: theorem conclusion doesn't match equation LHS".into(),
            ));
        }
        let hyps = self.merge_hyps(&thm1.hyps, &thm2.hyps);
        Ok(self.arena.alloc_thm(ThmDef { hyps, concl: q }))
    }

    fn deduct_antisym(&mut self, th1: ThmId, th2: ThmId) -> Result<ThmId, HolError> {
        let thm1 = self.arena.get_thm(th1);
        let thm2 = self.arena.get_thm(th2);
        let p = thm1.concl;
        let q = thm2.concl;
        let hyps1 = self.remove_hyp(&thm1.hyps, q);
        let hyps2 = self.remove_hyp(&thm2.hyps, p);
        let hyps = self.merge_hyps(&hyps1, &hyps2);
        let concl = self.mk_eq_term(p, q);
        Ok(self.arena.alloc_thm(ThmDef { hyps, concl }))
    }

    fn inst_rule(&mut self, pairs: &[(TermId, TermId)], th: ThmId) -> Result<ThmId, HolError> {
        // Validate: each old must be a Var, and types must match.
        for &(new, old) in pairs {
            match self.arena.get_term(old) {
                TermDef::Var(_, ty) => {
                    let new_ty = arena::type_of(&mut self.arena, new);
                    if !arena::types_eq(&self.arena, new_ty, ty) {
                        return Err(HolError::TypeMismatch(
                            "INST: replacement has different type".into(),
                        ));
                    }
                }
                _ => return Err(HolError::NotAVariable),
            }
        }
        let thm = self.arena.get_thm(th);
        let concl = thm.concl;
        let hyps = thm.hyps.clone();
        let new_concl = arena::vsubst(&mut self.arena, concl, pairs)?;
        let mut new_hyps = Vec::new();
        for h in hyps {
            new_hyps.push(arena::vsubst(&mut self.arena, h, pairs)?);
        }
        // Dedup hypotheses.
        let mut deduped = Vec::new();
        for h in new_hyps {
            if !deduped
                .iter()
                .any(|&existing: &TermId| arena::aconv(&self.arena, existing, h))
            {
                deduped.push(h);
            }
        }
        Ok(self.arena.alloc_thm(ThmDef {
            hyps: deduped,
            concl: new_concl,
        }))
    }

    fn inst_type_rule(&mut self, pairs: &[(TypeId, NameId)], th: ThmId) -> Result<ThmId, HolError> {
        let thm = self.arena.get_thm(th);
        let concl = thm.concl;
        let hyps = thm.hyps.clone();
        let new_concl = arena::inst_term(&mut self.arena, concl, pairs);
        let new_hyps: Vec<TermId> = hyps
            .iter()
            .map(|&h| arena::inst_term(&mut self.arena, h, pairs))
            .collect();
        // Dedup hypotheses after type instantiation.
        let mut deduped = Vec::new();
        for h in new_hyps {
            if !deduped
                .iter()
                .any(|&existing: &TermId| arena::aconv(&self.arena, existing, h))
            {
                deduped.push(h);
            }
        }
        Ok(self.arena.alloc_thm(ThmDef {
            hyps: deduped,
            concl: new_concl,
        }))
    }

    fn new_axiom(&mut self, tm: TermId) -> Result<ThmId, HolError> {
        if !self.is_bool(tm) {
            return Err(HolError::NotBoolean);
        }
        let thm_id = self.arena.alloc_thm(ThmDef {
            hyps: vec![],
            concl: tm,
        });
        self.axioms.push(thm_id);
        Ok(thm_id)
    }

    fn new_basic_definition(&mut self, tm: TermId) -> Result<ThmId, HolError> {
        let (lhs, rhs) = self
            .dest_eq_term(tm)
            .ok_or_else(|| HolError::BadDefinition("not an equation".into()))?;
        let (name, ty) = match self.arena.get_term(lhs) {
            TermDef::Var(n, ty) => (n, ty),
            _ => {
                return Err(HolError::BadDefinition("LHS must be a variable".into()));
            }
        };
        // RHS must have no free variables.
        let rhs_frees = arena::frees(&self.arena, rhs);
        if !rhs_frees.is_empty() {
            return Err(HolError::BadDefinition("RHS has free variables".into()));
        }
        // Type variables in RHS must be a subset of type variables in LHS type.
        let lhs_tyvars = arena::tyvars(&self.arena, ty);
        let rhs_ty = arena::type_of(&mut self.arena, rhs);
        let rhs_tyvars = arena::tyvars(&self.arena, rhs_ty);
        for tv in &rhs_tyvars {
            if !lhs_tyvars.contains(tv) {
                return Err(HolError::FreeTypeVarsInDefinition);
            }
        }
        // Register the constant.
        if self.constants.contains_key(&name) {
            return Err(HolError::ConstantAlreadyDefined(format!("{name}")));
        }
        self.constants.insert(name, ty);
        // Build the theorem.
        let const_term = self.arena.alloc_term(TermDef::Const(name, ty));
        let concl = self.mk_eq_term(const_term, rhs);
        Ok(self.arena.alloc_thm(ThmDef {
            hyps: vec![],
            concl,
        }))
    }

    fn new_basic_type_definition(
        &mut self,
        tyname: NameId,
        abs_name: NameId,
        rep_name: NameId,
        abs_var_name: NameId,
        rep_var_name: NameId,
        th: ThmId,
    ) -> Result<(ThmId, ThmId), HolError> {
        let thm = self.arena.get_thm(th);
        if !thm.hyps.is_empty() {
            return Err(HolError::BadTypeDefinition("theorem has hypotheses".into()));
        }
        let (pred, witness) = match self.arena.get_term(thm.concl) {
            TermDef::Comb(p, t) => (p, t),
            _ => {
                return Err(HolError::BadTypeDefinition(
                    "conclusion is not an application".into(),
                ));
            }
        };
        // Collect type variables from the witness type.
        let rty = arena::type_of(&mut self.arena, witness);
        let type_vars: Vec<NameId> = arena::tyvars(&self.arena, rty);
        let tyvar_args: Vec<TypeId> = type_vars
            .iter()
            .map(|&n| self.arena.alloc_type(HolTypeDef::Tyvar(n)))
            .collect();

        // Define the new type constructor.
        let arity = type_vars.len();
        if self.type_constants.contains_key(&tyname) {
            return Err(HolError::TypeAlreadyDefined(format!("{tyname}")));
        }
        self.type_constants.insert(tyname, arity);

        // The new abstract type.
        let abs_ty = self.arena.alloc_type(HolTypeDef::Tyapp(tyname, tyvar_args));

        // abs : rty -> abs_ty,  rep : abs_ty -> rty
        let abs_fn_ty = arena::mk_fun_type(&mut self.arena, self.fun_id, rty, abs_ty);
        let rep_fn_ty = arena::mk_fun_type(&mut self.arena, self.fun_id, abs_ty, rty);

        if self.constants.contains_key(&abs_name) {
            return Err(HolError::ConstantAlreadyDefined(format!("{abs_name}")));
        }
        self.constants.insert(abs_name, abs_fn_ty);
        if self.constants.contains_key(&rep_name) {
            return Err(HolError::ConstantAlreadyDefined(format!("{rep_name}")));
        }
        self.constants.insert(rep_name, rep_fn_ty);

        let abs_const = self.arena.alloc_term(TermDef::Const(abs_name, abs_fn_ty));
        let rep_const = self.arena.alloc_term(TermDef::Const(rep_name, rep_fn_ty));

        // Variable `a` of the abstract type.
        let a_var = self.arena.alloc_term(TermDef::Var(abs_var_name, abs_ty));
        // Variable `r` of the representation type.
        let r_var = self.arena.alloc_term(TermDef::Var(rep_var_name, rty));

        // Theorem 1: |- abs(rep(a)) = a
        let rep_a = self.arena.alloc_term(TermDef::Comb(rep_const, a_var));
        let abs_rep_a = self.arena.alloc_term(TermDef::Comb(abs_const, rep_a));
        let concl1 = self.mk_eq_term(abs_rep_a, a_var);
        let thm1 = self.arena.alloc_thm(ThmDef {
            hyps: vec![],
            concl: concl1,
        });

        // Theorem 2: |- P r <=> (rep(abs(r)) = r)
        let abs_r = self.arena.alloc_term(TermDef::Comb(abs_const, r_var));
        let rep_abs_r = self.arena.alloc_term(TermDef::Comb(rep_const, abs_r));
        let rep_abs_r_eq_r = self.mk_eq_term(rep_abs_r, r_var);
        let p_r = self.arena.alloc_term(TermDef::Comb(pred, r_var));
        let concl2 = self.mk_eq_term(p_r, rep_abs_r_eq_r);
        let thm2 = self.arena.alloc_thm(ThmDef {
            hyps: vec![],
            concl: concl2,
        });

        Ok((thm1, thm2))
    }

    fn new_type(&mut self, name: NameId, arity: usize) -> Result<(), HolError> {
        if self.type_constants.contains_key(&name) {
            return Err(HolError::TypeAlreadyDefined(format!("{name}")));
        }
        self.type_constants.insert(name, arity);
        Ok(())
    }

    fn new_constant(&mut self, name: NameId, ty: TypeId) -> Result<(), HolError> {
        if self.constants.contains_key(&name) {
            return Err(HolError::ConstantAlreadyDefined(format!("{name}")));
        }
        self.constants.insert(name, ty);
        Ok(())
    }

    fn get_axioms(&self) -> Vec<ThmId> {
        self.axioms.clone()
    }

    fn mk_type_validated(&mut self, name: NameId, args: Vec<TypeId>) -> Result<TypeId, HolError> {
        let arity = self
            .type_constants
            .get(&name)
            .ok_or(HolError::UnknownTypeConstructor(name))?;
        if args.len() != *arity {
            return Err(HolError::WrongTypeArity {
                expected: *arity,
                got: args.len(),
            });
        }
        Ok(self.arena.alloc_type(HolTypeDef::Tyapp(name, args)))
    }

    fn mk_const_validated(&mut self, name: NameId, ty: TypeId) -> Result<TermId, HolError> {
        let generic_ty = *self
            .constants
            .get(&name)
            .ok_or(HolError::UnknownConstant(name))?;
        if arena::type_match(&self.arena, generic_ty, ty, &mut Vec::new()).is_err() {
            return Err(HolError::NotAnInstance);
        }
        Ok(self.arena.alloc_term(TermDef::Const(name, ty)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn mk_kernel() -> HolKernel {
        HolKernel::new(FUN_TYCON_ID, BOOL_TYCON_ID, EQ_CONST_ID)
    }

    #[test]
    fn test_refl() {
        let mut k = mk_kernel();
        let b = k.bool_type();
        let x = k.mk_var(10, b);
        let th = k.refl(x).unwrap();
        assert!(k.hyps(th).is_empty());
        let concl = k.concl(th);
        let (l, r) = k.dest_eq_term(concl).unwrap();
        assert!(arena::aconv(&k.arena, l, x));
        assert!(arena::aconv(&k.arena, r, x));
    }

    #[test]
    fn test_trans() {
        let mut k = mk_kernel();
        let b = k.bool_type();
        let x = k.mk_var(10, b);
        let refl_x = k.refl(x).unwrap();
        let result = k.trans(refl_x, refl_x).unwrap();
        let concl = k.concl(result);
        let (l, r) = k.dest_eq_term(concl).unwrap();
        assert!(arena::aconv(&k.arena, l, x));
        assert!(arena::aconv(&k.arena, r, x));
    }

    #[test]
    fn test_mk_comb() {
        let mut k = mk_kernel();
        let b = k.bool_type();
        let fb = k.fun_type(b, b);
        let f = k.mk_var(10, fb);
        let x = k.mk_var(12, b);
        let th1 = k.refl(f).unwrap();
        let th2 = k.refl(x).unwrap();
        let result = k.mk_comb_rule(th1, th2).unwrap();
        let concl = k.concl(result);
        let (l, r) = k.dest_eq_term(concl).unwrap();
        assert!(arena::aconv(&k.arena, l, r));
    }

    #[test]
    fn test_mk_comb_type_mismatch() {
        let mut k = mk_kernel();
        let b = k.bool_type();
        let a = k.mk_tyvar(100);
        let fa = k.fun_type(a, b);
        let f = k.mk_var(10, fa);
        let x = k.mk_var(12, b);
        let th1 = k.refl(f).unwrap();
        let th2 = k.refl(x).unwrap();
        assert!(k.mk_comb_rule(th1, th2).is_err());
    }

    #[test]
    fn test_abs() {
        let mut k = mk_kernel();
        let b = k.bool_type();
        let x = k.mk_var(10, b);
        let y = k.mk_var(11, b);
        let th = k.refl(y).unwrap();
        let result = k.abs_rule(x, th).unwrap();
        let concl = k.concl(result);
        let (l, r) = k.dest_eq_term(concl).unwrap();
        assert!(arena::aconv(&k.arena, l, r));
        match k.arena.get_term(l) {
            TermDef::Abs(v, body) => {
                assert!(arena::terms_eq(&k.arena, v, x));
                assert!(arena::terms_eq(&k.arena, body, y));
            }
            _ => panic!("expected abstraction"),
        }
    }

    #[test]
    fn test_abs_free_in_hyp() {
        let mut k = mk_kernel();
        let b = k.bool_type();
        let x = k.mk_var(10, b);
        let concl = k.mk_eq_term(x, x);
        let th = k.arena.alloc_thm(ThmDef {
            hyps: vec![x],
            concl,
        });
        assert!(k.abs_rule(x, th).is_err());
    }

    #[test]
    fn test_beta() {
        let mut k = mk_kernel();
        let b = k.bool_type();
        let x = k.mk_var(10, b);
        let abs = k.mk_abs(x, x);
        let app = k.mk_comb(abs, x);
        let th = k.beta_conv(app).unwrap();
        let concl = k.concl(th);
        let (l, r) = k.dest_eq_term(concl).unwrap();
        assert!(arena::aconv(&k.arena, l, app));
        assert!(arena::aconv(&k.arena, r, x));
    }

    #[test]
    fn test_assume() {
        let mut k = mk_kernel();
        let b = k.bool_type();
        let p = k.mk_var(10, b);
        let th = k.assume_rule(p).unwrap();
        assert_eq!(k.hyps(th).len(), 1);
        assert!(arena::aconv(&k.arena, k.hyps(th)[0], p));
        assert!(arena::aconv(&k.arena, k.concl(th), p));
    }

    #[test]
    fn test_assume_non_boolean() {
        let mut k = mk_kernel();
        let a = k.mk_tyvar(100);
        let x = k.mk_var(10, a);
        assert!(k.assume_rule(x).is_err());
    }

    #[test]
    fn test_eq_mp() {
        let mut k = mk_kernel();
        let b = k.bool_type();
        let p = k.mk_var(10, b);
        let q = k.mk_var(11, b);
        let assume_p = k.assume_rule(p).unwrap();
        let assume_q = k.assume_rule(q).unwrap();
        let p_iff_q = k.deduct_antisym(assume_p, assume_q).unwrap();
        let result = k.eq_mp(p_iff_q, assume_p).unwrap();
        assert!(arena::aconv(&k.arena, k.concl(result), q));
    }

    #[test]
    fn test_deduct_antisym() {
        let mut k = mk_kernel();
        let b = k.bool_type();
        let p = k.mk_var(10, b);
        let q = k.mk_var(11, b);
        let th1 = k.assume_rule(p).unwrap();
        let th2 = k.assume_rule(q).unwrap();
        let result = k.deduct_antisym(th1, th2).unwrap();
        let concl = k.concl(result);
        let (l, r) = k.dest_eq_term(concl).unwrap();
        assert!(arena::aconv(&k.arena, l, p));
        assert!(arena::aconv(&k.arena, r, q));
        assert_eq!(k.hyps(result).len(), 2);
    }

    #[test]
    fn test_deduct_antisym_removes_hyp() {
        let mut k = mk_kernel();
        let b = k.bool_type();
        let p = k.mk_var(10, b);
        let th1 = k.assume_rule(p).unwrap();
        let th2 = k.assume_rule(p).unwrap();
        let result = k.deduct_antisym(th1, th2).unwrap();
        assert!(k.hyps(result).is_empty());
        let concl = k.concl(result);
        let (l, r) = k.dest_eq_term(concl).unwrap();
        assert!(arena::aconv(&k.arena, l, p));
        assert!(arena::aconv(&k.arena, r, p));
    }

    #[test]
    fn test_inst() {
        let mut k = mk_kernel();
        let b = k.bool_type();
        let x = k.mk_var(10, b);
        let y = k.mk_var(11, b);
        let th = k.refl(x).unwrap();
        let result = k.inst_rule(&[(y, x)], th).unwrap();
        let concl = k.concl(result);
        let (l, r) = k.dest_eq_term(concl).unwrap();
        assert!(arena::aconv(&k.arena, l, y));
        assert!(arena::aconv(&k.arena, r, y));
    }

    #[test]
    fn test_inst_type() {
        let mut k = mk_kernel();
        let a = k.mk_tyvar(100);
        let x = k.mk_var(10, a);
        let th = k.refl(x).unwrap();
        let b = k.bool_type();
        let result = k.inst_type_rule(&[(b, 100)], th).unwrap();
        let concl = k.concl(result);
        let (l, _) = k.dest_eq_term(concl).unwrap();
        let l_ty = k.type_of(l);
        assert!(arena::types_eq(&k.arena, l_ty, b));
    }

    #[test]
    fn test_new_basic_definition() {
        let mut k = mk_kernel();
        let b = k.bool_type();
        let p = k.mk_var(10, b);
        let id_bool = k.mk_abs(p, p);
        let t_def_rhs = k.mk_eq(id_bool, id_bool);
        let t_name: NameId = 100;
        let t_var = k.mk_var(t_name, b);
        let def_eq = k.mk_eq(t_var, t_def_rhs);
        let th = k.new_basic_definition(def_eq).unwrap();
        assert!(k.hyps(th).is_empty());
        let concl = k.concl(th);
        let (l, r) = k.dest_eq_term(concl).unwrap();
        match k.arena.get_term(l) {
            TermDef::Const(n, _) => assert_eq!(n, t_name),
            _ => panic!("expected constant"),
        }
        assert!(arena::aconv(&k.arena, r, t_def_rhs));
    }

    #[test]
    fn test_new_axiom() {
        let mut k = mk_kernel();
        let b = k.bool_type();
        let p = k.mk_var(10, b);
        let th = k.new_axiom(p).unwrap();
        assert!(k.hyps(th).is_empty());
        assert!(arena::aconv(&k.arena, k.concl(th), p));
        assert_eq!(k.axioms.len(), 1);
    }

    #[test]
    fn test_new_basic_type_definition() {
        let mut k = mk_kernel();
        let b = k.bool_type();
        let p = k.mk_var(10, b);
        let id_bool = k.mk_abs(p, p);
        let t_rhs = k.mk_eq(id_bool, id_bool);
        let t_name: NameId = 100;
        let t_var = k.mk_var(t_name, b);
        let def_eq = k.mk_eq(t_var, t_rhs);
        let _t_def = k.new_basic_definition(def_eq).unwrap();

        let t_const = k.mk_const(t_name, b);
        let pred_var = k.mk_var(20, b);
        let pred = k.mk_abs(pred_var, pred_var);
        let app = k.mk_comb(pred, t_const);
        let existence = k.new_axiom(app).unwrap();

        let tyname: NameId = 200;
        let abs_name: NameId = 201;
        let rep_name: NameId = 202;
        let abs_var: NameId = 210;
        let rep_var: NameId = 211;
        let (th1, th2) = k
            .new_basic_type_definition(tyname, abs_name, rep_name, abs_var, rep_var, existence)
            .unwrap();

        assert!(k.hyps(th1).is_empty());
        assert!(k.hyps(th2).is_empty());
        assert_eq!(k.type_constants.get(&tyname), Some(&0));
        assert!(k.constants.contains_key(&abs_name));
        assert!(k.constants.contains_key(&rep_name));
    }
}
