//! PureKernel — Isabelle/Pure LCF-style kernel with 11 inference rules.
//!
//! All theorems (`ThmId`) are allocated in the arena and can only be constructed
//! through the inference rules, ensuring soundness.

use smol_str::SmolStr;

use crate::arena::{self, PureArena};
use crate::theory::Theory;
use crate::traits::*;
use crate::types::*;

/// The Isabelle/Pure kernel state.
pub struct PureKernel {
    arena: PureArena,
    theory: Theory,
    fun_id: NameId,
    prop_id: NameId,
    imp_id: NameId,
    all_id: NameId,
    eq_id: NameId,
}

impl PureKernel {
    /// Create a new Pure kernel with built-in `fun`, `prop`, and the three
    /// meta-connectives (`==>`, `!!`, `==`).
    pub fn new() -> Self {
        let fun_id = FUN_TYCON_ID;
        let prop_id = PROP_TYCON_ID;
        let imp_id = IMP_CONST_ID;
        let all_id = ALL_CONST_ID;
        let eq_id = EQ_CONST_ID;

        let mut arena = PureArena::new();
        let mut theory = Theory::new();

        // Register built-in type constructors.
        theory.type_constructors.insert(fun_id, 2); // fun takes 2 args
        theory.type_constructors.insert(prop_id, 0); // prop takes 0 args

        let prop = arena.alloc_type(TypDef::Type(prop_id, vec![]));

        // ==> : prop => prop => prop
        let pp = arena.alloc_type(TypDef::Type(fun_id, vec![prop, prop]));
        let imp_ty = arena.alloc_type(TypDef::Type(fun_id, vec![prop, pp]));
        theory.constants.insert(imp_id, imp_ty);

        // !! : ('a => prop) => prop  (polymorphic in 'a)
        let a_ix = IndexName {
            name: NameId::MAX,
            index: 0,
        };
        let a_var = arena.alloc_type(TypDef::TVar(a_ix, Sort::universal()));
        let a_to_prop = arena.alloc_type(TypDef::Type(fun_id, vec![a_var, prop]));
        let all_ty = arena.alloc_type(TypDef::Type(fun_id, vec![a_to_prop, prop]));
        theory.constants.insert(all_id, all_ty);

        // == : 'a => 'a => prop  (polymorphic in 'a)
        let b_ix = IndexName {
            name: NameId::MAX,
            index: 0,
        };
        let b_var = arena.alloc_type(TypDef::TVar(b_ix, Sort::universal()));
        let b_to_prop = arena.alloc_type(TypDef::Type(fun_id, vec![b_var, prop]));
        let eq_ty = arena.alloc_type(TypDef::Type(fun_id, vec![b_var, b_to_prop]));
        theory.constants.insert(eq_id, eq_ty);

        PureKernel {
            arena,
            theory,
            fun_id,
            prop_id,
            imp_id,
            all_id,
            eq_id,
        }
    }

    /// Access the underlying arena.
    pub fn arena(&self) -> &PureArena {
        &self.arena
    }

    /// Mutable access to the underlying arena.
    pub fn arena_mut(&mut self) -> &mut PureArena {
        &mut self.arena
    }

    /// Access the underlying theory.
    pub fn theory(&self) -> &Theory {
        &self.theory
    }

    /// Mutable access to the underlying theory.
    pub fn theory_mut(&mut self) -> &mut Theory {
        &mut self.theory
    }

    // -------------------------------------------------------------------
    // Helpers
    // -------------------------------------------------------------------

    fn prop_ty(&mut self) -> TypId {
        self.arena.alloc_type(TypDef::Type(self.prop_id, vec![]))
    }

    fn fun_ty(&mut self, a: TypId, b: TypId) -> TypId {
        self.arena.alloc_type(TypDef::Type(self.fun_id, vec![a, b]))
    }

    /// Check if a term has type `prop`.
    fn is_prop(&self, tm: TermId) -> bool {
        arena::is_prop(&self.arena, self.fun_id, self.prop_id, tm)
    }

    /// Make an implication: `A ==> B`.
    fn mk_imp_term(&mut self, a: TermId, b: TermId) -> TermId {
        let prop = self.prop_ty();
        let pp = self.fun_ty(prop, prop);
        let imp_ty = self.fun_ty(prop, pp);
        let imp = self.arena.alloc_term(TermDef::Const(self.imp_id, imp_ty));
        let imp_a = self.arena.alloc_term(TermDef::App(imp, a));
        self.arena.alloc_term(TermDef::App(imp_a, b))
    }

    /// Make a universal: `!! x::ty. body` (body has Bound(0) for x).
    fn mk_all_term(&mut self, hint: NameId, ty: TypId, body: TermId) -> TermId {
        let prop = self.prop_ty();
        let ty_to_prop = self.fun_ty(ty, prop);
        let all_ty = self.fun_ty(ty_to_prop, prop);
        let all = self.arena.alloc_term(TermDef::Const(self.all_id, all_ty));
        let abs = self.arena.alloc_term(TermDef::Abs(hint, ty, body));
        self.arena.alloc_term(TermDef::App(all, abs))
    }

    /// Make an equality: `a == b`.
    fn mk_eq_term(&mut self, a: TermId, b: TermId) -> TermId {
        let ty = arena::type_of(&mut self.arena, a, self.fun_id);
        let prop = self.prop_ty();
        let ty_to_prop = self.fun_ty(ty, prop);
        let eq_ty = self.fun_ty(ty, ty_to_prop);
        let eq = self.arena.alloc_term(TermDef::Const(self.eq_id, eq_ty));
        let eq_a = self.arena.alloc_term(TermDef::App(eq, a));
        self.arena.alloc_term(TermDef::App(eq_a, b))
    }

    /// Destruct an implication `A ==> B`.
    fn dest_imp_term(&self, tm: TermId) -> Option<(TermId, TermId)> {
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

    /// Destruct a universal `!!x::ty. body`.
    fn dest_all_term(&self, tm: TermId) -> Option<(NameId, TypId, TermId)> {
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

    /// Destruct an equality `a == b`.
    fn dest_eq_term(&self, tm: TermId) -> Option<(TermId, TermId)> {
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

    /// Merge two hypothesis lists (de Bruijn => structural == is alpha-eq).
    fn merge_hyps(&self, h1: &[TermId], h2: &[TermId]) -> Vec<TermId> {
        let mut result = h1.to_vec();
        for &h in h2 {
            if !result
                .iter()
                .any(|&existing| arena::terms_eq(&self.arena, existing, h))
            {
                result.push(h);
            }
        }
        result
    }

    /// Remove a hypothesis by structural equality.
    fn remove_hyp(&self, hyps: &[TermId], tm: TermId) -> Vec<TermId> {
        hyps.iter()
            .filter(|&&h| !arena::terms_eq(&self.arena, h, tm))
            .copied()
            .collect()
    }
}

// -------------------------------------------------------------------
// Trait implementations
// -------------------------------------------------------------------

impl IsabelleTypes for PureKernel {
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
        self.prop_ty()
    }

    fn fun_type(&mut self, a: Self::Type, b: Self::Type) -> Self::Type {
        self.fun_ty(a, b)
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

impl IsabelleTerms for PureKernel {
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
        self.mk_imp_term(a, b)
    }

    fn mk_all(&mut self, hint: NameId, ty: Self::Type, body: Self::Term) -> Self::Term {
        self.mk_all_term(hint, ty, body)
    }

    fn mk_eq(&mut self, a: Self::Term, b: Self::Term) -> Self::Term {
        self.mk_eq_term(a, b)
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
        self.dest_imp_term(tm)
    }

    fn dest_all(&self, tm: Self::Term) -> Option<(NameId, Self::Type, Self::Term)> {
        self.dest_all_term(tm)
    }

    fn dest_eq(&self, tm: Self::Term) -> Option<(Self::Term, Self::Term)> {
        self.dest_eq_term(tm)
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

impl IsabelleKernel for PureKernel {
    type Thm = ThmId;

    fn hyps(&self, th: Self::Thm) -> Vec<Self::Term> {
        self.arena.get_thm(th).hyps
    }

    fn concl(&self, th: Self::Thm) -> Self::Term {
        self.arena.get_thm(th).concl
    }

    fn assume(&mut self, tm: Self::Term) -> Result<Self::Thm, PureError> {
        if !self.is_prop(tm) {
            return Err(PureError::NotAProp);
        }
        Ok(self.arena.alloc_thm(ThmDef {
            hyps: vec![tm],
            concl: tm,
        }))
    }

    fn implies_intr(&mut self, a: Self::Term, th: Self::Thm) -> Result<Self::Thm, PureError> {
        if !self.is_prop(a) {
            return Err(PureError::NotAProp);
        }
        let thm = self.arena.get_thm(th);
        let hyps = self.remove_hyp(&thm.hyps, a);
        let concl = self.mk_imp_term(a, thm.concl);
        Ok(self.arena.alloc_thm(ThmDef { hyps, concl }))
    }

    fn implies_elim(&mut self, th1: Self::Thm, th2: Self::Thm) -> Result<Self::Thm, PureError> {
        let thm1 = self.arena.get_thm(th1);
        let (a, b) = self
            .dest_imp_term(thm1.concl)
            .ok_or(PureError::NotAnImplication)?;
        let thm2 = self.arena.get_thm(th2);
        if !arena::terms_eq(&self.arena, a, thm2.concl) {
            return Err(PureError::TypeMismatch(
                "implies_elim: antecedent mismatch".into(),
            ));
        }
        let hyps = self.merge_hyps(&thm1.hyps, &thm2.hyps);
        Ok(self.arena.alloc_thm(ThmDef { hyps, concl: b }))
    }

    fn forall_intr(
        &mut self,
        x: NameId,
        ty: Self::Type,
        th: Self::Thm,
    ) -> Result<Self::Thm, PureError> {
        let thm = self.arena.get_thm(th);
        // x must not be free in any hypothesis
        for &hyp in &thm.hyps {
            if arena::free_in(&self.arena, x, ty, hyp) {
                return Err(PureError::FreeVariable);
            }
        }
        let body = arena::abstract_over(&mut self.arena, x, ty, thm.concl);
        let concl = self.mk_all_term(x, ty, body);
        let hyps = thm.hyps;
        Ok(self.arena.alloc_thm(ThmDef { hyps, concl }))
    }

    fn forall_elim(&mut self, t: Self::Term, th: Self::Thm) -> Result<Self::Thm, PureError> {
        let thm = self.arena.get_thm(th);
        let (_hint, _ty, body) = self.dest_all_term(thm.concl).ok_or(PureError::NotAForall)?;
        let concl = arena::subst_bound(&mut self.arena, body, t);
        let hyps = thm.hyps;
        Ok(self.arena.alloc_thm(ThmDef { hyps, concl }))
    }

    fn reflexive(&mut self, t: Self::Term) -> Result<Self::Thm, PureError> {
        let concl = self.mk_eq_term(t, t);
        Ok(self.arena.alloc_thm(ThmDef {
            hyps: vec![],
            concl,
        }))
    }

    fn symmetric(&mut self, th: Self::Thm) -> Result<Self::Thm, PureError> {
        let thm = self.arena.get_thm(th);
        let (s, t) = self
            .dest_eq_term(thm.concl)
            .ok_or(PureError::NotAnEquation)?;
        let concl = self.mk_eq_term(t, s);
        Ok(self.arena.alloc_thm(ThmDef {
            hyps: thm.hyps,
            concl,
        }))
    }

    fn transitive(&mut self, th1: Self::Thm, th2: Self::Thm) -> Result<Self::Thm, PureError> {
        let thm1 = self.arena.get_thm(th1);
        let (s, t1) = self
            .dest_eq_term(thm1.concl)
            .ok_or(PureError::NotAnEquation)?;
        let thm2 = self.arena.get_thm(th2);
        let (t2, u) = self
            .dest_eq_term(thm2.concl)
            .ok_or(PureError::NotAnEquation)?;
        if !arena::terms_eq(&self.arena, t1, t2) {
            return Err(PureError::TypeMismatch(
                "transitive: middle terms don't match".into(),
            ));
        }
        let hyps = self.merge_hyps(&thm1.hyps, &thm2.hyps);
        let concl = self.mk_eq_term(s, u);
        Ok(self.arena.alloc_thm(ThmDef { hyps, concl }))
    }

    fn beta_conversion(&mut self, t: Self::Term) -> Result<Self::Thm, PureError> {
        if let TermDef::App(f, arg) = self.arena.get_term(t) {
            if let TermDef::Abs(_, _, body) = self.arena.get_term(f) {
                let reduced = arena::subst_bound(&mut self.arena, body, arg);
                let concl = self.mk_eq_term(t, reduced);
                return Ok(self.arena.alloc_thm(ThmDef {
                    hyps: vec![],
                    concl,
                }));
            }
        }
        Err(PureError::NotBetaRedex)
    }

    fn combination(&mut self, th1: Self::Thm, th2: Self::Thm) -> Result<Self::Thm, PureError> {
        let thm1 = self.arena.get_thm(th1);
        let (f, g) = self
            .dest_eq_term(thm1.concl)
            .ok_or(PureError::NotAnEquation)?;
        let thm2 = self.arena.get_thm(th2);
        let (a, b) = self
            .dest_eq_term(thm2.concl)
            .ok_or(PureError::NotAnEquation)?;
        // Check type compatibility
        let f_ty = arena::type_of(&mut self.arena, f, self.fun_id);
        match self.arena.get_type(f_ty) {
            TypDef::Type(n, args) if n == self.fun_id && args.len() == 2 => {
                let domain = args[0];
                let a_ty = arena::type_of(&mut self.arena, a, self.fun_id);
                if !arena::types_eq(&self.arena, domain, a_ty) {
                    return Err(PureError::TypeMismatch(
                        "combination: domain type mismatch".into(),
                    ));
                }
            }
            _ => {
                return Err(PureError::TypeMismatch(
                    "combination: first equation is not a function".into(),
                ));
            }
        }
        let hyps = self.merge_hyps(&thm1.hyps, &thm2.hyps);
        let fa = self.arena.alloc_term(TermDef::App(f, a));
        let gb = self.arena.alloc_term(TermDef::App(g, b));
        let concl = self.mk_eq_term(fa, gb);
        Ok(self.arena.alloc_thm(ThmDef { hyps, concl }))
    }

    fn abstraction(
        &mut self,
        x: NameId,
        ty: Self::Type,
        th: Self::Thm,
    ) -> Result<Self::Thm, PureError> {
        let thm = self.arena.get_thm(th);
        let (s, t) = self
            .dest_eq_term(thm.concl)
            .ok_or(PureError::NotAnEquation)?;
        // x must not be free in any hypothesis
        for &hyp in &thm.hyps {
            if arena::free_in(&self.arena, x, ty, hyp) {
                return Err(PureError::FreeVariable);
            }
        }
        let s_body = arena::abstract_over(&mut self.arena, x, ty, s);
        let t_body = arena::abstract_over(&mut self.arena, x, ty, t);
        let lhs = self.arena.alloc_term(TermDef::Abs(x, ty, s_body));
        let rhs = self.arena.alloc_term(TermDef::Abs(x, ty, t_body));
        let concl = self.mk_eq_term(lhs, rhs);
        Ok(self.arena.alloc_thm(ThmDef {
            hyps: thm.hyps,
            concl,
        }))
    }

    fn instantiate_typ_rule(
        &mut self,
        pairs: &[(Self::Type, IndexName)],
        th: Self::Thm,
    ) -> Result<Self::Thm, PureError> {
        let thm = self.arena.get_thm(th);
        let new_concl = arena::instantiate_typ_in_term(&mut self.arena, thm.concl, pairs);
        let new_hyps: Vec<TermId> = thm
            .hyps
            .iter()
            .map(|&h| arena::instantiate_typ_in_term(&mut self.arena, h, pairs))
            .collect();
        let mut deduped = Vec::new();
        for h in new_hyps {
            if !deduped
                .iter()
                .any(|&existing| arena::terms_eq(&self.arena, existing, h))
            {
                deduped.push(h);
            }
        }
        Ok(self.arena.alloc_thm(ThmDef {
            hyps: deduped,
            concl: new_concl,
        }))
    }

    fn instantiate_rule(
        &mut self,
        pairs: &[(Self::Term, IndexName, Self::Type)],
        th: Self::Thm,
    ) -> Result<Self::Thm, PureError> {
        let thm = self.arena.get_thm(th);
        let new_concl = arena::instantiate_term(&mut self.arena, thm.concl, pairs);
        let new_hyps: Vec<TermId> = thm
            .hyps
            .iter()
            .map(|&h| arena::instantiate_term(&mut self.arena, h, pairs))
            .collect();
        let mut deduped = Vec::new();
        for h in new_hyps {
            if !deduped
                .iter()
                .any(|&existing| arena::terms_eq(&self.arena, existing, h))
            {
                deduped.push(h);
            }
        }
        Ok(self.arena.alloc_thm(ThmDef {
            hyps: deduped,
            concl: new_concl,
        }))
    }

    fn axiom(&self, name: &str) -> Result<Self::Thm, PureError> {
        self.theory
            .axioms
            .get(name)
            .copied()
            .ok_or_else(|| PureError::UnknownAxiom(name.into()))
    }

    fn add_axiom(&mut self, name: SmolStr, tm: Self::Term) -> Result<Self::Thm, PureError> {
        if !self.is_prop(tm) {
            return Err(PureError::NotAProp);
        }
        let thm_id = self.arena.alloc_thm(ThmDef {
            hyps: vec![],
            concl: tm,
        });
        self.theory.axioms.insert(name, thm_id);
        Ok(thm_id)
    }

    fn add_type(&mut self, name: NameId, arity: usize) -> Result<(), PureError> {
        if self.theory.type_constructors.contains_key(&name) {
            return Err(PureError::TypeAlreadyDefined(name));
        }
        self.theory.type_constructors.insert(name, arity);
        Ok(())
    }

    fn add_constant(&mut self, name: NameId, ty: Self::Type) -> Result<(), PureError> {
        if self.theory.constants.contains_key(&name) {
            return Err(PureError::ConstantAlreadyDefined(name));
        }
        self.theory.constants.insert(name, ty);
        Ok(())
    }

    fn add_class(&mut self, class: NameId) -> Result<(), PureError> {
        self.theory.sorts.add_class(class)
    }

    fn add_subclass(&mut self, sub: NameId, sup: NameId) -> Result<(), PureError> {
        self.theory.sorts.add_subclass(sub, sup)
    }

    fn add_arity(
        &mut self,
        tycon: NameId,
        arg_sorts: Vec<Sort>,
        class: NameId,
    ) -> Result<(), PureError> {
        self.theory.sorts.add_arity(tycon, arg_sorts, class)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn mk_kernel() -> PureKernel {
        PureKernel::new()
    }

    #[test]
    fn test_assume() {
        let mut k = mk_kernel();
        let prop = k.prop_ty();
        let p = k.arena.alloc_term(TermDef::Free(10, prop));
        let th = IsabelleKernel::assume(&mut k, p).unwrap();
        let thm = k.arena.get_thm(th);
        assert_eq!(thm.hyps.len(), 1);
        assert!(arena::terms_eq(&k.arena, thm.hyps[0], p));
        assert!(arena::terms_eq(&k.arena, thm.concl, p));
    }

    #[test]
    fn test_assume_non_prop() {
        let mut k = mk_kernel();
        let ty = k.arena.alloc_type(TypDef::TFree(10, Sort::universal()));
        let x = k.arena.alloc_term(TermDef::Free(10, ty));
        assert!(IsabelleKernel::assume(&mut k, x).is_err());
    }

    #[test]
    fn test_implies_intr_elim() {
        let mut k = mk_kernel();
        let prop = k.prop_ty();
        let a = k.arena.alloc_term(TermDef::Free(10, prop));
        let b = k.arena.alloc_term(TermDef::Free(11, prop));

        // {B} |- B
        let th_b = IsabelleKernel::assume(&mut k, b).unwrap();
        // {} |- B ==> B
        let imp_bb = k.implies_intr(b, th_b).unwrap();
        assert!(k.arena.get_thm(imp_bb).hyps.is_empty());

        // {A} |- A
        let th_a = IsabelleKernel::assume(&mut k, a).unwrap();
        // {} |- A ==> A
        let imp_aa = k.implies_intr(a, th_a).unwrap();
        assert!(k.arena.get_thm(imp_aa).hyps.is_empty());

        // implies_elim(A ==> A, A) = A
        let _ = b; // suppress unused warning
        let result = k.implies_elim(imp_aa, th_a).unwrap();
        assert!(arena::terms_eq(&k.arena, k.arena.get_thm(result).concl, a));
    }

    #[test]
    fn test_implies_intr_removes_hyp() {
        let mut k = mk_kernel();
        let prop = k.prop_ty();
        let a = k.arena.alloc_term(TermDef::Free(10, prop));

        let th_a = IsabelleKernel::assume(&mut k, a).unwrap();
        let result = k.implies_intr(a, th_a).unwrap();
        assert!(k.arena.get_thm(result).hyps.is_empty());
    }

    #[test]
    fn test_forall_intr_elim() {
        let mut k = mk_kernel();
        let prop = k.prop_ty();
        let x_name: NameId = 10;
        let x = k.arena.alloc_term(TermDef::Free(x_name, prop));

        // {x} |- x
        let th = IsabelleKernel::assume(&mut k, x).unwrap();

        // forall_intr should fail because x is free in hypothesis
        assert!(k.forall_intr(x_name, prop, th).is_err());

        // Use implies_intr first to clear the hypothesis
        let imp = k.implies_intr(x, th).unwrap();
        // {} |- x ==> x — Now forall_intr works
        let forall = k.forall_intr(x_name, prop, imp).unwrap();
        assert!(k.arena.get_thm(forall).hyps.is_empty());
        assert!(k.dest_all_term(k.arena.get_thm(forall).concl).is_some());

        // forall_elim with a different term
        let y = k.arena.alloc_term(TermDef::Free(11, prop));
        let result = k.forall_elim(y, forall).unwrap();
        // Should get y ==> y
        let (a, b) = k.dest_imp_term(k.arena.get_thm(result).concl).unwrap();
        assert!(arena::terms_eq(&k.arena, a, y));
        assert!(arena::terms_eq(&k.arena, b, y));
    }

    #[test]
    fn test_reflexive() {
        let mut k = mk_kernel();
        let prop = k.prop_ty();
        let x = k.arena.alloc_term(TermDef::Free(10, prop));
        let th = k.reflexive(x).unwrap();
        let thm = k.arena.get_thm(th);
        assert!(thm.hyps.is_empty());
        let (l, r) = k.dest_eq_term(thm.concl).unwrap();
        assert!(arena::terms_eq(&k.arena, l, x));
        assert!(arena::terms_eq(&k.arena, r, x));
    }

    #[test]
    fn test_symmetric() {
        let mut k = mk_kernel();
        let prop = k.prop_ty();
        let x = k.arena.alloc_term(TermDef::Free(10, prop));
        let y = k.arena.alloc_term(TermDef::Free(11, prop));

        // Build x == y manually for testing
        let eq_concl = k.mk_eq_term(x, y);
        let th = k.arena.alloc_thm(ThmDef {
            hyps: vec![],
            concl: eq_concl,
        });
        let sym = k.symmetric(th).unwrap();
        let (l, r) = k.dest_eq_term(k.arena.get_thm(sym).concl).unwrap();
        assert!(arena::terms_eq(&k.arena, l, y));
        assert!(arena::terms_eq(&k.arena, r, x));
    }

    #[test]
    fn test_transitive() {
        let mut k = mk_kernel();
        let prop = k.prop_ty();
        let x = k.arena.alloc_term(TermDef::Free(10, prop));
        let refl_x = k.reflexive(x).unwrap();
        let result = k.transitive(refl_x, refl_x).unwrap();
        let (l, r) = k.dest_eq_term(k.arena.get_thm(result).concl).unwrap();
        assert!(arena::terms_eq(&k.arena, l, x));
        assert!(arena::terms_eq(&k.arena, r, x));
    }

    #[test]
    fn test_beta_conversion() {
        let mut k = mk_kernel();
        let prop = k.prop_ty();
        let a = k.arena.alloc_term(TermDef::Free(42, prop));
        // (λx::prop. Bound(0)) a => a
        let body = k.arena.alloc_term(TermDef::Bound(0));
        let abs = k.arena.alloc_term(TermDef::Abs(99, prop, body));
        let app = k.arena.alloc_term(TermDef::App(abs, a));
        let th = k.beta_conversion(app).unwrap();
        let (_, rhs) = k.dest_eq_term(k.arena.get_thm(th).concl).unwrap();
        assert!(arena::terms_eq(&k.arena, rhs, a));
    }

    #[test]
    fn test_combination() {
        let mut k = mk_kernel();
        let prop = k.prop_ty();
        let f_ty = k.fun_ty(prop, prop);
        let f = k.arena.alloc_term(TermDef::Free(10, f_ty));
        let x = k.arena.alloc_term(TermDef::Free(12, prop));

        let refl_f = k.reflexive(f).unwrap();
        let refl_x = k.reflexive(x).unwrap();
        let result = k.combination(refl_f, refl_x).unwrap();
        let (l, r) = k.dest_eq_term(k.arena.get_thm(result).concl).unwrap();
        assert!(arena::terms_eq(&k.arena, l, r));
        match k.arena.get_term(l) {
            TermDef::App(ff, xx) => {
                assert!(arena::terms_eq(&k.arena, ff, f));
                assert!(arena::terms_eq(&k.arena, xx, x));
            }
            _ => panic!("expected App"),
        }
    }

    #[test]
    fn test_combination_type_mismatch() {
        let mut k = mk_kernel();
        let prop = k.prop_ty();
        let a_ty = k.arena.alloc_type(TypDef::TFree(100, Sort::universal()));
        let f_ty = k.fun_ty(a_ty, prop);
        let f = k.arena.alloc_term(TermDef::Free(10, f_ty));
        let x = k.arena.alloc_term(TermDef::Free(12, prop));

        let refl_f = k.reflexive(f).unwrap();
        let refl_x = k.reflexive(x).unwrap();
        assert!(k.combination(refl_f, refl_x).is_err());
    }

    #[test]
    fn test_abstraction() {
        let mut k = mk_kernel();
        let prop = k.prop_ty();
        let x_name: NameId = 10;
        let x = k.arena.alloc_term(TermDef::Free(x_name, prop));

        let refl_x = k.reflexive(x).unwrap();
        let result = k.abstraction(x_name, prop, refl_x).unwrap();
        let (l, r) = k.dest_eq_term(k.arena.get_thm(result).concl).unwrap();
        assert!(arena::terms_eq(&k.arena, l, r));
        match k.arena.get_term(l) {
            TermDef::Abs(hint, ty, body) => {
                assert_eq!(hint, x_name);
                assert!(arena::types_eq(&k.arena, ty, prop));
                assert_eq!(k.arena.get_term(body), TermDef::Bound(0));
            }
            _ => panic!("expected Abs"),
        }
    }

    #[test]
    fn test_add_axiom() {
        let mut k = mk_kernel();
        let prop = k.prop_ty();
        let a = k.arena.alloc_term(TermDef::Free(10, prop));
        let th = IsabelleKernel::add_axiom(&mut k, SmolStr::new("test"), a).unwrap();
        let thm = k.arena.get_thm(th);
        assert!(thm.hyps.is_empty());
        assert!(arena::terms_eq(&k.arena, thm.concl, a));

        let looked_up = k.axiom("test").unwrap();
        assert!(arena::terms_eq(
            &k.arena,
            k.arena.get_thm(looked_up).concl,
            a
        ));
    }

    #[test]
    fn test_add_axiom_non_prop() {
        let mut k = mk_kernel();
        let ty = k.arena.alloc_type(TypDef::TFree(10, Sort::universal()));
        let x = k.arena.alloc_term(TermDef::Free(10, ty));
        assert!(IsabelleKernel::add_axiom(&mut k, SmolStr::new("bad"), x).is_err());
    }

    #[test]
    fn test_unknown_axiom() {
        let k = mk_kernel();
        assert!(k.axiom("nonexistent").is_err());
    }

    #[test]
    fn test_add_type() {
        let mut k = mk_kernel();
        assert!(IsabelleKernel::add_type(&mut k, 100, 2).is_ok());
        assert!(IsabelleKernel::add_type(&mut k, 100, 1).is_err()); // duplicate
    }

    #[test]
    fn test_add_constant() {
        let mut k = mk_kernel();
        let ty = k.arena.alloc_type(TypDef::TFree(10, Sort::universal()));
        assert!(IsabelleKernel::add_constant(&mut k, 100, ty).is_ok());
        assert!(IsabelleKernel::add_constant(&mut k, 100, ty).is_err()); // duplicate
    }

    #[test]
    fn test_instantiate_typ_rule() {
        let mut k = mk_kernel();
        let ix = IndexName { name: 10, index: 0 };
        let ty = k
            .arena
            .alloc_type(TypDef::TVar(ix.clone(), Sort::universal()));
        let x = k.arena.alloc_term(TermDef::Free(42, ty));
        let th = k.reflexive(x).unwrap();
        let new_ty = k.arena.alloc_type(TypDef::Type(100, vec![]));
        let result = k.instantiate_typ_rule(&[(new_ty, ix)], th).unwrap();
        let (l, _) = k.dest_eq_term(k.arena.get_thm(result).concl).unwrap();
        match k.arena.get_term(l) {
            TermDef::Free(42, t) => assert!(arena::types_eq(&k.arena, t, new_ty)),
            _ => panic!("expected Free"),
        }
    }

    #[test]
    fn test_instantiate_rule() {
        let mut k = mk_kernel();
        let prop = k.prop_ty();
        let ix = IndexName { name: 10, index: 0 };
        let v = k.arena.alloc_term(TermDef::Var(ix.clone(), prop));
        let th = k.reflexive(v).unwrap();
        let replacement = k.arena.alloc_term(TermDef::Free(42, prop));
        let result = k.instantiate_rule(&[(replacement, ix, prop)], th).unwrap();
        let (l, r) = k.dest_eq_term(k.arena.get_thm(result).concl).unwrap();
        assert!(arena::terms_eq(&k.arena, l, replacement));
        assert!(arena::terms_eq(&k.arena, r, replacement));
    }

    #[test]
    fn test_implies_elim_mismatch() {
        let mut k = mk_kernel();
        let prop = k.prop_ty();
        let a = k.arena.alloc_term(TermDef::Free(10, prop));
        let b = k.arena.alloc_term(TermDef::Free(11, prop));
        let c = k.arena.alloc_term(TermDef::Free(12, prop));

        // Build A ==> B manually
        let imp_concl = k.mk_imp_term(a, b);
        let imp_ab = k.arena.alloc_thm(ThmDef {
            hyps: vec![],
            concl: imp_concl,
        });
        // Try implies_elim with C instead of A — should fail
        let th_c = IsabelleKernel::assume(&mut k, c).unwrap();
        assert!(k.implies_elim(imp_ab, th_c).is_err());

        // But with A it works
        let th_a = IsabelleKernel::assume(&mut k, a).unwrap();
        let result = k.implies_elim(imp_ab, th_a).unwrap();
        assert!(arena::terms_eq(&k.arena, k.arena.get_thm(result).concl, b));
    }

    #[test]
    fn test_built_in_types_and_constants() {
        let k = mk_kernel();
        assert_eq!(k.theory().type_constructors.get(&FUN_TYCON_ID), Some(&2));
        assert_eq!(k.theory().type_constructors.get(&PROP_TYCON_ID), Some(&0));
        assert!(k.theory().constants.contains_key(&IMP_CONST_ID));
        assert!(k.theory().constants.contains_key(&ALL_CONST_ID));
        assert!(k.theory().constants.contains_key(&EQ_CONST_ID));
    }
}
