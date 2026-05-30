//! Arena storage for Isabelle types, terms, and theorems.
//!
//! Plain `Vec` arenas with `&mut self` allocation and `&self` lookup.
//! `get_*` methods clone the small def out to avoid borrow-across-alloc issues.

use crate::types::*;

/// Arena storage for types, terms, and theorems.
pub struct PureArena {
    types: Vec<TypDef>,
    terms: Vec<TermDef>,
    thms: Vec<ThmDef>,
}

impl PureArena {
    /// Create an empty arena.
    pub fn new() -> Self {
        PureArena {
            types: Vec::new(),
            terms: Vec::new(),
            thms: Vec::new(),
        }
    }

    // -- Allocation --

    /// Allocate a type, returning its index.
    pub fn alloc_type(&mut self, def: TypDef) -> TypId {
        let id = TypId(self.types.len() as u32);
        self.types.push(def);
        id
    }

    /// Allocate a term, returning its index.
    pub fn alloc_term(&mut self, def: TermDef) -> TermId {
        let id = TermId(self.terms.len() as u32);
        self.terms.push(def);
        id
    }

    /// Allocate a theorem, returning its index.
    pub fn alloc_thm(&mut self, def: ThmDef) -> ThmId {
        let id = ThmId(self.thms.len() as u32);
        self.thms.push(def);
        id
    }

    // -- Lookup (clone out to avoid borrow conflicts) --

    /// Get a type definition by index (cloned).
    pub fn get_type(&self, id: TypId) -> TypDef {
        self.types[id.0 as usize].clone()
    }

    /// Get a term definition by index (cloned).
    pub fn get_term(&self, id: TermId) -> TermDef {
        self.terms[id.0 as usize].clone()
    }

    /// Get a theorem definition by index (cloned).
    pub fn get_thm(&self, id: ThmId) -> ThmDef {
        self.thms[id.0 as usize].clone()
    }

    // -- Slice access --

    /// All type definitions.
    pub fn types(&self) -> &[TypDef] {
        &self.types
    }

    /// All term definitions.
    pub fn terms(&self) -> &[TermDef] {
        &self.terms
    }

    /// All theorem definitions.
    pub fn thms(&self) -> &[ThmDef] {
        &self.thms
    }
}

// ---------------------------------------------------------------------------
// Arena-based free functions
// ---------------------------------------------------------------------------

/// Structural equality of types (recursive).
/// Since indices are unique per allocation, same index means same type.
/// Different indices require recursive comparison.
pub fn types_eq(arena: &PureArena, a: TypId, b: TypId) -> bool {
    if a == b {
        return true;
    }
    match (arena.get_type(a), arena.get_type(b)) {
        (TypDef::TFree(n1, s1), TypDef::TFree(n2, s2)) => n1 == n2 && s1 == s2,
        (TypDef::TVar(ix1, s1), TypDef::TVar(ix2, s2)) => ix1 == ix2 && s1 == s2,
        (TypDef::Type(n1, args1), TypDef::Type(n2, args2)) => {
            n1 == n2
                && args1.len() == args2.len()
                && args1
                    .iter()
                    .zip(args2.iter())
                    .all(|(&a, &b)| types_eq(arena, a, b))
        }
        _ => false,
    }
}

/// Structural equality of terms.
/// De Bruijn indices give alpha-equivalence for free.
pub fn terms_eq(arena: &PureArena, a: TermId, b: TermId) -> bool {
    if a == b {
        return true;
    }
    match (arena.get_term(a), arena.get_term(b)) {
        (TermDef::Bound(i1), TermDef::Bound(i2)) => i1 == i2,
        (TermDef::Free(n1, ty1), TermDef::Free(n2, ty2)) => n1 == n2 && types_eq(arena, ty1, ty2),
        (TermDef::Var(ix1, ty1), TermDef::Var(ix2, ty2)) => ix1 == ix2 && types_eq(arena, ty1, ty2),
        (TermDef::Const(n1, ty1), TermDef::Const(n2, ty2)) => n1 == n2 && types_eq(arena, ty1, ty2),
        (TermDef::App(f1, x1), TermDef::App(f2, x2)) => {
            terms_eq(arena, f1, f2) && terms_eq(arena, x1, x2)
        }
        (TermDef::Abs(h1, ty1, b1), TermDef::Abs(h2, ty2, b2)) => {
            h1 == h2 && types_eq(arena, ty1, ty2) && terms_eq(arena, b1, b2)
        }
        _ => false,
    }
}

/// Collect all free type variables (TFree) in a type.
pub fn tyfrees(arena: &PureArena, ty: TypId) -> Vec<(NameId, Sort)> {
    let mut result = Vec::new();
    tyfrees_acc(arena, ty, &mut result);
    result
}

fn tyfrees_acc(arena: &PureArena, ty: TypId, acc: &mut Vec<(NameId, Sort)>) {
    match arena.get_type(ty) {
        TypDef::TFree(n, s) => {
            if !acc.iter().any(|(name, _)| *name == n) {
                acc.push((n, s));
            }
        }
        TypDef::TVar(_, _) => {}
        TypDef::Type(_, args) => {
            for arg in args {
                tyfrees_acc(arena, arg, acc);
            }
        }
    }
}

/// Collect all schematic type variables (TVar) in a type.
pub fn tyvars(arena: &PureArena, ty: TypId) -> Vec<(IndexName, Sort)> {
    let mut result = Vec::new();
    tyvars_acc(arena, ty, &mut result);
    result
}

fn tyvars_acc(arena: &PureArena, ty: TypId, acc: &mut Vec<(IndexName, Sort)>) {
    match arena.get_type(ty) {
        TypDef::TFree(_, _) => {}
        TypDef::TVar(ix, s) => {
            if !acc.iter().any(|(name, _)| name == &ix) {
                acc.push((ix, s));
            }
        }
        TypDef::Type(_, args) => {
            for arg in args {
                tyvars_acc(arena, arg, acc);
            }
        }
    }
}

/// Instantiate schematic type variables.
/// `pairs` is `(new_type, old_indexname)`.
pub fn instantiate_typ(arena: &mut PureArena, ty: TypId, pairs: &[(TypId, IndexName)]) -> TypId {
    if pairs.is_empty() {
        return ty;
    }
    match arena.get_type(ty) {
        TypDef::TFree(_, _) => ty,
        TypDef::TVar(ix, _) => {
            for &(replacement, ref var) in pairs {
                if *var == ix {
                    return replacement;
                }
            }
            ty
        }
        TypDef::Type(name, args) => {
            let new_args: Vec<TypId> = args
                .iter()
                .map(|&a| instantiate_typ(arena, a, pairs))
                .collect();
            if new_args == args {
                ty
            } else {
                arena.alloc_type(TypDef::Type(name, new_args))
            }
        }
    }
}

/// Compute the type of a term.
/// Requires `fun_id` to identify function type constructors.
/// Allocates for the `Abs` case.
pub fn type_of(arena: &mut PureArena, tm: TermId, fun_id: NameId) -> TypId {
    type_of_env(arena, tm, fun_id, &[])
}

fn type_of_env(arena: &mut PureArena, tm: TermId, fun_id: NameId, bound_types: &[TypId]) -> TypId {
    match arena.get_term(tm) {
        TermDef::Bound(i) => bound_types[i as usize],
        TermDef::Free(_, ty) | TermDef::Var(_, ty) | TermDef::Const(_, ty) => ty,
        TermDef::App(f, _) => {
            let f_ty = type_of_env(arena, f, fun_id, bound_types);
            match arena.get_type(f_ty) {
                TypDef::Type(n, args) if n == fun_id && args.len() == 2 => args[1],
                _ => panic!("type_of: ill-typed application"),
            }
        }
        TermDef::Abs(_, var_ty, body) => {
            let mut new_env = vec![var_ty];
            new_env.extend_from_slice(bound_types);
            let body_ty = type_of_env(arena, body, fun_id, &new_env);
            arena.alloc_type(TypDef::Type(fun_id, vec![var_ty, body_ty]))
        }
    }
}

/// Read-only type_of — works without allocation for Bound/Free/Var/Const/App.
/// For Abs, searches the arena for an existing function type.
pub fn type_of_ro(arena: &PureArena, tm: TermId, fun_id: NameId) -> TypId {
    match arena.get_term(tm) {
        TermDef::Bound(_) => panic!("type_of_ro: cannot determine type of bare Bound"),
        TermDef::Free(_, ty) | TermDef::Var(_, ty) | TermDef::Const(_, ty) => ty,
        TermDef::App(f, _) => {
            let f_ty = type_of_ro(arena, f, fun_id);
            match arena.get_type(f_ty) {
                TypDef::Type(n, args) if n == fun_id && args.len() == 2 => args[1],
                _ => panic!("type_of_ro: ill-typed application"),
            }
        }
        TermDef::Abs(_, var_ty, body) => {
            let body_ty = type_of_ro(arena, body, fun_id);
            // Search the arena for an existing matching type
            for (i, def) in arena.types().iter().enumerate() {
                if let TypDef::Type(n, args) = def {
                    if *n == fun_id && args.len() == 2 && args[0] == var_ty && args[1] == body_ty {
                        return TypId(i as u32);
                    }
                }
            }
            panic!("type_of_ro: function type not yet in arena for Abs")
        }
    }
}

/// Collect free variables in a term.
pub fn frees(arena: &PureArena, tm: TermId) -> Vec<(NameId, TypId)> {
    let mut result = Vec::new();
    frees_acc(arena, tm, &mut result);
    result
}

fn frees_acc(arena: &PureArena, tm: TermId, acc: &mut Vec<(NameId, TypId)>) {
    match arena.get_term(tm) {
        TermDef::Free(n, ty) => {
            if !acc.iter().any(|(name, _)| *name == n) {
                acc.push((n, ty));
            }
        }
        TermDef::Bound(_) | TermDef::Var(_, _) | TermDef::Const(_, _) => {}
        TermDef::App(f, x) => {
            frees_acc(arena, f, acc);
            frees_acc(arena, x, acc);
        }
        TermDef::Abs(_, _, body) => {
            frees_acc(arena, body, acc);
        }
    }
}

/// Collect schematic variables in a term.
pub fn vars(arena: &PureArena, tm: TermId) -> Vec<(IndexName, TypId)> {
    let mut result = Vec::new();
    vars_acc(arena, tm, &mut result);
    result
}

fn vars_acc(arena: &PureArena, tm: TermId, acc: &mut Vec<(IndexName, TypId)>) {
    match arena.get_term(tm) {
        TermDef::Var(ix, ty) => {
            if !acc.iter().any(|(name, _)| name == &ix) {
                acc.push((ix, ty));
            }
        }
        TermDef::Bound(_) | TermDef::Free(_, _) | TermDef::Const(_, _) => {}
        TermDef::App(f, x) => {
            vars_acc(arena, f, acc);
            vars_acc(arena, x, acc);
        }
        TermDef::Abs(_, _, body) => {
            vars_acc(arena, body, acc);
        }
    }
}

/// Check if a free variable occurs in a term.
pub fn free_in(arena: &PureArena, name: NameId, ty: TypId, tm: TermId) -> bool {
    match arena.get_term(tm) {
        TermDef::Free(n, t) => n == name && types_eq(arena, t, ty),
        TermDef::Bound(_) | TermDef::Var(_, _) | TermDef::Const(_, _) => false,
        TermDef::App(f, x) => free_in(arena, name, ty, f) || free_in(arena, name, ty, x),
        TermDef::Abs(_, _, body) => free_in(arena, name, ty, body),
    }
}

/// Substitute `arg` for `Bound(0)` in `body`, decrementing all other indices.
/// This is the core of beta-reduction.
pub fn subst_bound(arena: &mut PureArena, body: TermId, arg: TermId) -> TermId {
    subst_bound_at(arena, body, arg, 0)
}

fn subst_bound_at(arena: &mut PureArena, tm: TermId, arg: TermId, level: u32) -> TermId {
    match arena.get_term(tm) {
        TermDef::Bound(i) => {
            if i == level {
                incr_boundvars(arena, arg, level, 0)
            } else if i > level {
                arena.alloc_term(TermDef::Bound(i - 1))
            } else {
                tm
            }
        }
        TermDef::Free(_, _) | TermDef::Var(_, _) | TermDef::Const(_, _) => tm,
        TermDef::App(f, x) => {
            let f2 = subst_bound_at(arena, f, arg, level);
            let x2 = subst_bound_at(arena, x, arg, level);
            if f2 == f && x2 == x {
                tm
            } else {
                arena.alloc_term(TermDef::App(f2, x2))
            }
        }
        TermDef::Abs(hint, ty, body) => {
            let body2 = subst_bound_at(arena, body, arg, level + 1);
            if body2 == body {
                tm
            } else {
                arena.alloc_term(TermDef::Abs(hint, ty, body2))
            }
        }
    }
}

/// Increment bound variable indices >= `cutoff` by `inc`.
pub fn incr_boundvars(arena: &mut PureArena, tm: TermId, inc: u32, cutoff: u32) -> TermId {
    if inc == 0 {
        return tm;
    }
    match arena.get_term(tm) {
        TermDef::Bound(i) => {
            if i >= cutoff {
                arena.alloc_term(TermDef::Bound(i + inc))
            } else {
                tm
            }
        }
        TermDef::Free(_, _) | TermDef::Var(_, _) | TermDef::Const(_, _) => tm,
        TermDef::App(f, x) => {
            let f2 = incr_boundvars(arena, f, inc, cutoff);
            let x2 = incr_boundvars(arena, x, inc, cutoff);
            if f2 == f && x2 == x {
                tm
            } else {
                arena.alloc_term(TermDef::App(f2, x2))
            }
        }
        TermDef::Abs(hint, ty, body) => {
            let body2 = incr_boundvars(arena, body, inc, cutoff + 1);
            if body2 == body {
                tm
            } else {
                arena.alloc_term(TermDef::Abs(hint, ty, body2))
            }
        }
    }
}

/// Turn `Free(name, ty)` into `Bound` — build an abstraction body.
/// Returns the body where all occurrences of `Free(name, ty)` are replaced
/// with `Bound(level)` (using the given starting level, typically 0).
pub fn abstract_over(arena: &mut PureArena, name: NameId, ty: TypId, body: TermId) -> TermId {
    abstract_at(arena, name, ty, body, 0)
}

fn abstract_at(arena: &mut PureArena, name: NameId, ty: TypId, tm: TermId, level: u32) -> TermId {
    match arena.get_term(tm) {
        TermDef::Free(n, t) if n == name && types_eq(arena, t, ty) => {
            arena.alloc_term(TermDef::Bound(level))
        }
        TermDef::Free(_, _) | TermDef::Bound(_) | TermDef::Var(_, _) | TermDef::Const(_, _) => tm,
        TermDef::App(f, x) => {
            let f2 = abstract_at(arena, name, ty, f, level);
            let x2 = abstract_at(arena, name, ty, x, level);
            if f2 == f && x2 == x {
                tm
            } else {
                arena.alloc_term(TermDef::App(f2, x2))
            }
        }
        TermDef::Abs(hint, abs_ty, body) => {
            let body2 = abstract_at(arena, name, ty, body, level + 1);
            if body2 == body {
                tm
            } else {
                arena.alloc_term(TermDef::Abs(hint, abs_ty, body2))
            }
        }
    }
}

/// Substitute schematic term variables.
/// `pairs` is `(new_term, old_indexname, old_type)`.
pub fn instantiate_term(
    arena: &mut PureArena,
    tm: TermId,
    pairs: &[(TermId, IndexName, TypId)],
) -> TermId {
    if pairs.is_empty() {
        return tm;
    }
    match arena.get_term(tm) {
        TermDef::Var(ix, ty) => {
            for &(replacement, ref var_ix, var_ty) in pairs {
                if *var_ix == ix && types_eq(arena, var_ty, ty) {
                    return replacement;
                }
            }
            tm
        }
        TermDef::Bound(_) | TermDef::Free(_, _) | TermDef::Const(_, _) => tm,
        TermDef::App(f, x) => {
            let f2 = instantiate_term(arena, f, pairs);
            let x2 = instantiate_term(arena, x, pairs);
            if f2 == f && x2 == x {
                tm
            } else {
                arena.alloc_term(TermDef::App(f2, x2))
            }
        }
        TermDef::Abs(hint, ty, body) => {
            let body2 = instantiate_term(arena, body, pairs);
            if body2 == body {
                tm
            } else {
                arena.alloc_term(TermDef::Abs(hint, ty, body2))
            }
        }
    }
}

/// Substitute schematic type variables in a term (propagates through types).
/// `pairs` is `(new_type, old_indexname)`.
pub fn instantiate_typ_in_term(
    arena: &mut PureArena,
    tm: TermId,
    pairs: &[(TypId, IndexName)],
) -> TermId {
    if pairs.is_empty() {
        return tm;
    }
    match arena.get_term(tm) {
        TermDef::Bound(_) => tm,
        TermDef::Free(n, ty) => {
            let ty2 = instantiate_typ(arena, ty, pairs);
            if ty2 == ty {
                tm
            } else {
                arena.alloc_term(TermDef::Free(n, ty2))
            }
        }
        TermDef::Var(ix, ty) => {
            let ty2 = instantiate_typ(arena, ty, pairs);
            if ty2 == ty {
                tm
            } else {
                arena.alloc_term(TermDef::Var(ix, ty2))
            }
        }
        TermDef::Const(n, ty) => {
            let ty2 = instantiate_typ(arena, ty, pairs);
            if ty2 == ty {
                tm
            } else {
                arena.alloc_term(TermDef::Const(n, ty2))
            }
        }
        TermDef::App(f, x) => {
            let f2 = instantiate_typ_in_term(arena, f, pairs);
            let x2 = instantiate_typ_in_term(arena, x, pairs);
            if f2 == f && x2 == x {
                tm
            } else {
                arena.alloc_term(TermDef::App(f2, x2))
            }
        }
        TermDef::Abs(hint, ty, body) => {
            let ty2 = instantiate_typ(arena, ty, pairs);
            let body2 = instantiate_typ_in_term(arena, body, pairs);
            if ty2 == ty && body2 == body {
                tm
            } else {
                arena.alloc_term(TermDef::Abs(hint, ty2, body2))
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Constructor helpers
// ---------------------------------------------------------------------------

/// Allocate the `prop` type.
pub fn mk_prop_type(arena: &mut PureArena, prop_id: NameId) -> TypId {
    arena.alloc_type(TypDef::Type(prop_id, vec![]))
}

/// Allocate a function type `a => b`.
pub fn mk_fun_type(arena: &mut PureArena, fun_id: NameId, domain: TypId, codomain: TypId) -> TypId {
    arena.alloc_type(TypDef::Type(fun_id, vec![domain, codomain]))
}

/// Check if a term has type `prop` (read-only, assumes prop type is in arena).
pub fn is_prop(arena: &PureArena, fun_id: NameId, prop_id: NameId, tm: TermId) -> bool {
    let ty = type_of_ro(arena, tm, fun_id);
    match arena.get_type(ty) {
        TypDef::Type(n, args) => n == prop_id && args.is_empty(),
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_alloc_and_get() {
        let mut arena = PureArena::new();
        let tv = arena.alloc_type(TypDef::TFree(10, Sort::universal()));
        assert_eq!(arena.get_type(tv), TypDef::TFree(10, Sort::universal()));
    }

    #[test]
    fn test_types_eq() {
        let mut arena = PureArena::new();
        let a = arena.alloc_type(TypDef::TFree(10, Sort::universal()));
        let b = arena.alloc_type(TypDef::TFree(10, Sort::universal()));
        assert!(types_eq(&arena, a, b));

        let c = arena.alloc_type(TypDef::TFree(11, Sort::universal()));
        assert!(!types_eq(&arena, a, c));
    }

    #[test]
    fn test_terms_eq_de_bruijn() {
        let mut arena = PureArena::new();
        let ty = arena.alloc_type(TypDef::TFree(10, Sort::universal()));
        // \x. Bound(0) and \y. Bound(0) are structurally equal
        let body = arena.alloc_term(TermDef::Bound(0));
        let abs1 = arena.alloc_term(TermDef::Abs(99, ty, body));
        let abs2 = arena.alloc_term(TermDef::Abs(99, ty, body));
        assert!(terms_eq(&arena, abs1, abs2));
    }

    #[test]
    fn test_prop_type() {
        let mut arena = PureArena::new();
        let p = mk_prop_type(&mut arena, PROP_TYCON_ID);
        assert_eq!(arena.get_type(p), TypDef::Type(PROP_TYCON_ID, vec![]));
    }

    #[test]
    fn test_fun_type() {
        let mut arena = PureArena::new();
        let a = arena.alloc_type(TypDef::TFree(10, Sort::universal()));
        let b = arena.alloc_type(TypDef::TFree(11, Sort::universal()));
        let f = mk_fun_type(&mut arena, FUN_TYCON_ID, a, b);
        assert_eq!(arena.get_type(f), TypDef::Type(FUN_TYCON_ID, vec![a, b]));
    }

    #[test]
    fn test_instantiate_typ() {
        let mut arena = PureArena::new();
        let ix = IndexName { name: 10, index: 0 };
        let a = arena.alloc_type(TypDef::TVar(ix.clone(), Sort::universal()));
        let f = mk_fun_type(&mut arena, FUN_TYCON_ID, a, a);
        let int_ty = arena.alloc_type(TypDef::Type(100, vec![]));
        let result = instantiate_typ(&mut arena, f, &[(int_ty, ix)]);
        assert_eq!(
            arena.get_type(result),
            TypDef::Type(FUN_TYCON_ID, vec![int_ty, int_ty])
        );
    }

    #[test]
    fn test_subst_bound_identity() {
        let mut arena = PureArena::new();
        let ty = arena.alloc_type(TypDef::TFree(10, Sort::universal()));
        // body = Bound(0), arg = Free(42, ty)
        let body = arena.alloc_term(TermDef::Bound(0));
        let arg = arena.alloc_term(TermDef::Free(42, ty));
        let result = subst_bound(&mut arena, body, arg);
        assert_eq!(arena.get_term(result), TermDef::Free(42, ty));
    }

    #[test]
    fn test_subst_bound_nested() {
        let mut arena = PureArena::new();
        let ty = arena.alloc_type(TypDef::TFree(10, Sort::universal()));
        // body = Abs(hint_y, ty, Bound(1)) — Bound(1) refers to outer binder
        let inner_body = arena.alloc_term(TermDef::Bound(1));
        let body = arena.alloc_term(TermDef::Abs(200, ty, inner_body));
        let arg = arena.alloc_term(TermDef::Free(42, ty));
        let result = subst_bound(&mut arena, body, arg);
        // Should be Abs(200, ty, Free(42, ty))
        match arena.get_term(result) {
            TermDef::Abs(hint, _, inner) => {
                assert_eq!(hint, 200);
                assert_eq!(arena.get_term(inner), TermDef::Free(42, ty));
            }
            _ => panic!("expected Abs"),
        }
    }

    #[test]
    fn test_abstract_over() {
        let mut arena = PureArena::new();
        let ty = arena.alloc_type(TypDef::TFree(10, Sort::universal()));
        let x = arena.alloc_term(TermDef::Free(42, ty));
        let f = arena.alloc_term(TermDef::Const(99, ty));
        let app = arena.alloc_term(TermDef::App(f, x));
        let body = abstract_over(&mut arena, 42, ty, app);
        match arena.get_term(body) {
            TermDef::App(f2, x2) => {
                assert_eq!(f2, f);
                assert_eq!(arena.get_term(x2), TermDef::Bound(0));
            }
            _ => panic!("expected App"),
        }
    }

    #[test]
    fn test_frees() {
        let mut arena = PureArena::new();
        let ty = arena.alloc_type(TypDef::TFree(10, Sort::universal()));
        let x = arena.alloc_term(TermDef::Free(1, ty));
        let y = arena.alloc_term(TermDef::Free(2, ty));
        let app = arena.alloc_term(TermDef::App(x, y));
        let result = frees(&arena, app);
        assert_eq!(result.len(), 2);
    }

    #[test]
    fn test_free_in() {
        let mut arena = PureArena::new();
        let ty = arena.alloc_type(TypDef::TFree(10, Sort::universal()));
        let x = arena.alloc_term(TermDef::Free(42, ty));
        let y = arena.alloc_term(TermDef::Free(43, ty));
        let app = arena.alloc_term(TermDef::App(x, y));
        assert!(free_in(&arena, 42, ty, app));
        assert!(free_in(&arena, 43, ty, app));
        assert!(!free_in(&arena, 44, ty, app));
    }

    #[test]
    fn test_type_of_free() {
        let mut arena = PureArena::new();
        let ty = arena.alloc_type(TypDef::TFree(10, Sort::universal()));
        let x = arena.alloc_term(TermDef::Free(42, ty));
        assert_eq!(type_of(&mut arena, x, FUN_TYCON_ID), ty);
    }

    #[test]
    fn test_type_of_abs() {
        let mut arena = PureArena::new();
        let ty = arena.alloc_type(TypDef::TFree(10, Sort::universal()));
        let body = arena.alloc_term(TermDef::Bound(0));
        let abs = arena.alloc_term(TermDef::Abs(99, ty, body));
        let result = type_of(&mut arena, abs, FUN_TYCON_ID);
        assert_eq!(
            arena.get_type(result),
            TypDef::Type(FUN_TYCON_ID, vec![ty, ty])
        );
    }

    #[test]
    fn test_instantiate_term() {
        let mut arena = PureArena::new();
        let ty = arena.alloc_type(TypDef::TFree(10, Sort::universal()));
        let ix = IndexName { name: 1, index: 0 };
        let v = arena.alloc_term(TermDef::Var(ix.clone(), ty));
        let replacement = arena.alloc_term(TermDef::Free(42, ty));
        let result = instantiate_term(&mut arena, v, &[(replacement, ix, ty)]);
        assert_eq!(result, replacement);
    }

    #[test]
    fn test_instantiate_typ_in_term() {
        let mut arena = PureArena::new();
        let ix = IndexName { name: 10, index: 0 };
        let ty = arena.alloc_type(TypDef::TVar(ix.clone(), Sort::universal()));
        let x = arena.alloc_term(TermDef::Free(42, ty));
        let new_ty = arena.alloc_type(TypDef::Type(100, vec![]));
        let result = instantiate_typ_in_term(&mut arena, x, &[(new_ty, ix)]);
        match arena.get_term(result) {
            TermDef::Free(42, t) => assert_eq!(t, new_ty),
            _ => panic!("expected Free"),
        }
    }
}
