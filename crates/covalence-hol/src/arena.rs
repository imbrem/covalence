//! Arena storage for HOL types, terms, and theorems.
//!
//! Plain `Vec` arenas with `&mut self` allocation and `&self` lookup.
//! `get_*` methods clone the small def out to avoid borrow-across-alloc issues.

use crate::types::*;

/// Arena storage for types, terms, and theorems.
pub struct HolArena {
    types: Vec<HolTypeDef>,
    terms: Vec<TermDef>,
    thms: Vec<ThmDef>,
}

impl HolArena {
    /// Create an empty arena.
    pub fn new() -> Self {
        HolArena {
            types: Vec::new(),
            terms: Vec::new(),
            thms: Vec::new(),
        }
    }

    // -- Allocation --

    /// Allocate a type, returning its index.
    pub fn alloc_type(&mut self, def: HolTypeDef) -> TypeId {
        let id = TypeId(self.types.len() as u32);
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
    pub fn get_type(&self, id: TypeId) -> HolTypeDef {
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
    pub fn types(&self) -> &[HolTypeDef] {
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

/// Structural equality of types.
pub fn types_eq(arena: &HolArena, a: TypeId, b: TypeId) -> bool {
    if a == b {
        return true;
    }
    match (arena.get_type(a), arena.get_type(b)) {
        (HolTypeDef::Tyvar(n1), HolTypeDef::Tyvar(n2)) => n1 == n2,
        (HolTypeDef::Tyapp(n1, args1), HolTypeDef::Tyapp(n2, args2)) => {
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
pub fn terms_eq(arena: &HolArena, a: TermId, b: TermId) -> bool {
    if a == b {
        return true;
    }
    match (arena.get_term(a), arena.get_term(b)) {
        (TermDef::Var(n1, ty1), TermDef::Var(n2, ty2)) => n1 == n2 && types_eq(arena, ty1, ty2),
        (TermDef::Const(n1, ty1), TermDef::Const(n2, ty2)) => n1 == n2 && types_eq(arena, ty1, ty2),
        (TermDef::Comb(f1, x1), TermDef::Comb(f2, x2)) => {
            terms_eq(arena, f1, f2) && terms_eq(arena, x1, x2)
        }
        (TermDef::Abs(v1, b1), TermDef::Abs(v2, b2)) => {
            terms_eq(arena, v1, v2) && terms_eq(arena, b1, b2)
        }
        _ => false,
    }
}

/// Alpha-equivalence of terms.
pub fn aconv(arena: &HolArena, tm1: TermId, tm2: TermId) -> bool {
    aconv_env(arena, tm1, tm2, &[])
}

/// Alpha-equivalence with an environment of bound variable pairs.
fn aconv_env(
    arena: &HolArena,
    tm1: TermId,
    tm2: TermId,
    env: &[(NameId, TypeId, NameId, TypeId)],
) -> bool {
    if tm1 == tm2 && env.is_empty() {
        return true;
    }
    match (arena.get_term(tm1), arena.get_term(tm2)) {
        (TermDef::Var(n1, ty1), TermDef::Var(n2, ty2)) => {
            for &(bn1, bty1, bn2, bty2) in env.iter().rev() {
                if n1 == bn1 && types_eq(arena, ty1, bty1) {
                    return n2 == bn2 && types_eq(arena, ty2, bty2);
                }
                if n2 == bn2 && types_eq(arena, ty2, bty2) {
                    return false;
                }
            }
            n1 == n2 && types_eq(arena, ty1, ty2)
        }
        (TermDef::Const(n1, ty1), TermDef::Const(n2, ty2)) => n1 == n2 && types_eq(arena, ty1, ty2),
        (TermDef::Comb(f1, x1), TermDef::Comb(f2, x2)) => {
            aconv_env(arena, f1, f2, env) && aconv_env(arena, x1, x2, env)
        }
        (TermDef::Abs(v1, b1), TermDef::Abs(v2, b2)) => {
            let vd1 = arena.get_term(v1);
            let vd2 = arena.get_term(v2);
            if let (TermDef::Var(n1, ty1), TermDef::Var(n2, ty2)) = (vd1, vd2) {
                if !types_eq(arena, ty1, ty2) {
                    return false;
                }
                let mut new_env = env.to_vec();
                new_env.push((n1, ty1, n2, ty2));
                aconv_env(arena, b1, b2, &new_env)
            } else {
                false
            }
        }
        _ => false,
    }
}

/// Get the type of a term. Allocates for the `Abs` case.
pub fn type_of(arena: &mut HolArena, tm: TermId) -> TypeId {
    match arena.get_term(tm) {
        TermDef::Var(_, ty) | TermDef::Const(_, ty) => ty,
        TermDef::Comb(f, _) => {
            let f_ty = type_of(arena, f);
            match arena.get_type(f_ty) {
                HolTypeDef::Tyapp(_, args) if args.len() == 2 => args[1],
                _ => panic!("type_of: ill-typed combination"),
            }
        }
        TermDef::Abs(var, body) => {
            let var_ty = type_of(arena, var);
            let body_ty = type_of(arena, body);
            arena.alloc_type(HolTypeDef::Tyapp(FUN_TYCON_ID, vec![var_ty, body_ty]))
        }
    }
}

/// Read-only type_of — panics on Abs (caller must ensure no Abs at top).
/// Used when we know the term is Var/Const/Comb.
pub fn type_of_ro(arena: &HolArena, tm: TermId) -> TypeId {
    match arena.get_term(tm) {
        TermDef::Var(_, ty) | TermDef::Const(_, ty) => ty,
        TermDef::Comb(f, _) => {
            let f_ty = type_of_ro(arena, f);
            match arena.get_type(f_ty) {
                HolTypeDef::Tyapp(_, args) if args.len() == 2 => args[1],
                _ => panic!("type_of: ill-typed combination"),
            }
        }
        TermDef::Abs(var, body) => {
            // Walk to find types without allocating — var/body should be accessible
            let var_ty = type_of_ro(arena, var);
            let body_ty = type_of_ro(arena, body);
            // Search the arena for an existing matching type
            for (i, def) in arena.types().iter().enumerate() {
                if let HolTypeDef::Tyapp(n, args) = def {
                    if *n == FUN_TYCON_ID
                        && args.len() == 2
                        && args[0] == var_ty
                        && args[1] == body_ty
                    {
                        return TypeId(i as u32);
                    }
                }
            }
            panic!("type_of_ro: function type not yet in arena for Abs")
        }
    }
}

/// Collect all type variables in a type.
pub fn tyvars(arena: &HolArena, ty: TypeId) -> Vec<NameId> {
    let mut result = Vec::new();
    tyvars_acc(arena, ty, &mut result);
    result.sort_unstable();
    result.dedup();
    result
}

fn tyvars_acc(arena: &HolArena, ty: TypeId, acc: &mut Vec<NameId>) {
    match arena.get_type(ty) {
        HolTypeDef::Tyvar(n) => acc.push(n),
        HolTypeDef::Tyapp(_, args) => {
            for arg in args {
                tyvars_acc(arena, arg, acc);
            }
        }
    }
}

/// Collect type variables from a term (all types occurring in the term).
pub fn term_tyvars(arena: &HolArena, tm: TermId) -> Vec<NameId> {
    let mut result = Vec::new();
    term_tyvars_acc(arena, tm, &mut result);
    result.sort_unstable();
    result.dedup();
    result
}

fn term_tyvars_acc(arena: &HolArena, tm: TermId, acc: &mut Vec<NameId>) {
    match arena.get_term(tm) {
        TermDef::Var(_, ty) | TermDef::Const(_, ty) => tyvars_acc(arena, ty, acc),
        TermDef::Comb(f, x) => {
            term_tyvars_acc(arena, f, acc);
            term_tyvars_acc(arena, x, acc);
        }
        TermDef::Abs(v, b) => {
            term_tyvars_acc(arena, v, acc);
            term_tyvars_acc(arena, b, acc);
        }
    }
}

/// Apply a type substitution: replace type variables according to `pairs`.
/// Each pair is `(new_type, old_tyvar_name)`.
pub fn type_inst(arena: &mut HolArena, ty: TypeId, pairs: &[(TypeId, NameId)]) -> TypeId {
    if pairs.is_empty() {
        return ty;
    }
    match arena.get_type(ty) {
        HolTypeDef::Tyvar(n) => {
            for &(replacement, var) in pairs {
                if var == n {
                    return replacement;
                }
            }
            ty
        }
        HolTypeDef::Tyapp(name, args) => {
            let new_args: Vec<TypeId> = args.iter().map(|&a| type_inst(arena, a, pairs)).collect();
            if new_args == args {
                ty
            } else {
                arena.alloc_type(HolTypeDef::Tyapp(name, new_args))
            }
        }
    }
}

/// Check if a variable occurs free in a term.
pub fn vfree_in(arena: &HolArena, var: TermId, tm: TermId) -> bool {
    match arena.get_term(tm) {
        TermDef::Abs(bv, body) => !terms_eq(arena, bv, var) && vfree_in(arena, var, body),
        TermDef::Comb(f, x) => vfree_in(arena, var, f) || vfree_in(arena, var, x),
        _ => terms_eq(arena, tm, var),
    }
}

/// Collect free variables in a term.
pub fn frees(arena: &HolArena, tm: TermId) -> Vec<TermId> {
    let mut result = Vec::new();
    frees_acc(arena, tm, &mut result);
    result
}

fn frees_acc(arena: &HolArena, tm: TermId, acc: &mut Vec<TermId>) {
    match arena.get_term(tm) {
        TermDef::Var(_, _) => {
            if !acc.iter().any(|&v| terms_eq(arena, v, tm)) {
                acc.push(tm);
            }
        }
        TermDef::Const(_, _) => {}
        TermDef::Comb(f, x) => {
            frees_acc(arena, f, acc);
            frees_acc(arena, x, acc);
        }
        TermDef::Abs(var, body) => {
            let mut body_frees = Vec::new();
            frees_acc(arena, body, &mut body_frees);
            for v in body_frees {
                if !terms_eq(arena, v, var) {
                    if !acc.iter().any(|&existing| terms_eq(arena, existing, v)) {
                        acc.push(v);
                    }
                }
            }
        }
    }
}

/// Apply a term substitution (with capture avoidance).
/// `pairs` is `(new_term, old_var)`.
pub fn vsubst(
    arena: &mut HolArena,
    tm: TermId,
    pairs: &[(TermId, TermId)],
) -> Result<TermId, HolError> {
    if !pairs.iter().any(|&(_, old)| vfree_in(arena, old, tm)) {
        return Ok(tm);
    }
    vsubst_inner(arena, tm, pairs)
}

fn vsubst_inner(
    arena: &mut HolArena,
    tm: TermId,
    pairs: &[(TermId, TermId)],
) -> Result<TermId, HolError> {
    match arena.get_term(tm) {
        TermDef::Var(_, _) => {
            for &(replacement, old) in pairs {
                if terms_eq(arena, old, tm) {
                    return Ok(replacement);
                }
            }
            Ok(tm)
        }
        TermDef::Const(_, _) => Ok(tm),
        TermDef::Comb(f, x) => {
            let f2 = vsubst_inner(arena, f, pairs)?;
            let x2 = vsubst_inner(arena, x, pairs)?;
            if f2 == f && x2 == x {
                Ok(tm)
            } else {
                Ok(arena.alloc_term(TermDef::Comb(f2, x2)))
            }
        }
        TermDef::Abs(var, body) => {
            let filtered: Vec<(TermId, TermId)> = pairs
                .iter()
                .filter(|&&(_, old)| !terms_eq(arena, old, var))
                .copied()
                .collect();
            if filtered.is_empty() {
                return Ok(tm);
            }
            let body2 = vsubst_inner(arena, body, &filtered)?;
            if body2 == body {
                return Ok(tm);
            }
            let captured = filtered.iter().any(|&(repl, _)| vfree_in(arena, var, repl));
            if captured {
                return Err(HolError::VariableCapture);
            }
            Ok(arena.alloc_term(TermDef::Abs(var, body2)))
        }
    }
}

/// Apply a type instantiation to a term.
/// `pairs` is `(new_type, old_tyvar_name)`.
pub fn inst_term(arena: &mut HolArena, tm: TermId, pairs: &[(TypeId, NameId)]) -> TermId {
    if pairs.is_empty() {
        return tm;
    }
    match arena.get_term(tm) {
        TermDef::Var(n, ty) => {
            let ty2 = type_inst(arena, ty, pairs);
            if ty2 == ty {
                tm
            } else {
                arena.alloc_term(TermDef::Var(n, ty2))
            }
        }
        TermDef::Const(n, ty) => {
            let ty2 = type_inst(arena, ty, pairs);
            if ty2 == ty {
                tm
            } else {
                arena.alloc_term(TermDef::Const(n, ty2))
            }
        }
        TermDef::Comb(f, x) => {
            let f2 = inst_term(arena, f, pairs);
            let x2 = inst_term(arena, x, pairs);
            if f2 == f && x2 == x {
                tm
            } else {
                arena.alloc_term(TermDef::Comb(f2, x2))
            }
        }
        TermDef::Abs(var, body) => {
            let var2 = inst_term(arena, var, pairs);
            let body2 = inst_term(arena, body, pairs);
            if var2 == var && body2 == body {
                tm
            } else {
                arena.alloc_term(TermDef::Abs(var2, body2))
            }
        }
    }
}

/// Try to match `pattern` against `target`, accumulating type variable bindings.
/// This checks that `target` is an instance of `pattern`.
pub fn type_match(
    arena: &HolArena,
    pattern: TypeId,
    target: TypeId,
    bindings: &mut Vec<(NameId, TypeId)>,
) -> Result<(), ()> {
    if pattern == target {
        return Ok(());
    }
    match (arena.get_type(pattern), arena.get_type(target)) {
        (HolTypeDef::Tyvar(n), _) => {
            for &(bound_n, bound_ty) in bindings.iter() {
                if bound_n == n {
                    if types_eq(arena, bound_ty, target) {
                        return Ok(());
                    } else {
                        return Err(());
                    }
                }
            }
            bindings.push((n, target));
            Ok(())
        }
        (HolTypeDef::Tyapp(n1, args1), HolTypeDef::Tyapp(n2, args2)) => {
            if n1 != n2 || args1.len() != args2.len() {
                return Err(());
            }
            for (a1, a2) in args1.iter().zip(args2.iter()) {
                type_match(arena, *a1, *a2, bindings)?;
            }
            Ok(())
        }
        _ => Err(()),
    }
}

/// Construct the boolean type in the arena.
pub fn mk_bool_type(arena: &mut HolArena, bool_id: NameId) -> TypeId {
    arena.alloc_type(HolTypeDef::Tyapp(bool_id, vec![]))
}

/// Construct the function type in the arena.
pub fn mk_fun_type(
    arena: &mut HolArena,
    fun_id: NameId,
    domain: TypeId,
    codomain: TypeId,
) -> TypeId {
    arena.alloc_type(HolTypeDef::Tyapp(fun_id, vec![domain, codomain]))
}

/// Construct an equality term `lhs = rhs` in the arena.
pub fn mk_eq_term(
    arena: &mut HolArena,
    eq_id: NameId,
    fun_id: NameId,
    bool_id: NameId,
    lhs: TermId,
    rhs: TermId,
) -> TermId {
    let ty = type_of(arena, lhs);
    let bool_ty = mk_bool_type(arena, bool_id);
    let inner_fun = mk_fun_type(arena, fun_id, ty, bool_ty);
    let eq_ty = mk_fun_type(arena, fun_id, ty, inner_fun);
    let eq_const = arena.alloc_term(TermDef::Const(eq_id, eq_ty));
    let eq_lhs = arena.alloc_term(TermDef::Comb(eq_const, lhs));
    arena.alloc_term(TermDef::Comb(eq_lhs, rhs))
}

/// Destruct an equation `(= l) r`, returning `(l, r)`.
/// Checks that the head constant has name `eq_id`.
pub fn dest_eq(arena: &HolArena, eq_id: NameId, tm: TermId) -> Option<(TermId, TermId)> {
    if let TermDef::Comb(f, r) = arena.get_term(tm) {
        if let TermDef::Comb(eq, l) = arena.get_term(f) {
            if let TermDef::Const(n, _) = arena.get_term(eq) {
                if n == eq_id {
                    return Some((l, r));
                }
            }
        }
    }
    None
}

/// Check if a term has boolean type (read-only: assumes bool type already in arena).
pub fn is_bool(arena: &HolArena, bool_id: NameId, tm: TermId) -> bool {
    let ty = type_of_ro(arena, tm);
    match arena.get_type(ty) {
        HolTypeDef::Tyapp(n, args) => n == bool_id && args.is_empty(),
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_alloc_and_get() {
        let mut arena = HolArena::new();
        let tv = arena.alloc_type(HolTypeDef::Tyvar(10));
        assert_eq!(arena.get_type(tv), HolTypeDef::Tyvar(10));
    }

    #[test]
    fn test_types_eq() {
        let mut arena = HolArena::new();
        let a = arena.alloc_type(HolTypeDef::Tyvar(10));
        let b = arena.alloc_type(HolTypeDef::Tyvar(10));
        assert!(types_eq(&arena, a, b));

        let c = arena.alloc_type(HolTypeDef::Tyvar(11));
        assert!(!types_eq(&arena, a, c));
    }

    #[test]
    fn test_bool_type() {
        let mut arena = HolArena::new();
        let b = mk_bool_type(&mut arena, BOOL_TYCON_ID);
        assert_eq!(arena.get_type(b), HolTypeDef::Tyapp(BOOL_TYCON_ID, vec![]));
    }

    #[test]
    fn test_fun_type() {
        let mut arena = HolArena::new();
        let b = mk_bool_type(&mut arena, BOOL_TYCON_ID);
        let f = mk_fun_type(&mut arena, FUN_TYCON_ID, b, b);
        assert_eq!(
            arena.get_type(f),
            HolTypeDef::Tyapp(FUN_TYCON_ID, vec![b, b])
        );
    }

    #[test]
    fn test_aconv_same_var() {
        let mut arena = HolArena::new();
        let ty = arena.alloc_type(HolTypeDef::Tyvar(10));
        let v = arena.alloc_term(TermDef::Var(5, ty));
        assert!(aconv(&arena, v, v));
    }

    #[test]
    fn test_aconv_alpha_equivalent() {
        let mut arena = HolArena::new();
        let ty = arena.alloc_type(HolTypeDef::Tyvar(10));
        let v1 = arena.alloc_term(TermDef::Var(1, ty));
        let v2 = arena.alloc_term(TermDef::Var(2, ty));
        let abs1 = arena.alloc_term(TermDef::Abs(v1, v1));
        let abs2 = arena.alloc_term(TermDef::Abs(v2, v2));
        assert!(aconv(&arena, abs1, abs2));
    }

    #[test]
    fn test_aconv_not_alpha_equivalent() {
        let mut arena = HolArena::new();
        let ty = arena.alloc_type(HolTypeDef::Tyvar(10));
        let v1 = arena.alloc_term(TermDef::Var(1, ty));
        let v2 = arena.alloc_term(TermDef::Var(2, ty));
        let abs1 = arena.alloc_term(TermDef::Abs(v1, v1));
        let abs2 = arena.alloc_term(TermDef::Abs(v1, v2));
        assert!(!aconv(&arena, abs1, abs2));
    }

    #[test]
    fn test_type_inst() {
        let mut arena = HolArena::new();
        let a = arena.alloc_type(HolTypeDef::Tyvar(10));
        let b = arena.alloc_type(HolTypeDef::Tyvar(11));
        let fun = mk_fun_type(&mut arena, FUN_TYCON_ID, a, b);
        let int_ty = arena.alloc_type(HolTypeDef::Tyapp(100, vec![]));
        let result = type_inst(&mut arena, fun, &[(int_ty, 10)]);
        assert_eq!(
            arena.get_type(result),
            HolTypeDef::Tyapp(FUN_TYCON_ID, vec![int_ty, b])
        );
    }

    #[test]
    fn test_frees() {
        let mut arena = HolArena::new();
        let ty = arena.alloc_type(HolTypeDef::Tyvar(10));
        let x = arena.alloc_term(TermDef::Var(1, ty));
        let y = arena.alloc_term(TermDef::Var(2, ty));
        let app = arena.alloc_term(TermDef::Comb(x, y));
        let abs = arena.alloc_term(TermDef::Abs(x, app));
        let free_vars = frees(&arena, abs);
        assert_eq!(free_vars.len(), 1);
        assert!(terms_eq(&arena, free_vars[0], y));
    }
}
