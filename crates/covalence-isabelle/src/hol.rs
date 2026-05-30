//! Isabelle/HOL bootstrap — registers HOL types, constants, and axioms on top of Pure.
//!
//! Demonstrates the separation: Pure is the framework, HOL is just one theory
//! loaded on top. Other object logics (FOL, ZF, etc.) could use the same Pure kernel.

use std::collections::HashMap;

use smol_str::SmolStr;

use crate::pure::PureKernel;
use crate::traits::IsabelleKernel;
use crate::types::*;

/// Name table for HOL bootstrap — maps strings to NameIds and back.
pub struct NameTable {
    to_id: HashMap<SmolStr, NameId>,
    to_name: Vec<SmolStr>,
}

impl NameTable {
    /// Create a new name table with the Pure built-in names pre-registered.
    pub fn new() -> Self {
        let mut table = NameTable {
            to_id: HashMap::new(),
            to_name: Vec::new(),
        };
        // Pre-register well-known Pure names at their expected IDs.
        let fun_id = table.intern(SmolStr::new("fun"));
        assert_eq!(fun_id, FUN_TYCON_ID);
        let prop_id = table.intern(SmolStr::new("prop"));
        assert_eq!(prop_id, PROP_TYCON_ID);
        let imp_id = table.intern(SmolStr::new("Pure.imp"));
        assert_eq!(imp_id, IMP_CONST_ID);
        let all_id = table.intern(SmolStr::new("Pure.all"));
        assert_eq!(all_id, ALL_CONST_ID);
        let eq_id = table.intern(SmolStr::new("Pure.eq"));
        assert_eq!(eq_id, EQ_CONST_ID);
        table
    }

    /// Intern a name, returning its ID (or existing ID if already interned).
    pub fn intern(&mut self, name: SmolStr) -> NameId {
        if let Some(&id) = self.to_id.get(&name) {
            return id;
        }
        let id = self.to_name.len() as NameId;
        self.to_name.push(name.clone());
        self.to_id.insert(name, id);
        id
    }

    /// Look up the string for a name ID.
    pub fn resolve(&self, id: NameId) -> Option<&SmolStr> {
        self.to_name.get(id as usize)
    }
}

/// Result of HOL bootstrap — name IDs for the registered HOL entities.
pub struct HolIds {
    pub bool_id: NameId,
    pub trueprop_id: NameId,
    pub true_id: NameId,
    pub false_id: NameId,
    pub not_id: NameId,
    pub conj_id: NameId,
    pub disj_id: NameId,
    pub implies_id: NameId,
    pub hol_all_id: NameId,
    pub hol_ex_id: NameId,
    pub hol_eq_id: NameId,
}

/// Bootstrap Isabelle/HOL on top of a Pure kernel.
///
/// Registers:
/// - Type: `bool` (arity 0)
/// - Constants: `Trueprop`, `True`, `False`, `Not`, `conj`, `disj`, `implies`, `All`, `Ex`, `eq`
/// - Axioms: core HOL axioms (`HOL.refl`, `HOL.True_def`)
pub fn bootstrap_hol(kernel: &mut PureKernel, names: &mut NameTable) -> Result<HolIds, PureError> {
    let fun_id = FUN_TYCON_ID;
    let prop_id = PROP_TYCON_ID;

    // Register type: bool (arity 0)
    let bool_id = names.intern(SmolStr::new("HOL.bool"));
    kernel.add_type(bool_id, 0)?;
    let bool_ty = kernel.arena_mut().alloc_type(TypDef::Type(bool_id, vec![]));
    let prop_ty = kernel.arena_mut().alloc_type(TypDef::Type(prop_id, vec![]));

    // Register constant: Trueprop : bool => prop
    let trueprop_id = names.intern(SmolStr::new("HOL.Trueprop"));
    let trueprop_ty = kernel
        .arena_mut()
        .alloc_type(TypDef::Type(fun_id, vec![bool_ty, prop_ty]));
    kernel.add_constant(trueprop_id, trueprop_ty)?;

    // Helper: wrap a bool term in Trueprop to get a prop
    let mk_trueprop = |arena: &mut crate::arena::PureArena, t: TermId| -> TermId {
        let imp_c = arena.alloc_term(TermDef::Const(trueprop_id, trueprop_ty));
        arena.alloc_term(TermDef::App(imp_c, t))
    };

    // Register constant: True : bool
    let true_id = names.intern(SmolStr::new("HOL.True"));
    kernel.add_constant(true_id, bool_ty)?;

    // Register constant: False : bool
    let false_id = names.intern(SmolStr::new("HOL.False"));
    kernel.add_constant(false_id, bool_ty)?;

    // Register constant: Not : bool => bool
    let not_id = names.intern(SmolStr::new("HOL.Not"));
    let not_ty = kernel
        .arena_mut()
        .alloc_type(TypDef::Type(fun_id, vec![bool_ty, bool_ty]));
    kernel.add_constant(not_id, not_ty)?;

    // Register constant: conj : bool => bool => bool
    let conj_id = names.intern(SmolStr::new("HOL.conj"));
    let bb = kernel
        .arena_mut()
        .alloc_type(TypDef::Type(fun_id, vec![bool_ty, bool_ty]));
    let bbb = kernel
        .arena_mut()
        .alloc_type(TypDef::Type(fun_id, vec![bool_ty, bb]));
    kernel.add_constant(conj_id, bbb)?;

    // Register constant: disj : bool => bool => bool
    let disj_id = names.intern(SmolStr::new("HOL.disj"));
    let bbb2 = kernel
        .arena_mut()
        .alloc_type(TypDef::Type(fun_id, vec![bool_ty, bb]));
    kernel.add_constant(disj_id, bbb2)?;

    // Register constant: implies : bool => bool => bool
    let implies_id = names.intern(SmolStr::new("HOL.implies"));
    let bbb3 = kernel
        .arena_mut()
        .alloc_type(TypDef::Type(fun_id, vec![bool_ty, bb]));
    kernel.add_constant(implies_id, bbb3)?;

    // Register constant: All : ('a => bool) => bool  (polymorphic)
    let hol_all_id = names.intern(SmolStr::new("HOL.All"));
    let a_ix = IndexName {
        name: NameId::MAX,
        index: 0,
    };
    let a_var = kernel
        .arena_mut()
        .alloc_type(TypDef::TVar(a_ix, Sort::universal()));
    let a_to_bool = kernel
        .arena_mut()
        .alloc_type(TypDef::Type(fun_id, vec![a_var, bool_ty]));
    let all_ty = kernel
        .arena_mut()
        .alloc_type(TypDef::Type(fun_id, vec![a_to_bool, bool_ty]));
    kernel.add_constant(hol_all_id, all_ty)?;

    // Register constant: Ex : ('a => bool) => bool  (polymorphic)
    let hol_ex_id = names.intern(SmolStr::new("HOL.Ex"));
    let ex_ty = kernel
        .arena_mut()
        .alloc_type(TypDef::Type(fun_id, vec![a_to_bool, bool_ty]));
    kernel.add_constant(hol_ex_id, ex_ty)?;

    // Register constant: eq : 'a => 'a => bool  (polymorphic)
    let hol_eq_id = names.intern(SmolStr::new("HOL.eq"));
    let a_to_bool2 = kernel
        .arena_mut()
        .alloc_type(TypDef::Type(fun_id, vec![a_var, bool_ty]));
    let eq_ty = kernel
        .arena_mut()
        .alloc_type(TypDef::Type(fun_id, vec![a_var, a_to_bool2]));
    kernel.add_constant(hol_eq_id, eq_ty)?;

    // --- Axioms ---

    // HOL.refl: Trueprop(eq x x)
    // Use a schematic type var for polymorphism
    let x_ix = IndexName {
        name: names.intern(SmolStr::new("x")),
        index: 0,
    };
    let x_var_ty = kernel.arena_mut().alloc_type(TypDef::TVar(
        IndexName {
            name: NameId::MAX - 1,
            index: 0,
        },
        Sort::universal(),
    ));
    let x_var = kernel.arena_mut().alloc_term(TermDef::Var(x_ix, x_var_ty));
    // eq : x_var_ty => x_var_ty => bool
    let xvt_to_bool = kernel
        .arena_mut()
        .alloc_type(TypDef::Type(fun_id, vec![x_var_ty, bool_ty]));
    let eq_inst_ty = kernel
        .arena_mut()
        .alloc_type(TypDef::Type(fun_id, vec![x_var_ty, xvt_to_bool]));
    let eq_const = kernel
        .arena_mut()
        .alloc_term(TermDef::Const(hol_eq_id, eq_inst_ty));
    let eq_x = kernel.arena_mut().alloc_term(TermDef::App(eq_const, x_var));
    let eq_x_x = kernel.arena_mut().alloc_term(TermDef::App(eq_x, x_var));
    let refl_prop = mk_trueprop(kernel.arena_mut(), eq_x_x);
    kernel.add_axiom(SmolStr::new("HOL.refl"), refl_prop)?;

    // HOL.True_def: Trueprop(eq True ((\x::bool. x) = (\x::bool. x)))
    let true_const = kernel
        .arena_mut()
        .alloc_term(TermDef::Const(true_id, bool_ty));
    let x_hint = names.intern(SmolStr::new("x"));
    let id_bool_body = kernel.arena_mut().alloc_term(TermDef::Bound(0));
    let id_bool = kernel
        .arena_mut()
        .alloc_term(TermDef::Abs(x_hint, bool_ty, id_bool_body));
    // eq_bb : bool => bool => bool
    let eq_bb_ty = kernel
        .arena_mut()
        .alloc_type(TypDef::Type(fun_id, vec![bool_ty, bb]));
    let eq_bb_const = kernel
        .arena_mut()
        .alloc_term(TermDef::Const(hol_eq_id, eq_bb_ty));
    let eq_bb_id = kernel
        .arena_mut()
        .alloc_term(TermDef::App(eq_bb_const, id_bool));
    let id_eq_id = kernel
        .arena_mut()
        .alloc_term(TermDef::App(eq_bb_id, id_bool));
    // eq True (id_eq_id) : use eq at bool type
    let eq_bool_ty = kernel
        .arena_mut()
        .alloc_type(TypDef::Type(fun_id, vec![bool_ty, bb]));
    let eq_bool_const = kernel
        .arena_mut()
        .alloc_term(TermDef::Const(hol_eq_id, eq_bool_ty));
    let eq_true = kernel
        .arena_mut()
        .alloc_term(TermDef::App(eq_bool_const, true_const));
    let true_def_body = kernel
        .arena_mut()
        .alloc_term(TermDef::App(eq_true, id_eq_id));
    let true_def_concl = mk_trueprop(kernel.arena_mut(), true_def_body);
    kernel.add_axiom(SmolStr::new("HOL.True_def"), true_def_concl)?;

    Ok(HolIds {
        bool_id,
        trueprop_id,
        true_id,
        false_id,
        not_id,
        conj_id,
        disj_id,
        implies_id,
        hol_all_id,
        hol_ex_id,
        hol_eq_id,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arena;

    #[test]
    fn test_bootstrap_hol() {
        let mut kernel = PureKernel::new();
        let mut names = NameTable::new();
        let ids = bootstrap_hol(&mut kernel, &mut names).unwrap();

        // Check types registered
        assert!(kernel.theory().type_constructors.contains_key(&ids.bool_id));
        assert_eq!(kernel.theory().type_constructors[&ids.bool_id], 0);

        // Check constants registered
        assert!(kernel.theory().constants.contains_key(&ids.trueprop_id));
        assert!(kernel.theory().constants.contains_key(&ids.true_id));
        assert!(kernel.theory().constants.contains_key(&ids.false_id));
        assert!(kernel.theory().constants.contains_key(&ids.not_id));
        assert!(kernel.theory().constants.contains_key(&ids.conj_id));
        assert!(kernel.theory().constants.contains_key(&ids.disj_id));
        assert!(kernel.theory().constants.contains_key(&ids.implies_id));
        assert!(kernel.theory().constants.contains_key(&ids.hol_all_id));
        assert!(kernel.theory().constants.contains_key(&ids.hol_ex_id));
        assert!(kernel.theory().constants.contains_key(&ids.hol_eq_id));

        // Check axioms registered
        assert!(kernel.axiom("HOL.refl").is_ok());
        assert!(kernel.axiom("HOL.True_def").is_ok());

        // Check name resolution
        assert_eq!(names.resolve(ids.bool_id).unwrap().as_str(), "HOL.bool");
        assert_eq!(
            names.resolve(ids.trueprop_id).unwrap().as_str(),
            "HOL.Trueprop"
        );
    }

    #[test]
    fn test_bootstrap_hol_double_fails() {
        let mut kernel = PureKernel::new();
        let mut names = NameTable::new();
        bootstrap_hol(&mut kernel, &mut names).unwrap();
        // Second bootstrap should fail (types/constants already defined)
        assert!(bootstrap_hol(&mut kernel, &mut names).is_err());
    }

    #[test]
    fn test_hol_axiom_is_prop() {
        let mut kernel = PureKernel::new();
        let mut names = NameTable::new();
        bootstrap_hol(&mut kernel, &mut names).unwrap();
        // The refl axiom should have type prop
        let refl = kernel.axiom("HOL.refl").unwrap();
        let concl = kernel.arena().get_thm(refl).concl;
        assert!(arena::is_prop(
            kernel.arena(),
            FUN_TYCON_ID,
            PROP_TYCON_ID,
            concl
        ));
    }
}
