//! **S-expressions as `sexp α := tree (option α)`** — the Lisp cons-cell
//! encoding layered on the binary-[`tree`](crate::init::tree) theory.
//!
//! A node of `tree (option α)` is read as an S-expression:
//!
//! ```text
//!   atom a  :=  leaf (some a)     -- an atom carrying a payload `a : α`
//!   nil     :=  leaf none         -- the empty list / nil
//!   cons x y:=  branch x y        -- a cons cell (car `x`, cdr `y`)
//! ```
//!
//! so a leaf `some a` is an atom, a leaf `none` is nil, and a `branch` is a
//! cons cell. This is the classic Lisp cons-cell view: lists are right-nested
//! cons cells terminated by `nil`, and atoms sit at the leaves.
//!
//! `sexp` is a **view / alias** over `tree`, not a fresh datatype — it reuses
//! `tree`'s constructors, recursor, and constructor-freeness theorems with
//! the element type fixed to `option α`. The kernel `option` constructors
//! ([`some`](crate::init::option::some) / [`none`](crate::init::option::none))
//! carry the atom/nil distinction; [`tree::leaf_inj`](crate::init::tree)
//! plus [`option::some_ne_none`](crate::init::option::some_ne_none) give the
//! genuine `atom a ≠ nil` fact, and `tree::leaf_ne_branch` gives
//! `atom a ≠ cons …` / `nil ≠ cons …`.
//!
//! ## What is provided
//!
//! - the element-type helper [`sexp_elem_ty`] (`option α`) and the carrier
//!   type [`sexp_ty`] (`tree (option α)` at the chosen `'r`);
//! - the atom/nil/cons constructors [`atom`], [`nil`], [`cons`];
//! - reconstruction lemmas: [`atom_ne_nil`], [`atom_ne_cons`],
//!   [`nil_ne_cons`] (all genuine kernel theorems via `tree` freeness).

use covalence_core::{Result, Term, Thm, Type};

use crate::init::ext::TermExt;
use crate::init::option::{none, some, some_ne_none};
use crate::init::tree;

/// `option α` — the element type of the `tree` underlying `sexp α`.
pub fn sexp_elem_ty(alpha: &Type) -> Type {
    covalence_core::defs::option(alpha.clone())
}

/// `sexp α = tree (option α)` (at the encoding's polymorphic result `'r`).
pub fn sexp_ty(alpha: &Type) -> Type {
    tree::tree_ty(&sexp_elem_ty(alpha))
}

// ============================================================================
// The atom / nil / cons view
// ============================================================================

/// `atom a := leaf (some a) : sexp α` — an atom carrying `a : α`.
pub fn atom(alpha: &Type, a: Term) -> Result<Term> {
    let some_a = some(alpha.clone()).apply(a)?;
    tree::leaf(&sexp_elem_ty(alpha), some_a)
}

/// `nil := leaf none : sexp α` — the empty S-expression.
pub fn nil(alpha: &Type) -> Result<Term> {
    tree::leaf(&sexp_elem_ty(alpha), none(alpha.clone()))
}

/// `cons x y := branch x y : sexp α` — a cons cell with car `x`, cdr `y`.
pub fn cons(alpha: &Type, x: Term, y: Term) -> Result<Term> {
    tree::branch(&sexp_elem_ty(alpha), x, y)
}

// ============================================================================
// Reconstruction / distinctness lemmas
// ============================================================================

/// `⊢ ¬(atom a = nil)` — an atom is never nil. From `leaf` injectivity
/// (`leaf (some a) = leaf none ⟹ some a = none`) contradicting
/// [`some_ne_none`](crate::init::option::some_ne_none).
pub fn atom_ne_nil(alpha: &Type, a: &Term) -> Result<Thm> {
    let elem = sexp_elem_ty(alpha);
    let some_a = some(alpha.clone()).apply(a.clone())?;
    let none_t = none(alpha.clone());

    // `⊢ leaf (some a) = leaf none ⟹ some a = none` (tree leaf-injectivity,
    // stated at the `'r := option α` observation type).
    let inj = tree::leaf_inj(&elem, &some_a, &none_t)?;
    // `⊢ ¬(some a = none)`.
    let snn = some_ne_none(alpha, a)?;

    // The injectivity antecedent `leaf (some a) = leaf none`, at the same
    // `'r := option α` observation type, rebuilt directly.
    let eq = tree::at_r(&tree::leaf(&elem, some_a.clone())?, &elem)?
        .equals(tree::at_r(&tree::leaf(&elem, none_t.clone())?, &elem)?)?;
    let h = Thm::assume(eq.clone())?;
    let some_eq_none = inj.imp_elim(h)?; // {H} ⊢ some a = none
    let f = snn.not_elim(some_eq_none)?; // {H} ⊢ F
    f.imp_intro(&eq)?.not_intro()
}

/// `⊢ ¬(atom a = cons x y)` — an atom is never a cons cell. Directly
/// `tree::leaf_ne_branch` at the `option α` element type (`atom = leaf (some
/// a)`, `cons = branch x y`).
pub fn atom_ne_cons(alpha: &Type, a: &Term, x: &Term, y: &Term) -> Result<Thm> {
    let elem = sexp_elem_ty(alpha);
    let some_a = some(alpha.clone()).apply(a.clone())?;
    tree::leaf_ne_branch(&elem, &some_a, x, y)
}

/// `⊢ ¬(nil = cons x y)` — nil is never a cons cell. `tree::leaf_ne_branch`
/// at `option α` with the leaf payload `none` (`nil = leaf none`).
pub fn nil_ne_cons(alpha: &Type, x: &Term, y: &Term) -> Result<Thm> {
    let elem = sexp_elem_ty(alpha);
    let none_t = none(alpha.clone());
    tree::leaf_ne_branch(&elem, &none_t, x, y)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn a_ty() -> Type {
        Type::tfree("a")
    }

    #[test]
    fn constructors_typed_and_distinct() {
        let alpha = a_ty();
        let a = Term::free("a", alpha.clone());
        let at = atom(&alpha, a.clone()).unwrap();
        let nl = nil(&alpha).unwrap();
        assert_eq!(at.type_of().unwrap(), sexp_ty(&alpha));
        assert_eq!(nl.type_of().unwrap(), sexp_ty(&alpha));
        let cl = cons(&alpha, at.clone(), nl.clone()).unwrap();
        assert_eq!(cl.type_of().unwrap(), sexp_ty(&alpha));
        // Distinct as terms (genuine syntax).
        assert_ne!(at, nl);
        assert_ne!(at, cl);
        assert_ne!(nl, cl);
    }

    #[test]
    fn atom_ne_nil_is_genuine() {
        let alpha = a_ty();
        let a = Term::free("a", alpha.clone());
        let thm = atom_ne_nil(&alpha, &a).unwrap();
        assert!(thm.hyps().is_empty() && thm.has_no_obs());
        assert!(thm.concl().as_app().is_some(), "a `¬…` conclusion");
    }

    #[test]
    fn atom_ne_cons_is_genuine() {
        let alpha = a_ty();
        let a = Term::free("a", alpha.clone());
        let x = nil(&alpha).unwrap();
        let y = nil(&alpha).unwrap();
        let thm = atom_ne_cons(&alpha, &a, &x, &y).unwrap();
        assert!(thm.hyps().is_empty() && thm.has_no_obs());
    }

    #[test]
    fn nil_ne_cons_is_genuine() {
        let alpha = a_ty();
        let x = nil(&alpha).unwrap();
        let y = nil(&alpha).unwrap();
        let thm = nil_ne_cons(&alpha, &x, &y).unwrap();
        assert!(thm.hyps().is_empty() && thm.has_no_obs());
    }
}
