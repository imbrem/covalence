//! **S-expressions as `sexp α := tree (option α)`** — the Lisp cons-cell
//! encoding layered on the binary-[`tree`] theory.
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
//! ([`some`] / [`none`])
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

use covalence_core::{Result, Term, Type, subst};
use covalence_hol_eval::EvalThm as Thm;

use crate::init::ext::{TermExt, ThmExt};
use crate::init::option::{none, some, some_ne_none};
use crate::init::tree;

/// `option α` — the element type of the `tree` underlying `sexp α`.
pub fn sexp_elem_ty(alpha: &Type) -> Type {
    covalence_hol_eval::defs::option(alpha.clone())
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
// Constant-form constructors (for the `.cov` surface / [`sexp_env`]).
//
// As in [`tree`], the `.cov` proof language applies head symbols by curried
// `Term::app` with no β-reduction, while the distinctness facts are stated
// over the β-reduced encoding. We expose the atom/nil/cons constructors as
// closed-λ / nullary CONSTANTS and bridge to their applied form with
// [`tree::to_applied`]-style β-bridging (here via the `tree` constant
// constructors directly).
// ============================================================================

/// `atom_fn : α → sexp α` — `atom` as a closed λ constant, `λa. atom a`.
pub fn atom_fn(alpha: &Type) -> Result<Term> {
    let a = Term::free("__a", alpha.clone());
    let body = atom(alpha, a)?;
    Ok(Term::abs(alpha.clone(), subst::close(&body, "__a")))
}

/// `app(atom_fn, a)` — the applied constant form of `atom a`.
pub fn atom_app(alpha: &Type, a: &Term) -> Result<Term> {
    Ok(Term::app(atom_fn(alpha)?, a.clone()))
}

/// `nil : sexp α` — `nil` as a (nullary) constant; this IS the reduced
/// encoding `leaf none`, so no applied form is needed.
pub fn nil_const(alpha: &Type) -> Result<Term> {
    nil(alpha)
}

/// `cons_fn : sexp α → sexp α → sexp α` — `cons` as a closed λ constant,
/// `λx y. cons x y` (= `tree::branch_fn` at element type `option α`).
pub fn cons_fn(alpha: &Type) -> Result<Term> {
    tree::branch_fn(&sexp_elem_ty(alpha))
}

/// `app(app(cons_fn, x), y)` — the applied constant form of `cons x y`.
pub fn cons_app(alpha: &Type, x: &Term, y: &Term) -> Result<Term> {
    tree::branch_app(&sexp_elem_ty(alpha), x, y)
}

// ============================================================================
// Reconstruction / distinctness lemmas
// ============================================================================

/// `⊢ ¬(atom a = nil)` — an atom is never nil. From `leaf` injectivity
/// (`leaf (some a) = leaf none ⟹ some a = none`) contradicting
/// [`some_ne_none`].
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

/// `⊢ ¬(atom a = nil)` at the **boolean** observation type (`'r := bool`),
/// the form the `.cov` seam uses so that all three `sexp` distinctness facts
/// share one observation type (and hence one set of constructor constants).
///
/// We fold both sides through `rec fl fb` at `'r := bool` with the leaf
/// handler `fl = λo:option α. option_case F (λ_:α. T) o` (the body of
/// `is_some`): `atom a = leaf (some a)` folds to `fl (some a) = T` (`case_some`)
/// while `nil = leaf none` folds to `fl none = F` (`case_none`). Under
/// `H : atom a = nil` congruence gives `T = F`, contradiction.
pub fn atom_ne_nil_bool(alpha: &Type, a: &Term) -> Result<Thm> {
    let elem = sexp_elem_ty(alpha);
    let bool_ty = Type::bool();
    let some_a = some(alpha.clone()).apply(a.clone())?;
    let none_t = none(alpha.clone());

    // fl = λo:option α. option_case F (λ_:α. T) o  : option α → bool
    let ff = Term::bool_lit(false);
    let tt = Term::bool_lit(true);
    let f_handler = Term::abs(alpha.clone(), tt.clone()); // λ_:α. T
    let o = Term::free("__o", elem.clone());
    let case_body = crate::init::option::option_case(alpha.clone(), bool_ty.clone())
        .apply(ff.clone())?
        .apply(f_handler.clone())?
        .apply(o.clone())?;
    let fl = Term::abs(elem.clone(), subst::close(&case_body, "__o"));
    // fb : bool → bool → bool — irrelevant (λu v. u).
    let fb = {
        let u = Term::free("__u", bool_ty.clone());
        let inner = Term::abs(bool_ty.clone(), u);
        Term::abs(bool_ty.clone(), subst::close(&inner, "__u"))
    };

    // The fold-function `λt:T⟨option α,bool⟩. rec fl fb t`, for congruence.
    let obs_tree = subst::subst_tfree_in_type(&tree::tree_ty(&elem), "r", &bool_ty);
    let t = Term::free("__t", obs_tree.clone());
    let fold = Term::abs(
        obs_tree.clone(),
        subst::close(&tree::rec(fl.clone(), fb.clone(), t)?, "__t"),
    );

    // The hypothesis `atom a = nil`, at `'r := bool`.
    let atom_b = tree::at_r(&atom(alpha, a.clone())?, &bool_ty)?;
    let nil_b = tree::at_r(&nil(alpha)?, &bool_ty)?;
    let eq = atom_b.clone().equals(nil_b.clone())?;
    let h = Thm::assume(eq.clone())?;

    // {H} ⊢ (λt. rec fl fb t) (atom a) = (λt. rec fl fb t) nil; β-reduce the
    // outer redex on each side to `rec fl fb (atom a)` / `rec fl fb nil`.
    let cong = h
        .cong_arg(fold)?
        .lhs_conv(|t| Thm::beta_conv(t.clone()))?
        .rhs_conv(|t| Thm::beta_conv(t.clone()))?;

    // The two fold values, each `T` / `F`, via the recursor leaf-equation
    // (`atom a = leaf (some a)`, `nil = leaf none`) + the option `case_*`.
    //   rec fl fb (atom a) = fl (some a) = option_case F (λ_.T) (some a) = T
    let rec_atom = tree::rec_leaf(&elem, fl.clone(), fb.clone(), some_a.clone())?
        .rhs_conv(|t| Thm::beta_conv(t.clone()))? // fl (some a) = option_case … (some a)
        .trans(
            crate::init::option::case_some(alpha, &bool_ty, &ff, &f_handler, a)?
                .rhs_conv(|t| t.reduce())?, // option_case … (some a) = T
        )?; // ⊢ rec fl fb (atom a) = T
    //   rec fl fb nil = fl none = option_case F (λ_.T) none = F
    let rec_nil = tree::rec_leaf(&elem, fl.clone(), fb.clone(), none_t.clone())?
        .rhs_conv(|t| Thm::beta_conv(t.clone()))? // fl none = option_case … none
        .trans(crate::init::option::case_none(
            alpha, &bool_ty, &ff, &f_handler,
        )?)?; // ⊢ rec fl fb nil = F

    // {H} ⊢ T = F.
    let t_eq_f = rec_atom.sym()?.trans(cong)?.trans(rec_nil)?;
    let f = t_eq_f.eq_mp(crate::init::logic::truth())?; // {H} ⊢ F
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

// ============================================================================
// Applied-form distinctness lemmas (for the `.cov` seam).
//
// Each bridges the `atom`/`cons` constructor occurrences in the corresponding
// reduced-encoding theorem to their `app(C_fn, …)` form. `nil = leaf none` is
// nullary, so it needs no bridging.
// ============================================================================

/// `⊢ ¬(atom_app a = nil)` — [`atom_ne_nil_bool`] over the applied `atom`
/// form, at observation type `'r := bool` (so all three `sexp` distinctness
/// facts — and hence the `sexp.cov` constructor constants — share one `'r`).
/// `nil` is already a nullary constant, so only the `atom` occurrence is
/// bridged.
pub fn atom_ne_nil_app(alpha: &Type, a: &Term) -> Result<Thm> {
    let bool_ty = Type::bool();
    let thm = atom_ne_nil_bool(alpha, a)?;
    let red_atom = tree::at_r(&atom(alpha, a.clone())?, &bool_ty)?;
    let app_atom = tree::at_r(&atom_app(alpha, a)?, &bool_ty)?;
    tree::to_applied(thm, &app_atom, &red_atom)
}

/// `⊢ ¬(atom_app a = cons_app x y)` — [`atom_ne_cons`] over the applied
/// `atom`/`cons` forms (observation type `'r := bool`).
pub fn atom_ne_cons_app(alpha: &Type, a: &Term, x: &Term, y: &Term) -> Result<Thm> {
    let bool_ty = Type::bool();
    let thm = atom_ne_cons(alpha, a, x, y)?;
    let red_atom = tree::at_r(&atom(alpha, a.clone())?, &bool_ty)?;
    let app_atom = tree::at_r(&atom_app(alpha, a)?, &bool_ty)?;
    let red_cons = tree::at_r(&cons(alpha, x.clone(), y.clone())?, &bool_ty)?;
    let app_cons = tree::at_r(&cons_app(alpha, x, y)?, &bool_ty)?;
    let thm = tree::to_applied(thm, &app_atom, &red_atom)?;
    tree::to_applied(thm, &app_cons, &red_cons)
}

/// `⊢ ¬(nil = cons_app x y)` — [`nil_ne_cons`] over the applied `cons` form
/// (observation type `'r := bool`). `nil` itself is already a constant.
pub fn nil_ne_cons_app(alpha: &Type, x: &Term, y: &Term) -> Result<Thm> {
    let bool_ty = Type::bool();
    let thm = nil_ne_cons(alpha, x, y)?;
    let red_cons = tree::at_r(&cons(alpha, x.clone(), y.clone())?, &bool_ty)?;
    let app_cons = tree::at_r(&cons_app(alpha, x, y)?, &bool_ty)?;
    tree::to_applied(thm, &app_cons, &red_cons)
}

// ============================================================================
// The `.cov` seam environment + ported theory
// ============================================================================

/// The `sexp` seam environment for [`crate::init::sexp::cov`] (`sexp.cov`):
/// the atom/nil/cons constructors as constants and the genuinely-proved
/// distinctness facts as universally-quantified Rust GIVENS, each stated over
/// the constructors' applied constant form.
///
/// Schematic in one element type `'a`. Distinctness is taken at each fact's
/// natural observation type (`atom_ne_nil` at `'r := option 'a`, the cons
/// facts at `'r := bool`).
pub fn sexp_env() -> crate::script::Env {
    use crate::script::ConstDef;

    let alpha = Type::tfree("a");
    let bool_ty = Type::bool();
    let mut e = crate::script::Env::empty();

    // -- constructors as constants, pinned to the boolean observation type --
    // All three distinctness facts share `'r := bool`, so the constructors are
    // monomorphic `Op`s there (the element type `'a` stays a tfree, matching
    // the `.cov` `'a`). Pinning `'r` is what lets the nil-only `atom_ne_nil`
    // `#concl` — which has no subtree to constrain `'r` — elaborate uniquely.
    let at_bool = |t: Term| subst::subst_tfree_in_term(&t, "r", &bool_ty);
    e.define_const(
        "sexp.atom",
        ConstDef::Op(at_bool(atom_fn(&alpha).expect("sexp_env: atom_fn"))),
    );
    e.define_const(
        "sexp.nil",
        ConstDef::Op(at_bool(nil_const(&alpha).expect("sexp_env: nil"))),
    );
    e.define_const(
        "sexp.cons",
        ConstDef::Op(at_bool(cons_fn(&alpha).expect("sexp_env: cons_fn"))),
    );

    // The cons subtrees range over the bool-observation carrier `sexp 'a`
    // at `'r := bool` (the type the `.cov` `#concl` quantifies over).
    let sexp_bool = subst::subst_tfree_in_type(&sexp_ty(&alpha), "r", &bool_ty);

    // ⊢ ∀(a : 'a). ¬(atom a = nil)   [at 'r := bool]
    let a = Term::free("a", alpha.clone());
    let ann = atom_ne_nil_app(&alpha, &a)
        .and_then(|t| t.all_intro("a", alpha.clone()))
        .expect("sexp_env: atom_ne_nil");
    e.define_lemma("atom_ne_nil", ann);

    // ⊢ ∀(a : 'a) (x y : sexp 'a). ¬(atom a = cons x y)   [at 'r := bool]
    // Builder takes the polymorphic-`'r` subtree vars; the fact instantiates
    // `'r := bool`, so the conclusion's `x`/`y` are `sexp 'a`(bool)-typed.
    let a2 = Term::free("a", alpha.clone());
    let x = Term::free("x", sexp_ty(&alpha));
    let y = Term::free("y", sexp_ty(&alpha));
    let anc = atom_ne_cons_app(&alpha, &a2, &x, &y)
        .and_then(|t| t.all_intro("y", sexp_bool.clone()))
        .and_then(|t| t.all_intro("x", sexp_bool.clone()))
        .and_then(|t| t.all_intro("a", alpha.clone()))
        .expect("sexp_env: atom_ne_cons");
    e.define_lemma("atom_ne_cons", anc);

    // ⊢ ∀(x y : sexp 'a). ¬(nil = cons x y)   [at 'r := bool]
    let nnc = nil_ne_cons_app(&alpha, &x, &y)
        .and_then(|t| t.all_intro("y", sexp_bool.clone()))
        .and_then(|t| t.all_intro("x", sexp_bool.clone()))
        .expect("sexp_env: nil_ne_cons");
    e.define_lemma("nil_ne_cons", nnc);

    e
}

crate::cov_theory! {
    /// `sexp` constructor-distinctness theorems ported to `sexp.cov`, over
    /// `core` + the `sexpprim` seam env. `atom_ne_nil` / `atom_ne_cons` /
    /// `nil_ne_cons` are re-exported genuinely (the proof `all-elim`s the
    /// seam given).
    pub mod cov from "sexp.cov" {
        import "core"     = crate::script::Env::core();
        import "sexpprim" = crate::init::sexp::sexp_env();
        "atom_ne_nil"  => pub fn atom_ne_nil_cov;
        "atom_ne_cons" => pub fn atom_ne_cons_cov;
        "nil_ne_cons"  => pub fn nil_ne_cons_cov;
    }
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
        assert!(thm.hyps().is_empty());
        assert!(thm.concl().as_app().is_some(), "a `¬…` conclusion");
    }

    #[test]
    fn atom_ne_cons_is_genuine() {
        let alpha = a_ty();
        let a = Term::free("a", alpha.clone());
        let x = nil(&alpha).unwrap();
        let y = nil(&alpha).unwrap();
        let thm = atom_ne_cons(&alpha, &a, &x, &y).unwrap();
        assert!(thm.hyps().is_empty());
    }

    #[test]
    fn nil_ne_cons_is_genuine() {
        let alpha = a_ty();
        let x = nil(&alpha).unwrap();
        let y = nil(&alpha).unwrap();
        let thm = nil_ne_cons(&alpha, &x, &y).unwrap();
        assert!(thm.hyps().is_empty());
    }

    // -- applied-form bridges (used by the `.cov` seam) -------------------

    #[test]
    fn atom_app_beta_reduces_to_atom() {
        let alpha = a_ty();
        let a = Term::free("a", alpha.clone());
        let app_nf = crate::init::eq::beta_nf(atom_app(&alpha, &a).unwrap())
            .concl()
            .as_eq()
            .unwrap()
            .1
            .clone();
        let red_nf = crate::init::eq::beta_nf(atom(&alpha, a).unwrap())
            .concl()
            .as_eq()
            .unwrap()
            .1
            .clone();
        assert_eq!(app_nf, red_nf);
    }

    #[test]
    fn atom_ne_nil_app_is_genuine() {
        let alpha = a_ty();
        let a = Term::free("a", alpha.clone());
        let thm = atom_ne_nil_app(&alpha, &a).unwrap();
        assert!(thm.hyps().is_empty());
    }
}

#[cfg(test)]
mod cov_tests {
    use super::*;

    /// `atom_ne_nil` from `sexp.cov` matches the seam given's conclusion,
    /// proved genuinely in the script layer.
    #[test]
    fn atom_ne_nil_cov_matches_seam() {
        let alpha = Type::tfree("a");
        let a = Term::free("a", alpha.clone());
        let expected = atom_ne_nil_app(&alpha, &a)
            .and_then(|t| t.all_intro("a", alpha.clone()))
            .unwrap();
        let thm = cov::atom_ne_nil_cov();
        assert_eq!(thm.concl(), expected.concl());
        assert!(thm.hyps().is_empty());
    }

    #[test]
    fn atom_ne_cons_cov_is_genuine() {
        let thm = cov::atom_ne_cons_cov();
        assert!(thm.hyps().is_empty());
    }

    #[test]
    fn nil_ne_cons_cov_is_genuine() {
        let thm = cov::nil_ne_cons_cov();
        assert!(thm.hyps().is_empty());
    }

    /// A downstream-style `.cov` script can `(#import sexp)` and consume the
    /// ported facts (the path internal languages will take). Specialises
    /// `atom_ne_nil` at a concrete atom.
    #[test]
    fn downstream_script_imports_sexp() {
        let src = r#"
            (#import core)  (#open core)
            (#import sexp)  (#open sexp)
            (#thm atom_a_ne_nil
              (#fix (a 'a))
              (#concl (not (= (app sexp.atom a) sexp.nil)))
              (#by
                (derive (all-elim a (atom_ne_nil)))))
        "#;
        let thms = crate::init::check_script(src).expect("downstream script checks");
        assert_eq!(thms.len(), 1);
        let thm = &thms[0].thm;
        assert!(thm.hyps().is_empty());
    }
}
