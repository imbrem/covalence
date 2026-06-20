//! **Binary trees reified inside HOL** — `tree α := leaf α | branch (tree
//! α) (tree α)` as honest HOL objects with no new kernel TCB, and the base
//! of the [`sexp`](crate::init::sexp) S-expression encoding.
//!
//! ## Encoding (the `sexpr` / `prop` Church pattern)
//!
//! As in [`crate::init::sexpr`], `tree` is a **Church / impredicative
//! encoding** over a fresh result type `'r` rather than a kernel subtype
//! carved through the recursion engine ([`crate::init::inductive`]). For a
//! first-order, *directly*-recursive datatype this gives constructors, a
//! recursor, and the constructor *freeness* facts (injectivity +
//! distinctness) for free — each a one-line HOL build / β-proof — and stays
//! rank-1 and TCB-free.
//!
//! `branch` has **two** recursive arguments, which is exactly the shape the
//! carve-a-subtype engine's `determinacy` / `recursor` layers were extended
//! to handle in this same change (see `init/inductive/{determinacy,recursor}`
//! and the engine `tree`-signature test). The Church route here delivers the
//! *user-facing* `tree` theory immediately; the engine route is the
//! kernel-subtype alternative.
//!
//! ```text
//!   T⟨α,'r⟩  :=  (α → 'r)          -- leaf
//!             → ('r → 'r → 'r)     -- branch
//!             → 'r
//! ```
//!
//! ## What is provided
//!
//! - constructors [`leaf`], [`branch`];
//! - the recursor [`rec`] — `rec fl fb (C …) = f_C …` holds **by β**,
//!   witnessed by [`rec_leaf`] / [`rec_branch`];
//! - **constructor freeness** as genuine theorems:
//!   - [`leaf_inj`] — `⊢ leaf a = leaf b ⟹ a = b` (first-order payload read);
//!   - [`leaf_ne_branch`] — `⊢ ¬(leaf a = branch l r)` (boolean tag read).
//!
//! `branch` injectivity (`branch l r = branch l' r' ⟹ l = l' ∧ r = r'`)
//! needs the recursor's subtree-recovery identity, hence the `Wf` carve —
//! deferred with full induction; see [`induct_note`] + `SKELETONS.md`.
//!
//! Distinct constructor applications are distinct HOL terms, so this is
//! genuine reified syntax (not a shallow embedding). Full structural
//! induction needs a well-formedness side condition (junk inhabits the bare
//! `T⟨α,'r⟩`); see [`induct_note`] + `SKELETONS.md`.

use covalence_core::{Result, Term, Thm, Type, subst};

use crate::init::eq::beta_nf;
use crate::init::ext::{TermExt, ThmExt};
use crate::init::logic::truth;

// ============================================================================
// The carrier `T⟨α,'r⟩`
// ============================================================================

fn rty() -> Type {
    Type::tfree("r")
}

/// `α → 'r` — the `leaf` handler slot.
fn leaf_h_ty(alpha: &Type) -> Type {
    Type::fun(alpha.clone(), rty())
}

/// `'r → 'r → 'r` — the `branch` handler slot.
fn branch_h_ty() -> Type {
    Type::fun(rty(), Type::fun(rty(), rty()))
}

/// `T⟨α,'r⟩ = (α→'r) → ('r→'r→'r) → 'r`.
pub fn tree_ty(alpha: &Type) -> Type {
    Type::fun(leaf_h_ty(alpha), Type::fun(branch_h_ty(), rty()))
}

/// The two handler binder names, in fold order.
const FL: &str = "fl";
const FB: &str = "fb";

fn fl_var(alpha: &Type) -> Term {
    Term::free(FL, leaf_h_ty(alpha))
}

fn fb_var() -> Term {
    Term::free(FB, branch_h_ty())
}

/// Wrap a fold `body : 'r` in the two handler abstractions → `T⟨α,'r⟩`.
fn close_handlers(alpha: &Type, body: Term) -> Term {
    let inner = Term::abs(branch_h_ty(), subst::close(&body, FB));
    Term::abs(leaf_h_ty(alpha), subst::close(&inner, FL))
}

/// Apply a `T⟨α,'r⟩` to the two handlers, producing its fold `: 'r`.
fn apply_handlers(alpha: &Type, t: Term) -> Result<Term> {
    t.apply(fl_var(alpha))?.apply(fb_var())
}

// ============================================================================
// Constructors
// ============================================================================

/// `leaf a : T⟨α,'r⟩` — a leaf carrying the payload `a : α`.
pub fn leaf(alpha: &Type, a: Term) -> Result<Term> {
    Ok(close_handlers(alpha, Term::app(fl_var(alpha), a)))
}

/// `branch l r : T⟨α,'r⟩` — an internal node with subtrees `l`, `r`.
pub fn branch(alpha: &Type, l: Term, r: Term) -> Result<Term> {
    let body = Term::app(
        Term::app(fb_var(), apply_handlers(alpha, l)?),
        apply_handlers(alpha, r)?,
    );
    Ok(close_handlers(alpha, body))
}

// ============================================================================
// Recursor + its defining equations (by β)
// ============================================================================

/// `rec fl fb t : r` — the catamorphism, simply `t fl fb`. The encoded
/// `t : T⟨α,'r⟩` is polymorphic in the result type; we instantiate `'r` to
/// the handlers' concrete result type (read off `fb`'s result) before
/// applying, so e.g. `nat`-valued folds typecheck. (Same trick as
/// [`crate::init::sexpr::rec`].)
pub fn rec(fl: Term, fb: Term, t: Term) -> Result<Term> {
    // `fl : α → r`, so the result type `r` is `fl`'s codomain.
    let r = match fl.type_of()?.kind().clone() {
        covalence_core::TypeKind::Fun(_, cod) => cod,
        _ => {
            return Err(covalence_core::Error::ConnectiveRule(
                "tree::rec: leaf handler is not a function".into(),
            ));
        }
    };
    let t_at = subst::subst_tfree_in_term(&t, "r", &r);
    t_at.apply(fl)?.apply(fb)
}

/// `⊢ rec fl fb (leaf a) = fl a` — the `leaf` recursor equation.
pub fn rec_leaf(alpha: &Type, fl: Term, fb: Term, a: Term) -> Result<Thm> {
    let lhs = rec(fl.clone(), fb, leaf(alpha, a.clone())?)?;
    let rhs = fl.apply(a)?;
    prove_rec_eq(lhs, rhs)
}

/// `⊢ rec fl fb (branch l r) = fb (rec fl fb l) (rec fl fb r)` — the
/// `branch` recursor equation. The recursive calls on `l` and `r` are
/// exactly the folds the encoding plugs in.
pub fn rec_branch(alpha: &Type, fl: Term, fb: Term, l: Term, r: Term) -> Result<Thm> {
    let lhs = rec(fl.clone(), fb.clone(), branch(alpha, l.clone(), r.clone())?)?;
    let rec_l = rec(fl.clone(), fb.clone(), l)?;
    let rec_r = rec(fl.clone(), fb.clone(), r)?;
    let rhs = fb.apply(rec_l)?.apply(rec_r)?;
    prove_rec_eq(lhs, rhs)
}

/// `⊢ lhs = rhs` by β-normalising both sides and checking they coincide.
fn prove_rec_eq(lhs: Term, rhs: Term) -> Result<Thm> {
    let conv = beta_nf(lhs.clone()); // ⊢ lhs = nf
    let nf = conv.concl().as_eq().expect("beta_nf equation").1.clone();
    let rhs_conv = beta_nf(rhs.clone()); // ⊢ rhs = nf'
    if nf == *rhs_conv.concl().as_eq().expect("eq").1 {
        conv.trans(rhs_conv.sym()?)
    } else {
        Err(covalence_core::Error::ConnectiveRule(format!(
            "tree rec equation: lhs normalises to `{nf}`, expected `{rhs}`"
        )))
    }
}

// ============================================================================
// Constructor freeness — injectivity + distinctness
// ============================================================================

/// `⊢ leaf a = leaf b ⟹ a = b` — `leaf` is injective. Observe the payload
/// with the identity leaf handler (`'r := α`, `fl := λx. x`): the recursor
/// reads `a` back out of `leaf a`, so the constructor equation transports to
/// `a = b`. The constructor equation is taken at the **observation type**
/// `'r := α` (a concrete instance of the polymorphic carrier).
pub fn leaf_inj(alpha: &Type, a: &Term, b: &Term) -> Result<Thm> {
    // The constructor equation at the observation type `'r := α`.
    let eq = at_r(&leaf(alpha, a.clone())?, alpha)?
        .equals(at_r(&leaf(alpha, b.clone())?, alpha)?)?;

    // Identity leaf handler `fl = λx:α. x`; the branch handler is irrelevant.
    let id_fl = {
        let x = Term::free("__x", alpha.clone());
        Term::abs(alpha.clone(), subst::close(&x, "__x"))
    };
    let fb = arbitrary_branch_handler(alpha);

    // Under H : leaf a = leaf b, observe both sides through `rec id fb`
    // (which reads the payload back): `{H} ⊢ a = b`.
    let h = Thm::assume(eq.clone())?;
    let a_eq_b = observe(&h, &id_fl, &fb, alpha)?; // {H} ⊢ a = b
    a_eq_b.imp_intro(&eq)
}

/// `⊢ ¬(leaf a = branch l r)` — the two constructors are distinct. Observe
/// with a boolean tag handler (`'r := bool`, `fl := λ_. T`, `fb := λ_ _. F`):
/// the recursor tags a leaf `T` and a branch `F`, so the constructor
/// equality would force `T = F`. Taken at the observation type `'r := bool`.
pub fn leaf_ne_branch(alpha: &Type, a: &Term, l: &Term, r: &Term) -> Result<Thm> {
    // The constructor equation at the observation type `'r := bool`.
    let bool_ty = Type::bool();
    let eq = at_r(&leaf(alpha, a.clone())?, &bool_ty)?
        .equals(at_r(&branch(alpha, l.clone(), r.clone())?, &bool_ty)?)?;

    let tt = Term::bool_lit(true);
    let ff = Term::bool_lit(false);
    // fl = λ_:α. T  (result type bool)
    let fl = Term::abs(alpha.clone(), tt.clone());
    // fb = λ_:bool _:bool. F
    let fb = {
        let inner = Term::abs(Type::bool(), ff.clone());
        Term::abs(Type::bool(), inner)
    };

    // Under H : leaf a = branch l r, observe both sides through the boolean
    // tag fold `rec fl fb ·` (`leaf ↦ T`, `branch ↦ F`): `{H} ⊢ T = F`.
    let h = Thm::assume(eq.clone())?;
    let t_eq_f = observe(&h, &fl, &fb, alpha)?; // {H} ⊢ T = F
    // T = F ⟹ F (eq_mp against ⊢ T), discharge H, negate.
    let contra = t_eq_f.eq_mp(truth())?; // {H} ⊢ F
    contra.imp_intro(&eq)?.not_intro()
}

/// Reinstantiate an encoded tree term's carrier `'r := r`. The freeness
/// lemmas state their constructor equation at a concrete *observation* type
/// (`leaf_inj` at `'r := α`, `leaf_ne_branch` at `'r := bool`); a downstream
/// consumer that must reconstruct that antecedent uses this.
pub fn at_r(t: &Term, r: &Type) -> Result<Term> {
    Ok(subst::subst_tfree_in_term(t, "r", r))
}

// ============================================================================
// Small builders for the freeness observations.
// ============================================================================

/// The fold's result type read off the leaf handler `fl : α → r`.
fn result_ty(fl: &Term) -> Result<Type> {
    match fl.type_of()?.kind().clone() {
        covalence_core::TypeKind::Fun(_, cod) => Ok(cod),
        _ => Err(covalence_core::Error::ConnectiveRule(
            "tree: leaf handler is not a function".into(),
        )),
    }
}

/// `rec fl fb` as `λt:T⟨α,r⟩. rec fl fb t`, with the **observed-tree** type
/// `T⟨α,r⟩` at the concrete result type `r` (the encoding reinstantiated at
/// `'r := r`). Built as an explicit λ so congruence (`cong_arg`) can apply it
/// to a tree-equality already reinstantiated to `'r := r`.
fn rec_partial(fl: &Term, fb: &Term, alpha: &Type) -> Result<Term> {
    let r = result_ty(fl)?;
    let obs_tree_ty = subst::subst_tfree_in_type(&tree_ty(alpha), "r", &r);
    let t = Term::free("__t", obs_tree_ty.clone());
    let body = rec(fl.clone(), fb.clone(), t.clone())?;
    Ok(Term::abs(obs_tree_ty, subst::close(&body, "__t")))
}

/// Observe both sides of a constructor equality `H : C₁ = C₂` (trees at the
/// polymorphic `'r`) through `rec fl fb`: reinstantiate `H` to `'r := r`,
/// then `cong_arg` the recursor function, yielding `⊢ rec… C₁ = rec… C₂` at
/// result type `r`.
fn observe(h: &Thm, fl: &Term, fb: &Term, alpha: &Type) -> Result<Thm> {
    let r = result_ty(fl)?;
    let h_at = h.clone().inst_tfree("r", r)?;
    // `(λt. rec fl fb t) Cᵢ` on each side; β-normalise (strong, under
    // binders) so each observed fold collapses to its value (`a`/`b`, or the
    // boolean tag), giving the value equality directly.
    let cong = h_at.cong_arg(rec_partial(fl, fb, alpha)?)?;
    let (lhs, rhs) = cong.concl().as_eq().ok_or(covalence_core::Error::NotAnEquation)?;
    let lhs_nf = beta_nf(lhs.clone()); // ⊢ lhs = nfL
    let rhs_nf = beta_nf(rhs.clone()); // ⊢ rhs = nfR
    lhs_nf.sym()?.trans(cong)?.trans(rhs_nf)
}

/// A fixed, total branch handler of type `'r → 'r → 'r` at `'r := α` — used
/// where the branch handler's value is irrelevant (leaf injectivity).
fn arbitrary_branch_handler(alpha: &Type) -> Term {
    // λu:α v:α. u
    let inner = {
        let u = Term::free("__u", alpha.clone());
        Term::abs(alpha.clone(), subst::close(&u, "__u"))
    };
    Term::abs(alpha.clone(), inner)
}

// ============================================================================
// Structural induction (note)
// ============================================================================

/// `⊢ (∀a. P (leaf a)) ⟹ (∀l r. P l ⟹ P r ⟹ P (branch l r)) ⟹ ∀t. P t`
/// is **not** derivable for the bare Church encoding without a
/// well-formedness side condition (junk terms inhabit `T⟨α,'r⟩`), exactly as
/// for [`crate::init::sexpr::induct_note`]. The recursor equations +
/// freeness above are what the `tree`/`sexp` `.cov` theory consumes; genuine
/// induction (carving the well-formed encodings with a `Wf` predicate, the
/// standard reducibility argument) is recorded in `SKELETONS.md`.
pub fn induct_note() {}

#[cfg(test)]
mod tests {
    use super::*;

    fn a_ty() -> Type {
        Type::tfree("a")
    }

    #[test]
    fn constructors_typed_and_distinct() {
        let alpha = a_ty();
        let x = Term::free("x", alpha.clone());
        let lf = leaf(&alpha, x.clone()).unwrap();
        assert_eq!(lf.type_of().unwrap(), tree_ty(&alpha));
        let br = branch(&alpha, lf.clone(), lf.clone()).unwrap();
        assert_eq!(br.type_of().unwrap(), tree_ty(&alpha));
        assert_ne!(lf, br);
    }

    #[test]
    fn rec_leaf_holds() {
        let alpha = Type::nat();
        let r = Type::nat();
        // fl = λ_:nat. 0, fb = λu v:nat. u
        let fl = Term::abs(alpha.clone(), Term::nat_lit(0u8));
        let fb = {
            let u = Term::free("u", r.clone());
            let inner = Term::abs(r.clone(), u);
            Term::abs(r.clone(), subst::close(&inner, "u"))
        };
        let a = Term::nat_lit(5u8);
        let thm = rec_leaf(&alpha, fl, fb, a).unwrap();
        assert!(thm.hyps().is_empty());
        assert!(thm.concl().as_eq().is_some());
    }

    #[test]
    fn rec_branch_holds() {
        let alpha = Type::nat();
        let r = Type::nat();
        let fl = Term::abs(alpha.clone(), Term::nat_lit(0u8));
        let fb = {
            let u = Term::free("u", r.clone());
            let inner = Term::abs(r.clone(), u);
            Term::abs(r.clone(), subst::close(&inner, "u"))
        };
        let l = leaf(&alpha, Term::nat_lit(1u8)).unwrap();
        let rt = leaf(&alpha, Term::nat_lit(2u8)).unwrap();
        let thm = rec_branch(&alpha, fl, fb, l, rt).unwrap();
        assert!(thm.hyps().is_empty());
        assert!(thm.concl().as_eq().is_some());
    }

    #[test]
    fn leaf_ne_branch_is_genuine() {
        let alpha = a_ty();
        let a = Term::free("a", alpha.clone());
        let l = leaf(&alpha, a.clone()).unwrap();
        let r = leaf(&alpha, a.clone()).unwrap();
        let thm = leaf_ne_branch(&alpha, &a, &l, &r).unwrap();
        assert!(thm.hyps().is_empty() && thm.has_no_obs());
        // The freeness fact is stated at the boolean observation type.
        let bool_ty = Type::bool();
        let expected = at_r(&leaf(&alpha, a.clone()).unwrap(), &bool_ty)
            .unwrap()
            .equals(at_r(&branch(&alpha, l, r).unwrap(), &bool_ty).unwrap())
            .unwrap()
            .not()
            .unwrap();
        assert_eq!(thm.concl(), &expected);
    }

    #[test]
    fn leaf_inj_is_genuine() {
        let alpha = a_ty();
        let a = Term::free("a", alpha.clone());
        let b = Term::free("b", alpha.clone());
        let thm = leaf_inj(&alpha, &a, &b).unwrap();
        assert!(thm.hyps().is_empty() && thm.has_no_obs());
        // Stated at the `'r := α` observation type.
        let expected = at_r(&leaf(&alpha, a.clone()).unwrap(), &alpha)
            .unwrap()
            .equals(at_r(&leaf(&alpha, b.clone()).unwrap(), &alpha).unwrap())
            .unwrap()
            .imp(a.equals(b).unwrap())
            .unwrap();
        assert_eq!(thm.concl(), &expected);
    }

}
