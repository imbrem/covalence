//! `cond` theorems: the `defs/cond.rs` definition re-exported, plus the
//! **derived** reduction clauses — mirroring how [`init::logic`] pairs
//! the connective definitions with their proved facts.
//!
//! [`init::logic`]: crate::init::logic
//!
//! ## No postulates
//!
//! `defs/cond.rs` defines the Boolean conditional as the HOL Light
//! `COND` let-body
//!
//! ```text
//!     cond ≡ λt x y. ε z. (t = T ⟹ z = x) ∧ (t = F ⟹ z = y)
//! ```
//!
//! and **this module proves its clauses outright** ([`cond_true`] /
//! [`cond_false`]):
//!
//! ```text
//!     ⊢ cond T x y = x        ⊢ cond F x y = y
//! ```
//!
//! Each is HOL Light's `COND_CLAUSES` derivation: δ-unfold `cond` and
//! β-reduce to the bare choice `ε P`, then use the choice axiom
//! [`Thm::select_ax`] to show `ε P` satisfies `P`, whose selecting
//! conjunct (its antecedent `b = b` discharged by reflexivity) is
//! exactly `ε P = x` / `ε P = y`. So every theorem here is genuine
//! (hypothesis- and oracle-free) — there is nothing to postulate.

use covalence_core::{Error, Result, Term, Thm, Type};

use crate::init::ext::{TermExt, ThmExt};

// Re-export the `defs/cond.rs` catalogue (the `cond_spec` handle stays
// in `covalence_core::defs`, reached via the blanket re-export there).
pub use covalence_core::defs::{cond, cond_spec};

// ============================================================================
// The reduction clauses.
// ============================================================================

/// `⊢ cond α T x y = x` — the *then* clause (HOL Light `COND_CLAUSES`,
/// `T` half). Genuine: hypothesis- and oracle-free.
pub fn cond_true(alpha: &Type, x: &Term, y: &Term) -> Result<Thm> {
    cond_clause(alpha, true, x, y)
}

/// `⊢ cond α F x y = y` — the *else* clause (HOL Light `COND_CLAUSES`,
/// `F` half). Genuine: hypothesis- and oracle-free.
pub fn cond_false(alpha: &Type, x: &Term, y: &Term) -> Result<Thm> {
    cond_clause(alpha, false, x, y)
}

/// `⊢ cond α b x y = (x if b else y)` for a literal `b ∈ {T, F}`.
///
/// δ-unfold `cond` and β-reduce to the bare choice `ε P`, then drive the
/// selected branch out of the choice axiom.
fn cond_clause(alpha: &Type, b: bool, x: &Term, y: &Term) -> Result<Thm> {
    // `cond α b x y` — `.apply` validates `x, y : α` (rejecting a branch
    // whose type disagrees with the supplied `α`).
    let cond_b = cond(alpha.clone())
        .apply(Term::bool_lit(b))?
        .apply(x.clone())?
        .apply(y.clone())?;

    // ⊢ cond b x y = ε P, where P = λz. (b=T ⟹ z=x) ∧ (b=F ⟹ z=y).
    let unfold = cond_b
        .delta_all(cond_spec().symbol())?
        .rhs_conv(|t| t.reduce())?;
    let eps = rhs_of(&unfold)?;
    let pred = eps.as_app().ok_or(Error::NotAnEquation)?.1.clone();

    // The branch the literal `b` selects: `x` for T, `y` for F.
    let witness = if b { x } else { y };

    // ⊢ ε P = witness, then chain with the unfolding.
    let eps_eq = choose(&pred, b, witness, x, y)?;
    unfold.trans(eps_eq)
}

/// `⊢ ε pred = witness`, given `pred = λz. (b=T ⟹ z=x) ∧ (b=F ⟹ z=y)`
/// and `witness` the branch the literal `b` selects.
///
/// `select_ax pred witness : ⊢ pred witness ⟹ pred (ε pred)`. We supply
/// `⊢ pred witness` (the conjunction holds at the witness), obtain
/// `⊢ pred (ε pred)`, take its *selecting* conjunct (`b=T ⟹ ε P = x` for
/// `b = T`, `b=F ⟹ ε P = y` for `b = F`), and discharge its antecedent
/// `b = b` by reflexivity.
fn choose(pred: &Term, b: bool, witness: &Term, x: &Term, y: &Term) -> Result<Thm> {
    // ⊢ pred witness.
    let at_witness = pred_at(pred, witness, b, x, y)?;
    // ⊢ pred (ε pred).
    let at_choice = Thm::select_ax(pred.clone(), witness.clone())?.imp_elim(at_witness)?;
    let choice = at_choice
        .concl()
        .as_app()
        .ok_or(Error::NotAnEquation)?
        .1
        .clone();
    // β-expose the conjunction at `ε pred`, then peel the selecting
    // conjunct and discharge `b = b`.
    let conj = Thm::beta_conv(Term::app(pred.clone(), choice))?.eq_mp(at_choice)?;
    let selecting = if b {
        conj.and_elim_l()?
    } else {
        conj.and_elim_r()?
    };
    selecting.imp_elim(Thm::refl(Term::bool_lit(b))?)
}

/// `⊢ pred w` — the conjunction `(b=T ⟹ w=x) ∧ (b=F ⟹ w=y)` proved at
/// `w`, then β-folded back into the applied form `pred w` that
/// `select_ax` expects.
fn pred_at(pred: &Term, w: &Term, b: bool, x: &Term, y: &Term) -> Result<Thm> {
    let t_lit = Term::bool_lit(true);
    let f_lit = Term::bool_lit(false);
    // The two literal antecedents; exactly one is satisfiable.
    let b_is_true = Term::bool_lit(b).equals(t_lit)?; //  b = T
    let b_is_false = Term::bool_lit(b).equals(f_lit)?; // b = F

    // `then` conjunct `b=T ⟹ w=x` (live iff b), `else` conjunct
    // `b=F ⟹ w=y` (live iff ¬b).
    let then_branch = clause_branch(&b_is_true, b, w, x)?;
    let else_branch = clause_branch(&b_is_false, !b, w, y)?;
    let conj = then_branch.and_intro(else_branch)?;

    // `pred w` β-reduces to that conjunction; transport `⊢ conj` across it.
    Thm::beta_conv(Term::app(pred.clone(), w.clone()))?
        .sym()?
        .eq_mp(conj)
}

/// `⊢ ante ⟹ (w = branch)` for one conjunct of the choice predicate.
///
/// On the live branch (`satisfiable`) `w` *is* `branch`, so `w = branch`
/// is reflexive. On the dead branch `ante` is a false literal equation
/// (`T = F` / `F = T`); `reduce_prim` decides it to `F`, and ex falso
/// gives the consequent vacuously.
fn clause_branch(ante: &Term, satisfiable: bool, w: &Term, branch: &Term) -> Result<Thm> {
    if satisfiable {
        // `w == branch` here, so `⊢ w = w` is `⊢ w = branch`.
        Thm::refl(w.clone())?.imp_intro(ante)
    } else {
        let goal = w.clone().equals(branch.clone())?;
        // {ante} ⊢ F  via  ⊢ ante = F  (reduce_prim)  and  {ante} ⊢ ante.
        let to_false = Thm::reduce_prim(ante.clone())?.eq_mp(Thm::assume(ante.clone())?)?;
        to_false.false_elim(goal)?.imp_intro(ante)
    }
}

/// The right-hand side of an equational theorem's conclusion.
fn rhs_of(thm: &Thm) -> Result<Term> {
    Ok(thm.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone())
}

/// Build the env for the `cond` proof language module.
///
/// `cond` is polymorphic (`bool → 'a → 'a → 'a`) so we register it at
/// the type variable `'a` so the `.cov` elaborator can use `(cond true x y)`
/// directly and unify `'a` with the argument types.
pub fn cond_env() -> crate::script::Env {
    let mut e = crate::script::Env::empty();
    e.define_const(
        "cond",
        crate::script::ConstDef::Op(cond(Type::tfree("a"))),
    );
    e
}

crate::cov_theory! {
    /// cond clauses ported to `cond.cov`, over `core` + the `cond` env.
    pub mod cov from "cond.cov" {
        import "core" = crate::script::Env::core();
        import "condprim" = crate::init::cond::cond_env();
        "cond_true"  => pub fn cond_true_cov;
        "cond_false" => pub fn cond_false_cov;
    }
}

#[cfg(test)]
mod cov_tests {
    use super::cov;
    use covalence_core::{Term, Type};

    fn alpha() -> Type {
        Type::tfree("a")
    }

    /// `⊢ ∀x y : 'a. cond T x y = x` — the ∀-closed form matching `cond.cov`.
    fn cond_true_forall() -> covalence_core::Thm {
        let a = alpha();
        let x = Term::free("x", a.clone());
        let y = Term::free("y", a.clone());
        super::cond_true(&a, &x, &y)
            .unwrap()
            .all_intro("y", a.clone())
            .unwrap()
            .all_intro("x", a.clone())
            .unwrap()
    }

    /// `⊢ ∀x y : 'a. cond F x y = y` — the ∀-closed form matching `cond.cov`.
    fn cond_false_forall() -> covalence_core::Thm {
        let a = alpha();
        let x = Term::free("x", a.clone());
        let y = Term::free("y", a.clone());
        super::cond_false(&a, &x, &y)
            .unwrap()
            .all_intro("y", a.clone())
            .unwrap()
            .all_intro("x", a.clone())
            .unwrap()
    }

    #[test]
    fn cond_cov_matches_rust() {
        assert_eq!(cov::cond_true_cov().concl(), cond_true_forall().concl());
        assert_eq!(cov::cond_false_cov().concl(), cond_false_forall().concl());
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn alpha() -> Type {
        Type::tfree("a")
    }

    fn x() -> Term {
        Term::free("x", alpha())
    }

    fn y() -> Term {
        Term::free("y", alpha())
    }

    #[test]
    fn cond_true_reduces_to_then_branch() {
        let thm = cond_true(&alpha(), &x(), &y()).unwrap();
        assert!(thm.hyps().is_empty(), "cond_true is proved, not postulated");
        assert!(thm.has_no_obs(), "cond_true is oracle-free");
        let lhs = Term::cond(Term::bool_lit(true), x(), y());
        assert_eq!(thm.concl(), &lhs.equals(x()).unwrap());
    }

    #[test]
    fn cond_false_reduces_to_else_branch() {
        let thm = cond_false(&alpha(), &x(), &y()).unwrap();
        assert!(
            thm.hyps().is_empty(),
            "cond_false is proved, not postulated"
        );
        assert!(thm.has_no_obs(), "cond_false is oracle-free");
        let lhs = Term::cond(Term::bool_lit(false), x(), y());
        assert_eq!(thm.concl(), &lhs.equals(y()).unwrap());
    }

    #[test]
    fn cond_clauses_work_at_a_concrete_type() {
        // cond at `nat` with literal branches.
        let nat = Type::nat();
        let a = Term::nat_lit(covalence_types::Nat::from_inner(7u32.into()));
        let bb = Term::nat_lit(covalence_types::Nat::from_inner(9u32.into()));
        let t = cond_true(&nat, &a, &bb).unwrap();
        assert_eq!(rhs_of(&t).unwrap(), a);
        let f = cond_false(&nat, &a, &bb).unwrap();
        assert_eq!(rhs_of(&f).unwrap(), bb);
        assert!(t.hyps().is_empty() && f.hyps().is_empty());
    }
}
