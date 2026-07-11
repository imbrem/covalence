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

use covalence_core::{Error, Result, Term, Type};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::derived::DerivedRules;

use crate::init::ext::{TermExt, ThmExt};

// Re-export the `defs/cond.rs` catalogue (the `cond_spec` handle stays
// in `covalence_hol_eval::defs`, reached via the blanket re-export there).
pub use covalence_hol_eval::defs::{cond, cond_spec};

// ============================================================================
// The reduction clauses.
// ============================================================================

/// `⊢ t = t'` collapsing a (possibly nested) leading `cond α (T|F) x y`
/// to its selected branch, recursively and **innermost-first**: the two
/// branches' own nested `cond`s are collapsed before the outer one, so
/// [`cond_true`]/[`cond_false`]'s choice machinery only ever sees simple
/// branches (an un-collapsed nested `cond` would otherwise leak into the
/// `select_ax` antecedent). Bottoms out at reflexivity on any node that is
/// not a `cond` on a bool literal.
///
/// A `rhs_conv`-shaped conversion (`&Term → Result<Thm>`): the tail of a
/// `reduce` pass that has already folded the `cond` *conditions* to `T`/`F`
/// literals but cannot fire the (defined-constant) `cond` clauses. Used by
/// the [`init::utf8`](crate::init::utf8) / [`init::utf16`](crate::init::utf16)
/// per-character encoders. Genuine.
pub fn collapse_conds(t: &Term) -> Result<Thm> {
    if let Some((c, x, y)) = as_cond(t)
        && let Some(b) = c.as_bool()
    {
        let x_eq = collapse_conds(&x)?; // ⊢ x = x'
        let y_eq = collapse_conds(&y)?; // ⊢ y = y'
        let x1 = rhs_of(&x_eq)?;
        let y1 = rhs_of(&y_eq)?;
        let alpha = x1.type_of()?;
        // ⊢ cond b x y = cond b x' y'  (congruence on the two branches).
        let cond_op = Term::app(cond(alpha.clone()), c.clone());
        let cong = Thm::refl(cond_op)?.cong_app(x_eq)?.cong_app(y_eq)?;
        let clause = if b {
            cond_true(&alpha, &x1, &y1)?
        } else {
            cond_false(&alpha, &x1, &y1)?
        };
        return cong.trans(clause);
    }
    Thm::refl(t.clone())
}

/// Match `cond α c x y`, returning `(c, x, y)`.
fn as_cond(t: &Term) -> Option<(Term, Term, Term)> {
    let (cxy, y) = t.as_app()?;
    let (cx, x) = cxy.as_app()?;
    let (head, c) = cx.as_app()?;
    let (spec, _args) = head.as_spec()?;
    if spec.symbol().label() == cond_spec().symbol().label() {
        Some((c.clone(), x.clone(), y.clone()))
    } else {
        None
    }
}

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
    // ⊢ cond b x y = ε P, where P = λz. (b=T ⟹ z=x) ∧ (b=F ⟹ z=y).
    //
    // Unfold **only the head** `cond` and β-reduce its three-arg redex,
    // leaving the branches `x`/`y` verbatim. A nested `cond` sitting in a
    // branch must NOT be δ-unfolded here: its ε-form would then appear in
    // `P` (and hence in the `select_ax` antecedent below) while `pred_at`
    // rebuilds the conjunction from the *literal* branch, so the two would
    // no longer match. (This is why the old `delta_all` + full `reduce`,
    // which unfold every `cond` occurrence on the spine, could not serve a
    // nested-`cond` branch.) The per-argument `cong_fn` also validates
    // `x, y : α` — an ill-typed branch is rejected as the application is built.
    let mut unfold = cond(alpha.clone()).delta()?; // ⊢ cond α = λt x y. ε(…)
    for a in [covalence_hol_eval::mk_bool(b), x.clone(), y.clone()] {
        unfold = unfold.cong_fn(a)?;
        let rhs = rhs_of(&unfold)?;
        unfold = unfold.trans(Thm::beta_conv(rhs)?)?;
    }
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
    selecting.imp_elim(Thm::refl(covalence_hol_eval::mk_bool(b))?)
}

/// `⊢ pred w` — the conjunction `(b=T ⟹ w=x) ∧ (b=F ⟹ w=y)` proved at
/// `w`, then β-folded back into the applied form `pred w` that
/// `select_ax` expects.
fn pred_at(pred: &Term, w: &Term, b: bool, x: &Term, y: &Term) -> Result<Thm> {
    let t_lit = covalence_hol_eval::mk_bool(true);
    let f_lit = covalence_hol_eval::mk_bool(false);
    // The two literal antecedents; exactly one is satisfiable.
    let b_is_true = covalence_hol_eval::mk_bool(b).equals(t_lit)?; //  b = T
    let b_is_false = covalence_hol_eval::mk_bool(b).equals(f_lit)?; // b = F

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
/// (`T = F` / `F = T`); the cert-path reducer
/// ([`covalence_hol_eval::reduce`]) decides it to `F`, and ex falso
/// gives the consequent vacuously.
fn clause_branch(ante: &Term, satisfiable: bool, w: &Term, branch: &Term) -> Result<Thm> {
    if satisfiable {
        // `w == branch` here, so `⊢ w = w` is `⊢ w = branch`.
        Thm::refl(w.clone())?.imp_intro(ante)
    } else {
        let goal = w.clone().equals(branch.clone())?;
        // {ante} ⊢ F  via  ⊢ ante = F  (cert-path reduce)  and  {ante} ⊢ ante.
        let to_false = covalence_hol_eval::reduce(ante)
            .ok_or(Error::NotReducible)?
            .eq_mp(Thm::assume(ante.clone())?)?;
        to_false.false_elim(goal)?.imp_intro(ante)
    }
}

/// The right-hand side of an equational theorem's conclusion.
fn rhs_of(thm: &Thm) -> Result<Term> {
    Ok(thm.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone())
}

crate::cov_theory! {
    /// cond clauses ported to `cond.cov`, over `core`. `cond` itself is
    /// defined **inline** in `cond.cov` via `#def` — a small proof-of-concept
    /// of the `#def`-eliminates-`*_env` migration.
    pub mod cov from "cond.cov" {
        import "core" = crate::script::Env::core();
        "cond.true"  => pub fn cond_true_cov;
        "cond.false" => pub fn cond_false_cov;
    }
}

#[cfg(test)]
mod cov_tests {
    use super::cov;
    use covalence_core::{Term, Type};

    fn alpha() -> Type {
        Type::tfree("a")
    }

    /// The **inline** `cond` constant — the very `TermSpec` that `cond.cov`'s
    /// `#def` introduced and `#export`ed (an opaque `SmolStr("cond")` spec, NOT
    /// the catalogue's `bool.cond`). Pulled from the module's exported env so
    /// the comparison below is genuine byte-identity (`==` on spec leaves is
    /// pointer-based), proving the `.cov` clauses really are *about* the
    /// inline-defined `cond`.
    fn inline_cond(a: &Type) -> Term {
        let c = cov::ENV
            .lookup_const("cond")
            .expect("cond.cov exports its inline `cond`");
        let constant = match c {
            crate::script::ConstDef::Op(t) | crate::script::ConstDef::Poly(t) => t,
            crate::script::ConstDef::Eq => unreachable!(),
        };
        let (spec, _) = constant.as_spec().unwrap();
        Term::term_spec(spec.clone(), vec![a.clone()])
    }

    /// Build the term `∀x y. cond_op b x y = (x|y)`.
    fn lhs_eq_rhs(cond_op: &Term, a: &Type, then_branch: bool) -> Term {
        use covalence_core::subst::close;
        let x = Term::free("x", a.clone());
        let y = Term::free("y", a.clone());
        let b = covalence_hol_eval::mk_bool(then_branch);
        let lhs = Term::app(
            Term::app(Term::app(cond_op.clone(), b), x.clone()),
            y.clone(),
        );
        let rhs = if then_branch { x } else { y };
        let body = Term::app(Term::app(Term::eq_op(a.clone()), lhs), rhs);
        // close over y then x, wrapping each in ∀.
        let inner = Term::abs(a.clone(), close(&body, "y"));
        let inner = Term::app(covalence_hol_eval::defs::forall(a.clone()), inner);
        let outer = Term::abs(a.clone(), close(&inner, "x"));
        Term::app(covalence_hol_eval::defs::forall(a.clone()), outer)
    }

    /// The `.cov`-proved clauses match the **inline-`cond`** statement exactly
    /// (the proof-of-concept: `cond` is now a `.cov` `#def`, not a `*prim`).
    #[test]
    fn cond_cov_matches_inline_def() {
        let a = alpha();
        let cond_op = inline_cond(&a);
        assert_eq!(
            cov::cond_true_cov().concl(),
            &lhs_eq_rhs(&cond_op, &a, true)
        );
        assert_eq!(
            cov::cond_false_cov().concl(),
            &lhs_eq_rhs(&cond_op, &a, false)
        );
        // Both are genuine, hypothesis-free theorems.
        assert!(cov::cond_true_cov().hyps().is_empty());
        assert!(cov::cond_false_cov().hyps().is_empty());
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
        assert!(thm.hyps().is_empty(), "cond.true is proved, not postulated");
        let lhs = Term::cond(covalence_hol_eval::mk_bool(true), x(), y());
        assert_eq!(thm.concl(), &lhs.equals(x()).unwrap());
    }

    #[test]
    fn cond_false_reduces_to_else_branch() {
        let thm = cond_false(&alpha(), &x(), &y()).unwrap();
        assert!(
            thm.hyps().is_empty(),
            "cond.false is proved, not postulated"
        );
        let lhs = Term::cond(covalence_hol_eval::mk_bool(false), x(), y());
        assert_eq!(thm.concl(), &lhs.equals(y()).unwrap());
    }

    #[test]
    fn cond_clauses_work_at_a_concrete_type() {
        // cond at `nat` with literal branches.
        let nat = Type::nat();
        let a = covalence_hol_eval::mk_nat(covalence_types::Nat::from_inner(7u32.into()));
        let bb = covalence_hol_eval::mk_nat(covalence_types::Nat::from_inner(9u32.into()));
        let t = cond_true(&nat, &a, &bb).unwrap();
        assert_eq!(rhs_of(&t).unwrap(), a);
        let f = cond_false(&nat, &a, &bb).unwrap();
        assert_eq!(rhs_of(&f).unwrap(), bb);
        assert!(t.hyps().is_empty() && f.hyps().is_empty());
    }
}
