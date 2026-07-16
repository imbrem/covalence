//! An **eval-TCB-free** `nat` order backend — the `succ`-tower twin of the
//! native eval `int` in [`order`](crate::order).
//!
//! [`SuccHol`] is a [`Hol`] backend that delegates every kernel operation to
//! [`NativeHol`] (terms / types / theorems are the same `covalence_core` types),
//! and carries the **`nat`** linear order (`nat.lt` / `nat.le`) as its
//! [`LinOrder`]. [`SuccDischarger`] discharges a *closed* comparison of `nat`
//! literals **by pure induction** — it represents each literal `n` as the
//! `succ`-tower `Sⁿ 0`, and proves / refutes `Sⁱ 0 ⋈ Sʲ 0` by peeling matched
//! successors down to a `0`-base fact (`not_succ_le_zero`, `not_lt_zero`,
//! `le_zero`, `zero_lt_succ`), all of which are inductively-proved `nat`
//! theorems. **No `covalence-hol-eval` computation cert is ever built**: there
//! is no `reduce`, no `decide`/`prove_true`, no `IntArithCert`, and the numerals
//! are `Sⁿ 0` towers rather than opaque `mk_nat n` literals that only evaluation
//! can compare.
//!
//! (The single `0` constant is `covalence_hol_eval::mk_nat(0)` — the `Nat(0)`
//! *term*, which is precisely the `0` the `nat` order lemmas are stated over. It
//! is a leaf constructor, not a computation certificate; the whole tower `Sⁿ 0`
//! is built by applying the `succ` constructor, and every comparison is decided
//! structurally by the inductive selector-clause lemmas.)
//!
//! This is the payoff of making the [`Discharger`] a parameter: the *same*
//! `covalence-kernel-smt` chain replay ([`refute_chain`](crate::order)) that runs
//! against the trusted eval kernel also runs here, closing `5 ≤ 2` by induction
//! with zero eval-TCB dependency. `SuccDischarger` is **nat-only** (no negative
//! literals): `lit` on `n < 0` returns a `0` tower, and `close` will simply fail
//! to refute a comparison it cannot express — it never mints an unsound `⊢ ⊥`.

use covalence_core::{Result, Term, Type};
use covalence_hol_eval::EvalThm;
use covalence_hol_eval::derived::DerivedRules;
use covalence_init::init::nat;

use crate::order::{Discharger, LinOrder, Strict};
use crate::{Hol, NativeHol, rewrite};

/// The `succ`-tower `nat` order backend. A unit struct: it holds no state and
/// forwards every [`Hol`] operation to [`NativeHol`], adding only the `nat`
/// [`LinOrder`] and pairing with [`SuccDischarger`] for eval-free closed
/// comparisons.
#[derive(Clone, Copy, Debug, Default)]
pub struct SuccHol;

impl Hol for SuccHol {
    type Type = Type;
    type Term = Term;
    type Thm = EvalThm;

    // -- Types --
    fn bool_ty(&self) -> Type {
        <NativeHol as Hol>::bool_ty(&NativeHol)
    }
    fn fun_ty(&self, a: Type, b: Type) -> Type {
        <NativeHol as Hol>::fun_ty(&NativeHol, a, b)
    }
    fn tvar(&self, name: &str) -> Type {
        <NativeHol as Hol>::tvar(&NativeHol, name)
    }

    // -- Term builders --
    fn var(&self, name: &str, ty: Type) -> Term {
        <NativeHol as Hol>::var(&NativeHol, name, ty)
    }
    fn app(&self, f: Term, x: Term) -> Result<Term> {
        <NativeHol as Hol>::app(&NativeHol, f, x)
    }
    fn lam(&self, name: &str, ty: Type, body: Term) -> Term {
        <NativeHol as Hol>::lam(&NativeHol, name, ty, body)
    }
    fn eq(&self, a: Term, b: Term) -> Result<Term> {
        <NativeHol as Hol>::eq(&NativeHol, a, b)
    }
    fn imp(&self, a: Term, b: Term) -> Result<Term> {
        <NativeHol as Hol>::imp(&NativeHol, a, b)
    }
    fn not(&self, a: Term) -> Result<Term> {
        <NativeHol as Hol>::not(&NativeHol, a)
    }
    fn and(&self, a: Term, b: Term) -> Result<Term> {
        <NativeHol as Hol>::and(&NativeHol, a, b)
    }
    fn forall(&self, name: &str, ty: Type, body: Term) -> Result<Term> {
        <NativeHol as Hol>::forall(&NativeHol, name, ty, body)
    }
    fn exists(&self, name: &str, ty: Type, body: Term) -> Result<Term> {
        <NativeHol as Hol>::exists(&NativeHol, name, ty, body)
    }
    fn select_op(&self, ty: Type) -> Term {
        <NativeHol as Hol>::select_op(&NativeHol, ty)
    }

    // -- Queries --
    fn type_of(&self, t: &Term) -> Result<Type> {
        <NativeHol as Hol>::type_of(&NativeHol, t)
    }
    fn dest_app(&self, t: &Term) -> Option<(Term, Term)> {
        <NativeHol as Hol>::dest_app(&NativeHol, t)
    }
    fn dest_eq(&self, t: &Term) -> Option<(Term, Term)> {
        <NativeHol as Hol>::dest_eq(&NativeHol, t)
    }
    fn dest_var(&self, t: &Term) -> Option<(String, Type)> {
        <NativeHol as Hol>::dest_var(&NativeHol, t)
    }
    fn subst_free(&self, t: &Term, name: &str, replacement: &Term) -> Term {
        <NativeHol as Hol>::subst_free(&NativeHol, t, name, replacement)
    }
    fn concl(&self, th: &EvalThm) -> Term {
        <NativeHol as Hol>::concl(&NativeHol, th)
    }
    fn hyps(&self, th: &EvalThm) -> Vec<Term> {
        <NativeHol as Hol>::hyps(&NativeHol, th)
    }

    // -- Rules --
    fn assume(&self, t: Term) -> Result<EvalThm> {
        <NativeHol as Hol>::assume(&NativeHol, t)
    }
    fn refl(&self, t: Term) -> Result<EvalThm> {
        <NativeHol as Hol>::refl(&NativeHol, t)
    }
    fn sym(&self, th: EvalThm) -> Result<EvalThm> {
        <NativeHol as Hol>::sym(&NativeHol, th)
    }
    fn trans(&self, a: EvalThm, b: EvalThm) -> Result<EvalThm> {
        <NativeHol as Hol>::trans(&NativeHol, a, b)
    }
    fn eq_mp(&self, eq: EvalThm, p: EvalThm) -> Result<EvalThm> {
        <NativeHol as Hol>::eq_mp(&NativeHol, eq, p)
    }
    fn beta_conv(&self, redex: Term) -> Result<EvalThm> {
        <NativeHol as Hol>::beta_conv(&NativeHol, redex)
    }
    fn eta_conv(&self, abs: Term) -> Result<EvalThm> {
        <NativeHol as Hol>::eta_conv(&NativeHol, abs)
    }
    fn cong_app(&self, f: EvalThm, x: EvalThm) -> Result<EvalThm> {
        <NativeHol as Hol>::cong_app(&NativeHol, f, x)
    }
    fn inst(&self, th: EvalThm, name: &str, t: Term) -> Result<EvalThm> {
        <NativeHol as Hol>::inst(&NativeHol, th, name, t)
    }
    fn all_intro(&self, th: EvalThm, name: &str, ty: Type) -> Result<EvalThm> {
        <NativeHol as Hol>::all_intro(&NativeHol, th, name, ty)
    }
    fn all_elim(&self, th: EvalThm, t: Term) -> Result<EvalThm> {
        <NativeHol as Hol>::all_elim(&NativeHol, th, t)
    }
    fn imp_intro(&self, th: EvalThm, h: &Term) -> Result<EvalThm> {
        <NativeHol as Hol>::imp_intro(&NativeHol, th, h)
    }
    fn imp_elim(&self, imp: EvalThm, ante: EvalThm) -> Result<EvalThm> {
        <NativeHol as Hol>::imp_elim(&NativeHol, imp, ante)
    }
    fn and_intro(&self, a: EvalThm, b: EvalThm) -> Result<EvalThm> {
        <NativeHol as Hol>::and_intro(&NativeHol, a, b)
    }
    fn and_elim_l(&self, th: EvalThm) -> Result<EvalThm> {
        <NativeHol as Hol>::and_elim_l(&NativeHol, th)
    }
    fn and_elim_r(&self, th: EvalThm) -> Result<EvalThm> {
        <NativeHol as Hol>::and_elim_r(&NativeHol, th)
    }
    fn false_elim(&self, false_th: EvalThm, goal: Term) -> Result<EvalThm> {
        <NativeHol as Hol>::false_elim(&NativeHol, false_th, goal)
    }
    fn select_ax(&self, pred: Term, witness: Term) -> Result<EvalThm> {
        <NativeHol as Hol>::select_ax(&NativeHol, pred, witness)
    }

    // -- Hard derived rules --
    fn beta_nf(&self, t: Term) -> Result<EvalThm> {
        <NativeHol as Hol>::beta_nf(&NativeHol, t)
    }
    fn exists_intro(&self, pred: Term, witness: Term, proof: EvalThm) -> Result<EvalThm> {
        <NativeHol as Hol>::exists_intro(&NativeHol, pred, witness, proof)
    }
    fn exists_elim(&self, exists_thm: EvalThm, c: Term, step: EvalThm) -> Result<EvalThm> {
        <NativeHol as Hol>::exists_elim(&NativeHol, exists_thm, c, step)
    }
    fn rw_all(&self, t: &Term, eq: &EvalThm) -> Result<EvalThm> {
        <NativeHol as Hol>::rw_all(&NativeHol, t, eq)
    }
}

// ============================================================================
// The `nat` linear order — proved lemmas, no eval
// ============================================================================

impl LinOrder for SuccHol {
    fn lt(&self, a: Term, b: Term) -> Result<Term> {
        Hol::app(self, Hol::app(self, nat::nat_lt(), a)?, b)
    }
    fn le(&self, a: Term, b: Term) -> Result<Term> {
        Hol::app(self, Hol::app(self, nat::nat_le(), a)?, b)
    }
    fn lt_trans(&self) -> Result<EvalThm> {
        Ok(nat::lt_trans())
    }
    fn le_trans(&self) -> Result<EvalThm> {
        Ok(nat::le_trans())
    }
    fn lt_of_le_of_lt(&self) -> Result<EvalThm> {
        Ok(nat::lt_of_le_of_lt())
    }
    fn lt_of_lt_of_le(&self) -> Result<EvalThm> {
        Ok(nat::lt_of_lt_of_le())
    }
    fn absurd_lt(&self, a: Term, lt_aa: EvalThm) -> Result<EvalThm> {
        // ⊢ ∀n. ¬(n<n)  ⟹  ⊢ ¬(a<a)  ⟹  ⊢ ⊥ against a : ⊢ a<a.
        nat::lt_irrefl().all_elim(a)?.not_elim(lt_aa)
    }
}

// ============================================================================
// The succ-tower discharger — closed comparisons by pure induction
// ============================================================================

/// The **eval-TCB-free** discharger for the `nat` order: closed comparisons of
/// `nat` numerals are proved / refuted by peeling matched `succ`s and bottoming
/// out on the inductively-proved `0`-base lemmas. See the [module docs](self)
/// for the "no eval cert" contract. Nat-only: no negative literals.
#[derive(Clone, Copy, Debug, Default)]
pub struct SuccDischarger;

/// `0 : nat` — the `Nat(0)` term the `nat` order lemmas are stated over. A leaf
/// constructor, not a computation cert.
fn zero() -> Term {
    covalence_hol_eval::mk_nat(0u32)
}

/// `S t`.
fn succ_of(t: Term) -> Term {
    Term::app(nat::nat_succ(), t)
}

/// The `succ`-tower `Sⁿ 0`.
fn tower(n: u32) -> Term {
    let mut t = zero();
    for _ in 0..n {
        t = succ_of(t);
    }
    t
}

impl SuccDischarger {
    /// `⊢ Sⁱ 0 ≤ Sʲ 0` for `i ≤ j`, by pure induction. Base `⊢ 0 ≤ S^(j-i) 0`
    /// (`le_zero`), then wrap `i` matched successors via `le_succ_succ`
    /// (`(S a ≤ S b) = (a ≤ b)`, so `a≤b ⊢ Sa≤Sb`). Errors on `i > j`.
    pub fn prove_le(&self, l: &SuccHol, i: u32, j: u32) -> Result<EvalThm> {
        if i > j {
            return Err(covalence_core::Error::NotAnEquation);
        }
        // base: 0 ≤ S^(j-i) 0.
        let mut a = zero();
        let mut b = tower(j - i);
        let mut thm = nat::le_zero().all_elim(b.clone())?; // ⊢ 0 ≤ S^(j-i) 0
        // wrap i successors: (a≤b) ⊢ (Sa≤Sb) via le_succ_succ.sym.eq_mp.
        for _ in 0..i {
            let bridge = nat::le_succ_succ()
                .all_elim(a.clone())?
                .all_elim(b.clone())?; // (Sa≤Sb) = (a≤b)
            thm = l.eq_mp(l.sym(bridge)?, thm)?; // ⊢ Sa ≤ Sb
            a = succ_of(a);
            b = succ_of(b);
        }
        Ok(thm)
    }

    /// `⊢ Sⁱ 0 < Sʲ 0` for `i < j`, by pure induction. Base `⊢ 0 < S^(j-i) 0`
    /// (`zero_lt_succ`, valid as `j-i ≥ 1`), then wrap `i` successors via
    /// `lt_succ_succ`. Errors on `i ≥ j`.
    pub fn prove_lt(&self, l: &SuccHol, i: u32, j: u32) -> Result<EvalThm> {
        if i >= j {
            return Err(covalence_core::Error::NotAnEquation);
        }
        // base: 0 < S^(j-i) 0 = S (S^(j-i-1) 0).
        let mut a = zero();
        let inner = tower(j - i - 1);
        let mut b = succ_of(inner.clone());
        let mut thm = nat::zero_lt_succ().all_elim(inner)?; // ⊢ 0 < S^(j-i) 0
        for _ in 0..i {
            let bridge = nat::lt_succ_succ()
                .all_elim(a.clone())?
                .all_elim(b.clone())?; // (Sa<Sb) = (a<b)
            thm = l.eq_mp(l.sym(bridge)?, thm)?; // ⊢ Sa < Sb
            a = succ_of(a);
            b = succ_of(b);
        }
        Ok(thm)
    }

    /// `⊢ ¬(Sⁱ 0 ≤ Sʲ 0)` for `i > j`, by pure induction. Peel `j` matched
    /// successors via `le_succ_succ` to `(Sⁱ 0 ≤ Sʲ 0) = (S^(i-j) 0 ≤ 0)`,
    /// whose RHS is refuted by `not_succ_le_zero` (`i-j ≥ 1`); rewrite the
    /// negation back through the equation. Errors on `i ≤ j`.
    pub fn refute_le(&self, l: &SuccHol, i: u32, j: u32) -> Result<EvalThm> {
        if i <= j {
            return Err(covalence_core::Error::NotAnEquation);
        }
        // Build ⊢ (Sⁱ 0 ≤ Sʲ 0) = (S^(i-j) 0 ≤ 0) by chaining le_succ_succ.
        let eq_to_base = self.peel_le(l, i, j)?; // ⊢ atom = (S^(i-j) 0 ≤ 0)
        // ⊢ ¬(S^(i-j) 0 ≤ 0)  (i-j ≥ 1, so S^(i-j) 0 = S(S^(i-j-1) 0)).
        let base_neg = nat::not_succ_le_zero().all_elim(tower(i - j - 1))?;
        // Rewrite the base negation's atom back to the full atom.
        rewrite(l, base_neg, &l.sym(eq_to_base)?) // ⊢ ¬atom
    }

    /// `⊢ ¬(Sⁱ 0 < Sʲ 0)` for `i ≥ j`, by pure induction. Peel `j` matched
    /// successors via `lt_succ_succ` to `(Sⁱ 0 < Sʲ 0) = (S^(i-j) 0 < 0)`,
    /// refuted by `not_lt_zero`; rewrite back. Errors on `i < j`.
    pub fn refute_lt(&self, l: &SuccHol, i: u32, j: u32) -> Result<EvalThm> {
        if i < j {
            return Err(covalence_core::Error::NotAnEquation);
        }
        let eq_to_base = self.peel_lt(l, i, j)?; // ⊢ atom = (S^(i-j) 0 < 0)
        let base_neg = nat::not_lt_zero().all_elim(tower(i - j))?; // ⊢ ¬(S^(i-j) 0 < 0)
        rewrite(l, base_neg, &l.sym(eq_to_base)?) // ⊢ ¬atom
    }

    /// `⊢ (Sⁱ 0 ≤ Sʲ 0) = (S^(i-j) 0 ≤ 0)` — chain `j` `le_succ_succ` steps
    /// (peeling the smaller tower `Sʲ 0` fully). Requires `i ≥ j`.
    fn peel_le(&self, l: &SuccHol, i: u32, j: u32) -> Result<EvalThm> {
        let (mut a, mut b) = (tower(i), tower(j));
        // start: reflexivity ⊢ (Sⁱ0≤Sʲ0) = (Sⁱ0≤Sʲ0).
        let mut acc = l.refl(LinOrder::le(l, a.clone(), b.clone())?)?;
        for _ in 0..j {
            let (a1, b1) = (dest_succ(&a), dest_succ(&b));
            let step = nat::le_succ_succ()
                .all_elim(a1.clone())?
                .all_elim(b1.clone())?; // (Sa1≤Sb1)=(a1≤b1)
            acc = l.trans(acc, step)?;
            a = a1;
            b = b1;
        }
        Ok(acc)
    }

    /// `⊢ (Sⁱ 0 < Sʲ 0) = (S^(i-j) 0 < 0)` — chain `j` `lt_succ_succ` steps.
    /// Requires `i ≥ j`.
    fn peel_lt(&self, l: &SuccHol, i: u32, j: u32) -> Result<EvalThm> {
        let (mut a, mut b) = (tower(i), tower(j));
        let mut acc = l.refl(LinOrder::lt(l, a.clone(), b.clone())?)?;
        for _ in 0..j {
            let (a1, b1) = (dest_succ(&a), dest_succ(&b));
            let step = nat::lt_succ_succ()
                .all_elim(a1.clone())?
                .all_elim(b1.clone())?;
            acc = l.trans(acc, step)?;
            a = a1;
            b = b1;
        }
        Ok(acc)
    }
}

/// `S t` → `t`. The argument is always a `succ`-headed tower here.
fn dest_succ(t: &Term) -> Term {
    t.as_app()
        .map(|(_, x)| x.clone())
        .expect("dest_succ on a succ-tower")
}

impl Discharger<SuccHol> for SuccDischarger {
    /// The literal `n` as the `succ`-tower `Sⁿ 0`. Negative `n` cannot be
    /// expressed in `nat`; it maps to `0` (and any comparison the caller builds
    /// with it that `close` is asked to refute will simply fail rather than
    /// mint an unsound refutation).
    fn lit(&self, _l: &SuccHol, n: i128) -> Term {
        tower(u32::try_from(n.max(0)).unwrap_or(u32::MAX))
    }

    /// Refute a false closed comparison of two `succ`-tower literals, by pure
    /// induction, and eliminate it against `acc : ⊢ a ⋈ b`.
    fn close(
        &self,
        l: &SuccHol,
        a: Term,
        b: Term,
        strict: Strict,
        acc: EvalThm,
    ) -> Result<EvalThm> {
        let i = tower_height(&a).ok_or(covalence_core::Error::NotAnEquation)?;
        let j = tower_height(&b).ok_or(covalence_core::Error::NotAnEquation)?;
        // Only a genuinely FALSE comparison is refutable; a true one errors
        // (so a bogus chain cannot mint ⊢ ⊥).
        let neg = match strict {
            Strict::Lt => self.refute_lt(l, i, j)?, // ¬(a<b) needs i ≥ j
            Strict::Le => self.refute_le(l, i, j)?, // ¬(a≤b) needs i > j
        };
        neg.not_elim(acc)
    }
}

/// The height `n` of a `succ`-tower `Sⁿ 0` (the `Nat(0)` leaf), or `None` if the
/// term is not a well-formed tower over that leaf.
fn tower_height(t: &Term) -> Option<u32> {
    let mut n = 0u32;
    let mut cur = t.clone();
    loop {
        if cur == zero() {
            return Some(n);
        }
        let (head, arg) = cur.as_app()?;
        if *head != nat::nat_succ() {
            return None;
        }
        n = n.checked_add(1)?;
        cur = arg.clone();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A refutation `⊢ ⊥` is genuine falsity: it proves an arbitrary goal.
    fn assert_is_falsity(l: &SuccHol, bot: EvalThm) {
        let q = l.var("q_goal", l.bool_ty());
        let anything = l.false_elim(bot, q.clone()).expect("⊥ proves anything");
        assert_eq!(l.concl(&anything), q, "the refutation is genuine falsity");
    }

    /// `prove_lt(2, 5)` yields a hypothesis-free `⊢ S²0 < S⁵0`, purely.
    #[test]
    fn prove_lt_two_lt_five() {
        let l = SuccHol;
        let d = SuccDischarger;
        let thm = d.prove_lt(&l, 2, 5).expect("2 < 5");
        assert!(
            l.hyps(&thm).is_empty(),
            "closed comparison is hypothesis-free"
        );
        let expected = LinOrder::lt(&l, tower(2), tower(5)).unwrap();
        assert_eq!(&l.concl(&thm), &expected);
    }

    /// `prove_le(2, 5)` yields `⊢ S²0 ≤ S⁵0`; `prove_le(5, 5)` yields `≤` refl.
    #[test]
    fn prove_le_holds() {
        let l = SuccHol;
        let d = SuccDischarger;
        let le = d.prove_le(&l, 2, 5).expect("2 ≤ 5");
        assert_eq!(
            &l.concl(&le),
            &LinOrder::le(&l, tower(2), tower(5)).unwrap()
        );
        assert!(l.hyps(&le).is_empty());
        // reflexive edge.
        let refl = d.prove_le(&l, 5, 5).expect("5 ≤ 5");
        assert_eq!(
            &l.concl(&refl),
            &LinOrder::le(&l, tower(5), tower(5)).unwrap()
        );
        // a "false" direction is not provable this way.
        assert!(d.prove_le(&l, 5, 2).is_err());
    }

    /// `SuccDischarger::close` refutes the false `⊢ 5 ≤ 2` (succ-towers) into a
    /// genuine `⊢ ⊥`, and FAILS on the true `⊢ 2 ≤ 5` — all by pure induction.
    #[test]
    fn close_refutes_five_le_two_but_not_two_le_five() {
        let l = SuccHol;
        let d = SuccDischarger;
        let (five, two) = (tower(5), tower(2));

        // false: 5 ≤ 2.
        let atom = LinOrder::le(&l, five.clone(), two.clone()).unwrap();
        let acc = l.assume(atom).unwrap();
        let bot = d
            .close(&l, five.clone(), two.clone(), Strict::Le, acc)
            .expect("5 ≤ 2 is refutable");
        assert_eq!(l.hyps(&bot).len(), 1, "only the assumed 5 ≤ 2 remains");
        assert_is_falsity(&l, bot);

        // true: 2 ≤ 5 must NOT refute.
        let atom_true = LinOrder::le(&l, two.clone(), five.clone()).unwrap();
        let acc_true = l.assume(atom_true).unwrap();
        assert!(
            d.close(&l, two, five, Strict::Le, acc_true).is_err(),
            "a true comparison is not refutable"
        );
    }

    /// `close` on a false strict `⊢ 5 < 5` (i.e. `i ≥ j` with `i = j`) refutes;
    /// a true strict `⊢ 2 < 5` does not.
    #[test]
    fn close_refutes_five_lt_five_but_not_two_lt_five() {
        let l = SuccHol;
        let d = SuccDischarger;
        let five = tower(5);

        let atom = LinOrder::lt(&l, five.clone(), five.clone()).unwrap();
        let acc = l.assume(atom).unwrap();
        let bot = d
            .close(&l, five.clone(), five.clone(), Strict::Lt, acc)
            .expect("5 < 5 is refutable");
        assert_is_falsity(&l, bot);

        let (two, five) = (tower(2), tower(5));
        let atom_true = LinOrder::lt(&l, two.clone(), five.clone()).unwrap();
        let acc_true = l.assume(atom_true).unwrap();
        assert!(d.close(&l, two, five, Strict::Lt, acc_true).is_err());
    }

    /// `tower_height` inverts `tower`, and rejects a non-tower term.
    #[test]
    fn tower_height_round_trips() {
        let l = SuccHol;
        for n in [0u32, 1, 4, 7] {
            assert_eq!(tower_height(&tower(n)), Some(n));
        }
        assert_eq!(tower_height(&l.var("x", l.bool_ty())), None);
    }
}
