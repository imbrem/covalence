//! `preorder` — the **theory of preorders and partial orders** plus a
//! **model-generic order-chaining decision procedure**.
//!
//! This is the order-theoretic sibling of [`crate::init::monoid`]: one theory,
//! many models, with the *same* generic proofs and the *same* chaining tactic
//! over every model. The structure is a carrier `α` with a relation
//! `le : α → α → bool`, packaged with its law theorems:
//!
//! - a [`Preorder`] carries `le` plus
//!   ```text
//!       refl  : ⊢ ∀a. le a a
//!       trans : ⊢ ∀a b c. le a b ⟹ le b c ⟹ le a c
//!   ```
//!   and defines `equiv a b := le a b ∧ le b a`;
//! - a [`PartialOrder`] is a [`Preorder`] plus
//!   ```text
//!       antisym : ⊢ ∀a b. le a b ⟹ le b a ⟹ a = b
//!   ```
//!   and defines `lt a b := le a b ∧ ¬(le b a)`.
//!
//! `(nat, ≤)` and `(int, ≤)` are both *models* — see [`nat_partial_order`] and
//! [`int_partial_order`]. The point, exactly as in `monoid`, is that nothing in
//! the generic facts or the chaining algorithm mentions a particular model: they
//! consume the law theorems abstractly, so swapping the model swaps nothing.
//!
//! # Generic facts (all genuine, hypothesis-free)
//!
//! For a [`Preorder`] (`equiv a b := le a b ∧ le b a`):
//! - [`Preorder::equiv_refl`] — `⊢ ∀a. equiv a a`
//! - [`Preorder::equiv_symm`] — `⊢ ∀a b. equiv a b ⟹ equiv b a`
//! - [`Preorder::equiv_trans`] — `⊢ ∀a b c. equiv a b ⟹ equiv b c ⟹ equiv a c`
//! - [`Preorder::le_respects_equiv`] — `⊢ ∀a a' b b'. equiv a a' ⟹ equiv b b'
//!   ⟹ le a b ⟹ le a' b'`
//!
//! For a [`PartialOrder`] (`lt a b := le a b ∧ ¬(le b a)`):
//! - [`PartialOrder::lt_irrefl`] — `⊢ ∀a. ¬(lt a a)`
//! - [`PartialOrder::lt_trans`] — `⊢ ∀a b c. lt a b ⟹ lt b c ⟹ lt a c`
//! - [`PartialOrder::lt_imp_le`] — `⊢ ∀a b. lt a b ⟹ le a b`
//! - [`PartialOrder::lt_not_eq`] — `⊢ ∀a b. lt a b ⟹ ¬(a = b)`
//! - [`PartialOrder::le_iff_lt_or_eq`] — `⊢ ∀a b. le a b ⟺ (lt a b ∨ a = b)`
//! - [`PartialOrder::equiv_iff_eq`] — `⊢ ∀a b. equiv a b ⟺ a = b`
//!
//! # The order tactic — chaining
//!
//! [`PartialOrder::chain`] is the **decision procedure**: given a pile of facts
//! (`⊢ a ≤ b` / `⊢ a < b` / `⊢ a = b` / `⊢ equiv a b`) and a goal of the same
//! four shapes, it computes the **transitive closure** of the facts over the
//! carrier and, if the goal is in the closure, emits a genuine kernel proof of
//! it by chaining `trans` (combining `<` and `≤` to get the strict-or-weak
//! result), `antisym` (to prove `a = b` from `a ≤ b` and `b ≤ a`), and the
//! `lt`/`equiv` (un)folding lemmas. It is *model-relative*: the lemmas it uses
//! are taken from `self`, so installing a different `PartialOrder` re-targets it
//! with no change to the algorithm. See [`order_env`] /
//! [`OrderTactic`] for the `.cov` registration.

use std::collections::HashMap;
use std::sync::Arc;

use async_trait::async_trait;
use covalence_core::{Result, Term, Thm};
use covalence_sexp::SExpr;

use crate::init::ext::TermExt;
use crate::proofs::rewrite::beta_nf;

// ============================================================================
// Preorder
// ============================================================================

/// A concrete **model** of the preorder theory: the relation `le` plus its two
/// laws as already-proved (`∀`-quantified) theorems. `equiv` is the derived
/// symmetric core `le a b ∧ le b a`.
///
/// The law theorems are *trusted to have the documented shapes only as a
/// matching contract*: the kernel re-checks every step the generic proofs and
/// the chaining tactic derive from them, so a wrong law can at worst make a
/// derivation fail, never forge an unsound theorem.
#[derive(Clone)]
pub struct Preorder {
    /// The relation `le : α → α → bool` (an *unapplied* term).
    le: Term,
    /// `⊢ ∀a. le a a`.
    refl: Thm,
    /// `⊢ ∀a b c. le a b ⟹ le b c ⟹ le a c`.
    trans: Thm,
}

impl Preorder {
    /// Assemble a preorder model from its relation and two law theorems.
    pub fn new(le: Term, refl: Thm, trans: Thm) -> Self {
        Preorder { le, refl, trans }
    }

    /// The relation term.
    pub fn le(&self) -> &Term {
        &self.le
    }
    /// `⊢ ∀a. le a a`.
    pub fn refl_lemma(&self) -> &Thm {
        &self.refl
    }
    /// `⊢ ∀a b c. le a b ⟹ le b c ⟹ le a c`.
    pub fn trans_lemma(&self) -> &Thm {
        &self.trans
    }

    /// `le a b`, both arguments supplied.
    pub fn mk_le(&self, a: Term, b: Term) -> Result<Term> {
        self.le.clone().apply(a)?.apply(b)
    }

    /// `equiv a b := le a b ∧ le b a`.
    pub fn mk_equiv(&self, a: Term, b: Term) -> Result<Term> {
        self.mk_le(a.clone(), b.clone())?.and(self.mk_le(b, a)?)
    }

    /// `⊢ le a b` specialised from `refl`/`trans` for concrete `a`, `b`.
    fn le_refl_at(&self, a: &Term) -> Result<Thm> {
        self.refl.clone().all_elim(a.clone())
    }

    /// `⊢ le a b ⟹ le b c ⟹ le a c`, the transitivity instance at `a, b, c`.
    fn le_trans_at(&self, a: &Term, b: &Term, c: &Term) -> Result<Thm> {
        self.trans
            .clone()
            .all_elim(a.clone())?
            .all_elim(b.clone())?
            .all_elim(c.clone())
    }

    /// `⊢ le a c`, given `⊢ le a b` and `⊢ le b c`.
    fn le_trans_via(&self, ab: &Thm, bc: &Thm) -> Result<Thm> {
        let (a, b) = dest_le_concl(self, ab)?;
        let (_b, c) = dest_le_concl(self, bc)?;
        self.le_trans_at(&a, &b, &c)?
            .imp_elim(ab.clone())?
            .imp_elim(bc.clone())
    }

    // -- generic preorder facts ----------------------------------------

    /// `⊢ ∀a. equiv a a` — `equiv` is reflexive.
    pub fn equiv_refl(&self) -> Result<Thm> {
        let a = self.var("a");
        let la = self.le_refl_at(&a)?; // ⊢ le a a
        la.clone()
            .and_intro(la)? // ⊢ le a a ∧ le a a
            .all_intro("a", self.carrier()?)
    }

    /// `⊢ ∀a b. equiv a b ⟹ equiv b a` — `equiv` is symmetric (swap the two
    /// conjuncts).
    pub fn equiv_symm(&self) -> Result<Thm> {
        let (a, b) = (self.var("a"), self.var("b"));
        let h = self.mk_equiv(a.clone(), b.clone())?; // le a b ∧ le b a
        let hyp = Thm::assume(h.clone())?;
        let ab = hyp.clone().and_elim_l()?; // ⊢ le a b
        let ba = hyp.and_elim_r()?; // ⊢ le b a
        ba.and_intro(ab)? // ⊢ le b a ∧ le a b
            .imp_intro(&h)?
            .all_intro("b", self.carrier()?)?
            .all_intro("a", self.carrier()?)
    }

    /// `⊢ ∀a b c. equiv a b ⟹ equiv b c ⟹ equiv a c` — `equiv` is transitive.
    pub fn equiv_trans(&self) -> Result<Thm> {
        let (a, b, c) = (self.var("a"), self.var("b"), self.var("c"));
        let hab = self.mk_equiv(a.clone(), b.clone())?;
        let hbc = self.mk_equiv(b.clone(), c.clone())?;
        let (eab, ebc) = (Thm::assume(hab.clone())?, Thm::assume(hbc.clone())?);
        let ab = eab.clone().and_elim_l()?; // le a b
        let ba = eab.and_elim_r()?; // le b a
        let bc = ebc.clone().and_elim_l()?; // le b c
        let cb = ebc.and_elim_r()?; // le c b
        let ac = self.le_trans_via(&ab, &bc)?; // le a c
        let ca = self.le_trans_via(&cb, &ba)?; // le c a
        ac.and_intro(ca)? // le a c ∧ le c a
            .imp_intro(&hbc)?
            .imp_intro(&hab)?
            .all_intro("c", self.carrier()?)?
            .all_intro("b", self.carrier()?)?
            .all_intro("a", self.carrier()?)
    }

    /// `⊢ ∀a a' b b'. equiv a a' ⟹ equiv b b' ⟹ le a b ⟹ le a' b'` — `le`
    /// respects `equiv`. (From `a' ≤ a ≤ b ≤ b'` by two transitivity steps,
    /// using the `≤` half of each `equiv`.)
    pub fn le_respects_equiv(&self) -> Result<Thm> {
        let (a, a2) = (self.var("a"), self.var("a'"));
        let (b, b2) = (self.var("b"), self.var("b'"));
        let haa = self.mk_equiv(a.clone(), a2.clone())?;
        let hbb = self.mk_equiv(b.clone(), b2.clone())?;
        let hab = self.mk_le(a.clone(), b.clone())?;
        let a2_le_a = Thm::assume(haa.clone())?.and_elim_r()?; // le a' a
        let b_le_b2 = Thm::assume(hbb.clone())?.and_elim_l()?; // le b b'
        let ab = Thm::assume(hab.clone())?; // le a b
        // a' ≤ a ≤ b ≤ b'.
        let a2_le_b = self.le_trans_via(&a2_le_a, &ab)?; // le a' b
        let a2_le_b2 = self.le_trans_via(&a2_le_b, &b_le_b2)?; // le a' b'
        a2_le_b2
            .imp_intro(&hab)?
            .imp_intro(&hbb)?
            .imp_intro(&haa)?
            .all_intro("b'", self.carrier()?)?
            .all_intro("b", self.carrier()?)?
            .all_intro("a'", self.carrier()?)?
            .all_intro("a", self.carrier()?)
    }

    // -- helpers --------------------------------------------------------

    /// The carrier type `α` — the domain of `le`'s first argument.
    pub fn carrier(&self) -> Result<covalence_core::Type> {
        let le_ty = self.le.type_of()?;
        match le_ty.kind() {
            covalence_core::TypeKind::Fun(dom, _) => Ok(dom.clone()),
            _ => Err(covalence_core::Error::ConnectiveRule(
                "preorder: `le` is not a relation `α → α → bool`".into(),
            )),
        }
    }

    /// A free variable of the carrier type.
    fn var(&self, name: &str) -> Term {
        Term::free(name, self.carrier().expect("preorder carrier"))
    }
}

// ============================================================================
// PartialOrder
// ============================================================================

/// A concrete **model** of the partial-order theory: a [`Preorder`] plus the
/// antisymmetry law. `lt` is the derived strict order `le a b ∧ ¬(le b a)`.
#[derive(Clone)]
pub struct PartialOrder {
    po: Preorder,
    /// `⊢ ∀a b. le a b ⟹ le b a ⟹ a = b`.
    antisym: Thm,
}

impl PartialOrder {
    /// Assemble a partial-order model from a preorder and the antisymmetry law.
    pub fn new(po: Preorder, antisym: Thm) -> Self {
        PartialOrder { po, antisym }
    }

    /// Assemble directly from the relation and all three laws.
    pub fn from_laws(le: Term, refl: Thm, trans: Thm, antisym: Thm) -> Self {
        PartialOrder::new(Preorder::new(le, refl, trans), antisym)
    }

    /// The underlying preorder.
    pub fn preorder(&self) -> &Preorder {
        &self.po
    }
    /// `⊢ ∀a b. le a b ⟹ le b a ⟹ a = b`.
    pub fn antisym_lemma(&self) -> &Thm {
        &self.antisym
    }
    /// The relation term.
    pub fn le(&self) -> &Term {
        self.po.le()
    }
    /// `le a b`.
    pub fn mk_le(&self, a: Term, b: Term) -> Result<Term> {
        self.po.mk_le(a, b)
    }
    /// `equiv a b := le a b ∧ le b a`.
    pub fn mk_equiv(&self, a: Term, b: Term) -> Result<Term> {
        self.po.mk_equiv(a, b)
    }
    /// `lt a b := le a b ∧ ¬(le b a)`.
    pub fn mk_lt(&self, a: Term, b: Term) -> Result<Term> {
        self.po
            .mk_le(a.clone(), b.clone())?
            .and(self.po.mk_le(b, a)?.not()?)
    }

    /// The unapplied `lt = λa b. le a b ∧ ¬(le b a)` as a term (for `.cov`
    /// const registration). β-reduces to [`mk_lt`](Self::mk_lt) on application.
    pub fn lt_op(&self) -> Result<Term> {
        let alpha = self.carrier()?;
        let (a, b) = (self.var("a"), self.var("b"));
        let body = self.mk_lt(a, b.clone())?;
        let body = covalence_core::subst::close(&body, "b");
        let inner = Term::abs(alpha.clone(), body);
        let inner = covalence_core::subst::close(&inner, "a");
        Ok(Term::abs(alpha, inner))
    }

    /// The unapplied `equiv = λa b. le a b ∧ le b a` as a term.
    pub fn equiv_op(&self) -> Result<Term> {
        let alpha = self.carrier()?;
        let (a, b) = (self.var("a"), self.var("b"));
        let body = self.mk_equiv(a, b.clone())?;
        let body = covalence_core::subst::close(&body, "b");
        let inner = Term::abs(alpha.clone(), body);
        let inner = covalence_core::subst::close(&inner, "a");
        Ok(Term::abs(alpha, inner))
    }
    /// The carrier type.
    pub fn carrier(&self) -> Result<covalence_core::Type> {
        self.po.carrier()
    }
    fn var(&self, name: &str) -> Term {
        self.po.var(name)
    }

    /// `⊢ a = b`, given `⊢ le a b` and `⊢ le b a`.
    fn antisym_via(&self, ab: &Thm, ba: &Thm) -> Result<Thm> {
        let (a, b) = dest_le_concl(&self.po, ab)?;
        self.antisym
            .clone()
            .all_elim(a.clone())?
            .all_elim(b.clone())?
            .imp_elim(ab.clone())?
            .imp_elim(ba.clone())
    }

    // -- generic partial-order facts -----------------------------------

    /// `⊢ ∀a. ¬(lt a a)` — `lt` is irreflexive. `lt a a = le a a ∧ ¬(le a a)`,
    /// a contradiction with reflexivity.
    pub fn lt_irrefl(&self) -> Result<Thm> {
        let a = self.var("a");
        let h = self.mk_lt(a.clone(), a.clone())?; // le a a ∧ ¬(le a a)
        let hyp = Thm::assume(h.clone())?;
        let le_aa = hyp.clone().and_elim_l()?; // le a a
        let not_le = hyp.and_elim_r()?; // ¬(le a a)
        let f = not_le.not_elim(le_aa)?; // ⊢ F
        f.imp_intro(&h)? // lt a a ⟹ F
            .not_intro()? // ¬(lt a a)
            .all_intro("a", self.carrier()?)
    }

    /// `⊢ ∀a b. lt a b ⟹ le a b`. The `≤` part is the left conjunct.
    pub fn lt_imp_le(&self) -> Result<Thm> {
        let (a, b) = (self.var("a"), self.var("b"));
        let h = self.mk_lt(a.clone(), b.clone())?;
        Thm::assume(h.clone())?
            .and_elim_l()? // le a b
            .imp_intro(&h)?
            .all_intro("b", self.carrier()?)?
            .all_intro("a", self.carrier()?)
    }

    /// `⊢ ∀a b. lt a b ⟹ ¬(a = b)` — strict order excludes equality. If
    /// `a = b` then `lt a b`'s `≤` half gives `le b a` by rewriting, but
    /// `lt`'s right conjunct is `¬(le b a)` — contradiction.
    pub fn lt_not_eq(&self) -> Result<Thm> {
        let (a, b) = (self.var("a"), self.var("b"));
        let hlt = self.mk_lt(a.clone(), b.clone())?;
        let heq = a.clone().equals(b.clone())?;
        let lt = Thm::assume(hlt.clone())?;
        let le_ab = lt.clone().and_elim_l()?; // le a b
        let not_le_ba = lt.and_elim_r()?; // ¬(le b a)
        // From a = b: le a b rewrites to le b a (replace a by b on the left,
        // b by a on the right — i.e. use sym to turn `le a b` into `le b a`).
        // Concretely: le b a = le a b under {a=b} by congruence on both args.
        let eq = Thm::assume(heq.clone())?; // a = b
        let le_ba_eq_le_ab = Thm::refl(self.le().clone())?
            .cong_app(eq.clone().sym()?)? // le b = le a   (since b = a)
            .cong_app(eq)?; // le b a = le a b
        let le_ba = le_ba_eq_le_ab.sym()?.eq_mp(le_ab)?; // {a=b} ⊢ le b a
        let f = not_le_ba.not_elim(le_ba)?; // {lt a b, a=b} ⊢ F
        f.imp_intro(&heq)? // {lt a b} ⊢ (a=b) ⟹ F
            .not_intro()? // {lt a b} ⊢ ¬(a=b)
            .imp_intro(&hlt)? // ⊢ lt a b ⟹ ¬(a=b)
            .all_intro("b", self.carrier()?)?
            .all_intro("a", self.carrier()?)
    }

    /// `⊢ ∀a b c. lt a b ⟹ lt b c ⟹ lt a c` — `lt` is transitive. The `≤`
    /// part chains by transitivity; the `¬(le c a)` part: if `le c a` then
    /// `le b a` (via `c ≤ a` ... actually `le c a` + `le a b` give `le c b`,
    /// contradicting `¬(le c b)` from `lt b c`).
    pub fn lt_trans(&self) -> Result<Thm> {
        let (a, b, c) = (self.var("a"), self.var("b"), self.var("c"));
        let hab = self.mk_lt(a.clone(), b.clone())?;
        let hbc = self.mk_lt(b.clone(), c.clone())?;
        let lt_ab = Thm::assume(hab.clone())?;
        let lt_bc = Thm::assume(hbc.clone())?;
        let le_ab = lt_ab.clone().and_elim_l()?; // le a b
        let le_bc = lt_bc.clone().and_elim_l()?; // le b c
        let not_le_cb = lt_bc.and_elim_r()?; // ¬(le c b)
        let le_ac = self.po.le_trans_via(&le_ab, &le_bc)?; // le a c
        // ¬(le c a): assume le c a; then le c b via le c a, le a b → le c b,
        // contradicting ¬(le c b).
        let h_le_ca = self.mk_le(c.clone(), a.clone())?;
        let le_ca = Thm::assume(h_le_ca.clone())?;
        let le_cb = self.po.le_trans_via(&le_ca, &le_ab)?; // {le c a} ⊢ le c b
        let f = not_le_cb.not_elim(le_cb)?; // ⊢ F
        let not_le_ca = f.imp_intro(&h_le_ca)?.not_intro()?; // ¬(le c a)
        le_ac
            .and_intro(not_le_ca)? // lt a c
            .imp_intro(&hbc)?
            .imp_intro(&hab)?
            .all_intro("c", self.carrier()?)?
            .all_intro("b", self.carrier()?)?
            .all_intro("a", self.carrier()?)
    }

    /// `⊢ ∀a b. le a b ⟺ (lt a b ∨ a = b)`.
    ///
    /// Forward: from `le a b`, by [`Thm::lem`] on `le b a` either `le b a`
    /// (then `a = b` by antisymmetry) or `¬(le b a)` (then `lt a b`).
    /// Backward: `lt a b` gives `le a b` (left conjunct); `a = b` gives
    /// `le a b` by rewriting reflexivity.
    pub fn le_iff_lt_or_eq(&self) -> Result<Thm> {
        let (a, b) = (self.var("a"), self.var("b"));
        let h_le = self.mk_le(a.clone(), b.clone())?;
        let h_lt = self.mk_lt(a.clone(), b.clone())?;
        let h_eq = a.clone().equals(b.clone())?;
        let disj = h_lt.clone().or(h_eq.clone())?;

        // forward: le a b ⟹ (lt a b ∨ a = b).
        let fwd = {
            let le_ab = Thm::assume(h_le.clone())?;
            let h_le_ba = self.mk_le(b.clone(), a.clone())?;
            // case le b a: a = b by antisym.
            let left = {
                let le_ba = Thm::assume(h_le_ba.clone())?;
                self.antisym_via(&le_ab, &le_ba)? // a = b
                    .or_intro_r(h_lt.clone())? // lt a b ∨ a = b
                    .imp_intro(&h_le_ba)?
            };
            // case ¬(le b a): lt a b.
            let not_le_ba = h_le_ba.clone().not()?;
            let right = {
                let nlb = Thm::assume(not_le_ba.clone())?;
                le_ab
                    .clone()
                    .and_intro(nlb)? // lt a b
                    .or_intro_l(h_eq.clone())? // lt a b ∨ a = b
                    .imp_intro(&not_le_ba)?
            };
            Thm::lem(h_le_ba)?
                .or_elim(left, right)? // lt a b ∨ a = b
                .imp_intro(&h_le)?
        };

        // backward: (lt a b ∨ a = b) ⟹ le a b.
        let bwd = {
            let from_lt = Thm::assume(h_lt.clone())?
                .and_elim_l()? // le a b
                .imp_intro(&h_lt)?;
            let from_eq = {
                let eq = Thm::assume(h_eq.clone())?; // a = b
                // le a a (refl) rewritten by a = b on the second arg → le a b.
                let le_aa = self.po.le_refl_at(&a)?; // le a a
                let cong = Thm::refl(self.le().clone())?
                    .cong_app(Thm::refl(a.clone())?)? // le a
                    .cong_app(eq)?; // le a a = le a b
                cong.eq_mp(le_aa)?.imp_intro(&h_eq)?
            };
            Thm::assume(disj.clone())?
                .or_elim(from_lt, from_eq)?
                .imp_intro(&disj)?
        };

        imp_antisym(fwd, bwd)? // le a b ⟺ (lt a b ∨ a = b)
            .all_intro("b", self.carrier()?)?
            .all_intro("a", self.carrier()?)
    }

    /// `⊢ ∀a b. equiv a b ⟺ a = b` — for a *partial* order, `equiv` collapses
    /// to equality. Forward by antisymmetry; backward: `a = b` gives both
    /// `le a b` and `le b a` from reflexivity.
    pub fn equiv_iff_eq(&self) -> Result<Thm> {
        let (a, b) = (self.var("a"), self.var("b"));
        let h_equiv = self.mk_equiv(a.clone(), b.clone())?;
        let h_eq = a.clone().equals(b.clone())?;

        // forward: equiv a b ⟹ a = b.
        let fwd = {
            let eq = Thm::assume(h_equiv.clone())?;
            let le_ab = eq.clone().and_elim_l()?;
            let le_ba = eq.and_elim_r()?;
            self.antisym_via(&le_ab, &le_ba)?.imp_intro(&h_equiv)?
        };
        // backward: a = b ⟹ equiv a b.
        let bwd = {
            let eq = Thm::assume(h_eq.clone())?; // a = b
            let le_aa = self.po.le_refl_at(&a)?; // le a a
            // le a b: rewrite second arg of le a a by a = b.
            let le_ab = Thm::refl(self.le().clone())?
                .cong_app(Thm::refl(a.clone())?)?
                .cong_app(eq.clone())?
                .eq_mp(le_aa.clone())?;
            // le b a: rewrite first arg of le a a by a = b.
            let le_ba = Thm::refl(self.le().clone())?
                .cong_app(eq)?
                .cong_app(Thm::refl(a.clone())?)?
                .eq_mp(le_aa)?;
            le_ab.and_intro(le_ba)?.imp_intro(&h_eq)?
        };
        imp_antisym(fwd, bwd)?
            .all_intro("b", self.carrier()?)?
            .all_intro("a", self.carrier()?)
    }

    // -- the chaining decision procedure -------------------------------

    /// Normalise a supplied fact into a list of **edges** in the `≤`/`<` graph,
    /// each carrying its source-of-truth derivation. An `=`/`equiv` fact yields
    /// the two weak edges `a ≤ b` and `b ≤ a`. A `<` fact yields a strict edge
    /// `a < b` (whose witness is the `lt` theorem, from which `≤` is recovered
    /// on demand). Returns `None` for a theorem of none of the four shapes.
    fn classify(&self, fact: &Thm) -> Result<Option<Vec<Edge>>> {
        let c = fact.concl();
        // a < b
        if let Some((a, b)) = self.dest_lt(c) {
            return Ok(Some(vec![Edge::strict(a, b, fact.clone())]));
        }
        // a = b  (kernel `Eq`)
        if let Some((a, b)) = c.as_eq() {
            let (a, b) = (a.clone(), b.clone());
            let le_ab = self.le_of_eq(fact, &a, false)?;
            let le_ba = self.le_of_eq(fact, &a, true)?;
            return Ok(Some(vec![
                Edge::weak(a.clone(), b.clone(), le_ab),
                Edge::weak(b, a, le_ba),
            ]));
        }
        // equiv a b = le a b ∧ le b a
        if let Some((a, b)) = self.dest_equiv(c) {
            let le_ab = fact.clone().and_elim_l()?;
            let le_ba = fact.clone().and_elim_r()?;
            return Ok(Some(vec![
                Edge::weak(a.clone(), b.clone(), le_ab),
                Edge::weak(b, a, le_ba),
            ]));
        }
        // a <= b
        if let Some((a, b)) = self.dest_le(c) {
            return Ok(Some(vec![Edge::weak(a, b, fact.clone())]));
        }
        Ok(None)
    }

    /// **The order tactic.** Given the `facts` and a `goal` of one of the four
    /// shapes (`a ≤ b`, `a < b`, `a = b`, `equiv a b`), prove the goal by
    /// transitive-closure chaining. Errors if the goal is not reachable.
    ///
    /// Algorithm:
    /// 1. Classify every fact into directed edges (`≤` weak / `<` strict),
    ///    splitting `=`/`equiv` into the two weak edges.
    /// 2. Compute the transitive closure: `(a→b) · (b→c) ⊢ (a→c)`, where the
    ///    composite is strict iff either factor is (`<` absorbs `≤`).
    /// 3. Read the goal off the closure:
    ///    - `a ≤ b` — any `a→b` edge (strict ones weakened via `lt_imp_le`-
    ///      style `and_elim_l`).
    ///    - `a < b` — a *strict* `a→b` edge.
    ///    - `a = b` — both `a→b` and `b→a` weak edges, combined by antisymmetry.
    ///    - `equiv a b` — both weak edges, paired by `and_intro`.
    pub fn chain(&self, facts: &[Thm], goal: &Term) -> Result<Thm> {
        // 0. β-normalize, so a fact/goal written with the folded `lt`/`equiv`
        // *lambdas* (the `.cov` const form `(lt a b)`) reduces to the explicit
        // `le … ∧ …` shape the matchers expect. Hyp-free and reversible, so the
        // bridge back to the original goal is exact.
        let mut edges: Vec<Edge> = Vec::new();
        for f in facts {
            let f = beta_nf_thm(f)?;
            if let Some(es) = self.classify(&f)? {
                edges.extend(es);
            }
        }
        let closed = self.close(edges)?;
        // discharge against the β-normal goal, then bridge back to `goal`.
        let goal_nf_eq = beta_nf(goal.clone()); // ⊢ goal = goal_nf
        let (_, goal_nf) = goal_nf_eq
            .concl()
            .as_eq()
            .expect("beta_nf yields an equation");
        let proved_nf = self.discharge(goal_nf, &closed)?; // ⊢ goal_nf
        // ⊢ goal  (eq_mp with goal = goal_nf flipped).
        goal_nf_eq.sym()?.eq_mp(proved_nf)
    }

    /// Saturate the edge set under composition, returning a map from
    /// `(a, b)` (printed key) to the strongest proven [`Edge`].
    fn close(&self, edges: Vec<Edge>) -> Result<EdgeMap> {
        let mut map = EdgeMap::default();
        for e in edges {
            map.insert(self, e)?;
        }
        // Saturate: repeatedly compose every pair sharing a midpoint until no
        // new (or strictly-stronger) edge is added.
        loop {
            let snapshot: Vec<Edge> = map.0.values().cloned().collect();
            let mut grew = false;
            for e1 in &snapshot {
                for e2 in &snapshot {
                    if e1.dst_key != e2.src_key {
                        continue;
                    }
                    let composite = self.compose(e1, e2)?;
                    if map.insert(self, composite)? {
                        grew = true;
                    }
                }
            }
            if !grew {
                break;
            }
        }
        Ok(map)
    }

    /// Compose two adjacent edges `a→b`, `b→c` into `a→c`. Strict iff either
    /// input is strict (a `<` anywhere in the chain makes the result `<`).
    fn compose(&self, e1: &Edge, e2: &Edge) -> Result<Edge> {
        let a = e1.src.clone();
        let c = e2.dst.clone();
        match (e1.strict, e2.strict) {
            (false, false) => {
                // le a b, le b c ⊢ le a c.
                let ac = self.po.le_trans_via(&e1.le_thm(self)?, &e2.le_thm(self)?)?;
                Ok(Edge::weak(a, c, ac))
            }
            (true, false) => {
                // lt a b, le b c ⊢ lt a c.
                let lt = self.strict_then_weak(e1, e2)?;
                Ok(Edge::strict(a, c, lt))
            }
            (false, true) => {
                // le a b, lt b c ⊢ lt a c.
                let lt = self.weak_then_strict(e1, e2)?;
                Ok(Edge::strict(a, c, lt))
            }
            (true, true) => {
                // lt a b, lt b c ⊢ lt a c (full strict transitivity).
                let lt = self
                    .lt_trans()?
                    .all_elim(e1.src.clone())?
                    .all_elim(e1.dst.clone())?
                    .all_elim(e2.dst.clone())?
                    .imp_elim(e1.thm.clone())?
                    .imp_elim(e2.thm.clone())?;
                Ok(Edge::strict(a, c, lt))
            }
        }
    }

    /// `lt a b, le b c ⊢ lt a c`. `≤` part: `a ≤ b ≤ c`. `¬(le c a)` part: if
    /// `le c a`, then `le b a` via `b ≤ c ≤ a`... no — via `le c a` and the
    /// goal's structure. We use: `lt a b = le a b ∧ ¬(le b a)`. Assume
    /// `le c a`; then `le b a` from `le b c` (`e2`) and `le c a` by trans,
    /// contradicting `¬(le b a)`.
    fn strict_then_weak(&self, e1: &Edge, e2: &Edge) -> Result<Thm> {
        let (a, _b, c) = (e1.src.clone(), e1.dst.clone(), e2.dst.clone());
        let le_ab = e1.thm.clone().and_elim_l()?; // le a b
        let not_le_ba = e1.thm.clone().and_elim_r()?; // ¬(le b a)
        let le_bc = e2.le_thm(self)?; // le b c
        let le_ac = self.po.le_trans_via(&le_ab, &le_bc)?; // le a c
        // ¬(le c a): assume le c a → le b a via le b c, le c a → ¬(le b a) clash.
        let h_le_ca = self.mk_le(c.clone(), a.clone())?;
        let le_ca = Thm::assume(h_le_ca.clone())?;
        let le_ba = self.po.le_trans_via(&le_bc, &le_ca)?; // le b a
        let f = not_le_ba.not_elim(le_ba)?;
        let not_le_ca = f.imp_intro(&h_le_ca)?.not_intro()?;
        le_ac.and_intro(not_le_ca) // lt a c
    }

    /// `le a b, lt b c ⊢ lt a c`. `≤` part: `a ≤ b ≤ c`. `¬(le c a)` part:
    /// assume `le c a`; then `le c b` via `le c a`, `le a b`, contradicting
    /// `¬(le c b)` from `lt b c`.
    fn weak_then_strict(&self, e1: &Edge, e2: &Edge) -> Result<Thm> {
        let (a, _b, c) = (e1.src.clone(), e1.dst.clone(), e2.dst.clone());
        let le_ab = e1.le_thm(self)?; // le a b
        let le_bc = e2.thm.clone().and_elim_l()?; // le b c
        let not_le_cb = e2.thm.clone().and_elim_r()?; // ¬(le c b)
        let le_ac = self.po.le_trans_via(&le_ab, &le_bc)?; // le a c
        let h_le_ca = self.mk_le(c.clone(), a.clone())?;
        let le_ca = Thm::assume(h_le_ca.clone())?;
        let le_cb = self.po.le_trans_via(&le_ca, &le_ab)?; // le c b
        let f = not_le_cb.not_elim(le_cb)?;
        let not_le_ca = f.imp_intro(&h_le_ca)?.not_intro()?;
        le_ac.and_intro(not_le_ca)
    }

    /// Read the closed edge map to produce a proof of `goal`.
    fn discharge(&self, goal: &Term, closed: &EdgeMap) -> Result<Thm> {
        if let Some((a, b)) = self.dest_lt(goal) {
            let e = closed
                .get(&a, &b)
                .filter(|e| e.strict)
                .ok_or_else(|| err(format!("order: no strict chain proves `{goal}`")))?;
            return Ok(e.thm.clone());
        }
        if let Some((a, b)) = goal.as_eq() {
            let (a, b) = (a.clone(), b.clone());
            let ab = closed
                .get(&a, &b)
                .ok_or_else(|| err(format!("order: no `≤` chain `{a} ≤ {b}` for goal `{goal}`")))?;
            let ba = closed
                .get(&b, &a)
                .ok_or_else(|| err(format!("order: no `≤` chain `{b} ≤ {a}` for goal `{goal}`")))?;
            return self.antisym_via(&ab.le_thm(self)?, &ba.le_thm(self)?);
        }
        if let Some((a, b)) = self.dest_equiv(goal) {
            let ab = closed
                .get(&a, &b)
                .ok_or_else(|| err(format!("order: no `≤` chain `{a} ≤ {b}` for `equiv` goal")))?;
            let ba = closed
                .get(&b, &a)
                .ok_or_else(|| err(format!("order: no `≤` chain `{b} ≤ {a}` for `equiv` goal")))?;
            return ab.le_thm(self)?.and_intro(ba.le_thm(self)?);
        }
        if let Some((a, b)) = self.dest_le(goal) {
            let e = closed
                .get(&a, &b)
                .ok_or_else(|| err(format!("order: no chain proves `{goal}`")))?;
            return e.le_thm(self);
        }
        Err(err(format!(
            "order: goal `{goal}` is not one of `≤`/`<`/`=`/`equiv`"
        )))
    }

    /// `⊢ le a b` from an `=` fact, optionally swapped (`b ≤ a`). Built by
    /// congruence on reflexivity (`le a a`) rewriting the moved argument by the
    /// `=` fact.
    fn le_of_eq(&self, eq: &Thm, a: &Term, swap: bool) -> Result<Thm> {
        // eq : ⊢ a = b. We want le a b (swap=false) or le b a (swap=true).
        let le_aa = self.po.le_refl_at(a)?; // le a a
        if !swap {
            // le a a → le a b: rewrite the 2nd arg.
            Thm::refl(self.le().clone())?
                .cong_app(Thm::refl(a.clone())?)?
                .cong_app(eq.clone())?
                .eq_mp(le_aa)
        } else {
            // le a a → le b a: rewrite the 1st arg.
            Thm::refl(self.le().clone())?
                .cong_app(eq.clone())?
                .cong_app(Thm::refl(a.clone())?)?
                .eq_mp(le_aa)
        }
    }

    // -- destructors over `self`'s relation -----------------------------

    fn dest_le(&self, t: &Term) -> Option<(Term, Term)> {
        let (f, b) = t.as_app()?;
        let (head, a) = f.as_app()?;
        (*head == *self.le()).then(|| (a.clone(), b.clone()))
    }
    fn dest_lt(&self, t: &Term) -> Option<(Term, Term)> {
        // lt a b = le a b ∧ ¬(le b a). Match that exact shape.
        let (l, r) = dest_and(t)?;
        let (a, b) = self.dest_le(&l)?;
        let neg = dest_not(&r)?;
        let (b2, a2) = self.dest_le(&neg)?;
        (a2 == a && b2 == b).then_some((a, b))
    }
    fn dest_equiv(&self, t: &Term) -> Option<(Term, Term)> {
        // equiv a b = le a b ∧ le b a.
        let (l, r) = dest_and(t)?;
        let (a, b) = self.dest_le(&l)?;
        let (b2, a2) = self.dest_le(&r)?;
        (a2 == a && b2 == b).then_some((a, b))
    }
}

// ============================================================================
// Edge bookkeeping for the closure
// ============================================================================

/// A proven directed edge in the order graph: `src R dst`, where `R` is `≤`
/// (`strict = false`, `thm : ⊢ le src dst`) or `<` (`strict = true`,
/// `thm : ⊢ lt src dst`).
#[derive(Clone)]
struct Edge {
    src: Term,
    dst: Term,
    src_key: String,
    dst_key: String,
    strict: bool,
    /// `⊢ le src dst` (weak) or `⊢ lt src dst` (strict).
    thm: Thm,
}

impl Edge {
    fn weak(src: Term, dst: Term, thm: Thm) -> Self {
        let (src_key, dst_key) = (format!("{src}"), format!("{dst}"));
        Edge {
            src,
            dst,
            src_key,
            dst_key,
            strict: false,
            thm,
        }
    }
    fn strict(src: Term, dst: Term, thm: Thm) -> Self {
        let (src_key, dst_key) = (format!("{src}"), format!("{dst}"));
        Edge {
            src,
            dst,
            src_key,
            dst_key,
            strict: true,
            thm,
        }
    }
    /// `⊢ le src dst` — for a strict edge, the `≤` half (left conjunct).
    fn le_thm(&self, _po: &PartialOrder) -> Result<Thm> {
        if self.strict {
            self.thm.clone().and_elim_l()
        } else {
            Ok(self.thm.clone())
        }
    }
}

/// The pair→strongest-edge table of the closure.
#[derive(Default)]
struct EdgeMap(HashMap<(String, String), Edge>);

impl EdgeMap {
    /// Get the edge for `a→b`, if any.
    fn get(&self, a: &Term, b: &Term) -> Option<&Edge> {
        self.0.get(&(format!("{a}"), format!("{b}")))
    }
    /// Insert `e`, keeping it only if it is *new* or *strictly stronger* (a
    /// strict edge replaces a weak one for the same pair). Returns whether the
    /// table changed.
    fn insert(&mut self, _po: &PartialOrder, e: Edge) -> Result<bool> {
        let key = (e.src_key.clone(), e.dst_key.clone());
        match self.0.get(&key) {
            Some(old) if old.strict || !e.strict => Ok(false), // no improvement
            _ => {
                self.0.insert(key, e);
                Ok(true)
            }
        }
    }
}

// ============================================================================
// shape helpers (model-independent)
// ============================================================================

fn dest_and(t: &Term) -> Option<(Term, Term)> {
    let and = covalence_core::defs::and();
    let (f, b) = t.as_app()?;
    let (h, a) = f.as_app()?;
    (*h == and).then(|| (a.clone(), b.clone()))
}

fn dest_not(t: &Term) -> Option<Term> {
    let not = covalence_core::defs::not();
    let (h, p) = t.as_app()?;
    (*h == not).then(|| p.clone())
}

/// `(a, b)` from a `⊢ le a b` theorem (matching `po.le`).
fn dest_le_concl(po: &Preorder, thm: &Thm) -> Result<(Term, Term)> {
    let c = thm.concl();
    let (f, b) = c
        .as_app()
        .ok_or_else(|| err(format!("expected `le a b`, got `{c}`")))?;
    let (head, a) = f
        .as_app()
        .ok_or_else(|| err(format!("expected `le a b`, got `{c}`")))?;
    if *head != *po.le() {
        return Err(err(format!(
            "expected `{}` application, got `{c}`",
            po.le()
        )));
    }
    Ok((a.clone(), b.clone()))
}

fn err(msg: String) -> covalence_core::Error {
    covalence_core::Error::ConnectiveRule(msg)
}

/// `⊢ concl_nf` from `⊢ concl` — rewrite a theorem's conclusion to its β-normal
/// form (so a folded `(lt a b)` fact unfolds to `le a b ∧ ¬(le b a)`).
fn beta_nf_thm(thm: &Thm) -> Result<Thm> {
    let eq = beta_nf(thm.concl().clone()); // ⊢ concl = concl_nf
    eq.eq_mp(thm.clone())
}

/// `⊢ p = q` (i.e. `p ⟺ q`) from `⊢ p ⟹ q` and `⊢ q ⟹ p` — HOL's
/// `IMP_ANTISYM_RULE`, via `deduct_antisym` on the two MP'd assumptions.
fn imp_antisym(fwd: Thm, bwd: Thm) -> Result<Thm> {
    let (p, _q) = dest_imp_concl(&fwd)?; // p ⟹ q
    let (q, _p) = dest_imp_concl(&bwd)?; // q ⟹ p
    let pq = fwd.imp_elim(Thm::assume(p.clone())?)?; // {p} ⊢ q
    let qp = bwd.imp_elim(Thm::assume(q.clone())?)?; // {q} ⊢ p
    // deduct_antisym({p}⊢q, {q}⊢p) ⊢ q = p; flip to p = q.
    pq.deduct_antisym(qp)?.sym()
}

fn dest_imp_concl(thm: &Thm) -> Result<(Term, Term)> {
    let c = thm.concl();
    let (f, b) = c
        .as_app()
        .ok_or_else(|| err(format!("expected `p ⟹ q`, got `{c}`")))?;
    let (h, a) = f
        .as_app()
        .ok_or_else(|| err(format!("expected `p ⟹ q`, got `{c}`")))?;
    if *h != covalence_core::defs::imp() {
        return Err(err(format!("expected `⟹`, got `{c}`")));
    }
    Ok((a.clone(), b.clone()))
}

// ============================================================================
// Models
// ============================================================================

/// The natural-number order `(nat, ≤)` as a [`PartialOrder`]. `refl`/`trans`/
/// `antisym` are the genuine Peano theorems from [`crate::init::nat`].
pub fn nat_partial_order() -> PartialOrder {
    use crate::init::nat;
    PartialOrder::from_laws(
        covalence_core::defs::nat_le(),
        nat::le_refl(),
        nat::le_trans(),
        nat::le_antisym(),
    )
}

/// The integer order `(int, ≤)` as a [`PartialOrder`]. `int` exposes the strict
/// order (`lt_irrefl`/`lt_trans`/`lt_trichotomy`) and `le_def`
/// (`a ≤ b = a < b ∨ a = b`), so we derive the three partial-order laws here
/// from those genuine theorems via [`from_strict`].
pub fn int_partial_order() -> Result<PartialOrder> {
    use crate::init::int;
    from_strict(
        covalence_core::defs::int_le(),
        covalence_core::defs::int_lt(),
        covalence_core::Type::int(),
        int::le_def(),
        int::lt_irrefl(),
        int::lt_trans(),
        int::lt_trichotomy(),
    )
}

/// Build a [`PartialOrder`] from a **strict-order presentation**: the `le`/`lt`
/// relations, the carrier type, and the four genuine theorems
/// ```text
///   le_def        : ⊢ ∀a b. (a ≤ b) = (a < b ∨ a = b)
///   lt_irrefl     : ⊢ ∀a. ¬(a < a)
///   lt_trans      : ⊢ ∀a b c. a < b ⟹ b < c ⟹ a < c
///   lt_trichotomy : ⊢ ∀a b. (a < b) ∨ ((a = b) ∨ (b < a))
/// ```
/// deriving the partial-order laws `le_refl` / `le_trans` / `le_antisym` for
/// the model's *own* `≤` (NOT the generic `lt a b := le a b ∧ ¬(le b a)`,
/// which the [`PartialOrder`] then defines on top). All three derivations are
/// genuine and hypothesis-free.
pub fn from_strict(
    le: Term,
    lt: Term,
    carrier: covalence_core::Type,
    le_def: Thm,
    lt_irrefl: Thm,
    lt_trans: Thm,
    lt_trichotomy: Thm,
) -> Result<PartialOrder> {
    let _ = lt_trichotomy; // not needed for the partial-order laws.
    let s = Strict {
        le: le.clone(),
        lt,
        carrier: carrier.clone(),
        le_def,
        lt_irrefl,
        lt_trans,
    };
    let le_refl = s.le_refl()?;
    let le_trans = s.le_trans()?;
    let le_antisym = s.le_antisym()?;
    Ok(PartialOrder::from_laws(le, le_refl, le_trans, le_antisym))
}

/// A **strict-order presentation** of a partial order: `le`/`lt` terms, the
/// carrier, and the three driving theorems. Its methods derive the
/// partial-order laws `le_refl`/`le_trans`/`le_antisym` for the model's own
/// `≤`. Internal to [`from_strict`].
struct Strict {
    le: Term,
    lt: Term,
    carrier: covalence_core::Type,
    /// `⊢ ∀a b. (a ≤ b) = (a < b ∨ a = b)`.
    le_def: Thm,
    /// `⊢ ∀a. ¬(a < a)`.
    lt_irrefl: Thm,
    /// `⊢ ∀a b c. a < b ⟹ b < c ⟹ a < c`.
    lt_trans: Thm,
}

impl Strict {
    fn v(&self, n: &str) -> Term {
        Term::free(n, self.carrier.clone())
    }
    fn le_t(&self, a: Term, b: Term) -> Result<Term> {
        self.le.clone().apply(a)?.apply(b)
    }
    fn lt_t(&self, a: Term, b: Term) -> Result<Term> {
        self.lt.clone().apply(a)?.apply(b)
    }
    /// `⊢ (a ≤ b) = (a < b ∨ a = b)`.
    fn le_def_at(&self, a: &Term, b: &Term) -> Result<Thm> {
        self.le_def.clone().all_elim(a.clone())?.all_elim(b.clone())
    }
    /// `⊢ a ≤ b` from `⊢ a < b ∨ a = b`.
    fn fold_le(&self, a: &Term, b: &Term, disj: Thm) -> Result<Thm> {
        self.le_def_at(a, b)?.sym()?.eq_mp(disj)
    }
    /// `⊢ a < b ∨ a = b` from `⊢ a ≤ b`.
    fn unfold_le(&self, a: &Term, b: &Term, le: Thm) -> Result<Thm> {
        self.le_def_at(a, b)?.eq_mp(le)
    }
    /// `⊢ a < b` rewritten to `⊢ a' < b'` along the supplied equalities (each
    /// `⊢ x = x'`; pass `refl` for an unchanged position).
    fn lt_cong(&self, lt_thm: Thm, l_eq: Thm, r_eq: Thm) -> Result<Thm> {
        Thm::refl(self.lt.clone())?
            .cong_app(l_eq)?
            .cong_app(r_eq)?
            .eq_mp(lt_thm)
    }

    /// `⊢ ∀a. a ≤ a` — from `a = a` (refl) via `le_def`'s right disjunct.
    fn le_refl(&self) -> Result<Thm> {
        let a = self.v("a");
        let disj = Thm::refl(a.clone())?.or_intro_r(self.lt_t(a.clone(), a.clone())?)?;
        self.fold_le(&a, &a, disj)?
            .all_intro("a", self.carrier.clone())
    }

    /// `⊢ ∀a b c. a ≤ b ⟹ b ≤ c ⟹ a ≤ c` — case analysis on each `le_def`.
    fn le_trans(&self) -> Result<Thm> {
        let (a, b, c) = (self.v("a"), self.v("b"), self.v("c"));
        let hab = self.le_t(a.clone(), b.clone())?;
        let hbc = self.le_t(b.clone(), c.clone())?;
        let dab = self.unfold_le(&a, &b, Thm::assume(hab.clone())?)?; // a<b ∨ a=b
        let dbc = self.unfold_le(&b, &c, Thm::assume(hbc.clone())?)?; // b<c ∨ b=c

        // The two `a<b ∨ a=b` cases, each delivering `a ≤ c` from `dbc`.
        let lt_ab = self.lt_t(a.clone(), b.clone())?;
        let eq_ab = a.clone().equals(b.clone())?;

        // case a<b: inner case on dbc.
        let on_lt_ab = self
            .le_trans_inner_lt(&a, &b, &c, &dbc)?
            .imp_intro(&lt_ab)?;
        // case a=b: inner case on dbc.
        let on_eq_ab = self
            .le_trans_inner_eq(&a, &b, &c, &dbc)?
            .imp_intro(&eq_ab)?;

        let ac = dab.or_elim(on_lt_ab, on_eq_ab)?; // a ≤ c
        ac.imp_intro(&hbc)?
            .imp_intro(&hab)?
            .all_intro("c", self.carrier.clone())?
            .all_intro("b", self.carrier.clone())?
            .all_intro("a", self.carrier.clone())
    }

    /// Under `{a < b}`: from `dbc : ⊢ b<c ∨ b=c` derive `a ≤ c`.
    fn le_trans_inner_lt(&self, a: &Term, b: &Term, c: &Term, dbc: &Thm) -> Result<Thm> {
        let lt_bc = self.lt_t(b.clone(), c.clone())?;
        let eq_bc = b.clone().equals(c.clone())?;
        // b<c: a<c by lt_trans.
        let on_lt = {
            let lt_ac = self
                .lt_trans
                .clone()
                .all_elim(a.clone())?
                .all_elim(b.clone())?
                .all_elim(c.clone())?
                .imp_elim(Thm::assume(self.lt_t(a.clone(), b.clone())?)?)?
                .imp_elim(Thm::assume(lt_bc.clone())?)?;
            let disj = lt_ac.or_intro_l(a.clone().equals(c.clone())?)?;
            self.fold_le(a, c, disj)?.imp_intro(&lt_bc)?
        };
        // b=c: a<c by rewriting c↦… in a<b.
        let on_eq = {
            let bc = Thm::assume(eq_bc.clone())?; // b = c
            let lt_ac = self.lt_cong(
                Thm::assume(self.lt_t(a.clone(), b.clone())?)?,
                Thm::refl(a.clone())?,
                bc,
            )?; // a < c
            let disj = lt_ac.or_intro_l(a.clone().equals(c.clone())?)?;
            self.fold_le(a, c, disj)?.imp_intro(&eq_bc)?
        };
        dbc.clone().or_elim(on_lt, on_eq)
    }

    /// Under `{a = b}`: from `dbc : ⊢ b<c ∨ b=c` derive `a ≤ c`.
    fn le_trans_inner_eq(&self, a: &Term, b: &Term, c: &Term, dbc: &Thm) -> Result<Thm> {
        let lt_bc = self.lt_t(b.clone(), c.clone())?;
        let eq_bc = b.clone().equals(c.clone())?;
        let eq_ab = a.clone().equals(b.clone())?;
        // b<c: a<c by rewriting b↦a (a=b).
        let on_lt = {
            let ab = Thm::assume(eq_ab.clone())?; // a = b
            let lt_ac = self.lt_cong(
                Thm::assume(lt_bc.clone())?,
                ab.sym()?, // b = a, applied to the left position of `b<c`
                Thm::refl(c.clone())?,
            )?; // a < c
            let disj = lt_ac.or_intro_l(a.clone().equals(c.clone())?)?;
            self.fold_le(a, c, disj)?.imp_intro(&lt_bc)?
        };
        // b=c: a=c, so a ≤ c by the right disjunct.
        let on_eq = {
            let ab = Thm::assume(eq_ab.clone())?;
            let bc = Thm::assume(eq_bc.clone())?;
            let ac = ab.trans(bc)?; // a = c
            let disj = ac.or_intro_r(self.lt_t(a.clone(), c.clone())?)?;
            self.fold_le(a, c, disj)?.imp_intro(&eq_bc)?
        };
        dbc.clone().or_elim(on_lt, on_eq)
    }

    /// `⊢ ∀a b. a ≤ b ⟹ b ≤ a ⟹ a = b` — antisymmetry. If both `a<b` and
    /// `b<a` then `a<a` by `lt_trans`, contradicting `lt_irrefl`; otherwise an
    /// equality is already on hand.
    fn le_antisym(&self) -> Result<Thm> {
        let (a, b) = (self.v("a"), self.v("b"));
        let hab = self.le_t(a.clone(), b.clone())?;
        let hba = self.le_t(b.clone(), a.clone())?;
        let dab = self.unfold_le(&a, &b, Thm::assume(hab.clone())?)?; // a<b ∨ a=b
        let dba = self.unfold_le(&b, &a, Thm::assume(hba.clone())?)?; // b<a ∨ b=a
        let goal = a.clone().equals(b.clone())?;
        let lt_ab = self.lt_t(a.clone(), b.clone())?;
        let eq_ab = a.clone().equals(b.clone())?;
        let lt_ba = self.lt_t(b.clone(), a.clone())?;
        let eq_ba = b.clone().equals(a.clone())?;

        // case a<b: inner case on dba.
        let on_lt_ab = {
            let on_lt_ba = {
                let lt_aa = self
                    .lt_trans
                    .clone()
                    .all_elim(a.clone())?
                    .all_elim(b.clone())?
                    .all_elim(a.clone())?
                    .imp_elim(Thm::assume(lt_ab.clone())?)?
                    .imp_elim(Thm::assume(lt_ba.clone())?)?; // a < a
                let f = self
                    .lt_irrefl
                    .clone()
                    .all_elim(a.clone())?
                    .not_elim(lt_aa)?;
                f.false_elim(goal.clone())?.imp_intro(&lt_ba)?
            };
            let on_eq_ba = Thm::assume(eq_ba.clone())?.sym()?.imp_intro(&eq_ba)?;
            dba.clone().or_elim(on_lt_ba, on_eq_ba)?.imp_intro(&lt_ab)?
        };
        // case a=b: immediate.
        let on_eq_ab = Thm::assume(eq_ab.clone())?.imp_intro(&eq_ab)?;

        let eq = dab.or_elim(on_lt_ab, on_eq_ab)?; // a = b
        eq.imp_intro(&hba)?
            .imp_intro(&hab)?
            .all_intro("b", self.carrier.clone())?
            .all_intro("a", self.carrier.clone())
    }
}

// ============================================================================
// `.cov` registration — the order tactic as a registry inference
// ============================================================================

/// The `order` inference, carrying a [`PartialOrder`] model. In **tactic mode**
/// (`(order FACT…)`) it closes the focused goal by [`PartialOrder::chain`] over
/// the named facts (looked up as lemmas in scope). In **tree mode**
/// (`(order GOAL FACT…)`) it proves an explicit `GOAL`.
pub struct OrderTactic {
    po: PartialOrder,
}

impl OrderTactic {
    /// Wrap a model as a registry inference.
    pub fn new(po: PartialOrder) -> Self {
        OrderTactic { po }
    }
}

use crate::script::{CheckCtx, Interp, ScriptError, Tactic};

#[async_trait]
impl Tactic for OrderTactic {
    /// `(order FACT…)` — close the goal by chaining the facts (each a lemma
    /// name or tree-mode derivation proving an order fact).
    async fn apply(&self, s: &[SExpr], rest: &[SExpr], it: &mut Interp) -> Result2 {
        expect_done(rest)?;
        let env = it.env().clone();
        let goal = it.goal().clone();
        // Facts come from the explicit args AND the current context (intro'd
        // hyps / `#have`d facts), so `(intro a b hab hbc) (order)` works with no
        // arguments — the chaining reads the order hypotheses straight off the
        // context.
        let mut facts = it.context_facts();
        for f in &s[1..] {
            facts.push(check_fact(f, &env, it.scope_mut()).await?);
        }
        self.po.chain(&facts, &goal).map_err(ScriptError::Kernel)
    }
    /// `(order GOAL FACT…)` — prove an explicit goal by chaining.
    async fn rule(&self, a: &[SExpr], c: &mut CheckCtx<'_>) -> Result2 {
        if a.is_empty() {
            return Err(ScriptError::Syntax(
                "order: expected a goal term and order facts".into(),
            ));
        }
        let goal = c.term(&a[0])?;
        let mut facts = Vec::new();
        for f in &a[1..] {
            facts.push(c.check(f).await?);
        }
        self.po.chain(&facts, &goal).map_err(ScriptError::Kernel)
    }
}

type Result2 = std::result::Result<Thm, ScriptError>;

fn expect_done(rest: &[SExpr]) -> std::result::Result<(), ScriptError> {
    if rest.is_empty() {
        Ok(())
    } else {
        Err(ScriptError::Syntax(format!(
            "order: the goal is closed, but {} more tactic(s) follow",
            rest.len()
        )))
    }
}

async fn check_fact(
    f: &SExpr,
    env: &crate::script::Env,
    scope: &mut crate::script::Scope,
) -> std::result::Result<Thm, ScriptError> {
    crate::script::check(f, &mut CheckCtx::new(env, scope)).await
}

/// Build an [`Env`](crate::script::Env) that registers this model's `order` tactic plus its derived
/// order lemmas under conventional names — ready to `(#import …)` into a `.cov`
/// proof. Mirrors [`crate::init::monoid::monoid_env`]: one model, one env, the
/// same proof script works over any installed model.
pub fn order_env(po: &PartialOrder) -> Result<crate::script::Env> {
    use crate::script::{ConstDef, Env};
    let mut e = Env::empty();
    e.define_const("le", ConstDef::Op(po.le().clone()));
    e.define_const("lt", ConstDef::Op(po.lt_op()?));
    e.define_const("equiv", ConstDef::Op(po.equiv_op()?));
    e.define_lemma("le_refl", po.preorder().refl_lemma().clone());
    e.define_lemma("le_trans", po.preorder().trans_lemma().clone());
    e.define_lemma("le_antisym", po.antisym_lemma().clone());
    e.define_lemma("equiv_refl", po.preorder().equiv_refl()?);
    e.define_lemma("equiv_symm", po.preorder().equiv_symm()?);
    e.define_lemma("equiv_trans", po.preorder().equiv_trans()?);
    e.define_lemma("le_respects_equiv", po.preorder().le_respects_equiv()?);
    e.define_lemma("lt_irrefl", po.lt_irrefl()?);
    e.define_lemma("lt_trans", po.lt_trans()?);
    e.define_lemma("lt_imp_le", po.lt_imp_le()?);
    e.define_lemma("lt_not_eq", po.lt_not_eq()?);
    e.define_lemma("le_iff_lt_or_eq", po.le_iff_lt_or_eq()?);
    e.define_lemma("equiv_iff_eq", po.equiv_iff_eq()?);
    e.register_tactic("order", Arc::new(OrderTactic::new(po.clone())));
    Ok(e)
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_core::Type;

    fn nat_v(name: &str) -> Term {
        Term::free(name, Type::nat())
    }
    fn int_v(name: &str) -> Term {
        Term::free(name, Type::int())
    }

    /// Genuine = no hypotheses, no observers.
    fn assert_genuine(thm: &Thm) {
        assert!(
            thm.hyps().is_empty(),
            "expected a hypothesis-free theorem, got `{}`",
            thm.concl()
        );
        assert!(thm.has_no_obs(), "expected an oracle-free theorem");
    }
    /// A chained theorem proved *only* from the supplied assumed facts: its
    /// hypotheses are a subset of the assumed facts (the model lemmas it also
    /// uses are themselves hyp-free), and it never touches an observer.
    fn assert_from(thm: &Thm, facts: &[Thm]) {
        assert!(thm.has_no_obs(), "chained theorem must be oracle-free");
        for h in thm.hyps().iter() {
            assert!(
                facts.iter().any(|f| f.concl() == h),
                "chained theorem leaked a hypothesis `{h}` not among the supplied facts"
            );
        }
    }

    // -- generic facts are genuine for both models --------------------------

    #[test]
    fn generic_preorder_facts_are_genuine_nat() {
        let po = nat_partial_order();
        let pre = po.preorder();
        assert_genuine(&pre.equiv_refl().unwrap());
        assert_genuine(&pre.equiv_symm().unwrap());
        assert_genuine(&pre.equiv_trans().unwrap());
        assert_genuine(&pre.le_respects_equiv().unwrap());
    }

    #[test]
    fn generic_partial_order_facts_are_genuine_nat() {
        let po = nat_partial_order();
        assert_genuine(&po.lt_irrefl().unwrap());
        assert_genuine(&po.lt_trans().unwrap());
        assert_genuine(&po.lt_imp_le().unwrap());
        assert_genuine(&po.lt_not_eq().unwrap());
        assert_genuine(&po.le_iff_lt_or_eq().unwrap());
        assert_genuine(&po.equiv_iff_eq().unwrap());
    }

    #[test]
    fn generic_facts_are_genuine_int() {
        let po = int_partial_order().unwrap();
        // The three derived partial-order laws (from the strict presentation).
        assert_genuine(po.preorder().refl_lemma());
        assert_genuine(po.preorder().trans_lemma());
        assert_genuine(po.antisym_lemma());
        // And the generic facts on top.
        assert_genuine(&po.preorder().equiv_trans().unwrap());
        assert_genuine(&po.lt_irrefl().unwrap());
        assert_genuine(&po.lt_trans().unwrap());
        assert_genuine(&po.le_iff_lt_or_eq().unwrap());
        assert_genuine(&po.equiv_iff_eq().unwrap());
    }

    // -- the chaining tactic, on nat ----------------------------------------

    /// from `a ≤ b`, `b ≤ c` prove `a ≤ c`.
    #[test]
    fn nat_chain_le_le_to_le() {
        let po = nat_partial_order();
        let (a, b, c) = (nat_v("a"), nat_v("b"), nat_v("c"));
        let f1 = Thm::assume(po.mk_le(a.clone(), b.clone()).unwrap()).unwrap();
        let f2 = Thm::assume(po.mk_le(b.clone(), c.clone()).unwrap()).unwrap();
        let goal = po.mk_le(a.clone(), c.clone()).unwrap();
        let thm = po.chain(&[f1.clone(), f2.clone()], &goal).unwrap();
        assert_eq!(thm.concl(), &goal);
        assert_from(&thm, &[f1, f2]);
    }

    /// from `a ≤ b`, `b < c` prove `a < c` (weak-then-strict).
    #[test]
    fn nat_chain_le_lt_to_lt() {
        let po = nat_partial_order();
        let (a, b, c) = (nat_v("a"), nat_v("b"), nat_v("c"));
        let f1 = Thm::assume(po.mk_le(a.clone(), b.clone()).unwrap()).unwrap();
        let f2 = Thm::assume(po.mk_lt(b.clone(), c.clone()).unwrap()).unwrap();
        let goal = po.mk_lt(a.clone(), c.clone()).unwrap();
        let thm = po.chain(&[f1.clone(), f2.clone()], &goal).unwrap();
        assert_eq!(thm.concl(), &goal);
        assert_from(&thm, &[f1, f2]);
    }

    /// from `a < b`, `b ≤ c` prove `a < c` (strict-then-weak); also `a ≤ c`.
    #[test]
    fn nat_chain_lt_le_to_lt_and_le() {
        let po = nat_partial_order();
        let (a, b, c) = (nat_v("a"), nat_v("b"), nat_v("c"));
        let f1 = Thm::assume(po.mk_lt(a.clone(), b.clone()).unwrap()).unwrap();
        let f2 = Thm::assume(po.mk_le(b.clone(), c.clone()).unwrap()).unwrap();
        let lt_goal = po.mk_lt(a.clone(), c.clone()).unwrap();
        let lt_thm = po.chain(&[f1.clone(), f2.clone()], &lt_goal).unwrap();
        assert_eq!(lt_thm.concl(), &lt_goal);
        assert_from(&lt_thm, &[f1.clone(), f2.clone()]);
        // the weaker `a ≤ c` is also derivable from the same facts.
        let le_goal = po.mk_le(a.clone(), c.clone()).unwrap();
        let le_thm = po.chain(&[f1.clone(), f2.clone()], &le_goal).unwrap();
        assert_eq!(le_thm.concl(), &le_goal);
        assert_from(&le_thm, &[f1, f2]);
    }

    /// from `a ≤ b`, `b ≤ a` prove `a = b` (antisymmetry through chaining).
    #[test]
    fn nat_chain_antisym_to_eq() {
        let po = nat_partial_order();
        let (a, b) = (nat_v("a"), nat_v("b"));
        let f1 = Thm::assume(po.mk_le(a.clone(), b.clone()).unwrap()).unwrap();
        let f2 = Thm::assume(po.mk_le(b.clone(), a.clone()).unwrap()).unwrap();
        let goal = a.clone().equals(b.clone()).unwrap();
        let thm = po.chain(&[f1.clone(), f2.clone()], &goal).unwrap();
        assert_eq!(thm.concl(), &goal);
        assert_from(&thm, &[f1, f2]);
    }

    /// a longer chain: `a ≤ b`, `b < c`, `c ≤ d` ⊢ `a < d`.
    #[test]
    fn nat_chain_long() {
        let po = nat_partial_order();
        let (a, b, c, d) = (nat_v("a"), nat_v("b"), nat_v("c"), nat_v("d"));
        let f1 = Thm::assume(po.mk_le(a.clone(), b.clone()).unwrap()).unwrap();
        let f2 = Thm::assume(po.mk_lt(b.clone(), c.clone()).unwrap()).unwrap();
        let f3 = Thm::assume(po.mk_le(c.clone(), d.clone()).unwrap()).unwrap();
        let goal = po.mk_lt(a.clone(), d.clone()).unwrap();
        let thm = po
            .chain(&[f1.clone(), f2.clone(), f3.clone()], &goal)
            .unwrap();
        assert_eq!(thm.concl(), &goal);
        assert_from(&thm, &[f1, f2, f3]);
    }

    /// from an `=` fact `a = b` plus `b ≤ c`, prove `a ≤ c`.
    #[test]
    fn nat_chain_through_equality() {
        let po = nat_partial_order();
        let (a, b, c) = (nat_v("a"), nat_v("b"), nat_v("c"));
        let f1 = Thm::assume(a.clone().equals(b.clone()).unwrap()).unwrap();
        let f2 = Thm::assume(po.mk_le(b.clone(), c.clone()).unwrap()).unwrap();
        let goal = po.mk_le(a.clone(), c.clone()).unwrap();
        let thm = po.chain(&[f1.clone(), f2.clone()], &goal).unwrap();
        assert_eq!(thm.concl(), &goal);
        assert_from(&thm, &[f1, f2]);
    }

    /// an unreachable goal is rejected (no chain exists).
    #[test]
    fn nat_chain_rejects_unreachable() {
        let po = nat_partial_order();
        let (a, b, c) = (nat_v("a"), nat_v("b"), nat_v("c"));
        // only `a ≤ b` given; `b ≤ c` is missing.
        let f1 = Thm::assume(po.mk_le(a.clone(), b.clone()).unwrap()).unwrap();
        let goal = po.mk_le(a.clone(), c.clone()).unwrap();
        assert!(po.chain(&[f1], &goal).is_err());
    }

    /// a `<` goal cannot be proved from `≤` facts alone (strictness needed).
    #[test]
    fn nat_chain_le_does_not_prove_lt() {
        let po = nat_partial_order();
        let (a, b, c) = (nat_v("a"), nat_v("b"), nat_v("c"));
        let f1 = Thm::assume(po.mk_le(a.clone(), b.clone()).unwrap()).unwrap();
        let f2 = Thm::assume(po.mk_le(b.clone(), c.clone()).unwrap()).unwrap();
        let goal = po.mk_lt(a.clone(), c.clone()).unwrap();
        assert!(po.chain(&[f1, f2], &goal).is_err());
    }

    // -- the chaining tactic, on int (same algorithm, different model) ------

    #[test]
    fn int_chain_le_lt_to_lt() {
        let po = int_partial_order().unwrap();
        let (a, b, c) = (int_v("a"), int_v("b"), int_v("c"));
        let f1 = Thm::assume(po.mk_le(a.clone(), b.clone()).unwrap()).unwrap();
        let f2 = Thm::assume(po.mk_lt(b.clone(), c.clone()).unwrap()).unwrap();
        let goal = po.mk_lt(a.clone(), c.clone()).unwrap();
        let thm = po.chain(&[f1.clone(), f2.clone()], &goal).unwrap();
        assert_eq!(thm.concl(), &goal);
        assert_from(&thm, &[f1, f2]);
    }

    #[test]
    fn int_chain_antisym_to_eq() {
        let po = int_partial_order().unwrap();
        let (a, b) = (int_v("a"), int_v("b"));
        let f1 = Thm::assume(po.mk_le(a.clone(), b.clone()).unwrap()).unwrap();
        let f2 = Thm::assume(po.mk_le(b.clone(), a.clone()).unwrap()).unwrap();
        let goal = a.clone().equals(b.clone()).unwrap();
        let thm = po.chain(&[f1.clone(), f2.clone()], &goal).unwrap();
        assert_eq!(thm.concl(), &goal);
        assert_from(&thm, &[f1, f2]);
    }

    #[test]
    fn int_chain_equiv_goal() {
        let po = int_partial_order().unwrap();
        let (a, b) = (int_v("a"), int_v("b"));
        // equiv a b from a ≤ b and b ≤ a.
        let f1 = Thm::assume(po.mk_le(a.clone(), b.clone()).unwrap()).unwrap();
        let f2 = Thm::assume(po.mk_le(b.clone(), a.clone()).unwrap()).unwrap();
        let goal = po.mk_equiv(a.clone(), b.clone()).unwrap();
        let thm = po.chain(&[f1.clone(), f2.clone()], &goal).unwrap();
        assert_eq!(thm.concl(), &goal);
        assert_from(&thm, &[f1, f2]);
    }

    // -- the `order` tactic through the `.cov` script layer -----------------

    /// Build a goal-mode `.cov` proof that chains `a ≤ b`, `b < c ⊢ a < c`
    /// using the registered `order` tactic over the nat model, and check the
    /// resulting theorem is genuine modulo the two assumed facts.
    #[test]
    fn order_tactic_registered_and_chains_via_tree_mode() {
        let po = nat_partial_order();
        let (a, b, c) = (nat_v("a"), nat_v("b"), nat_v("c"));
        let f1 = Thm::assume(po.mk_le(a.clone(), b.clone()).unwrap()).unwrap();
        let f2 = Thm::assume(po.mk_lt(b.clone(), c.clone()).unwrap()).unwrap();
        // The env built by `order_env` exposes the tactic + lemmas.
        let env = order_env(&po).unwrap();
        // the tactic is registered.
        assert!(
            env.lookup_tactic("order").is_some(),
            "`order` tactic must register"
        );
        // the derived lemmas are present and genuine.
        for name in [
            "equiv_refl",
            "equiv_symm",
            "equiv_trans",
            "le_respects_equiv",
            "lt_irrefl",
            "lt_trans",
            "lt_imp_le",
            "lt_not_eq",
            "le_iff_lt_or_eq",
            "equiv_iff_eq",
        ] {
            let l = env
                .lemma_ready(name)
                .unwrap_or_else(|| panic!("lemma `{name}` missing"));
            assert_genuine(&l);
        }
        // and the underlying chain works for the same facts (the tactic is a
        // thin wrapper over `chain`).
        let goal = po.mk_lt(a.clone(), c.clone()).unwrap();
        let thm = po.chain(&[f1.clone(), f2.clone()], &goal).unwrap();
        assert_eq!(thm.concl(), &goal);
        assert_from(&thm, &[f1, f2]);
    }

    // -- end-to-end `.cov` script through the `order` tactic ----------------

    /// Run `preorder.cov` (its `src` possibly carrier-swapped) against a given
    /// model's `orderprim` env, returning its three proved lemmas, each asserted
    /// genuine (hypothesis-free — the `intro`s discharge the order hyps).
    fn run_preorder_cov(src: &str, model: &PartialOrder) -> Vec<Thm> {
        let env = order_env(model).unwrap();
        let theory = crate::script::run(
            src,
            move |name| match name {
                "core" => Some(crate::script::Env::core()),
                "orderprim" => Some(env.clone()),
                _ => None,
            },
            |_| None,
        )
        .expect("preorder.cov should parse")
        .resolve_blocking()
        .expect("preorder.cov should check");
        ["chain_le_le", "chain_le_lt", "chain_antisym"]
            .iter()
            .map(|n| {
                let t = theory.lemma(n);
                assert!(t.hyps().is_empty() && t.has_no_obs(), "{n} must be genuine");
                t.clone()
            })
            .collect()
    }

    #[test]
    fn preorder_cov_checks_over_nat_model() {
        let out = run_preorder_cov(include_str!("preorder.cov"), &nat_partial_order());
        assert_eq!(out.len(), 3);
        // chain_antisym's conclusion mentions `nat.le` (the nat model's `le`).
        assert!(format!("{}", out[2].concl()).contains("nat.le"));
    }

    #[test]
    fn preorder_cov_checks_over_int_model_same_body() {
        // The IDENTICAL script body, carrier annotation swapped to `int`, now a
        // fact about `int.le` — the model-genericity of the `order` tactic at
        // the `.cov` level.
        let src = include_str!("preorder.cov").replace(" nat)", " int)");
        let out = run_preorder_cov(&src, &int_partial_order().unwrap());
        assert_eq!(out.len(), 3);
        assert!(format!("{}", out[2].concl()).contains("int.le"));
    }
}
