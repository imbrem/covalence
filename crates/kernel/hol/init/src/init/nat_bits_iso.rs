//! `nat_bits_iso` — the **`list bool ≅ nat` bitstring isomorphism** (stage
//! NP3, the generally-useful payoff of the NP1 binary normal form).
//!
//! NP1 ([`crate::init::nat_binary`]) built `nat_of_bits : list bool → nat`
//! (the little-endian bit fold) and proved it *surjective* by an existence
//! argument. This module makes the inverse **explicit** and turns the
//! isomorphism into concrete, computable functions:
//!
//! - **[`bit_succ`]** `: list bool → list bool` — the **increment** on bit
//!   lists (little-endian binary `+1`), defined structurally by a `foldr`
//!   into a pair (the paramorphism-via-`foldr` trick, as in
//!   [`crate::init::nat_parse`]'s `span`). Its clauses are
//!   [`bit_succ_nil`] / [`bit_succ_cons_true`] / [`bit_succ_cons_false`].
//! - **[`bit_succ_correct`]** `⊢ ∀bs. nat_of_bits (bit_succ bs) =
//!   succ (nat_of_bits bs)` — **the lifted operation**: bit-list successor
//!   agrees with `nat` successor across the fold. This is the "lift one
//!   operation across the iso" deliverable, and the concrete form of NP1's
//!   `inc_lemma`.
//! - **[`nat_to_bits`]** `: nat → list bool` ≡ `natRec nil (λ_ acc.
//!   bit_succ acc)` — iterate the increment `n` times from `nil`. A closed
//!   `natRec` term (no strong recursion needed), producing the **canonical**
//!   (no-trailing-`false`) little-endian bit list for `n`.
//! - **[`bits_round_trip`]** `⊢ ∀n. nat_of_bits (nat_to_bits n) = n` — the
//!   section/retraction identity: `nat_of_bits ∘ nat_to_bits = id`. So
//!   `nat_of_bits` is surjective *with an explicit section*, and
//!   `nat_to_bits` is injective ([`nat_to_bits_inj`]).
//!
//! Together these exhibit the bijection `nat ≅ {canonical bit lists}`
//! (`nat_to_bits` maps `nat` onto the canonical bit lists, `nat_of_bits`
//! maps back, and they are mutually inverse on that domain). The remaining
//! half — `nat_to_bits (nat_of_bits bs) = bs` for a *canonical* `bs` — needs
//! a canonicality predicate and is recorded in the generated open-work index.

use covalence_core::{Result, Term, Type, subst};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::defs;
use covalence_hol_eval::defs::{cond, fst, list_foldr, nat_rec, nat_succ, pair, snd};
use covalence_hol_eval::derived::DerivedRules;

use crate::init::cond::{cond_false, cond_true};
use crate::init::eq::{beta_expand, beta_nf_concl, beta_reduce};
use crate::init::ext::{TermExt, ThmExt};
use crate::init::list::list_induct;
use crate::init::list_recursion::{foldr_cons, foldr_nil};
use crate::init::logic::exists_intro;
use crate::init::nat_binary::{
    bit1, cons_bool, double, double_succ, double_zero, nat_of_bits, nat_of_bits_app,
    nat_of_bits_cons_false, nat_of_bits_cons_true, nat_of_bits_nil,
};
use crate::init::nat_div::bool_cases;
use crate::init::prod::{fst_pair, snd_pair};

// ============================================================================
// Small type / term helpers.
// ============================================================================

fn nat() -> Type {
    Type::nat()
}

fn boolt() -> Type {
    Type::bool()
}

/// `list bool` — the bitstring type.
fn lb() -> Type {
    defs::list(boolt())
}

/// `list bool × list bool` — the `inc_pair` accumulator carrier.
fn pp() -> Type {
    defs::prod(lb(), lb())
}

fn zero() -> Term {
    crate::init::nat::zero()
}

fn succ(n: Term) -> Term {
    Term::app(nat_succ(), n)
}

/// `nil : list bool`.
fn nil_b() -> Term {
    defs::nil(boolt())
}

/// `cons b bs : list bool`.
fn cons_b(b: Term, bs: Term) -> Term {
    cons_bool(b, bs).expect("nat_bits_iso: cons bool")
}

/// `[true] : list bool`.
fn one_bits() -> Term {
    cons_b(covalence_hol_eval::mk_bool(true), nil_b())
}

/// `pair a b : list bool × list bool`.
fn pair_pp(a: Term, b: Term) -> Term {
    Term::app(Term::app(pair(lb(), lb()), a), b)
}

/// `fst p` for `p : list bool × list bool`.
fn fst_pp(p: Term) -> Term {
    Term::app(fst(lb(), lb()), p)
}

/// `snd p` for `p : list bool × list bool`.
fn snd_pp(p: Term) -> Term {
    Term::app(snd(lb(), lb()), p)
}

/// `cond[list bool] b x y`.
fn cond_lb(b: Term, x: Term, y: Term) -> Term {
    Term::app(Term::app(Term::app(cond(lb()), b), x), y)
}

/// `λname:ty. body`.
fn lam(name: &str, ty: Type, body: Term) -> Term {
    Term::abs(ty, subst::close(&body, name))
}

/// The RHS of an equational theorem (panics if not `⊢ _ = _`).
fn rhs(thm: &Thm) -> Term {
    thm.concl()
        .as_eq()
        .expect("init::nat_bits_iso: expected an equation")
        .1
        .clone()
}

// ============================================================================
// `bit_succ` — increment on little-endian bit lists, via the
// paramorphism-through-`foldr` pair trick.
//
//   inc_pair nil          = (nil, [true])
//   inc_pair (b :: bs)    = ( b :: fst (inc_pair bs)
//                           , if b then false :: snd (inc_pair bs)   -- carry
//                                  else true  :: fst (inc_pair bs) ) -- no carry
//
// The `fst` component reconstructs the original list (so no paramorphism is
// needed); `snd` is the incremented list. `bit_succ bs := snd (inc_pair bs)`.
// ============================================================================

/// `λb p. pair (cons b (fst p)) (cond b (cons false (snd p)) (cons true (fst p)))`
/// — the `inc_pair` fold step.
fn inc_step() -> Term {
    let b = Term::free("b", boolt());
    let p = Term::free("p", pp());
    let orig = fst_pp(p.clone()); // reconstructed original tail
    let inc = snd_pp(p.clone()); // incremented tail
    let recon = cons_b(b.clone(), orig.clone());
    let carry = cons_b(covalence_hol_eval::mk_bool(false), inc); // b = true
    let no_carry = cons_b(covalence_hol_eval::mk_bool(true), orig); // b = false
    let body = pair_pp(recon, cond_lb(b.clone(), carry, no_carry));
    lam("b", boolt(), lam("p", pp(), body))
}

/// `inc_pair : list bool → (list bool × list bool)` ≡
/// `foldr inc_step (pair nil [true])`.
fn inc_pair() -> Term {
    Term::app(
        Term::app(list_foldr(boolt(), pp()), inc_step()),
        pair_pp(nil_b(), one_bits()),
    )
}

/// `inc_pair bs` applied.
fn inc_pair_app(bs: &Term) -> Term {
    Term::app(inc_pair(), bs.clone())
}

/// `bit_succ : list bool → list bool` — the little-endian binary increment
/// (`+1`), the `snd` component of `inc_pair`, as a **function term**
/// (`λbs. snd (inc_pair bs)`). Used where a first-class function is needed
/// (e.g. the `nat_to_bits` `natRec` step). For the *applied* form prefer
/// [`bit_succ_app`], which is reduce-stable (not a β-redex).
pub fn bit_succ() -> Term {
    let bs = Term::free("bs", lb());
    lam("bs", lb(), snd_pp(inc_pair_app(&bs)))
}

/// `bit_succ bs` ≡ `snd (inc_pair bs)` — the applied increment, built as the
/// stuck projection `snd (inc_pair bs)` (**not** the β-redex
/// `(λbs. …) bs`), so it is stable under `reduce`. Every clause and theorem
/// below states `bit_succ bs` in this form.
pub fn bit_succ_app(bs: &Term) -> Term {
    snd_pp(inc_pair_app(bs))
}

/// `⊢ inc_pair nil = pair nil [true]` — the fold base clause.
fn inc_pair_nil() -> Result<Thm> {
    foldr_nil(&boolt(), &pp(), &inc_step(), &pair_pp(nil_b(), one_bits()))
}

/// `⊢ inc_pair (cons b bs) = pair (cons b (fst (inc_pair bs)))
///     (cond b (cons false (snd (inc_pair bs))) (cons true (fst (inc_pair bs))))`
/// — the general fold step clause (β-reduced).
fn inc_pair_cons(b: &Term, bs: &Term) -> Result<Thm> {
    let base = pair_pp(nil_b(), one_bits());
    let fc = foldr_cons(&boolt(), &pp(), &inc_step(), &base, b, bs)?;
    let red = rhs(&fc).reduce()?;
    fc.trans(red)
}

cached_thm! {
    /// `⊢ ∀bs. fst (inc_pair bs) = bs` — the `fst` component reconstructs the
    /// original list (the identity accumulator). By `list`-induction.
    pub fn inc_pair_fst() -> Result<Thm> {
        // motive P ≔ λbs. fst (inc_pair bs) = bs.
        let bs = Term::free("bs", lb());
        let motive = {
            let body = fst_pp(inc_pair_app(&bs)).equals(bs.clone())?;
            Term::abs(lb(), subst::close(&body, "bs"))
        };

        // base: fst (inc_pair nil) = fst (pair nil [true]) = nil.
        let base = {
            let f = fst_pair(&lb(), &lb(), &nil_b(), &one_bits())?; // fst (pair nil [true]) = nil
            let eq = inc_pair_nil()?.cong_arg(fst(lb(), lb()))?.trans(f)?;
            beta_expand(&motive, nil_b(), eq)?
        };

        // cons_case: ∀b bs. P bs ⟹ P (cons b bs).
        let b = Term::free("b", boolt());
        let cons_case = {
            let consbb = cons_b(b.clone(), bs.clone());
            let ante = Term::app(motive.clone(), bs.clone());
            let ih = beta_reduce(Thm::assume(ante.clone())?)?; // fst (inc_pair bs) = bs
            let orig = fst_pp(inc_pair_app(&bs));
            let inc = snd_pp(inc_pair_app(&bs));
            // fst (inc_pair (cons b bs)) = fst (pair (cons b orig) (cond …)) = cons b orig.
            let cons_clause = inc_pair_cons(&b, &bs)?;
            let cond_branch = cond_lb(
                b.clone(),
                cons_b(covalence_hol_eval::mk_bool(false), inc.clone()),
                cons_b(covalence_hol_eval::mk_bool(true), orig.clone()),
            );
            let fp = fst_pair(&lb(), &lb(), &cons_b(b.clone(), orig.clone()), &cond_branch)?;
            let fst_eq = cons_clause.cong_arg(fst(lb(), lb()))?.trans(fp)?; // = cons b orig
            // cons b orig = cons b bs  (via IH).
            let use_ih = ih.cong_arg(Term::app(defs::cons(boolt()), b.clone()))?;
            let eq = fst_eq.trans(use_ih)?; // fst (inc_pair (cons b bs)) = cons b bs
            let p_cons = beta_expand(&motive, consbb, eq)?;
            p_cons
                .imp_intro(&ante)?
                .all_intro("bs", lb())?
                .all_intro("b", boolt())?
        };

        beta_nf_concl(list_induct(&boolt(), &motive, base, cons_case)?)
    }
}

/// `⊢ bit_succ nil = [true]` — incrementing the empty (`= 0`) bit list gives
/// `[true]` (`= 1`). Genuine.
pub fn bit_succ_nil() -> Result<Thm> {
    // bit_succ nil = snd (inc_pair nil) = snd (pair nil [true]) = [true].
    let snd_eq = inc_pair_nil()?.cong_arg(snd(lb(), lb()))?; // snd (inc_pair nil) = snd (pair nil [true])
    let sp = snd_pair(&lb(), &lb(), &nil_b(), &one_bits())?; // snd (pair nil [true]) = [true]
    snd_eq.trans(sp)
}

/// `⊢ bit_succ (cons b bs) = cond b (cons false (bit_succ bs)) (cons true bs)`
/// — the general (unresolved-`cond`) `cons` clause. Uses [`inc_pair_fst`] to
/// rewrite the reconstructed `fst (inc_pair bs)` back to `bs`. Genuine.
pub fn bit_succ_cons(b: &Term, bs: &Term) -> Result<Thm> {
    // bit_succ (cons b bs) = snd (inc_pair (cons b bs)) — already the
    // `bit_succ_app` form, so no unfolding step is needed.
    let cons_clause = inc_pair_cons(b, bs)?; // inc_pair (cons b bs) = pair X Y
    // Extract the exact pair components `X` (reconstructed head) and `Y`
    // (the cond branch) from the reduced RHS, so `snd_pair` matches on the
    // nose.
    let clause_rhs = rhs(&cons_clause);
    let (pair_x, y) = clause_rhs
        .as_app()
        .expect("inc_pair_cons RHS is `pair X Y`");
    let x = pair_x.as_app().expect("`pair X`").1.clone();
    let y = y.clone();
    let sp = snd_pair(&lb(), &lb(), &x, &y)?; // snd (pair X Y) = Y
    // bit_succ (cons b bs) = Y = cond b (cons false (snd (inc_pair bs)))
    //                                   (cons true (fst (inc_pair bs))).
    let snd_eq = cons_clause.cong_arg(snd(lb(), lb()))?.trans(sp)?;
    // The carry branch's `snd (inc_pair bs)` is already `bit_succ bs`; only
    // rewrite `fst (inc_pair bs) → bs` in the no-carry branch.
    let fst_eq = inc_pair_fst().all_elim(bs.clone())?; // fst (inc_pair bs) = bs
    snd_eq.rhs_conv(|t| t.rw_all(&fst_eq))
}

/// `⊢ bit_succ (cons true bs) = cons false (bit_succ bs)` — the carry clause.
pub fn bit_succ_cons_true(bs: &Term) -> Result<Thm> {
    let general = bit_succ_cons(&covalence_hol_eval::mk_bool(true), bs)?;
    let carry = cons_b(covalence_hol_eval::mk_bool(false), bit_succ_app(bs));
    let no_carry = cons_b(covalence_hol_eval::mk_bool(true), bs.clone());
    general.trans(cond_true(&lb(), &carry, &no_carry)?)
}

/// `⊢ bit_succ (cons false bs) = cons true bs` — the no-carry clause.
pub fn bit_succ_cons_false(bs: &Term) -> Result<Thm> {
    let general = bit_succ_cons(&covalence_hol_eval::mk_bool(false), bs)?;
    let carry = cons_b(covalence_hol_eval::mk_bool(false), bit_succ_app(bs));
    let no_carry = cons_b(covalence_hol_eval::mk_bool(true), bs.clone());
    general.trans(cond_false(&lb(), &carry, &no_carry)?)
}

// ============================================================================
// `bit_succ_correct` — the LIFTED OPERATION: `bit_succ` on bit lists agrees
// with `succ` on `nat` across `nat_of_bits`. By `list`-induction with a
// `bool.cases` split on the head.
// ============================================================================

cached_thm! {
    /// `⊢ ∀bs. nat_of_bits (bit_succ bs) = succ (nat_of_bits bs)` — **the
    /// lifted operation**: incrementing a bit list corresponds to taking the
    /// successor of its `nat` value. The concrete form of NP1's `inc_lemma`.
    /// By `list`-induction on `bs`, `bool.cases` on the head bit.
    pub fn bit_succ_correct() -> Result<Thm> {
        // motive P ≔ λbs. nat_of_bits (bit_succ bs) = succ (nat_of_bits bs).
        let bs = Term::free("bs", lb());
        let motive = {
            let body = nat_of_bits_app(bit_succ_app(&bs))
                .equals(succ(nat_of_bits_app(bs.clone())))?;
            Term::abs(lb(), subst::close(&body, "bs"))
        };

        // ---- base: nat_of_bits (bit_succ nil) = succ (nat_of_bits nil). ----
        let base = {
            // nat_of_bits (bit_succ nil) = nat_of_bits [true].
            let l = bit_succ_nil()?.cong_arg(nat_of_bits())?; // nat_of_bits (bit_succ nil) = nat_of_bits [true]
            let ct = nat_of_bits_cons_true(nil_b())?; // nat_of_bits [true] = bit1 (nat_of_bits nil)
            let nob_nil = nat_of_bits_nil()?; // nat_of_bits nil = 0
            // bit1 (nat_of_bits nil) = succ (double (nat_of_bits nil)) — definitional.
            let nob = nat_of_bits_app(nil_b());
            let bit1_def = Thm::refl(bit1(nob.clone()))?; // bit1 nob = succ (double nob)
            // double (nat_of_bits nil) = nat_of_bits nil (both 0).
            let d_id = nob_nil
                .clone()
                .cong_arg(double())?
                .trans(double_zero())?
                .trans(nob_nil.sym()?)?; // double nob = nob
            let rhs_eq = bit1_def.trans(d_id.cong_arg(nat_succ())?)?; // bit1 nob = succ nob
            let eq = l.trans(ct)?.trans(rhs_eq)?; // = succ (nat_of_bits nil)
            beta_expand(&motive, nil_b(), eq)?
        };

        // ---- cons_case: ∀b bs. P bs ⟹ P (cons b bs). ----
        let b = Term::free("b", boolt());
        let cons_case = {
            let consbb = cons_b(b.clone(), bs.clone());
            let ante = Term::app(motive.clone(), bs.clone());
            let ih = beta_reduce(Thm::assume(ante.clone())?)?; // nat_of_bits (bit_succ bs) = succ (nat_of_bits bs)
            let nob_bs = nat_of_bits_app(bs.clone());

            // `⊢ cons lit bs = cons b bs` from `hlit : ⊢ b = lit` — a
            // *targeted* congruence (only the `cons _ bs` head, so the literal
            // `T`/`F`s buried in `inc_pair`'s definition are untouched, unlike a
            // global `lit → b` rewrite).
            let head_eq = |hlit: &Thm| -> Result<Thm> {
                hlit
                    .clone()
                    .sym()? // lit = b
                    .cong_arg(defs::cons(boolt()))? // cons lit = cons b
                    .cong_fn(bs.clone()) // cons lit bs = cons b bs
            };

            // b = true (carry): bit_succ (cons true bs) = cons false (bit_succ bs).
            // Prove `goal[true]` concretely, then transport to `goal[b]` via the
            // head congruence `cons true bs = cons b bs`.
            let branch_t = {
                let hyp = b.clone().equals(covalence_hol_eval::mk_bool(true))?;
                // LHS: nat_of_bits (bit_succ (cons true bs))
                //    = nat_of_bits (cons false (bit_succ bs))
                //    = bit0 (nat_of_bits (bit_succ bs)) = double (nat_of_bits (bit_succ bs))
                //    = double (succ (nat_of_bits bs))               (IH)
                //    = succ (succ (double (nat_of_bits bs))).
                let l1 = bit_succ_cons_true(&bs)?.cong_arg(nat_of_bits())?;
                let l2 = nat_of_bits_cons_false(bit_succ_app(&bs))?; // = bit0 (…) = double (…)
                let l3 = ih.clone().cong_arg(double())?; // double (nob(bit_succ bs)) = double (succ nob)
                let l4 = double_succ().all_elim(nob_bs.clone())?; // double (succ nob) = succ (succ (double nob))
                let lhs = l1.trans(l2)?.trans(l3)?.trans(l4)?;
                // RHS: succ (nat_of_bits (cons true bs)) = succ (bit1 nob) = succ (succ (double nob)).
                let rc = nat_of_bits_cons_true(bs.clone())?.cong_arg(nat_succ())?;
                let pt = lhs.trans(rc.sym()?)?; // goal[true]
                let hlit = Thm::assume(hyp.clone())?;
                pt.rewrite(&head_eq(&hlit)?)?
                    .imp_intro(&hyp)?
            };

            // b = false (no carry): bit_succ (cons false bs) = cons true bs.
            let branch_f = {
                let hyp = b.clone().equals(covalence_hol_eval::mk_bool(false))?;
                // LHS: nat_of_bits (bit_succ (cons false bs)) = nat_of_bits (cons true bs)
                //    = bit1 nob = succ (double nob).
                let l1 = bit_succ_cons_false(&bs)?.cong_arg(nat_of_bits())?;
                let l2 = nat_of_bits_cons_true(bs.clone())?; // = bit1 nob
                let lhs = l1.trans(l2)?;
                // RHS: succ (nat_of_bits (cons false bs)) = succ (bit0 nob) = succ (double nob).
                let rc = nat_of_bits_cons_false(bs.clone())?.cong_arg(nat_succ())?;
                let pf = lhs.trans(rc.sym()?)?; // goal[false]  (bit1 nob = succ (bit0 nob) definitionally)
                let hlit = Thm::assume(hyp.clone())?;
                pf.rewrite(&head_eq(&hlit)?)?
                    .imp_intro(&hyp)?
            };

            let combined = bool_cases()
                .all_elim(b.clone())?
                .or_elim(branch_t, branch_f)?;
            let p_cons = beta_expand(&motive, consbb, combined)?;
            p_cons
                .imp_intro(&ante)?
                .all_intro("bs", lb())?
                .all_intro("b", boolt())?
        };

        beta_nf_concl(list_induct(&boolt(), &motive, base, cons_case)?)
    }
}

// ============================================================================
// `nat_to_bits` — the explicit inverse: iterate `bit_succ` `n` times from
// `nil`. `natRec nil (λ_ acc. bit_succ acc)`.
// ============================================================================

/// `λ_:nat. λacc:list bool. bit_succ acc` — the `natRec` step for
/// `nat_to_bits` (ignore the index, increment the accumulator).
fn nat_to_bits_step() -> Term {
    let acc = Term::free("acc", lb());
    let inner = lam("acc", lb(), bit_succ_app(&acc));
    lam("_n", nat(), inner)
}

/// `nat_to_bits : nat → list bool` ≡ `natRec nil (λ_ acc. bit_succ acc)` —
/// the little-endian binary representation of `n` (canonical: no trailing
/// `false`). The explicit inverse of [`nat_of_bits`] on `nat`.
pub fn nat_to_bits() -> Term {
    Term::app(Term::app(nat_rec(lb()), nil_b()), nat_to_bits_step())
}

/// `nat_to_bits n` applied.
pub fn nat_to_bits_app(n: &Term) -> Term {
    Term::app(nat_to_bits(), n.clone())
}

/// The `natRec` equations for `nat_to_bits`'s result type `list bool`.
fn rec_at_lb() -> Result<Thm> {
    crate::init::recursion::rec_holds_proof_at(&lb())
}

/// `⊢ nat_to_bits 0 = nil` — the base recursion law.
pub fn nat_to_bits_zero() -> Result<Thm> {
    rec_at_lb()?
        .all_elim(nil_b())?
        .all_elim(nat_to_bits_step())?
        .and_elim_l()
}

/// `⊢ ∀n. nat_to_bits (succ n) = bit_succ (nat_to_bits n)` — the step law.
pub fn nat_to_bits_succ() -> Result<Thm> {
    let n = Term::free("n", nat());
    let step = rec_at_lb()?
        .all_elim(nil_b())?
        .all_elim(nat_to_bits_step())?
        .and_elim_r()?
        .all_elim(n.clone())?; // nat_to_bits (succ n) = step n (nat_to_bits n)
    let red = rhs(&step).reduce()?; // β: = bit_succ (nat_to_bits n)
    step.trans(red)?.all_intro("n", nat())
}

// ============================================================================
// The round-trip: `nat_of_bits ∘ nat_to_bits = id`, so `nat_of_bits` is a
// retraction (surjective with the explicit section `nat_to_bits`), and
// `nat_to_bits` is injective. By `nat`-induction through `bit_succ_correct`.
// ============================================================================

cached_thm! {
    /// `⊢ ∀n. nat_of_bits (nat_to_bits n) = n` — **the round-trip identity**:
    /// `nat_of_bits ∘ nat_to_bits = id`. By `nat`-induction: `0` maps to
    /// `nat_of_bits nil = 0`, and the successor step is [`bit_succ_correct`]
    /// composed with [`nat_to_bits_succ`].
    pub fn bits_round_trip() -> Result<Thm> {
        let n = Term::free("n", nat());
        // motive Q ≔ λn. nat_of_bits (nat_to_bits n) = n.
        let motive = {
            let body = nat_of_bits_app(nat_to_bits_app(&n)).equals(n.clone())?;
            Term::abs(nat(), subst::close(&body, "n"))
        };

        // base: nat_of_bits (nat_to_bits 0) = nat_of_bits nil = 0.
        let base = {
            let l = nat_to_bits_zero()?.cong_arg(nat_of_bits())?; // = nat_of_bits nil
            l.trans(nat_of_bits_nil()?)? // = 0
        };

        // step: (nat_of_bits (nat_to_bits n) = n) ⟹ (nat_of_bits (nat_to_bits (succ n)) = succ n).
        let ihc = nat_of_bits_app(nat_to_bits_app(&n)).equals(n.clone())?;
        let ih = Thm::assume(ihc.clone())?;
        // nat_of_bits (nat_to_bits (succ n)) = nat_of_bits (bit_succ (nat_to_bits n))
        //   = succ (nat_of_bits (nat_to_bits n))   (bit_succ_correct)
        //   = succ n                               (IH).
        let l1 = nat_to_bits_succ()?.all_elim(n.clone())?.cong_arg(nat_of_bits())?;
        let l2 = bit_succ_correct().all_elim(nat_to_bits_app(&n))?;
        let l3 = ih.cong_arg(nat_succ())?; // succ (nat_of_bits (nat_to_bits n)) = succ n
        let step = l1.trans(l2)?.trans(l3)?.imp_intro(&ihc)?;

        induct(&motive, base, step)
    }
}

cached_thm! {
    /// `⊢ ∀m n. (nat_to_bits m = nat_to_bits n) ⟹ (m = n)` — `nat_to_bits`
    /// is **injective** (it has the left inverse `nat_of_bits`, by
    /// [`bits_round_trip`]). So the bit-list representation of a `nat` is
    /// unique.
    pub fn nat_to_bits_inj() -> Result<Thm> {
        let m = Term::free("m", nat());
        let n = Term::free("n", nat());
        let hyp = nat_to_bits_app(&m).equals(nat_to_bits_app(&n))?;
        // apply nat_of_bits to both sides of the hypothesis.
        let mapped = Thm::assume(hyp.clone())?.cong_arg(nat_of_bits())?; // nat_of_bits (nat_to_bits m) = nat_of_bits (nat_to_bits n)
        // rewrite both sides via the round-trip: m = n.
        let rt_m = bits_round_trip().all_elim(m.clone())?; // nat_of_bits (nat_to_bits m) = m
        let rt_n = bits_round_trip().all_elim(n.clone())?; // nat_of_bits (nat_to_bits n) = n
        let m_eq_n = rt_m.sym()?.trans(mapped)?.trans(rt_n)?; // m = n
        m_eq_n
            .imp_intro(&hyp)?
            .all_intro("n", nat())?
            .all_intro("m", nat())
    }
}

cached_thm! {
    /// `⊢ ∀n. ∃bs. nat_of_bits bs = n` — the **representation theorem** again,
    /// now with the *explicit* witness `nat_to_bits n` (constructive
    /// surjectivity), from [`bits_round_trip`]. (NP1's `nat_of_bits_surjective`
    /// proved the same statement by an existence argument; this re-derives it
    /// from the section.)
    pub fn nat_of_bits_surjective_explicit() -> Result<Thm> {
        let n = Term::free("n", nat());
        let w = Term::free("w", lb());
        let pred = {
            let body = nat_of_bits_app(w.clone()).equals(n.clone())?;
            Term::abs(lb(), subst::close(&body, "w"))
        };
        let wit = nat_to_bits_app(&n);
        let proof = bits_round_trip().all_elim(n.clone())?; // nat_of_bits (nat_to_bits n) = n
        // pred wit is a redex; bridge across β.
        let pred_wit = Term::app(pred.clone(), wit.clone());
        let proof_redex = Thm::beta_conv(pred_wit)?.sym()?.eq_mp(proof)?; // ⊢ pred wit
        exists_intro(pred, wit, proof_redex)?.all_intro("n", nat())
    }
}

/// Prove `⊢ ∀n. body` by `nat`-induction. `motive` is `λn. body`; `base`
/// proves `body[0/n]`; `step` proves `body[n] ⟹ body[S n]`.
fn induct(motive: &Term, base: Thm, step: Thm) -> Result<Thm> {
    let n = Term::free("n", nat());
    let base = beta_expand(motive, zero(), base)?;
    let pn = Term::app(motive.clone(), n.clone());
    let body_n = beta_reduce(Thm::assume(pn.clone())?)?;
    let body_sn = step.imp_elim(body_n)?;
    let p_sn = beta_expand(motive, succ(n.clone()), body_sn)?;
    let step = p_sn.imp_intro(&pn)?;
    beta_nf_concl(crate::init::ext::nat_induct(base, step)?)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `succ` applied `k` times to `0` — unary form.
    fn succn(k: u32) -> Term {
        let mut t = zero();
        for _ in 0..k {
            t = succ(t);
        }
        t
    }

    #[test]
    fn bit_succ_clauses_are_genuine() {
        let bs = Term::free("bs", lb());
        for t in [
            bit_succ_nil().unwrap(),
            bit_succ_cons(&covalence_hol_eval::mk_bool(true), &bs).unwrap(),
            bit_succ_cons_true(&bs).unwrap(),
            bit_succ_cons_false(&bs).unwrap(),
            inc_pair_fst(),
        ] {
            assert!(t.hyps().is_empty(), "bit_succ clause must be axiom-free");
        }
        // bit_succ_nil resolves to [true].
        assert_eq!(rhs(&bit_succ_nil().unwrap()), one_bits());
        // cons_true / cons_false resolve.
        let ct = bit_succ_cons_true(&bs).unwrap();
        assert_eq!(
            rhs(&ct),
            cons_b(covalence_hol_eval::mk_bool(false), bit_succ_app(&bs))
        );
        let cf = bit_succ_cons_false(&bs).unwrap();
        assert_eq!(
            rhs(&cf),
            cons_b(covalence_hol_eval::mk_bool(true), bs.clone())
        );
    }

    #[test]
    fn bit_succ_correct_is_genuine() {
        let thm = bit_succ_correct();
        assert!(thm.hyps().is_empty(), "bit_succ_correct must be axiom-free");
        // ∀bs. nat_of_bits (bit_succ bs) = succ (nat_of_bits bs)
        let bs = Term::free("xs", lb());
        let inst = thm.all_elim(bs).unwrap();
        assert!(inst.concl().type_of().unwrap().is_bool());
    }

    /// Evaluate `bit_succ` on a concrete little-endian bit list, resolving the
    /// cond clauses.
    fn eval_bit_succ(bits: &[bool]) -> Thm {
        if bits.is_empty() {
            return bit_succ_nil().unwrap();
        }
        let head = bits[0];
        let tail = bits_term(&bits[1..]);
        if head {
            // bit_succ (true :: tail) = false :: bit_succ tail.
            let step = bit_succ_cons_true(&tail).unwrap();
            let rec = eval_bit_succ(&bits[1..]); // bit_succ tail = <lit>
            step.rhs_conv(|t| t.rw_all(&rec)).unwrap()
        } else {
            bit_succ_cons_false(&tail).unwrap()
        }
    }

    /// A `list bool` term from a little-endian bool slice.
    fn bits_term(bits: &[bool]) -> Term {
        let mut t = nil_b();
        for &b in bits.iter().rev() {
            t = cons_b(covalence_hol_eval::mk_bool(b), t);
        }
        t
    }

    #[test]
    fn bit_succ_computes() {
        // bit_succ [true, false, true] (=5, LE) = [false, true, true] (=6).
        let five = [true, false, true];
        let thm = eval_bit_succ(&five);
        assert!(thm.hyps().is_empty());
        assert_eq!(rhs(&thm), bits_term(&[false, true, true]));
        // bit_succ [true, true] (=3) = [false, false, true] (=4, carry ripples).
        let three = eval_bit_succ(&[true, true]);
        assert_eq!(rhs(&three), bits_term(&[false, false, true]));
    }

    /// `⊢ nat_to_bits (succn k) = <bit list>` by iterating the step law.
    fn eval_nat_to_bits(k: u32) -> Thm {
        let mut thm = nat_to_bits_zero().unwrap(); // nat_to_bits 0 = nil
        for i in 0..k {
            // thm : nat_to_bits (succn i) = <bits_i>
            let step = nat_to_bits_succ().unwrap().all_elim(succn(i)).unwrap(); // nat_to_bits (succ (succn i)) = bit_succ (nat_to_bits (succn i))
            thm = step.rhs_conv(|t| t.rw_all(&thm)).unwrap(); // = bit_succ <bits_i>
            // reduce the bit_succ application to a concrete bit list.
            thm = resolve_bit_succ(thm);
        }
        thm
    }

    /// Given `⊢ x = snd (inc_pair <concrete bits>)` (the `bit_succ_app`
    /// form), resolve the RHS to a concrete bit list.
    fn resolve_bit_succ(thm: Thm) -> Thm {
        let rhs_t = rhs(&thm); // snd (inc_pair <bits>)
        let inc_app = rhs_t.as_app().unwrap().1.clone(); // inc_pair <bits>
        let bits = inc_app.as_app().unwrap().1.clone(); // <bits>
        let bits_vec = bits_of_term(&bits);
        let ev = eval_bit_succ(&bits_vec); // bit_succ <bits> = <lit>
        thm.rhs_conv(|t| t.rw_all(&ev)).unwrap()
    }

    /// Read a concrete little-endian `list bool` term back into a bool vec.
    fn bits_of_term(t: &Term) -> Vec<bool> {
        let mut out = Vec::new();
        let mut cur = t.clone();
        while let Some((f, tail)) = cur.as_app() {
            // f = cons b ; extract b.
            let (_cons, b) = f.as_app().unwrap();
            out.push(*b == covalence_hol_eval::mk_bool(true));
            cur = tail.clone();
        }
        out
    }

    #[test]
    fn nat_to_bits_computes() {
        // nat_to_bits 5 = [true, false, true] (LE binary of 5).
        let thm = eval_nat_to_bits(5);
        assert!(thm.hyps().is_empty());
        assert_eq!(rhs(&thm), bits_term(&[true, false, true]));
        // nat_to_bits 4 = [false, false, true].
        assert_eq!(rhs(&eval_nat_to_bits(4)), bits_term(&[false, false, true]));
        // nat_to_bits 0 = nil, nat_to_bits 1 = [true].
        assert_eq!(rhs(&eval_nat_to_bits(0)), nil_b());
        assert_eq!(rhs(&eval_nat_to_bits(1)), bits_term(&[true]));
    }

    #[test]
    fn round_trip_is_genuine() {
        let thm = bits_round_trip();
        assert!(thm.hyps().is_empty(), "round-trip must be axiom-free");
        // ∀n. nat_of_bits (nat_to_bits n) = n
        let inst = thm.all_elim(succ(zero())).unwrap();
        assert!(inst.hyps().is_empty());
        assert_eq!(
            inst.concl(),
            &nat_of_bits_app(nat_to_bits_app(&succ(zero())))
                .equals(succ(zero()))
                .unwrap()
        );
    }

    #[test]
    fn injectivity_is_genuine() {
        let thm = nat_to_bits_inj();
        assert!(thm.hyps().is_empty(), "injectivity must be axiom-free");
        let (m, n) = (Term::free("m", nat()), Term::free("n", nat()));
        let inst = thm.all_elim(m).unwrap().all_elim(n).unwrap();
        assert!(inst.concl().type_of().unwrap().is_bool());
    }

    #[test]
    fn explicit_surjectivity_is_genuine() {
        let thm = nat_of_bits_surjective_explicit();
        assert!(thm.hyps().is_empty());
        let inst = thm.all_elim(succ(zero())).unwrap();
        assert!(inst.concl().type_of().unwrap().is_bool());
    }
}
