//! `nat_binary` — the **binary normal form** for `nat`, in the HOL-only
//! dialect (no reliance on `nat` *literals*): a `nat` is built from `0`,
//! [`double`] `n = 2·n`, and `succ`, giving a *log-depth* representation
//! (`5 = succ(double(double(succ 0))) = 0b101`).
//!
//! Everything here is a genuine `init`-level derivation over the existing
//! kernel rules — no new kernel surface, no postulates.
//!
//! ## The pieces
//!
//! - **[`double`]** `: nat → nat` ≡ `natRec 0 (λ_ k. succ (succ k))`
//!   (`= 2·n`). Computation laws [`double_zero`] / [`double_succ`], the
//!   homomorphism [`double_add`] (`double (a+b) = double a + double b`),
//!   the bridge [`double_eq_add_self`] (`double n = n + n`), and
//!   injectivity [`double_inj`].
//! - **The two digit constructors** `bit0 n := double n` (an even number)
//!   and `bit1 n := succ (double n)` (an odd number). These are the little
//!   "binary digits": a nat's binary form is `bitᵦₖ (… (bitᵦ₀ 0) …)`. The
//!   definitional relations are [`bit0_eq_double`] / [`bit1_eq_succ_double`]
//!   / [`succ_bit0_eq_bit1`], and their recursion laws reuse the `double`
//!   laws ([`bit0_zero`] / [`bit0_succ`]).
//! - **[`nat_of_bits`]** `: list bool → nat` — the little-endian fold
//!   `foldr (λb acc. if b then bit1 acc else bit0 acc) 0`, the bridge to
//!   the `list bool ≅ nat` bitstring isomorphism (stage NP3). Its
//!   computation clauses are [`nat_of_bits_nil`] / [`nat_of_bits_cons`]
//!   (general, `cond`-headed) and the resolved [`nat_of_bits_cons_true`] /
//!   [`nat_of_bits_cons_false`].
//! - **The representation theorem** [`nat_of_bits_surjective`]
//!   (`∀n. ∃bs. nat_of_bits bs = n` — every nat has a binary form), proved
//!   by `nat`-induction through the **increment lemma** [`inc_lemma`]
//!   (`∀bs. ∃bs'. nat_of_bits bs' = succ (nat_of_bits bs)`, by `list`
//!   induction with a carry `bool.cases`).
//!
//! See the generated open-work index for what is still open (the parity / canonical-form
//! uniqueness facts and the log-depth `bit_add` carry addition).

use covalence_core::{Result, Term, Type, subst};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::defs;
use covalence_hol_eval::defs::{cond, list_foldr, nat_add, nat_rec, nat_succ};
use covalence_hol_eval::derived::DerivedRules;

use crate::init::cond::{cond_false, cond_true};
use crate::init::eq::{beta_expand, beta_nf_concl, beta_reduce};
use crate::init::ext::{TermExt, ThmExt};
use crate::init::list::list_induct;
use crate::init::list_recursion::{foldr_cons, foldr_nil};
use crate::init::logic::{exists_elim, exists_intro};
use crate::init::nat::{
    add_base, add_lt_add, add_step, add_succ_r, lt_irrefl, lt_trichotomy, rec_holds,
};
use crate::init::nat_div::bool_cases;

// ============================================================================
// Small term helpers (private — the public surface is the term builders +
// theorems).
// ============================================================================

fn nat() -> Type {
    Type::nat()
}

fn boolt() -> Type {
    Type::bool()
}

fn zero() -> Term {
    // Reuse `init::nat`'s `0` term rather than minting a fresh nat-literal
    // constructor (keeps the toHOL literal-ctor purge ratchet flat).
    crate::init::nat::zero()
}

fn succ(n: Term) -> Term {
    Term::app(nat_succ(), n)
}

fn add(a: Term, b: Term) -> Term {
    Term::app(Term::app(nat_add(), a), b)
}

fn var(name: &str) -> Term {
    Term::free(name, nat())
}

/// The RHS of an equational theorem (panics if not `⊢ _ = _`).
fn rhs(thm: &Thm) -> Term {
    thm.concl()
        .as_eq()
        .expect("init::nat_binary: expected an equation")
        .1
        .clone()
}

/// `⊢ x + c = y + c` from `⊢ x = y` — congruence on `+`'s left argument.
fn cong_add_l(eq: Thm, c: Term) -> Result<Thm> {
    eq.cong_arg(nat_add())?.cong_fn(c)
}

// ============================================================================
// `double` — the doubling map `natRec 0 (λ_ k. S (S k))`.
// ============================================================================

/// `λ_:nat. λk:nat. S (S k)` — the `natRec` step function `double` uses:
/// it ignores the index and adds two successors to the recursive result.
fn double_step() -> Term {
    let inner = Term::abs(nat(), subst::close(&succ(succ(var("k"))), "k")); // λk. S(S k)
    Term::abs(nat(), inner) // λ_. (λk. S(S k))
}

/// `double : nat → nat` ≡ `natRec 0 (λ_ k. S (S k))` (`= 2·n`). A closed
/// `natRec` term — no new kernel constant; the computation laws
/// ([`double_zero`] / [`double_succ`]) come straight from [`rec_holds`].
pub fn double() -> Term {
    Term::app(Term::app(nat_rec(nat()), zero()), double_step())
}

/// `double n` applied.
pub fn double_app(n: Term) -> Term {
    Term::app(double(), n)
}

cached_thm! {
    /// `⊢ double 0 = 0` — the base recursion law.
    pub fn double_zero() -> Result<Thm> {
        rec_holds()
            .all_elim(zero())?
            .all_elim(double_step())?
            .and_elim_l()
    }
}

cached_thm! {
    /// `⊢ ∀n. double (S n) = S (S (double n))` — the step recursion law.
    pub fn double_succ() -> Result<Thm> {
        let n = var("n");
        let step = rec_holds()
            .all_elim(zero())?
            .all_elim(double_step())?
            .and_elim_r()?
            .all_elim(n)?; // double (S n) = f n (double n)
        let red = rhs(&step).reduce()?; // f n (double n) = S (S (double n))
        step.trans(red)?.all_intro("n", nat())
    }
}

// ============================================================================
// The two digit constructors: `bit0 n = double n` (even), `bit1 n =
// succ (double n)` (odd).
// ============================================================================

/// `bit0 n := double n` — the "0" binary digit (an even number). A pure
/// abbreviation for [`double_app`]; the recursion laws are the `double`
/// laws ([`bit0_zero`] / [`bit0_succ`]).
pub fn bit0(n: Term) -> Term {
    double_app(n)
}

/// `bit1 n := succ (double n)` — the "1" binary digit (an odd number).
pub fn bit1(n: Term) -> Term {
    succ(double_app(n))
}

cached_thm! {
    /// `⊢ ∀n. bit0 n = double n` — the digit `bit0` *is* `double`.
    pub fn bit0_eq_double() -> Result<Thm> {
        let n = var("n");
        Thm::refl(bit0(n))?.all_intro("n", nat())
    }
}

cached_thm! {
    /// `⊢ ∀n. bit1 n = succ (double n)` — `bit1` is an odd number.
    pub fn bit1_eq_succ_double() -> Result<Thm> {
        let n = var("n");
        Thm::refl(bit1(n))?.all_intro("n", nat())
    }
}

cached_thm! {
    /// `⊢ ∀n. succ (bit0 n) = bit1 n` — `succ` steps an even digit to the
    /// odd one at the same "weight".
    pub fn succ_bit0_eq_bit1() -> Result<Thm> {
        let n = var("n");
        Thm::refl(succ(bit0(n)))?.all_intro("n", nat())
    }
}

cached_thm! {
    /// `⊢ bit0 0 = 0` — the empty binary form is zero.
    pub fn bit0_zero() -> Thm {
        double_zero()
    }
}

cached_thm! {
    /// `⊢ ∀n. bit0 (S n) = S (S (bit0 n))` — `bit0`'s recursion law.
    pub fn bit0_succ() -> Thm {
        double_succ()
    }
}

// ============================================================================
// `double_add` — the additive homomorphism, by induction.
// ============================================================================

/// Prove `⊢ ∀n. body` by `nat`-induction. `motive` is `λn. body`; `base`
/// proves `body[0/n]`; `step` proves `body[n] ⟹ body[S n]` for the free
/// variable `n`. (A local copy of the `init::nat` helper.)
fn induct(motive: &Term, base: Thm, step: Thm) -> Result<Thm> {
    induct_on("n", motive, base, step)
}

/// As [`induct`], but with the induction variable named `ivar`.
fn induct_on(ivar: &str, motive: &Term, base: Thm, step: Thm) -> Result<Thm> {
    let n = var(ivar);
    let base = beta_expand(motive, zero(), base)?; // ⊢ motive 0
    let pn = Term::app(motive.clone(), n.clone());
    let body_n = beta_reduce(Thm::assume(pn.clone())?)?; // {motive n} ⊢ body[n]
    let body_sn = step.imp_elim(body_n)?; //               {motive n} ⊢ body[S n]
    let p_sn = beta_expand(motive, succ(n.clone()), body_sn)?; // {motive n} ⊢ motive (S n)
    let step = p_sn.imp_intro(&pn)?; //                          ⊢ motive n ⟹ motive (S n)
    beta_nf_concl(crate::init::ext::nat_induct(base, step)?)
}

cached_thm! {
    /// `⊢ ∀a b. double (a + b) = double a + double b` — `double` is an
    /// additive homomorphism. Induction on `a` (with `b` quantified in the
    /// motive), from the `double` / `+` recursion laws.
    pub fn double_add() -> Result<Thm> {
        // body[a] ≔ ∀b. double (a + b) = double a + double b
        let body_at = |t: &Term| -> Result<Term> {
            let b = var("b");
            double_app(add(t.clone(), b.clone()))
                .equals(add(double_app(t.clone()), double_app(b)))?
                .forall("b", nat())
        };
        let motive = Term::abs(nat(), subst::close(&body_at(&var("a"))?, "a"));

        // base: ∀b. double (0 + b) = double 0 + double b.
        let base = {
            let b = var("b");
            let l = add_base().all_elim(b.clone())?.cong_arg(double())?; // double(0+b) = double b
            // double 0 + double b = 0 + double b = double b
            let r = cong_add_l(double_zero(), double_app(b.clone()))?
                .trans(add_base().all_elim(double_app(b.clone()))?)?;
            l.trans(r.sym()?)?.all_intro("b", nat())?
        };

        // step: body[a] ⟹ body[S a].
        let a = var("a");
        let ihc = body_at(&a)?;
        let inner = {
            let b = var("b");
            let ih_b = Thm::assume(ihc.clone())?.all_elim(b.clone())?; // double(a+b) = double a + double b

            // LHS: double(S a + b) = S(S(double a + double b)).
            let l1 = add_step().all_elim(a.clone())?.all_elim(b.clone())?.cong_arg(double())?; // double(Sa+b) = double(S(a+b))
            let l2 = double_succ().all_elim(add(a.clone(), b.clone()))?; // double(S(a+b)) = S(S(double(a+b)))
            let l3 = ih_b.cong_arg(nat_succ())?.cong_arg(nat_succ())?; // S(S(double(a+b))) = S(S(double a + double b))
            let lhs = l1.trans(l2)?.trans(l3)?;

            // RHS: double(S a) + double b = S(S(double a + double b)).
            let r0 = cong_add_l(double_succ().all_elim(a.clone())?, double_app(b.clone()))?; // double(Sa)+db = S(S(double a))+db
            let r1 = add_step()
                .all_elim(succ(double_app(a.clone())))?
                .all_elim(double_app(b.clone()))?; // S(S(da))+db = S(S(da)+db)
            let r2 = add_step()
                .all_elim(double_app(a.clone()))?
                .all_elim(double_app(b.clone()))?
                .cong_arg(nat_succ())?; // S(S(da)+db) = S(S(da+db))
            let rhs_chain = r0.trans(r1)?.trans(r2)?;

            lhs.trans(rhs_chain.sym()?)?.all_intro("b", nat())?
        };
        let step = inner.imp_intro(&ihc)?;
        induct_on("a", &motive, base, step)?.all_intro("a", nat())
    }
}

cached_thm! {
    /// `⊢ ∀n. double n = n + n` — the bridge from `double` to repeated
    /// addition (`2·n = n + n`). By induction on `n`.
    pub fn double_eq_add_self() -> Result<Thm> {
        let n = var("n");
        let body = double_app(n.clone()).equals(add(n.clone(), n.clone()))?;
        let motive = Term::abs(nat(), subst::close(&body, "n"));

        // base: double 0 = 0 + 0.
        let base = double_zero().trans(add_base().all_elim(zero())?.sym()?)?;

        // step: (double n = n + n) ⟹ (double (S n) = S n + S n).
        let ihc = double_app(n.clone()).equals(add(n.clone(), n.clone()))?;
        let ih = Thm::assume(ihc.clone())?;
        // double(Sn) = S(S(double n)) = S(S(n+n)).
        let lhs = double_succ()
            .all_elim(n.clone())?
            .trans(ih.cong_arg(nat_succ())?.cong_arg(nat_succ())?)?;
        // S n + S n = S(n + S n) = S(S(n+n)).
        let rhs_chain = add_step()
            .all_elim(n.clone())?
            .all_elim(succ(n.clone()))?
            .trans(add_succ_r().all_elim(n.clone())?.all_elim(n.clone())?.cong_arg(nat_succ())?)?;
        let step = lhs.trans(rhs_chain.sym()?)?.imp_intro(&ihc)?;

        induct(&motive, base, step)
    }
}

fn lt_t(a: Term, b: Term) -> Term {
    Term::app(Term::app(defs::nat_lt(), a), b)
}

cached_thm! {
    /// `⊢ ∀m n. (double m = double n) ⟹ (m = n)` — `double` is injective.
    /// By trichotomy: if `m < n` (or `n < m`) then `double m < double n`
    /// (`add_lt_add` on `double = +`-self), contradicting the equality via
    /// `lt_irrefl`; so `m = n`.
    pub fn double_inj() -> Result<Thm> {
        let (m, n) = (var("m"), var("n"));
        let hyp = double_app(m.clone()).equals(double_app(n.clone()))?; // double m = double n
        let eq_mn = m.clone().equals(n.clone())?; // goal: m = n

        // `p < q ⟹ p = q` reduced to False when `double p = double q`, for
        // the ordered pair `(p, q)` (so `add_lt_add` gives `double p < double q`).
        let contra = |p: &Term, q: &Term| -> Result<Thm> {
            let hpq = lt_t(p.clone(), q.clone());
            // p+p < q+q  (add two copies of p<q).
            let dbl_lt = add_lt_add()
                .all_elim(p.clone())?
                .all_elim(q.clone())?
                .all_elim(p.clone())?
                .all_elim(q.clone())?
                .imp_elim(Thm::assume(hpq.clone())?)?
                .imp_elim(Thm::assume(hpq.clone())?)?; // {p<q} ⊢ p+p < q+q
            // rewrite p+p ↦ double p, q+q ↦ double q.
            let d_lt = dbl_lt
                .rewrite(&double_eq_add_self().all_elim(p.clone())?.sym()?)?
                .rewrite(&double_eq_add_self().all_elim(q.clone())?.sym()?)?; // {p<q} ⊢ double p < double q
            // rewrite with `double m = double n` to collapse to `double n < double n`.
            let dn_lt_dn = d_lt.rewrite(&Thm::assume(hyp.clone())?)?; // {p<q, hyp} ⊢ double n < double n
            let f = lt_irrefl()
                .all_elim(double_app(n.clone()))?
                .not_elim(dn_lt_dn)?; // {p<q, hyp} ⊢ False
            f.false_elim(eq_mn.clone())?.imp_intro(&hpq) // {hyp} ⊢ (p<q) ⟹ (m=n)
        };

        let branch_lt = contra(&m, &n)?; // (m<n) ⟹ (m=n)
        let branch_gt = contra(&n, &m)?; // (n<m) ⟹ (m=n)
        let branch_eq = Thm::assume(eq_mn.clone())?.imp_intro(&eq_mn)?; // (m=n) ⟹ (m=n)

        // trichotomy: m<n ∨ ((m=n) ∨ (n<m)).
        let tri = lt_trichotomy().all_elim(m.clone())?.all_elim(n.clone())?;
        let mid = eq_mn.clone().or(lt_t(n.clone(), m.clone()))?; // (m=n) ∨ (n<m)
        let inner = Thm::assume(mid.clone())?
            .or_elim(branch_eq, branch_gt)?
            .imp_intro(&mid)?; // {hyp} ⊢ mid ⟹ (m=n)
        tri.or_elim(branch_lt, inner)? // {hyp} ⊢ m = n
            .imp_intro(&hyp)?
            .all_intro("n", nat())?
            .all_intro("m", nat())
    }
}

// ============================================================================
// `nat_of_bits : list bool → nat` — the little-endian bit fold. The bridge
// to the `list bool ≅ nat` bitstring isomorphism (stage NP3).
// ============================================================================

/// `λb:bool. λacc:nat. cond b (bit1 acc) (bit0 acc)` — the fold step: a
/// `true` head contributes an odd digit, a `false` head an even one, over
/// the (already-folded) tail value `acc`.
fn bit_step() -> Term {
    let acc = var("acc");
    let b = Term::free("b", boolt());
    let cnd = Term::app(
        Term::app(Term::app(cond(nat()), b.clone()), bit1(acc.clone())),
        bit0(acc.clone()),
    );
    let lam_acc = Term::abs(nat(), subst::close(&cnd, "acc"));
    Term::abs(boolt(), subst::close(&lam_acc, "b"))
}

/// `nat_of_bits : list bool → nat` ≡ `foldr (λb acc. if b then bit1 acc
/// else bit0 acc) 0` — reads a `list bool` **little-endian** (head = least
/// significant bit).
pub fn nat_of_bits() -> Term {
    Term::app(Term::app(list_foldr(boolt(), nat()), bit_step()), zero())
}

/// `nat_of_bits bs` applied.
pub fn nat_of_bits_app(bs: Term) -> Term {
    Term::app(nat_of_bits(), bs)
}

/// `cons b bs : list bool`.
pub(crate) fn cons_bool(b: Term, bs: Term) -> Result<Term> {
    defs::cons(boolt()).apply(b)?.apply(bs)
}

pub fn nat_of_bits_nil() -> Result<Thm> {
    // nat_of_bits nil = foldr bit_step 0 nil = 0.
    foldr_nil(&boolt(), &nat(), &bit_step(), &zero())
}

/// `⊢ nat_of_bits (cons b bs) = cond b (bit1 (nat_of_bits bs))
/// (bit0 (nat_of_bits bs))` — the general (unresolved-`cond`) cons clause.
pub fn nat_of_bits_cons(b: Term, bs: Term) -> Result<Thm> {
    let fc = foldr_cons(&boolt(), &nat(), &bit_step(), &zero(), &b, &bs)?; // = bit_step b (nat_of_bits bs)
    let red = rhs(&fc).reduce()?; // bit_step b (nob) = cond b (bit1 nob) (bit0 nob)
    fc.trans(red)
}

/// `⊢ nat_of_bits (cons true bs) = bit1 (nat_of_bits bs)`.
pub fn nat_of_bits_cons_true(bs: Term) -> Result<Thm> {
    let nob = nat_of_bits_app(bs.clone());
    let general = nat_of_bits_cons(covalence_hol_eval::mk_bool(true), bs)?;
    general.trans(cond_true(&nat(), &bit1(nob.clone()), &bit0(nob))?)
}

/// `⊢ nat_of_bits (cons false bs) = bit0 (nat_of_bits bs)`.
pub fn nat_of_bits_cons_false(bs: Term) -> Result<Thm> {
    let nob = nat_of_bits_app(bs.clone());
    let general = nat_of_bits_cons(covalence_hol_eval::mk_bool(false), bs)?;
    general.trans(cond_false(&nat(), &bit1(nob.clone()), &bit0(nob))?)
}

// ============================================================================
// The representation theorem: `nat_of_bits` is surjective, so *every* nat has
// a binary (bit-list) representation. Proved by `nat`-induction on the value,
// using an **increment lemma** over the bit list (`inc_lemma`, by
// `list`-induction on the bits).
// ============================================================================

/// `list bool` — the bitstring type.
fn lbool() -> Type {
    defs::list(boolt())
}

/// `∃w:list bool. nat_of_bits w = v` — the "`v` has a binary form" predicate,
/// as a term.
fn exists_bits_eq(v: &Term) -> Result<Term> {
    let w = Term::free("w", lbool());
    nat_of_bits_app(w).equals(v.clone())?.exists("w", lbool())
}

/// `λw. nat_of_bits w = v` — the ∃-predicate for [`exists_bits_eq`].
fn bits_pred(v: &Term) -> Result<Term> {
    let w = Term::free("w", lbool());
    let body = nat_of_bits_app(w).equals(v.clone())?;
    Ok(Term::abs(lbool(), subst::close(&body, "w")))
}

/// `⊢ ∃w. nat_of_bits w = v` from a witness `wit` and `⊢ nat_of_bits wit = v`.
fn exists_bits_intro(v: &Term, wit: Term, proof: Thm) -> Result<Thm> {
    let pred = bits_pred(v)?;
    let pred_w = pred.clone().apply(wit.clone())?; // (λw. …) wit  — a redex
    let proof_redex = Thm::beta_conv(pred_w)?.sym()?.eq_mp(proof)?; // ⊢ pred wit
    exists_intro(pred, wit, proof_redex)
}

cached_thm! {
    /// `⊢ ∀bs. ∃bs'. nat_of_bits bs' = succ (nat_of_bits bs)` — the
    /// **increment lemma**: every bit list has a "successor" bit list. By
    /// `list`-induction on `bs`, splitting the `cons` head with `bool.cases`:
    /// a `false`/`nil` head flips to `true` (no carry); a `true` head flips to
    /// `false` and recurses on the tail's increment (carry).
    pub fn inc_lemma() -> Result<Thm> {
        // motive P ≔ λbs. ∃bs'. nat_of_bits bs' = succ (nat_of_bits bs).
        let bs = Term::free("bs", lbool());
        let motive = {
            let ex = exists_bits_eq(&succ(nat_of_bits_app(bs.clone())))?;
            Term::abs(lbool(), subst::close(&ex, "bs"))
        };

        // ---- base: P nil. witness `cons true nil` (nat_of_bits = succ 0). ----
        let base = {
            let nnil = nat_of_bits_app(defs::nil(boolt())); // nat_of_bits nil
            let wit = cons_bool(covalence_hol_eval::mk_bool(true), defs::nil(boolt()))?;
            let e_nil = nat_of_bits_nil()?; // nat_of_bits nil = 0
            // double (nat_of_bits nil) = nat_of_bits nil  (both are 0).
            let d_id = e_nil
                .clone()
                .cong_arg(double())?
                .trans(double_zero())?
                .trans(e_nil.sym()?)?;
            // nat_of_bits (cons true nil) = bit1 (nat_of_bits nil) = succ (double …)
            let proof = nat_of_bits_cons_true(defs::nil(boolt()))?
                .trans(d_id.cong_arg(nat_succ())?)?; // = succ (nat_of_bits nil)
            let base_ex = exists_bits_intro(&succ(nnil), wit, proof)?; // ⊢ ∃bs'. … = succ(nat_of_bits nil)
            beta_expand(&motive, defs::nil(boolt()), base_ex)? // ⊢ P nil  (redex form)
        };

        // ---- cons_case: ∀b bs. P bs ⟹ P (cons b bs). ----
        let b = Term::free("b", boolt());
        let cons_case = {
            let consbb = cons_bool(b.clone(), bs.clone())?; // cons b bs
            let ante = Term::app(motive.clone(), bs.clone()); // P bs  (redex)
            let ih = beta_reduce(Thm::assume(ante.clone())?)?; // {P bs} ⊢ ∃bs'. … = succ(nat_of_bits bs)
            let goal = exists_bits_eq(&succ(nat_of_bits_app(consbb.clone())))?; // P (cons b bs) reduced
            let nob_bs = nat_of_bits_app(bs.clone());

            // The ∃-predicate carried by the IH: λbs'. nat_of_bits bs' = succ(nat_of_bits bs).
            let ih_pred = bits_pred(&succ(nob_bs.clone()))?;
            let bsp = Term::free("bs'", lbool());
            let pred_bsp = ih_pred.apply(bsp.clone())?; // redex
            let hprime = Thm::beta_conv(pred_bsp.clone())?
                .eq_mp(Thm::assume(pred_bsp.clone())?)?; // {pred bs'} ⊢ nat_of_bits bs' = succ(nat_of_bits bs)

            // b = true (carry): witness `cons false bs'`.
            let branch_t = {
                let hbt = Thm::assume(b.clone().equals(covalence_hol_eval::mk_bool(true))?)?; // {b=T}
                // nat_of_bits (cons b bs) = bit1 (nat_of_bits bs)   (via cons_true, b↦true).
                let cb = nat_of_bits_cons_true(bs.clone())?.rewrite(&hbt.clone().sym()?)?;
                // succ (nat_of_bits (cons b bs)) = succ (succ (double (nat_of_bits bs))).
                let rhs_bridge = cb.cong_arg(nat_succ())?;
                // nat_of_bits (cons false bs') = double (nat_of_bits bs')
                //   = double (succ (nat_of_bits bs)) = succ (succ (double (nat_of_bits bs))).
                let lhs = nat_of_bits_cons_false(bsp.clone())?
                    .trans(hprime.clone().cong_arg(double())?)?
                    .trans(double_succ().all_elim(nob_bs.clone())?)?;
                let proof = lhs.trans(rhs_bridge.sym()?)?; // = succ (nat_of_bits (cons b bs))
                let wit = cons_bool(covalence_hol_eval::mk_bool(false), bsp.clone())?;
                let concl = exists_bits_intro(&succ(nat_of_bits_app(consbb.clone())), wit, proof)?; // {pred bs', b=T} ⊢ goal
                let step = concl.imp_intro(&pred_bsp)?.all_intro("bs'", lbool())?; // {b=T} ⊢ ∀bs'. pred bs' ⟹ goal
                exists_elim(ih.clone(), goal.clone(), step)? // {P bs, b=T} ⊢ goal
                    .imp_intro(&b.clone().equals(covalence_hol_eval::mk_bool(true))?)? // {P bs} ⊢ (b=T) ⟹ goal
            };

            // b = false (no carry): witness `cons true bs`.
            let branch_f = {
                let hbf = Thm::assume(b.clone().equals(covalence_hol_eval::mk_bool(false))?)?; // {b=F}
                // nat_of_bits (cons b bs) = bit0 (nat_of_bits bs) = double (nat_of_bits bs).
                let cb = nat_of_bits_cons_false(bs.clone())?.rewrite(&hbf.clone().sym()?)?;
                let rhs_bridge = cb.cong_arg(nat_succ())?; // succ(nat_of_bits(cons b bs)) = succ(double(nat_of_bits bs))
                // nat_of_bits (cons true bs) = bit1 (nat_of_bits bs) = succ (double (nat_of_bits bs)).
                let lhs = nat_of_bits_cons_true(bs.clone())?;
                let proof = lhs.trans(rhs_bridge.sym()?)?; // = succ (nat_of_bits (cons b bs))
                let wit = cons_bool(covalence_hol_eval::mk_bool(true), bs.clone())?;
                exists_bits_intro(&succ(nat_of_bits_app(consbb.clone())), wit, proof)? // {b=F} ⊢ goal
                    .imp_intro(&b.clone().equals(covalence_hol_eval::mk_bool(false))?)? // ⊢ (b=F) ⟹ goal
            };

            let combined = bool_cases()
                .all_elim(b.clone())?
                .or_elim(branch_t, branch_f)?; // {P bs} ⊢ goal
            let p_cons = beta_expand(&motive, consbb, combined)?; // {P bs} ⊢ P (cons b bs)
            p_cons
                .imp_intro(&ante)? // ⊢ P bs ⟹ P (cons b bs)
                .all_intro("bs", lbool())?
                .all_intro("b", boolt())? // ⊢ ∀b bs. P bs ⟹ P (cons b bs)
        };

        list_induct(&boolt(), &motive, base, cons_case)
    }
}

cached_thm! {
    /// `⊢ ∀n. ∃bs. nat_of_bits bs = n` — **the representation theorem**:
    /// `nat_of_bits` is surjective, so every `nat` is `nat_of_bits` of some
    /// bit list. By `nat`-induction on `n`: `0` is `nat_of_bits nil`, and the
    /// successor step consumes the previous witness through [`inc_lemma`].
    pub fn nat_of_bits_surjective() -> Result<Thm> {
        let n = var("n");
        // motive Q ≔ λn. ∃bs. nat_of_bits bs = n.
        let motive = {
            let ex = exists_bits_eq(&n)?;
            Term::abs(nat(), subst::close(&ex, "n"))
        };

        // base: ∃bs. nat_of_bits bs = 0  (witness nil).
        let base = exists_bits_intro(&zero(), defs::nil(boolt()), nat_of_bits_nil()?)?;

        // step: (∃bs. nat_of_bits bs = n) ⟹ (∃bs. nat_of_bits bs = succ n).
        let ex_n = exists_bits_eq(&n)?;
        let ex_sn = exists_bits_eq(&succ(n.clone()))?;
        let step = {
            let bs = Term::free("bs", lbool());
            // pred_n bs (redex) ⟹ nat_of_bits bs = n.
            let pred_n_bs = bits_pred(&n)?.apply(bs.clone())?;
            let hn = Thm::beta_conv(pred_n_bs.clone())?
                .eq_mp(Thm::assume(pred_n_bs.clone())?)?; // {pred_n bs} ⊢ nat_of_bits bs = n

            // inc_lemma at bs: ∃bs'. nat_of_bits bs' = succ (nat_of_bits bs).
            let inc_at = beta_reduce(inc_lemma().all_elim(bs.clone())?)?;
            let inc_pred = bits_pred(&succ(nat_of_bits_app(bs.clone())))?;
            let bsp = Term::free("bs'", lbool());
            let pred_bsp = inc_pred.apply(bsp.clone())?;
            let hprime = Thm::beta_conv(pred_bsp.clone())?
                .eq_mp(Thm::assume(pred_bsp.clone())?)?; // {pred bs'} ⊢ nat_of_bits bs' = succ(nat_of_bits bs)
            let hprime2 = hprime.rewrite(&hn)?; // {pred bs', pred_n bs} ⊢ nat_of_bits bs' = succ n
            let inner = exists_bits_intro(&succ(n.clone()), bsp.clone(), hprime2)?;
            let step2 = inner.imp_intro(&pred_bsp)?.all_intro("bs'", lbool())?; // {pred_n bs} ⊢ ∀bs'. …
            let from_inc = exists_elim(inc_at, ex_sn.clone(), step2)?; // {pred_n bs} ⊢ ∃bs. … = succ n
            let outer_step = from_inc.imp_intro(&pred_n_bs)?.all_intro("bs", lbool())?; // ⊢ ∀bs. pred_n bs ⟹ ex_sn
            exists_elim(Thm::assume(ex_n.clone())?, ex_sn.clone(), outer_step)?
                .imp_intro(&ex_n)? // ⊢ ex_n ⟹ ex_sn
        };
        let _ = &motive;
        induct(&motive, base, step)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `succ` applied `k` times to `0` — the numeral in *unary* HOL-only
    /// form (no `nat` literal), which is what the recursion laws produce.
    fn succn(k: u32) -> Term {
        let mut t = zero();
        for _ in 0..k {
            t = succ(t);
        }
        t
    }

    /// `⊢ double (succn k) = succn (2k)` — by chaining the `double`
    /// recursion laws up from `double 0 = 0`.
    fn eval_double(k: u32) -> Thm {
        let mut thm = double_zero(); // double 0 = 0
        for i in 0..k {
            // thm : double (succn i) = succn (2i)
            let step = double_succ().all_elim(succn(i)).unwrap(); // double(S(succn i)) = S(S(double(succn i)))
            thm = step.rewrite(&thm).unwrap(); // = S(S(succn 2i)) = succn(2(i+1))
        }
        thm
    }

    #[test]
    fn double_laws_are_genuine() {
        for t in [
            double_zero(),
            double_succ(),
            double_add(),
            double_eq_add_self(),
            double_inj(),
        ] {
            assert!(
                t.hyps().is_empty(),
                "double law must be axiom-free: {}",
                t.concl()
            );
        }
    }

    #[test]
    fn double_computes_on_sample_values() {
        // double 3 = 6, double 5 = 10 — in unary succ form, via the laws.
        let e3 = eval_double(3);
        assert!(e3.hyps().is_empty());
        assert_eq!(rhs(&e3), succn(6), "double 3 = 6");
        assert_eq!(rhs(&eval_double(5)), succn(10), "double 5 = 10");
        assert_eq!(rhs(&eval_double(0)), succn(0), "double 0 = 0");
    }

    #[test]
    fn double_zero_and_succ_shapes() {
        let dz = double_zero();
        let (l, r) = dz.concl().as_eq().unwrap();
        assert_eq!(l, &double_app(zero()));
        assert_eq!(r, &zero());
        // ∀n. double (S n) = S (S (double n))
        let n = var("k");
        let inst = double_succ().all_elim(n.clone()).unwrap();
        let (l, r) = inst.concl().as_eq().unwrap();
        assert_eq!(l, &double_app(succ(n.clone())));
        assert_eq!(r, &succ(succ(double_app(n))));
    }

    #[test]
    fn double_inj_is_usable() {
        // Instantiate at concrete m, n and check the implication shape.
        let (m, n) = (var("m"), var("n"));
        let inst = double_inj()
            .all_elim(m.clone())
            .unwrap()
            .all_elim(n.clone())
            .unwrap();
        let concl = inst.concl();
        // (double m = double n) ⟹ (m = n)
        let (ante, conseq) = concl
            .as_app()
            .and_then(|(f, c)| f.as_app().map(|(_, a)| (a.clone(), c.clone())))
            .unwrap();
        assert!(ante.as_eq().is_some());
        let (cl, cr) = conseq.as_eq().unwrap();
        assert_eq!(cl, &m);
        assert_eq!(cr, &n);
    }

    #[test]
    fn bit_relations_are_genuine() {
        for t in [
            bit0_eq_double(),
            bit1_eq_succ_double(),
            succ_bit0_eq_bit1(),
            bit0_zero(),
            bit0_succ(),
        ] {
            assert!(t.hyps().is_empty());
        }
    }

    #[test]
    fn nat_of_bits_clauses_are_genuine() {
        let bs = Term::free("bs", defs::list(boolt()));
        let nil_eq = nat_of_bits_nil().unwrap();
        assert!(nil_eq.hyps().is_empty());
        assert_eq!(rhs(&nil_eq), zero());
        for t in [
            nat_of_bits_cons(covalence_hol_eval::mk_bool(true), bs.clone()).unwrap(),
            nat_of_bits_cons_true(bs.clone()).unwrap(),
            nat_of_bits_cons_false(bs.clone()).unwrap(),
        ] {
            assert!(t.hyps().is_empty());
        }
        // cons_true / cons_false resolve to bit1 / bit0.
        let ct = nat_of_bits_cons_true(bs.clone()).unwrap();
        assert_eq!(rhs(&ct), bit1(nat_of_bits_app(bs.clone())));
        let cf = nat_of_bits_cons_false(bs.clone()).unwrap();
        assert_eq!(rhs(&cf), bit0(nat_of_bits_app(bs)));
    }

    /// `⊢ bit0 e = succn (2v)` from `⊢ e = succn v`.
    fn eval_bit0(e_eq: &Thm, v: u32) -> Thm {
        e_eq.clone()
            .cong_arg(double())
            .unwrap() // double e = double(succn v)
            .trans(eval_double(v))
            .unwrap() // = succn(2v)
    }

    /// `⊢ bit1 e = succn (2v + 1)` from `⊢ e = succn v`.
    fn eval_bit1(e_eq: &Thm, v: u32) -> Thm {
        eval_bit0(e_eq, v).cong_arg(nat_succ()).unwrap() // succ(bit0 e) = succ(succn 2v)
    }

    #[test]
    fn nat_of_bits_evaluates_little_endian() {
        // [true, false, true] little-endian = 1 + 0·2 + 1·4 = 5.
        let nil_b = defs::nil(boolt());
        let l1 = cons_bool(covalence_hol_eval::mk_bool(true), nil_b.clone()).unwrap(); // [t]
        let l2 = cons_bool(covalence_hol_eval::mk_bool(false), l1.clone()).unwrap(); // [f, t]
        let l3 = cons_bool(covalence_hol_eval::mk_bool(true), l2.clone()).unwrap(); // [t, f, t]

        let e3 = nat_of_bits_cons_true(l2.clone()).unwrap(); // = bit1 (nat_of_bits l2)
        let e2 = nat_of_bits_cons_false(l1.clone()).unwrap();
        let e1 = nat_of_bits_cons_true(nil_b.clone()).unwrap();
        let e0 = nat_of_bits_nil().unwrap();

        let chained = e3
            .rewrite(&e2)
            .unwrap()
            .rewrite(&e1)
            .unwrap()
            .rewrite(&e0)
            .unwrap(); // nat_of_bits l3 = bit1(bit0(bit1 0))
        assert_eq!(
            rhs(&chained),
            bit1(bit0(bit1(zero()))),
            "fold builds the little-endian bit tree"
        );

        // Evaluate the bit tree bottom-up to its unary value: 5.
        let v_bit1_0 = eval_bit1(&Thm::refl(zero()).unwrap(), 0); // bit1 0 = succn 1
        let v_bit0 = eval_bit0(&v_bit1_0, 1); // bit0(bit1 0) = succn 2
        let v_bit1 = eval_bit1(&v_bit0, 2); // bit1(bit0(bit1 0)) = succn 5
        let value = chained.trans(v_bit1).unwrap(); // nat_of_bits l3 = succn 5
        assert!(value.hyps().is_empty());
        assert_eq!(rhs(&value), succn(5), "nat_of_bits [t,f,t] = 5");
        let (l, _) = value.concl().as_eq().unwrap();
        assert_eq!(l, &nat_of_bits_app(l3));
    }

    #[test]
    fn increment_lemma_is_genuine() {
        let thm = inc_lemma();
        assert!(thm.hyps().is_empty(), "inc_lemma must be axiom-free");
        // ⊢ ∀bs. ∃bs'. nat_of_bits bs' = succ (nat_of_bits bs)
        let bs = Term::free("xs", lbool());
        let inst = beta_reduce(thm.all_elim(bs.clone()).unwrap()).unwrap();
        assert!(inst.concl().type_of().unwrap().is_bool());
    }

    #[test]
    fn representation_theorem_is_genuine() {
        let thm = nat_of_bits_surjective();
        assert!(thm.hyps().is_empty(), "surjectivity must be axiom-free");
        // ∀n. ∃bs. nat_of_bits bs = n — instantiate at a concrete n (the
        // `induct` helper already β-normalises the conclusion).
        let inst = thm.all_elim(succ(zero())).unwrap();
        assert!(inst.hyps().is_empty());
        assert!(inst.concl().type_of().unwrap().is_bool());
        // It is the existential `∃bs. nat_of_bits bs = succ 0`.
        assert_eq!(inst.concl(), &exists_bits_eq(&succ(zero())).unwrap());
    }
}
