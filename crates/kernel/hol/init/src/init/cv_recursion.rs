//! Course-of-values recursion — **existence**.
//!
//! The recursion dual of [`strong_induct`]:
//! every below-`x`-extensional step functional `F : nat → (nat → 'a) → 'a` has a
//! fixpoint. This is what lets a *function* be **defined** by course-of-values
//! recursion on a `nat` code — the `WfTyCode` / `Typed` / `El` decoders the
//! λ_iter deep embedding needs, and the recursive floor witness the `nat`
//! division facts need.
//!
//! ## Statement
//!
//! With `Hext F := ∀x p q. (∀m. m < x ⟹ p m = q m) ⟹ F x p = F x q`,
//!
//! > [`cv_exists`] :  `⊢ Hext F ⟹ ∃f. ∀n. f n = F n f`     (`F`, `d` free)
//!
//! Paired with [`cv_unique`](crate::init::lambda_iter::cv_unique) (determinacy),
//! this is the full course-of-values recursion theorem.
//!
//! ## Construction — bounded iteration
//!
//! The seed `d : 'a` and the **bounded approximation**
//! `B := natRec (λx. d) (λk g x. F x g) : nat → (nat → 'a)` iterate `F`:
//! `B 0 = (λx. d)` and `B (S k) = (λx. F x (B k))` (`b_succ`). `B j x` is `F`
//! iterated `j` times read off at `x`. Because `F` reads its argument only
//! *below* `x`, the value stabilises once the fuel exceeds `x`:
//!
//! > `key` :  `Hext F ⊢ ∀j m. m < j ⟹ B j m = B (S m) m`
//!
//! proved by course-of-values induction on `j` (the one essential use of
//! `strong_induct`): at a positive `j = S k`, `B j m = F m (B k)` and
//! `B (S m) m = F m (B m)`, and `Hext` collapses them because the two histories
//! `B k` and `B m` agree below `m` — each entry `B k i` / `B m i` (for `i < m`)
//! equals the canonical `B (S i) i` by the strong IH at the smaller fuels
//! `k, m < j`. The fixpoint is then `f := λx. B (S x) x`, and
//! `f n = B (S n) n = F n (B n) = F n f` by `key` (the histories `B n` and `f`
//! agree below `n`).
//!
//! Authored in Rust (not `.cov`): the function-valued `natRec` term algebra is
//! impractical to drive by hand in the script surface.

use covalence_core::{Result, Term, Type, subst};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::defs;
use covalence_hol_eval::derived::DerivedRules;

use crate::init::eq::{beta_expand, beta_nf, beta_nf_concl, beta_reduce};
use crate::init::ext::{TermExt, ThmExt};
use crate::init::lambda_iter::{
    cvrec_rec_succ, nat_lt_le_trans, nat_lt_pred, nat_lt_succ_imp_le, nat_lt_succ_self,
    strong_induct,
};

// ============================================================================
// The construction's terms (schematic in `F`, `d`, and the result type `'a`)
// ============================================================================

fn nat() -> Type {
    Type::nat()
}
fn a_ty() -> Type {
    Type::tfree("a")
}
/// `nat → 'a` — a "history" function.
fn g_ty() -> Type {
    Type::fun(nat(), a_ty())
}
/// `nat → (nat → 'a) → 'a` — the step functional `F`.
fn f_ty() -> Type {
    Type::fun(nat(), Type::fun(g_ty(), a_ty()))
}

fn ff() -> Term {
    Term::free("F", f_ty())
}
fn dd() -> Term {
    Term::free("d", a_ty())
}
fn nvar(s: &str) -> Term {
    Term::free(s, nat())
}
fn succ(n: Term) -> Term {
    Term::app(defs::nat_succ(), n)
}
/// `a < b`.
fn lt(a: Term, b: Term) -> Term {
    Term::app(Term::app(defs::nat_lt(), a), b)
}
/// `F m g` for a history `g`.
fn fapp(m: Term, g: Term) -> Term {
    Term::app(Term::app(ff(), m), g)
}

/// `λx:nat. d` — the natRec base (a constant history).
fn base() -> Term {
    Term::abs(nat(), dd())
}
/// `λk g x. F x g` — the natRec step (drops the previous fuel `k`).
fn step() -> Term {
    let body = Term::app(Term::app(ff(), nvar("x")), Term::free("g", g_ty())); // F x g
    let l1 = Term::abs(nat(), subst::close(&body, "x")); // λx. F x g
    let l2 = Term::abs(g_ty(), subst::close(&l1, "g")); // λg x. F x g
    Term::abs(nat(), subst::close(&l2, "k")) // λk g x. F x g
}
/// `B := natRec base step : nat → (nat → 'a)`.
fn b_term() -> Term {
    Term::app(Term::app(defs::nat_rec(g_ty()), base()), step())
}
/// `B j` (a history).
fn b1(j: Term) -> Term {
    Term::app(b_term(), j)
}
/// `B j m`.
fn b2(j: Term, m: Term) -> Term {
    Term::app(b1(j), m)
}

/// The extensionality hypothesis `Hext F`.
fn hext_term() -> Result<Term> {
    let (x, p, q, m) = (
        nvar("x"),
        Term::free("p", g_ty()),
        Term::free("q", g_ty()),
        nvar("m"),
    );
    let agree = Term::app(p.clone(), m.clone()).equals(Term::app(q.clone(), m.clone()))?; // p m = q m
    let agree = lt(m, x.clone()).imp(agree)?.forall("m", nat())?; // ∀m. m<x ⟹ p m = q m
    let concl = fapp(x.clone(), p.clone()).equals(fapp(x.clone(), q.clone()))?; // F x p = F x q
    agree
        .imp(concl)?
        .forall("q", g_ty())?
        .forall("p", g_ty())?
        .forall("x", nat())
}

// ============================================================================
// B's successor equation
// ============================================================================

/// `⊢ B (S k) m = F m (B k)`.
fn b_succ(k: &Term, m: &Term) -> Result<Thm> {
    // natRec succ at z:=base, s:=step, n:=k :  ⊢ B (S k) = step k (B k)
    let rec = cvrec_rec_succ()
        .all_elim(base())?
        .all_elim(step())?
        .all_elim(k.clone())?;
    let rec_m = rec.cong_fn(m.clone())?; // ⊢ B (S k) m = step k (B k) m
    let rhs_redex = Term::app(
        Term::app(Term::app(step(), k.clone()), b1(k.clone())),
        m.clone(),
    );
    rec_m.trans(beta_nf(rhs_redex)) // β: step k (B k) m  →  F m (B k)
}

// ============================================================================
// Course-of-values induction (Rust driver)
// ============================================================================

/// Prove `⊢ ∀<ivar>. body` by course-of-values induction, where
/// `motive = λ<ivar>. body`. `prove_case(jv, ih)` proves `⊢ body[jv]` given the
/// free induction variable `jv` and the IH `ih : {…} ⊢ ∀m. m < jv ⟹ motive m`.
pub(crate) fn strong_induct_on(
    ivar: &str,
    motive: &Term,
    prove_case: impl FnOnce(&Term, &Thm) -> Result<Thm>,
) -> Result<Thm> {
    let jv = nvar(ivar);
    let m = nvar("m");
    let ih_redex = lt(m.clone(), jv.clone())
        .imp(Term::app(motive.clone(), m.clone()))? // m < jv ⟹ motive m
        .forall("m", nat())?; // ∀m. m < jv ⟹ motive m
    let ih = Thm::assume(ih_redex.clone())?;
    let body_jv = prove_case(&jv, &ih)?; // ⊢ body[jv]
    let p_jv = beta_expand(motive, jv.clone(), body_jv)?; // ⊢ motive jv
    let step = p_jv.imp_intro(&ih_redex)?.all_intro(ivar, nat())?;
    let si = strong_induct().all_elim(motive.clone())?; // ⊢ (strong step) ⟹ ∀n. motive n
    beta_nf_concl(si.imp_elim(step)?)
}

// ============================================================================
// Stabilisation (`key`) and the fixpoint
// ============================================================================

/// `Hext F ⊢ ∀j m. m < j ⟹ B j m = B (S m) m`.
fn key(hext: &Thm) -> Result<Thm> {
    // motive = λj. ∀m. m < j ⟹ B j m = B (S m) m
    let (j, m0) = (nvar("j"), nvar("m"));
    let body_j = lt(m0.clone(), j.clone())
        .imp(b2(j.clone(), m0.clone()).equals(b2(succ(m0.clone()), m0.clone()))?)?
        .forall("m", nat())?;
    let motive = Term::abs(nat(), subst::close(&body_j, "j"));

    strong_induct_on("j", &motive, |jv, ih| {
        // prove  ∀m. m < jv ⟹ B jv m = B (S m) m
        let m = nvar("m");
        let hm = Thm::assume(lt(m.clone(), jv.clone()))?; // m < jv
        // ∃k. jv = S k
        let exk = nat_lt_pred()
            .all_elim(m.clone())?
            .all_elim(jv.clone())?
            .imp_elim(hm.clone())?;
        let goal = b2(jv.clone(), m.clone()).equals(b2(succ(m.clone()), m.clone()))?;
        let elim_step = {
            let k = nvar("k");
            // exists_elim wants the step's antecedent as `pred k` (a β-redex);
            // assume that, β-reduce to the usable `jv = S k`.
            let pred = exk.concl().as_app().expect("∃ is an application").1.clone();
            let hk_redex = Term::app(pred, k.clone());
            let hk = beta_reduce(Thm::assume(hk_redex.clone())?)?; // ⊢ jv = S k
            key_case(&m, &k, &hk, &hm, ih, hext)?
                .imp_intro(&hk_redex)?
                .all_intro("k", nat())?
        };
        crate::init::logic::exists_elim(exk, goal, elim_step)? // ⊢ B jv m = B (S m) m
            .imp_intro(&lt(m.clone(), jv.clone()))?
            .all_intro("m", nat())
    })
}

/// The body of `key`'s strong step, with the predecessor `k` (`jv = S k`)
/// exposed. Proves `⊢ B jv m = B (S m) m`.
#[allow(clippy::too_many_arguments)]
fn key_case(
    m: &Term,
    k: &Term,
    hk: &Thm, // ⊢ jv = S k  (so the goal's `jv` rides in via `hk`)
    hm: &Thm, // ⊢ m < jv
    ih: &Thm, // ⊢ ∀m'. m' < jv ⟹ motive m'
    hext: &Thm,
) -> Result<Thm> {
    // m < S k, hence m ≤ k.
    let m_lt_sk = Thm::refl(Term::app(defs::nat_lt(), m.clone()))?
        .mk_comb(hk.clone())? // (lt m) jv = (lt m) (S k)
        .eq_mp(hm.clone())?; // ⊢ m < S k
    let m_le_k = nat_lt_succ_imp_le()
        .all_elim(m.clone())?
        .all_elim(k.clone())?
        .imp_elim(m_lt_sk)?; // ⊢ m ≤ k

    // k < jv  (from jv = S k and k < S k).
    let k_lt_sk = nat_lt_succ_self().all_elim(k.clone())?; // ⊢ k < S k
    let k_lt_jv = Thm::refl(Term::app(defs::nat_lt(), k.clone()))?
        .mk_comb(hk.clone().sym()?)? // ⊢ (k < S k) = (k < jv)
        .eq_mp(k_lt_sk)?; // ⊢ k < jv

    // LHS: B jv m = B (S k) m = F m (B k).
    let lhs = Thm::refl(b_term())?
        .mk_comb(hk.clone())? // B jv = B (S k)
        .cong_fn(m.clone())? // B jv m = B (S k) m
        .trans(b_succ(k, m)?)?; // ⊢ B jv m = F m (B k)

    // agree below m:  ∀i. i < m ⟹ B k i = B m i.
    let agree = {
        let i = nvar("i");
        let hi = Thm::assume(lt(i.clone(), m.clone()))?; // i < m
        let i_lt_k = nat_lt_le_trans()
            .all_elim(i.clone())?
            .all_elim(m.clone())?
            .all_elim(k.clone())?
            .imp_elim(hi.clone())?
            .imp_elim(m_le_k.clone())?; // i < k
        // B k i = B (S i) i  (IH at k)
        let bk_i = ih_at(ih, k, &k_lt_jv, &i, &i_lt_k)?;
        // B m i = B (S i) i  (IH at m)
        let bm_i = ih_at(ih, m, hm, &i, &hi)?;
        bk_i.trans(bm_i.sym()?)? // ⊢ B k i = B m i
            .imp_intro(&lt(i.clone(), m.clone()))?
            .all_intro("i", nat())?
    };
    // Hext at (m, B k, B m):  F m (B k) = F m (B m).
    let hext_eq = hext
        .clone()
        .all_elim(m.clone())?
        .all_elim(b1(k.clone()))?
        .all_elim(b1(m.clone()))?
        .imp_elim(agree)?; // ⊢ F m (B k) = F m (B m)

    // RHS: B (S m) m = F m (B m).
    let rhs = b_succ(m, m)?; // ⊢ B (S m) m = F m (B m)

    lhs.trans(hext_eq)?.trans(rhs.sym()?) // ⊢ B jv m = B (S m) m
}

/// From `ih : ⊢ ∀m'. m' < jv ⟹ motive m'`, the fuel `fuel` with
/// `fuel_lt : ⊢ fuel < jv`, and `i` with `i_lt : ⊢ i < fuel`, derive
/// `⊢ B fuel i = B (S i) i`.
fn ih_at(ih: &Thm, fuel: &Term, fuel_lt: &Thm, i: &Term, i_lt: &Thm) -> Result<Thm> {
    let motive_fuel = ih
        .clone()
        .all_elim(fuel.clone())?
        .imp_elim(fuel_lt.clone())?; // ⊢ motive fuel  (β-redex)
    beta_reduce(motive_fuel)? // ⊢ ∀i'. i' < fuel ⟹ B fuel i' = B (S i') i'
        .all_elim(i.clone())?
        .imp_elim(i_lt.clone()) // ⊢ B fuel i = B (S i) i
}

// ============================================================================
// The fixpoint and ∃-introduction
// ============================================================================

/// `f := λx. B (S x) x`.
fn f_term() -> Term {
    Term::abs(nat(), subst::close(&b2(succ(nvar("x")), nvar("x")), "x"))
}

/// The **explicit fixpoint witness** `f := λx. B (S x) x` — schematic in the step
/// functional `F` and seed `d` (both free). Instantiating `F`/`d`/`'a` at a
/// concrete recursion gives a closed, **choice-free** term that *is* the
/// course-of-values-recursive function (used to define `nat.div` directly,
/// rather than ε-selecting it). Pair with [`cv_fixpoint`] for its recurrence.
pub fn cv_witness() -> Term {
    f_term()
}

/// `⊢ Hext F ⟹ ∀n. f n = F n f` — the recurrence satisfied by the **explicit**
/// witness [`cv_witness`] (schematic in `F`, `d`). Unlike [`cv_exists`] this does
/// not `∃`-introduce, so the equation is about the concrete term: instantiate at
/// a recursion and discharge `Hext` to read off the computation rule.
pub fn cv_fixpoint() -> Result<Thm> {
    let hext = Thm::assume(hext_term()?)?;
    let fix = fixpoint(&hext, &key(&hext)?)?; // {Hext} ⊢ ∀n. f n = F n f
    fix.imp_intro(&hext_term()?) // ⊢ Hext ⟹ ∀n. f n = F n f
}

/// `Hext F ⊢ ∀n. f n = F n f`.
fn fixpoint(hext: &Thm, key: &Thm) -> Result<Thm> {
    let n = nvar("n");
    // f n = B (S n) n
    let fn_eq = Thm::beta_conv(Term::app(f_term(), n.clone()))?; // ⊢ f n = B (S n) n
    let bsn = b_succ(&n, &n)?; // ⊢ B (S n) n = F n (B n)

    // agree below n:  ∀i. i < n ⟹ B n i = f i.
    let agree = {
        let i = nvar("i");
        let hi = Thm::assume(lt(i.clone(), n.clone()))?; // i < n
        let bn_i = key
            .clone()
            .all_elim(n.clone())?
            .all_elim(i.clone())?
            .imp_elim(hi.clone())?; // ⊢ B n i = B (S i) i
        let fi = Thm::beta_conv(Term::app(f_term(), i.clone()))?; // ⊢ f i = B (S i) i
        bn_i.trans(fi.sym()?)? // ⊢ B n i = f i
            .imp_intro(&lt(i.clone(), n.clone()))?
            .all_intro("i", nat())?
    };
    let hext_eq = hext
        .clone()
        .all_elim(n.clone())?
        .all_elim(b1(n.clone()))?
        .all_elim(f_term())?
        .imp_elim(agree)?; // ⊢ F n (B n) = F n f

    fn_eq
        .trans(bsn)?
        .trans(hext_eq)? // ⊢ f n = F n f
        .all_intro("n", nat())
}

/// `⊢ Hext F ⟹ ∃f. ∀n. f n = F n f` (`F`, `d` free — the schematic
/// course-of-values recursion theorem).
pub fn cv_exists() -> Result<Thm> {
    let hext = Thm::assume(hext_term()?)?;
    let fix = fixpoint(&hext, &key(&hext)?)?; // {Hext} ⊢ ∀n. f n = F n f
    // ∃-intro at pred := λf'. ∀n. f' n = F n f'.
    let fv = Term::free("f", g_ty());
    let pred_body = Term::app(fv.clone(), nvar("n"))
        .equals(fapp(nvar("n"), fv.clone()))?
        .forall("n", nat())?;
    let pred = Term::abs(g_ty(), subst::close(&pred_body, "f"));
    let ex = crate::init::logic::exists_intro(
        pred.clone(),
        f_term(),
        beta_expand(&pred, f_term(), fix)?, // ⊢ pred f
    )?; // {Hext} ⊢ ∃f. ∀n. f n = F n f
    ex.imp_intro(&hext_term()?)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `B (S k) m = F m (B k)` builds with the expected conclusion.
    #[test]
    fn b_succ_shape() {
        let (k, m) = (nvar("k"), nvar("m"));
        let thm = b_succ(&k, &m).expect("b_succ");
        let want = b2(succ(k.clone()), m.clone())
            .equals(fapp(m, b1(k)))
            .unwrap();
        assert_eq!(thm.concl(), &want, "b_succ conclusion");
    }

    /// The full existence theorem `⊢ Hext ⟹ ∃f. ∀n. f n = F n f`.
    #[test]
    fn cv_exists_proves() {
        let thm = cv_exists().expect("cv_exists");
        assert!(thm.hyps().is_empty(), "cv_exists should be closed");
    }
}
