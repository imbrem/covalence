//! `set` theorems: the `defs/set.rs` catalogue re-exported, plus a
//! **high-level, implementation-hiding** proof API for sets — mirroring
//! how [`init::logic`] pairs the connective definitions with their
//! proved facts.
//!
//! [`init::logic`]: crate::init::logic
//!
//! ## The abstraction barrier
//!
//! `defs/set.rs` implements `set α` as a `newtype` over the membership
//! predicate `α → bool`, with every operation funnelling through the
//! `abs`/`rep` coercions (named [`set_mk`] / [`set_mem`]). **Downstream
//! set proofs must not see that.** They should reason entirely through
//! two primitives exposed here —
//!
//! - **membership computation** ([`mem_mk`] and the per-operation
//!   [`mem_empty`] / [`mem_singleton`] / [`mem_insert`] / [`mem_union`]
//!   / [`mem_intersect`] / [`mem_diff`] lemmas): `⊢ set.mem x (op …) =
//!   <bool formula>`; and
//! - **extensionality** ([`ext`]): from `⊢ ∀x. mem x s = mem x t`
//!   conclude `⊢ s = t`.
//!
//! Everything else (`union_comm`, …) is derived from those two, and a
//! consumer that stays above this line never mentions `abs`/`rep`. The
//! `newtype` representation could be swapped for a literal-backed
//! builtin without touching a single downstream proof.
//!
//! ## No postulates
//!
//! Unlike [`init::nat`] (whose recursion equations are still postulated
//! pending the recursion theorem), **`init::set` postulates nothing**.
//! The whole API bottoms out in the kernel's witness-free subtype laws
//! [`Thm::spec_abs_rep`] / [`Thm::spec_rep_abs_fwd`] — the round-trip
//! equations for a derived type — so every theorem here is genuine
//! (hypothesis- and oracle-free).
//!
//! [`init::nat`]: crate::init::nat

use covalence_core::defs::Symbol;
use covalence_core::{Error, Result, Term, Thm, Type};

use crate::init::eq::trans_chain;
use crate::init::ext::{TermExt, ThmExt};
use crate::init::logic::{and_sym, or_sym, simp, truth};

// Re-export the `defs/set.rs` term catalogue (the `*_spec` handles stay
// in `covalence_core::defs`, reached via the blanket re-export there).
pub use covalence_core::defs::{
    list_elems, set, set_all, set_any, set_card, set_card_opt, set_diff, set_empty, set_finite,
    set_flatten, set_image, set_insert, set_intersect, set_is_empty, set_mem, set_min, set_mk,
    set_preimage, set_singleton, set_subset, set_union,
};

use covalence_core::defs::{
    set_diff_spec, set_empty_spec, set_insert_spec, set_intersect_spec, set_mem_spec, set_mk_spec,
    set_singleton_spec, set_spec, set_union_spec,
};

// ============================================================================
// Term helpers (private — the public surface is membership lemmas + theorems)
// ============================================================================

/// `set.mem[α] x s : bool` — membership as a builder.
fn mem(alpha: &Type, x: &Term, s: &Term) -> Term {
    Term::app(Term::app(set_mem(alpha.clone()), x.clone()), s.clone())
}

/// `set.union[α] s t : set α`.
fn union(alpha: &Type, s: &Term, t: &Term) -> Term {
    Term::app(Term::app(set_union(alpha.clone()), s.clone()), t.clone())
}

// ============================================================================
// THE SEAM — the only code aware that `set` is a newtype over `α → bool`.
//
// `set.mk = λp. abs p` and `set.mem = λx s. (rep s) x`, so the two
// round-trip equations of the `set` newtype —
//   rep (abs p) = p   (carrier side, used by `mem_mk`)
//   abs (rep s) = s   (wrapper side, used by `ext`)
// — are exactly what membership computation and extensionality need.
// Both come straight from the kernel's subtype laws; `set`'s predicate
// is `λ_. T`, so the conditional `rep`-side law's premise is discharged
// by `truth`.
// ============================================================================

/// Raw `abs : (α → bool) → set α` coercion of the `set` newtype.
fn set_abs(alpha: &Type) -> Term {
    Term::spec_abs(set_spec(), vec![alpha.clone()])
}

/// `⊢ rep (abs p) = p` — the carrier-side round-trip. From the kernel's
/// [`Thm::spec_rep_abs_fwd`] (`⊢ (λ_. T) p ⟹ rep (abs p) = p` for the
/// `set` newtype), discharging the always-true premise via β + [`truth`].
fn rep_abs(alpha: &Type, p: &Term) -> Result<Thm> {
    let fwd = Thm::spec_rep_abs_fwd(set_spec(), vec![alpha.clone()], p.clone())?;
    // `fwd : ⊢ prem ⟹ (rep (abs p) = p)`; peel the antecedent `prem`.
    let (imp_p, _eq) = fwd.concl().as_app().ok_or(Error::NotAnEquation)?;
    let (_imp, prem) = imp_p.as_app().ok_or(Error::NotAnEquation)?;
    // `prem = (λ_. T) p`  →β  `T`; transport `⊢ T` back across it.
    let prem_thm = Thm::beta_conv(prem.clone())?.sym()?.eq_mp(truth())?;
    fwd.imp_elim(prem_thm)
}

/// `⊢ abs (rep s) = s` — the wrapper-side round-trip, straight from the
/// kernel's unconditional [`Thm::spec_abs_rep`].
fn abs_rep(alpha: &Type, s: &Term) -> Result<Thm> {
    Thm::spec_abs_rep(set_spec(), vec![alpha.clone()], s.clone())
}

// ============================================================================
// Foundation: membership computation + extensionality.
// ============================================================================

/// `⊢ set.mem x (set.mk p) = p x` — the defining computation of
/// membership against a predicate-built set. The bridge from the
/// `set.mk` constructor to its membership predicate; every per-operation
/// `mem_*` lemma is this plus a δ/β unfolding of the operation.
pub fn mem_mk(alpha: &Type, x: &Term, p: &Term) -> Result<Thm> {
    // set.mem x (set.mk p):  δ-unfold `set.mem` then `set.mk`, βι-reduce
    // to `(rep (abs p)) x`, then collapse `rep (abs p)` to `p`.
    let mk_p = Term::app(set_mk(alpha.clone()), p.clone());
    let lhs = mem(alpha, x, &mk_p);
    let d_mem = lhs.delta_all(set_mem_spec().symbol())?; // = (λx s. rep s x) x (set.mk p)
    let after_mem = rhs_of(&d_mem)?;
    let d_mk = after_mem.delta_all(set_mk_spec().symbol())?; // unfold the inner set.mk
    let reduced = rhs_of(&d_mk)?.reduce()?; // βι → (rep (abs p)) x
    // `rep (abs p) = p`, lifted to `(rep (abs p)) x = p x` by congruence.
    let cong = rep_abs(alpha, p)?.cong_fn(x.clone())?;
    trans_chain([d_mem, d_mk, reduced, cong])
}

/// **Set extensionality.** From `mem_eq : Γ ⊢ ∀x. set.mem x s = set.mem
/// x t`, conclude `Γ ⊢ s = t`. The companion to [`mem_mk`]: together
/// they are the complete interface to `set`, hiding `abs`/`rep`.
///
/// Derivation (HOL Light's `EQ_EXT` over the newtype): each side's
/// membership is `(rep ·) x`, so `∀x. (rep s) x = (rep t) x`; `abs` +
/// η-contraction give `rep s = rep t`, congruence under `abs` gives
/// `abs (rep s) = abs (rep t)`, and the wrapper round-trip [`abs_rep`]
/// rewrites both sides to `s` and `t`.
pub fn ext(alpha: &Type, s: &Term, t: &Term, mem_eq: Thm) -> Result<Thm> {
    const PT: &str = "_ext_x";
    let v = Term::free(PT, alpha.clone());
    let pointwise = mem_eq.all_elim(v.clone())?; // Γ ⊢ mem v s = mem v t
    // Rewrite each membership to the raw `(rep ·) v`.
    let rep_s = mem_rep(alpha, &v, s)?; // ⊢ mem v s = (rep s) v
    let rep_t = mem_rep(alpha, &v, t)?; // ⊢ mem v t = (rep t) v
    let rep_pointwise = rep_s.sym()?.trans(pointwise)?.trans(rep_t)?; // Γ ⊢ (rep s) v = (rep t) v
    // ABS then η on both sides: rep s = rep t.
    let abstracted = rep_pointwise.abs(PT, alpha.clone())?; // Γ ⊢ (λv. (rep s) v) = (λv. (rep t) v)
    let reps_eq = abstracted
        .lhs_conv(|tm| Thm::eta_conv(tm.clone()))?
        .rhs_conv(|tm| Thm::eta_conv(tm.clone()))?; // Γ ⊢ rep s = rep t
    // Congruence under `abs`, then collapse `abs (rep ·)` on each side.
    let abs_cong = reps_eq.cong_arg(set_abs(alpha))?; // Γ ⊢ abs (rep s) = abs (rep t)
    let s_eq = abs_rep(alpha, s)?; // ⊢ abs (rep s) = s
    let t_eq = abs_rep(alpha, t)?; // ⊢ abs (rep t) = t
    s_eq.sym()?.trans(abs_cong)?.trans(t_eq) // Γ ⊢ s = t
}

/// `⊢ set.mem x s = (rep s) x` — unfold membership to the raw `rep`
/// coercion (no `set.mk` involved, so `s` stays opaque). Internal to the
/// seam.
fn mem_rep(alpha: &Type, x: &Term, s: &Term) -> Result<Thm> {
    let lhs = mem(alpha, x, s);
    let d = lhs.delta_all(set_mem_spec().symbol())?; // = (λx s. rep s x) x s
    d.rhs_conv(|tm| tm.reduce()) // βι → (rep s) x
}

// ============================================================================
// Membership lemmas — the high-level computational surface.
//
// Each says `mem x (op args) = <bool formula>` and is proved uniformly:
// δ-unfold `op` to expose `set.mk pred`, push membership through with
// `mem_mk`, then β-reduce `pred x` to the formula.
// ============================================================================

/// `⊢ set.mem x set.empty = F`.
pub fn mem_empty(alpha: &Type, x: &Term) -> Result<Thm> {
    let st = set_empty(alpha.clone());
    mem_of(alpha, x, &st, set_empty_spec().symbol())
}

/// `⊢ set.mem x (set.singleton a) = (x = a)`.
pub fn mem_singleton(alpha: &Type, x: &Term, a: &Term) -> Result<Thm> {
    let st = Term::app(set_singleton(alpha.clone()), a.clone());
    mem_of(alpha, x, &st, set_singleton_spec().symbol())
}

/// `⊢ set.mem x (set.insert a s) = (x = a ∨ set.mem x s)`.
pub fn mem_insert(alpha: &Type, x: &Term, a: &Term, s: &Term) -> Result<Thm> {
    let st = Term::app(Term::app(set_insert(alpha.clone()), a.clone()), s.clone());
    mem_of(alpha, x, &st, set_insert_spec().symbol())
}

/// `⊢ set.mem x (set.union s t) = (set.mem x s ∨ set.mem x t)`.
pub fn mem_union(alpha: &Type, x: &Term, s: &Term, t: &Term) -> Result<Thm> {
    let st = union(alpha, s, t);
    mem_of(alpha, x, &st, set_union_spec().symbol())
}

/// `⊢ set.mem x (set.intersect s t) = (set.mem x s ∧ set.mem x t)`.
pub fn mem_intersect(alpha: &Type, x: &Term, s: &Term, t: &Term) -> Result<Thm> {
    let st = Term::app(Term::app(set_intersect(alpha.clone()), s.clone()), t.clone());
    mem_of(alpha, x, &st, set_intersect_spec().symbol())
}

/// `⊢ set.mem x (set.diff s t) = (set.mem x s ∧ ¬ set.mem x t)`.
pub fn mem_diff(alpha: &Type, x: &Term, s: &Term, t: &Term) -> Result<Thm> {
    let st = Term::app(Term::app(set_diff(alpha.clone()), s.clone()), t.clone());
    mem_of(alpha, x, &st, set_diff_spec().symbol())
}

/// `⊢ set.mem x st = body[x]`, where `st` δ-unfolds (`op`) and β-reduces
/// to `set.mk (λ. body)`. The shared engine of the `mem_*` lemmas.
fn mem_of(alpha: &Type, x: &Term, st: &Term, op: &dyn Symbol) -> Result<Thm> {
    // st = set.mk pred  (δ-unfold the operation, β-reduce the spine).
    let as_mk = st.delta_all(op)?.rhs_conv(|t| t.reduce())?;
    let mk_pred = rhs_of(&as_mk)?;
    let pred = mk_pred.as_app().ok_or(Error::NotAnEquation)?.1.clone();
    // mem x st = mem x (set.mk pred):
    let mem_head = Term::app(set_mem(alpha.clone()), x.clone());
    let step1 = as_mk.cong_arg(mem_head)?;
    // mem x (set.mk pred) = pred x:
    let step2 = mem_mk(alpha, x, &pred)?;
    // pred x = body[x] by β.
    let step3 = rhs_of(&step2)?.reduce()?;
    trans_chain([step1, step2, step3])
}

// ============================================================================
// Theorems — derived purely through `mem_*` + `ext` (no `abs`/`rep`).
// ============================================================================

/// `⊢ set.union s t = set.union t s` — commutativity of union (free
/// `s`, `t : set 'a`). Pointwise: membership in either side is the same
/// disjunction up to [`or_comm_eq`], so the sets agree by [`ext`].
pub fn union_comm() -> Thm {
    binop_comm(set_union_spec().symbol().label(), or_comm_eq, union).expect("union_comm")
}

/// `⊢ set.intersect s t = set.intersect t s` — commutativity of
/// intersection.
pub fn inter_comm() -> Thm {
    let inter = |a: &Type, s: &Term, t: &Term| {
        Term::app(Term::app(set_intersect(a.clone()), s.clone()), t.clone())
    };
    binop_comm(set_intersect_spec().symbol().label(), and_comm_eq, inter).expect("inter_comm")
}

/// `⊢ set.union s set.empty = s` — the empty set is a right identity for
/// union. Pointwise `mem x (s ∪ ∅) = (mem x s ∨ F) = mem x s`.
pub fn union_empty() -> Thm {
    let alpha = Type::tfree("a");
    let s = Term::free("s", set(alpha.clone()));
    let v = Term::free("x", alpha.clone());
    let empty = set_empty(alpha.clone());
    let st = union(&alpha, &s, &empty);

    // mem x (s ∪ ∅) = (mem x s ∨ mem x ∅)
    let lm = mem_union(&alpha, &v, &s, &empty).expect("union_empty: mem_union");
    // mem x ∅ = F, used to rewrite the right disjunct.
    let me = mem_empty(&alpha, &v).expect("union_empty: mem_empty");
    let with_f = lm.rhs_conv(|t| t.rw_all(&me)).expect("union_empty: rewrite ∅→F");
    // (mem x s ∨ F) = mem x s
    let or_f = simp(&rhs_of_owned(&with_f)).expect("union_empty: simp ∨F");
    let mem_eq = with_f.trans(or_f).expect("union_empty: chain");

    let all = mem_eq.all_intro("x", alpha.clone()).expect("union_empty: ∀x");
    ext(&alpha, &st, &s, all).expect("union_empty: ext")
}

/// Generic commutativity proof for a pointwise binary set operation
/// `op` whose membership is `combine (mem x s) (mem x t)`, given the
/// connective's commutativity-as-equation `comm_eq`.
fn binop_comm(
    op_label: &str,
    comm_eq: fn(Term, Term) -> Result<Thm>,
    build: impl Fn(&Type, &Term, &Term) -> Term,
) -> Result<Thm> {
    let alpha = Type::tfree("a");
    let sa = set(alpha.clone());
    let s = Term::free("s", sa.clone());
    let t = Term::free("t", sa.clone());
    let v = Term::free("x", alpha.clone());

    let mem_op = |s: &Term, t: &Term| mem_binop(&alpha, &v, s, t, op_label);
    let lm = mem_op(&s, &t)?; // mem x (op s t) = combine (mem x s) (mem x t)
    let rm = mem_op(&t, &s)?; // mem x (op t s) = combine (mem x t) (mem x s)
    let cc = comm_eq(mem(&alpha, &v, &s), mem(&alpha, &v, &t))?; // combine swap
    let mem_eq = trans_chain([lm, cc, rm.sym()?])?; // mem x (op s t) = mem x (op t s)

    let all = mem_eq.all_intro("x", alpha.clone())?;
    ext(&alpha, &build(&alpha, &s, &t), &build(&alpha, &t, &s), all)
}

/// Dispatch a pointwise binary-op membership lemma by the operation's
/// catalogue label (used by [`binop_comm`], which is generic over the op).
fn mem_binop(alpha: &Type, x: &Term, s: &Term, t: &Term, op_label: &str) -> Result<Thm> {
    match op_label {
        l if l == set_union_spec().symbol().label() => mem_union(alpha, x, s, t),
        l if l == set_intersect_spec().symbol().label() => mem_intersect(alpha, x, s, t),
        l if l == set_diff_spec().symbol().label() => mem_diff(alpha, x, s, t),
        other => Err(Error::ConnectiveRule(format!(
            "mem_binop: unsupported set operation `{other}`"
        ))),
    }
}

// ============================================================================
// Connective commutativity as equations (helpers shared by the theorems).
// ============================================================================

/// `⊢ (p ∨ q) = (q ∨ p)` — disjunction commutativity as an equation,
/// from the two directions of [`or_sym`] via `deduct_antisym`.
fn or_comm_eq(p: Term, q: Term) -> Result<Thm> {
    let pq = p.clone().or(q.clone())?;
    let qp = q.or(p)?;
    let fwd = or_sym(Thm::assume(pq.clone())?)?; // {p∨q} ⊢ q∨p
    let bwd = or_sym(Thm::assume(qp.clone())?)?; // {q∨p} ⊢ p∨q
    bwd.deduct_antisym(fwd) // ⊢ (p∨q) = (q∨p)
}

/// `⊢ (p ∧ q) = (q ∧ p)` — conjunction commutativity as an equation.
fn and_comm_eq(p: Term, q: Term) -> Result<Thm> {
    let pq = p.clone().and(q.clone())?;
    let qp = q.and(p)?;
    let fwd = and_sym(Thm::assume(pq.clone())?)?; // {p∧q} ⊢ q∧p
    let bwd = and_sym(Thm::assume(qp.clone())?)?; // {q∧p} ⊢ p∧q
    bwd.deduct_antisym(fwd) // ⊢ (p∧q) = (q∧p)
}

// ============================================================================
// Small accessors.
// ============================================================================

/// The right-hand side of an equational theorem.
fn rhs_of(thm: &Thm) -> Result<Term> {
    Ok(thm.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone())
}

/// The right-hand side of an equational theorem (panicking — for the
/// `expect`-style closed proofs).
fn rhs_of_owned(thm: &Thm) -> Term {
    thm.concl().as_eq().expect("equational theorem").1.clone()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn alpha() -> Type {
        Type::tfree("a")
    }

    fn setvar(name: &str) -> Term {
        Term::free(name, set(alpha()))
    }

    fn elem(name: &str) -> Term {
        Term::free(name, alpha())
    }

    #[test]
    fn mem_mk_computes() {
        // mem x (mk (λy. y = a)) = (x = a).
        let x = elem("x");
        let a = elem("a");
        let pred = Term::abs(alpha(), {
            // λy. y = a  (closed in `y`)
            let y = Term::free("y", alpha());
            covalence_core::subst::close(&y.equals(a.clone()).unwrap(), "y")
        });
        let thm = mem_mk(&alpha(), &x, &pred).unwrap();
        assert!(thm.hyps().is_empty());
        let (lhs, rhs) = thm.concl().as_eq().unwrap();
        let mk_p = Term::app(set_mk(alpha()), pred.clone());
        assert_eq!(lhs, &mem(&alpha(), &x, &mk_p));
        // `mem_mk` lands on the raw application `p x` (β is the caller's
        // job — `mem_of` follows up with a reduce); here `p x = (λy. y=a) x`,
        // which β-reduces to `x = a`.
        assert_eq!(rhs, &Term::app(pred, x.clone()), "membership reduces to `p x`");
        assert_eq!(
            rhs.reduce().unwrap().concl().as_eq().unwrap().1,
            &x.equals(a).unwrap(),
            "`p x` β-reduces to `x = a`"
        );
    }

    #[test]
    fn mem_empty_is_false() {
        let thm = mem_empty(&alpha(), &elem("x")).unwrap();
        assert!(thm.hyps().is_empty() && thm.has_no_obs());
        assert_eq!(rhs_of(&thm).unwrap(), Term::bool_lit(false));
    }

    #[test]
    fn mem_union_is_disjunction() {
        let (x, s, t) = (elem("x"), setvar("s"), setvar("t"));
        let thm = mem_union(&alpha(), &x, &s, &t).unwrap();
        assert!(thm.hyps().is_empty());
        let expected = mem(&alpha(), &x, &s)
            .or(mem(&alpha(), &x, &t))
            .unwrap();
        assert_eq!(rhs_of(&thm).unwrap(), expected);
    }

    #[test]
    fn mem_intersect_is_conjunction() {
        let (x, s, t) = (elem("x"), setvar("s"), setvar("t"));
        let thm = mem_intersect(&alpha(), &x, &s, &t).unwrap();
        let expected = mem(&alpha(), &x, &s)
            .and(mem(&alpha(), &x, &t))
            .unwrap();
        assert_eq!(rhs_of(&thm).unwrap(), expected);
    }

    #[test]
    fn mem_singleton_is_equality() {
        let (x, a) = (elem("x"), elem("a"));
        let thm = mem_singleton(&alpha(), &x, &a).unwrap();
        assert_eq!(rhs_of(&thm).unwrap(), x.equals(a).unwrap());
    }

    #[test]
    fn ext_from_pointwise_membership() {
        // A trivial use of ext: reflexive membership ⟹ s = s.
        let s = setvar("s");
        let v = Term::free("_ext_x", alpha());
        let refl = Thm::refl(mem(&alpha(), &v, &s)).unwrap();
        let all = refl.all_intro("_ext_x", alpha()).unwrap();
        let eq = ext(&alpha(), &s, &s, all).unwrap();
        assert_eq!(eq.concl(), &s.clone().equals(s).unwrap());
    }

    #[test]
    fn union_comm_is_genuine() {
        let thm = union_comm();
        assert!(thm.hyps().is_empty(), "union_comm is proved, not postulated");
        assert!(thm.has_no_obs(), "union_comm is oracle-free");
        let alpha = alpha();
        let s = setvar("s");
        let t = setvar("t");
        let expected = union(&alpha, &s, &t)
            .equals(union(&alpha, &t, &s))
            .unwrap();
        assert_eq!(thm.concl(), &expected);
    }

    #[test]
    fn inter_comm_is_genuine() {
        let thm = inter_comm();
        assert!(thm.hyps().is_empty());
        assert!(thm.has_no_obs());
    }

    #[test]
    fn union_empty_right_identity() {
        let thm = union_empty();
        assert!(thm.hyps().is_empty(), "union_empty is proved");
        assert!(thm.has_no_obs());
        let alpha = alpha();
        let s = setvar("s");
        let expected = union(&alpha, &s, &set_empty(alpha.clone()))
            .equals(s)
            .unwrap();
        assert_eq!(thm.concl(), &expected);
    }
}
