//! `stream` theorems: the `defs/stream.rs` catalogue re-exported, plus
//! the computational lemmas for the `stream` newtype — the same
//! abstraction-barrier pattern as [`init::set`].
//!
//! [`init::set`]: crate::init::set
//!
//! `stream α` is a `newtype` over `nat → α`, with `streamMk = abs` and
//! `streamAt = rep` the round-trip coercions. The single computational
//! primitive exposed here is
//!
//! - [`at_mk`]: `⊢ streamAt (streamMk f) n = f n`
//!
//! — the stream analogue of [`set::mem_mk`](crate::init::set::mem_mk).
//! Every operation lemma ([`const_at`], [`head_const`], …) is this plus
//! a head-only δ-unfolding of the operation, so downstream proofs reason
//! through element access and never touch `abs`/`rep`.
//!
//! This is the first foundation block under `list α := stream (option α)
//! where finite`, hence under `set.finite` / `set.card`.

use covalence_core::{Error, Result, Term, Thm, Type};

use crate::init::eq::{delta_head, trans_chain};
use crate::init::ext::{TermExt, ThmExt};
use crate::init::logic::truth;
use crate::script::{ConstDef, Env};

// Re-export the `defs/stream.rs` term catalogue.
pub use covalence_core::defs::{
    finite, stream, stream_at, stream_const, stream_head, stream_iterate, stream_mk, stream_nth,
    stream_tail,
};

use covalence_core::defs::{stream_at_spec, stream_mk_spec, stream_spec};
use covalence_core::defs::nat_succ;

// ============================================================================
// Term helpers.
// ============================================================================

/// `streamAt[α] s n : α` — element access as a builder.
fn at(alpha: &Type, s: &Term, n: &Term) -> Term {
    Term::app(Term::app(stream_at(alpha.clone()), s.clone()), n.clone())
}

/// `streamMk[α] f : stream α`.
fn mk(alpha: &Type, f: &Term) -> Term {
    Term::app(stream_mk(alpha.clone()), f.clone())
}

// ============================================================================
// THE SEAM — the only code aware that `stream` is a newtype over `nat→α`.
//
// `streamAt = rep` and `streamMk = abs` (both are the bare coercions,
// not lambdas), so the carrier-side round-trip `rep (abs f) = f` — the
// newtype law from the kernel's `spec_rep_abs_fwd`, premise discharged
// by `truth` — is exactly what element access against a built stream
// needs.
// ============================================================================

/// `⊢ rep (abs f) = f` for the `stream` newtype, from the kernel's
/// [`Thm::spec_rep_abs_fwd`] with the always-true premise discharged by
/// β + [`truth`].
fn rep_abs(alpha: &Type, f: &Term) -> Result<Thm> {
    let fwd = Thm::spec_rep_abs_fwd(stream_spec(), vec![alpha.clone()], f.clone())?;
    let (imp_p, _eq) = fwd.concl().as_app().ok_or(Error::NotAnEquation)?;
    let (_imp, prem) = imp_p.as_app().ok_or(Error::NotAnEquation)?;
    let prem_thm = Thm::beta_conv(prem.clone())?.sym()?.eq_mp(truth())?;
    fwd.imp_elim(prem_thm)
}

// ============================================================================
// Foundation: element access against a built stream.
// ============================================================================

/// `⊢ streamAt (streamMk f) n = f n` — the defining computation of
/// stream element access. Every per-operation `*_at` lemma is this plus
/// a δ-unfolding of the operation.
pub fn at_mk(alpha: &Type, f: &Term, n: &Term) -> Result<Thm> {
    // streamAt (streamMk f) n:  δ-unfold streamAt → rep, streamMk → abs,
    // leaving `(rep (abs f)) n`, then collapse `rep (abs f)` to `f`.
    let lhs = at(alpha, &mk(alpha, f), n);
    let d_at = lhs.delta_all(stream_at_spec().symbol())?; // streamAt → rep
    let d_mk = rhs_of(&d_at)?.delta_all(stream_mk_spec().symbol())?; // streamMk → abs
    let collapse = rep_abs(alpha, f)?.cong_fn(n.clone())?; // ⊢ (rep (abs f)) n = f n
    trans_chain([d_at, d_mk, collapse])
}

// ============================================================================
// Stream extensionality — the wrapper-side seam (companion to `at_mk`).
//
// `stream_at = rep` and `stream_mk = abs`, so the wrapper round-trip
// `abs (rep s) = s` (the kernel's unconditional `spec_abs_rep`) is what
// turns "equal at every index" into "equal streams".
// ============================================================================

/// Raw `abs : (nat → α) → stream α` coercion of the `stream` newtype.
fn stream_abs(alpha: &Type) -> Term {
    Term::spec_abs(stream_spec(), vec![alpha.clone()])
}

/// `⊢ abs (rep s) = s` — the wrapper-side round-trip, straight from the
/// kernel's unconditional [`Thm::spec_abs_rep`].
fn abs_rep(alpha: &Type, s: &Term) -> Result<Thm> {
    Thm::spec_abs_rep(stream_spec(), vec![alpha.clone()], s.clone())
}

/// `⊢ stream_at s n = (rep s) n` — δ-unfold element access to the raw
/// `rep` coercion (no `stream_mk` involved, so `s` stays opaque). Since
/// `stream_at` *is* `rep` (the bare coercion, not a lambda), this is a
/// single head δ-step.
fn at_rep(alpha: &Type, s: &Term, n: &Term) -> Result<Thm> {
    delta_head(&at(alpha, s, n))
}

/// **Stream extensionality.** From `at_eq : Γ ⊢ ∀n. stream_at s n =
/// stream_at t n`, conclude `Γ ⊢ s = t`. The companion to [`at_mk`]:
/// together they are the complete element-access interface to `stream`,
/// hiding `abs`/`rep`.
///
/// Derivation (HOL Light's `EQ_EXT` over the newtype): each side's element
/// access is `(rep ·) n`, so `∀n. (rep s) n = (rep t) n`; `abs` +
/// η-contraction give `rep s = rep t`, congruence under `abs` gives
/// `abs (rep s) = abs (rep t)`, and the wrapper round-trip [`abs_rep`]
/// rewrites both sides to `s` and `t`.
pub fn ext(alpha: &Type, s: &Term, t: &Term, at_eq: Thm) -> Result<Thm> {
    const PT: &str = "_ext_n";
    let v = Term::free(PT, Type::nat());
    let pointwise = at_eq.all_elim(v.clone())?; // Γ ⊢ stream_at s v = stream_at t v
    // Rewrite each access to the raw `(rep ·) v`.
    let rep_s = at_rep(alpha, s, &v)?; // ⊢ stream_at s v = (rep s) v
    let rep_t = at_rep(alpha, t, &v)?; // ⊢ stream_at t v = (rep t) v
    let rep_pointwise = rep_s.sym()?.trans(pointwise)?.trans(rep_t)?; // Γ ⊢ (rep s) v = (rep t) v
    // ABS then η on both sides: rep s = rep t.
    let abstracted = rep_pointwise.abs(PT, Type::nat())?; // Γ ⊢ (λv. (rep s) v) = (λv. (rep t) v)
    let reps_eq = abstracted
        .lhs_conv(|tm| Thm::eta_conv(tm.clone()))?
        .rhs_conv(|tm| Thm::eta_conv(tm.clone()))?; // Γ ⊢ rep s = rep t
    // Congruence under `abs`, then collapse `abs (rep ·)` on each side.
    let abs_cong = reps_eq.cong_arg(stream_abs(alpha))?; // Γ ⊢ abs (rep s) = abs (rep t)
    let s_eq = abs_rep(alpha, s)?; // ⊢ abs (rep s) = s
    let t_eq = abs_rep(alpha, t)?; // ⊢ abs (rep t) = t
    s_eq.sym()?.trans(abs_cong)?.trans(t_eq) // Γ ⊢ s = t
}

// ============================================================================
// `*_mk` lemmas — head/tail of a built stream (`at_mk` plus a δ-unfold).
// ============================================================================

/// `⊢ stream_head (stream_mk f) = f 0` — the head of a built stream is
/// `f`'s value at index 0.
pub fn head_mk(alpha: &Type, f: &Term) -> Result<Thm> {
    // stream_head (stream_mk f) = stream_at (stream_mk f) 0 = f 0.
    let built = mk(alpha, f);
    let head_eq = delta_head(&Term::app(stream_head(alpha.clone()), built.clone()))?
        .rhs_conv(|t| t.reduce())?; // ⊢ stream_head (stream_mk f) = stream_at (stream_mk f) 0
    let at_eq = at_mk(alpha, f, &zero())?; // ⊢ stream_at (stream_mk f) 0 = f 0
    head_eq.trans(at_eq)
}

// ============================================================================
// Operation lemmas — head-only δ-unfold then `at_mk`.
// ============================================================================

/// `⊢ streamAt (streamConst x) n = x` — every element of a constant
/// stream is `x`.
pub fn const_at(alpha: &Type, x: &Term, n: &Term) -> Result<Thm> {
    at_of(alpha, n, &Term::app(stream_const(alpha.clone()), x.clone()))
}

/// `⊢ streamHead (streamConst x) = x`.
pub fn head_const(alpha: &Type, x: &Term) -> Result<Thm> {
    // streamHead (streamConst x) = streamAt (streamConst x) 0 = x.
    let cst = Term::app(stream_const(alpha.clone()), x.clone());
    let head_eq = delta_head(&Term::app(stream_head(alpha.clone()), cst.clone()))?
        .rhs_conv(|t| t.reduce())?; // ⊢ streamHead (streamConst x) = streamAt (streamConst x) 0
    let at_eq = const_at(alpha, x, &zero())?; // ⊢ streamAt (streamConst x) 0 = x
    head_eq.trans(at_eq)
}

/// `⊢ streamAt (streamTail s) n = streamAt s (succ n)`.
pub fn tail_at(alpha: &Type, s: &Term, n: &Term) -> Result<Thm> {
    at_of(alpha, n, &Term::app(stream_tail(alpha.clone()), s.clone()))
}

// ============================================================================
// Extensionality applications — stream equalities proved by [`ext`].
// ============================================================================

/// `⊢ stream_tail (stream_const x) = stream_const x` — the tail of a
/// constant stream is the same constant stream. Proved **extensionally**:
/// at every index `n`, both `stream_at (stream_tail (stream_const x)) n`
/// (`= stream_at (stream_const x) (succ n) = x` via [`tail_at`] +
/// [`const_at`]) and `stream_at (stream_const x) n` (`= x` via
/// [`const_at`]) equal `x`; [`ext`] concludes.
pub fn tail_const(alpha: &Type, x: &Term) -> Result<Thm> {
    let cst = Term::app(stream_const(alpha.clone()), x.clone());
    let tail = Term::app(stream_tail(alpha.clone()), cst.clone());
    let n = Term::free("n", Type::nat());
    let succ_n = Term::app(nat_succ(), n.clone());
    // stream_at (stream_tail (stream_const x)) n = x.
    let lhs_at = tail_at(alpha, &cst, &n)? // = stream_at (stream_const x) (succ n)
        .trans(const_at(alpha, x, &succ_n)?)?; // = x
    // stream_at (stream_const x) n = x.
    let rhs_at = const_at(alpha, x, &n)?;
    let pointwise = lhs_at.trans(rhs_at.sym()?)?; // ⊢ at (tail cst) n = at cst n
    let all = pointwise.all_intro("n", Type::nat())?;
    ext(alpha, &tail, &cst, all)
}

/// `⊢ stream_mk (λn. stream_at s n) = s` — the round-trip: a stream is the
/// `stream_mk` of its own element-access function. The `stream_at`/`stream_mk`
/// β/η-newtype identity, proved **extensionally**: at every index `n`,
/// `stream_at (stream_mk (λk. stream_at s k)) n = (λk. stream_at s k) n =
/// stream_at s n` (via [`at_mk`] + β), so the two streams agree everywhere
/// and [`ext`] concludes.
pub fn mk_at(alpha: &Type, s: &Term) -> Result<Thm> {
    // f := λn. stream_at s n.
    let n_body = at(alpha, s, &Term::bound(0));
    let f = Term::abs(Type::nat(), n_body);
    let built = mk(alpha, &f);
    let n = Term::free("n", Type::nat());
    // stream_at (stream_mk f) n = f n = stream_at s n.
    let lhs_at = at_mk(alpha, &f, &n)? // = (λk. stream_at s k) n
        .rhs_conv(|t| t.reduce())?; // = stream_at s n
    let all = lhs_at.all_intro("n", Type::nat())?;
    ext(alpha, &built, s, all)
}

/// `⊢ streamAt st n = body[n]`, where the **head** operation of `st`
/// δ-unfolds (its arguments staying opaque) and β-reduces to `streamMk
/// (λ. body)`. The shared engine of the `*_at` lemmas.
fn at_of(alpha: &Type, n: &Term, st: &Term) -> Result<Thm> {
    // st = streamMk f  (δ-unfold ONLY the head op, β-reduce the spine).
    let as_mk = delta_head(st)?.rhs_conv(|t| t.reduce())?;
    let f = rhs_of(&as_mk)?
        .as_app()
        .ok_or(Error::NotAnEquation)?
        .1
        .clone();
    // streamAt st n = streamAt (streamMk f) n:
    let step1 = as_mk
        .cong_arg(stream_at(alpha.clone()))? // ⊢ streamAt st = streamAt (streamMk f)
        .cong_fn(n.clone())?; // ⊢ streamAt st n = streamAt (streamMk f) n
    // streamAt (streamMk f) n = f n:
    let step2 = at_mk(alpha, &f, n)?;
    // f n = body[n] by β.
    let step3 = rhs_of(&step2)?.reduce()?;
    trans_chain([step1, step2, step3])
}

// ============================================================================
// Small helpers.
// ============================================================================

fn rhs_of(thm: &Thm) -> Result<Term> {
    Ok(thm.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone())
}

fn zero() -> Term {
    Term::nat_lit(covalence_types::Nat::zero())
}

// ============================================================================
// .cov proof language support
// ============================================================================

/// The primitives environment for `stream.cov`: the stream operators
/// (monomorphic at `'a`) as `Op` entries, plus the `at_mk` seam lemma —
/// universally quantified over `f : nat→'a` and `n : nat` — as a given.
///
/// `at_mk` uses `spec_rep_abs_fwd` in Rust (TCB-coupled); it stays a given.
/// `const_at`, `head_const`, `tail_at` are proved in `stream.cov` from this.
pub fn stream_env() -> Env {
    let a = Type::tfree("a");
    let nat_to_a = Type::fun(Type::nat(), a.clone());
    let mut e = Env::empty();
    // Operators, registered **polymorphically** (`Poly`): each is a scheme
    // over its element type variable, so a single occurrence can instantiate
    // at a fresh type (e.g. `stream_iterate` mixing carriers). They are used
    // here schematically in one element type, but `Poly` is the honest shape.
    e.define_const("stream_at", ConstDef::Poly(stream_at(a.clone())));
    e.define_const("stream_mk", ConstDef::Poly(stream_mk(a.clone())));
    e.define_const("stream_const", ConstDef::Poly(stream_const(a.clone())));
    e.define_const("stream_head", ConstDef::Poly(stream_head(a.clone())));
    e.define_const("stream_tail", ConstDef::Poly(stream_tail(a.clone())));
    e.define_const("stream_iterate", ConstDef::Poly(stream_iterate(a.clone())));

    let f = Term::free("f", nat_to_a.clone());
    let n = Term::free("n", Type::nat());
    let s = Term::free("s", stream(a.clone()));
    let t = Term::free("t", stream(a.clone()));

    // Seam: ⊢ ∀(f:nat→'a)(n:nat). streamAt (streamMk f) n = f n.
    e.define_lemma(
        "at_mk",
        at_mk(&a, &f, &n)
            .and_then(|t| t.all_intro("n", Type::nat()))
            .and_then(|t| t.all_intro("f", nat_to_a.clone()))
            .expect("stream_env: at_mk seam"),
    );
    // head_mk : ⊢ ∀(f:nat→'a). streamHead (streamMk f) = f 0.
    e.define_lemma(
        "head_mk",
        head_mk(&a, &f)
            .and_then(|t| t.all_intro("f", nat_to_a))
            .expect("stream_env: head_mk"),
    );
    // tail_at : ⊢ ∀(s:stream 'a)(n:nat). streamAt (streamTail s) n
    //                                     = streamAt s (succ n).
    e.define_lemma(
        "tail_at",
        tail_at(&a, &s, &n)
            .and_then(|t| t.all_intro("n", Type::nat()))
            .and_then(|t| t.all_intro("s", stream(a.clone())))
            .expect("stream_env: tail_at"),
    );
    // ext : ⊢ ∀(s t:stream 'a). (∀n. streamAt s n = streamAt t n) ⟹ s = t.
    let h = at(&a, &s, &n)
        .equals(at(&a, &t, &n))
        .unwrap()
        .forall("n", Type::nat())
        .unwrap();
    e.define_lemma(
        "ext",
        ext(&a, &s, &t, Thm::assume(h.clone()).unwrap())
            .and_then(|thm| thm.imp_intro(&h))
            .and_then(|thm| thm.all_intro("t", stream(a.clone())))
            .and_then(|thm| thm.all_intro("s", stream(a.clone())))
            .expect("stream_env: ext"),
    );
    e
}

// Universally-quantified wrappers used by the test to match against the
// per-element Rust proofs.

cached_thm! {
    /// `⊢ ∀(x:'a)(n:nat). streamAt (streamConst x) n = x`
    pub fn const_at_thm() -> Thm {
        let a = Type::tfree("a");
        let x = Term::free("x", a.clone());
        let n = Term::free("n", Type::nat());
        const_at(&a, &x, &n)
            .and_then(|t| t.all_intro("n", Type::nat()))
            .and_then(|t| t.all_intro("x", a))
            .expect("const_at_thm")
    }
}

cached_thm! {
    /// `⊢ ∀(x:'a). streamHead (streamConst x) = x`
    pub fn head_const_thm() -> Thm {
        let a = Type::tfree("a");
        let x = Term::free("x", a.clone());
        head_const(&a, &x)
            .and_then(|t| t.all_intro("x", a))
            .expect("head_const_thm")
    }
}

cached_thm! {
    /// `⊢ ∀(s:stream 'a)(n:nat). streamAt (streamTail s) n = streamAt s (succ n)`
    pub fn tail_at_thm() -> Thm {
        let a = Type::tfree("a");
        let s = Term::free("s", stream(a.clone()));
        let n = Term::free("n", Type::nat());
        tail_at(&a, &s, &n)
            .and_then(|t| t.all_intro("n", Type::nat()))
            .and_then(|t| t.all_intro("s", stream(a)))
            .expect("tail_at_thm")
    }
}

cached_thm! {
    /// `⊢ ∀(f:nat→'a). streamHead (streamMk f) = f 0`
    pub fn head_mk_thm() -> Thm {
        let a = Type::tfree("a");
        let f = Term::free("f", Type::fun(Type::nat(), a.clone()));
        head_mk(&a, &f)
            .and_then(|t| t.all_intro("f", Type::fun(Type::nat(), a)))
            .expect("head_mk_thm")
    }
}

cached_thm! {
    /// `⊢ ∀(x:'a). streamTail (streamConst x) = streamConst x`
    pub fn tail_const_thm() -> Thm {
        let a = Type::tfree("a");
        let x = Term::free("x", a.clone());
        tail_const(&a, &x)
            .and_then(|t| t.all_intro("x", a))
            .expect("tail_const_thm")
    }
}

cached_thm! {
    /// `⊢ ∀(s:stream 'a). streamMk (λn. streamAt s n) = s`
    pub fn mk_at_thm() -> Thm {
        let a = Type::tfree("a");
        let s = Term::free("s", stream(a.clone()));
        mk_at(&a, &s)
            .and_then(|t| t.all_intro("s", stream(a)))
            .expect("mk_at_thm")
    }
}

crate::cov_theory! {
    /// stream lemmas ported to `stream.cov`, over `core` + the `streamprim` env.
    pub mod cov from "stream.cov" {
        import "core" = crate::script::Env::core();
        import "streamprim" = crate::init::stream::stream_env();
        "const_at"     => pub fn const_at_cov;
        "head_const"   => pub fn head_const_cov;
        "tail_at"      => pub fn tail_at_cov;
        "head_mk"      => pub fn head_mk_cov;
        "tail_const"   => pub fn tail_const_cov;
        "mk_at"        => pub fn mk_at_cov;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn alpha() -> Type {
        Type::tfree("a")
    }

    fn nat_lit(n: u32) -> Term {
        Term::nat_lit(covalence_types::Nat::from_inner(n.into()))
    }

    #[test]
    fn at_mk_computes() {
        // streamAt (streamMk f) n = f n, with f a free `nat → α`.
        let f = Term::free("f", Type::fun(Type::nat(), alpha()));
        let n = Term::free("n", Type::nat());
        let thm = at_mk(&alpha(), &f, &n).unwrap();
        assert!(thm.hyps().is_empty() && thm.has_no_obs());
        let (lhs, rhs) = thm.concl().as_eq().unwrap();
        assert_eq!(lhs, &at(&alpha(), &mk(&alpha(), &f), &n));
        assert_eq!(rhs, &Term::app(f, n));
    }

    #[test]
    fn const_at_is_the_element() {
        // streamAt (streamConst x) 5 = x.
        let x = Term::free("x", alpha());
        let thm = const_at(&alpha(), &x, &nat_lit(5)).unwrap();
        assert!(thm.hyps().is_empty());
        assert_eq!(thm.concl().as_eq().unwrap().1, &x);
    }

    #[test]
    fn head_const_is_the_element() {
        let x = Term::free("x", alpha());
        let thm = head_const(&alpha(), &x).unwrap();
        assert!(thm.hyps().is_empty());
        assert_eq!(thm.concl().as_eq().unwrap().1, &x);
    }

    #[test]
    fn tail_at_shifts_by_one() {
        // streamAt (streamTail s) n = streamAt s (succ n).
        let s = Term::free("s", stream(alpha()));
        let n = Term::free("n", Type::nat());
        let thm = tail_at(&alpha(), &s, &n).unwrap();
        assert!(thm.hyps().is_empty());
        // rhs is `streamAt s (succ n)`.
        let succ_n = Term::app(covalence_core::defs::nat_succ(), n.clone());
        assert_eq!(thm.concl().as_eq().unwrap().1, &at(&alpha(), &s, &succ_n));
    }

    #[test]
    fn head_mk_is_f_zero() {
        // stream_head (stream_mk f) = f 0.
        let f = Term::free("f", Type::fun(Type::nat(), alpha()));
        let thm = head_mk(&alpha(), &f).unwrap();
        assert!(thm.hyps().is_empty() && thm.has_no_obs());
        assert_eq!(thm.concl().as_eq().unwrap().1, &Term::app(f, zero()));
    }

    #[test]
    fn tail_const_is_const() {
        // stream_tail (stream_const x) = stream_const x.
        let x = Term::free("x", alpha());
        let thm = tail_const(&alpha(), &x).unwrap();
        assert!(thm.hyps().is_empty() && thm.has_no_obs());
        let cst = Term::app(stream_const(alpha()), x);
        let tail = Term::app(stream_tail(alpha()), cst.clone());
        assert_eq!(thm.concl(), &tail.equals(cst).unwrap());
    }

    #[test]
    fn mk_at_is_roundtrip() {
        // stream_mk (λn. stream_at s n) = s.
        let s = Term::free("s", stream(alpha()));
        let thm = mk_at(&alpha(), &s).unwrap();
        assert!(thm.hyps().is_empty() && thm.has_no_obs());
        assert_eq!(thm.concl().as_eq().unwrap().1, &s);
    }

    #[test]
    fn ext_from_pointwise_access() {
        // A trivial use of ext: reflexive access ⟹ s = s.
        let s = Term::free("s", stream(alpha()));
        let v = Term::free("_ext_n", Type::nat());
        let refl = Thm::refl(at(&alpha(), &s, &v)).unwrap();
        let all = refl.all_intro("_ext_n", Type::nat()).unwrap();
        let eq = ext(&alpha(), &s, &s, all).unwrap();
        assert_eq!(eq.concl(), &s.clone().equals(s).unwrap());
    }

    #[test]
    fn stream_cov_matches_rust() {
        // Every ported stream lemma must state exactly what the Rust proof states.
        assert_eq!(cov::const_at_cov().concl(), super::const_at_thm().concl());
        assert_eq!(
            cov::head_const_cov().concl(),
            super::head_const_thm().concl()
        );
        assert_eq!(cov::tail_at_cov().concl(), super::tail_at_thm().concl());
        assert_eq!(cov::head_mk_cov().concl(), super::head_mk_thm().concl());
        assert_eq!(
            cov::tail_const_cov().concl(),
            super::tail_const_thm().concl()
        );
        assert_eq!(cov::mk_at_cov().concl(), super::mk_at_thm().concl());
    }

    #[test]
    fn new_stream_cov_lemmas_are_genuine() {
        // The newly-proved `.cov` theorems must be genuine, oracle-free.
        for thm in [
            cov::head_mk_cov(),
            cov::tail_const_cov(),
            cov::mk_at_cov(),
        ] {
            assert!(thm.hyps().is_empty(), "new stream lemma must be proved");
            assert!(thm.has_no_obs(), "new stream lemma must be oracle-free");
        }
    }
}
