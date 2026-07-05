//! `stream` theorems: the `defs/stream.rs` catalogue re-exported, plus
//! the computational lemmas for the `stream` newtype — the same
//! abstraction-barrier pattern as [`init::set`].
//!
//! [`init::set`]: mod@crate::init::set
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
// Extensionality — pointwise-equal streams are equal.
// ============================================================================

/// `⊢ s = t`, given `holds_eq : ⊢ streamAt s n = streamAt t n` with `n =
/// Free(name, nat)` not free in `s` / `t` — **stream extensionality**.
///
/// `streamAt = rep` (the newtype's carrier projection), so the pointwise
/// equation is `rep s n = rep t n`; [`fun_ext`](crate::init::cat::fun_ext)
/// lifts it to `rep s = rep t`, and the unconditional round-trip
/// `abs (rep ·) = ·` ([`Thm::spec_abs_rep`]) bridges back to `s = t`.
pub fn ext(alpha: &Type, s: &Term, t: &Term, name: &str, holds_eq: Thm) -> Result<Thm> {
    // δ-unfold `streamAt` on both sides: streamAt s n = rep s n.
    let n = Term::free(name, Type::nat());
    let s_at = at(alpha, s, &n).delta_all(stream_at_spec().symbol())?; // streamAt s n = rep s n
    let t_at = at(alpha, t, &n).delta_all(stream_at_spec().symbol())?; // streamAt t n = rep t n
    let rep_eq = s_at.sym()?.trans(holds_eq)?.trans(t_at)?; // ⊢ rep s n = rep t n

    // fun_ext over the index: rep s = rep t.
    let reps_eq = crate::init::cat::fun_ext(rep_eq, name, &Type::nat())?; // ⊢ rep s = rep t
    // abs (rep s) = abs (rep t).
    let abs = Term::spec_abs(stream_spec(), vec![alpha.clone()]);
    let abs_eq = reps_eq.cong_arg(abs)?; // ⊢ abs (rep s) = abs (rep t)
    // Bridge each side: abs (rep s) = s, abs (rep t) = t.
    let ar_s = Thm::spec_abs_rep(stream_spec(), vec![alpha.clone()], s.clone())?; // abs (rep s) = s
    let ar_t = Thm::spec_abs_rep(stream_spec(), vec![alpha.clone()], t.clone())?; // abs (rep t) = t
    ar_s.sym()?.trans(abs_eq)?.trans(ar_t)
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
// Stream round-trips (the wrapper-side companions of `at_mk`/`const_at`).
// ============================================================================

/// `⊢ streamHead (streamMk f) = f 0`.
pub fn head_mk(alpha: &Type, f: &Term) -> Result<Thm> {
    let built = mk(alpha, f);
    let head_eq = delta_head(&Term::app(stream_head(alpha.clone()), built.clone()))?
        .rhs_conv(|t| t.reduce())?; // ⊢ streamHead (streamMk f) = streamAt (streamMk f) 0
    let at_eq = at_mk(alpha, f, &zero())?; // ⊢ streamAt (streamMk f) 0 = f 0
    head_eq.trans(at_eq)
}

/// `⊢ streamTail (streamConst x) = streamConst x` (extensional, via `ext`).
pub fn tail_const(alpha: &Type, x: &Term) -> Result<Thm> {
    let cst = Term::app(stream_const(alpha.clone()), x.clone());
    let tail = Term::app(stream_tail(alpha.clone()), cst.clone());
    let n = Term::free("n", Type::nat());
    let succ_n = Term::app(covalence_core::defs::nat_succ(), n.clone());
    // streamAt (streamTail (streamConst x)) n = x  vs  streamAt (streamConst x) n = x.
    let lhs_at = tail_at(alpha, &cst, &n)?.trans(const_at(alpha, x, &succ_n)?)?;
    let rhs_at = const_at(alpha, x, &n)?;
    let pointwise = lhs_at.trans(rhs_at.sym()?)?; // ⊢ at (tail cst) n = at cst n  (open at `n`)
    ext(alpha, &tail, &cst, "n", pointwise)
}

/// `⊢ streamMk (λn. streamAt s n) = s` — the round-trip (extensional).
pub fn mk_at(alpha: &Type, s: &Term) -> Result<Thm> {
    let f = Term::abs(Type::nat(), at(alpha, s, &Term::bound(0))); // λn. streamAt s n
    let built = mk(alpha, &f);
    let n = Term::free("n", Type::nat());
    // streamAt (streamMk f) n = f n = streamAt s n.
    let pointwise = at_mk(alpha, &f, &n)?.rhs_conv(|t| t.reduce())?; // open at `n`
    ext(alpha, &built, s, "n", pointwise)
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
    let mut e = Env::empty();
    // Operators (monomorphic at 'a).
    e.define_const("stream_at", ConstDef::Op(stream_at(a.clone())));
    e.define_const("stream_mk", ConstDef::Op(stream_mk(a.clone())));
    e.define_const("stream_const", ConstDef::Op(stream_const(a.clone())));
    e.define_const("stream_head", ConstDef::Op(stream_head(a.clone())));
    e.define_const("stream_tail", ConstDef::Op(stream_tail(a.clone())));
    // Seam: ⊢ ∀(f:nat→'a)(n:nat). streamAt (streamMk f) n = f n.
    let f = Term::free("f", Type::fun(Type::nat(), a.clone()));
    let n = Term::free("n", Type::nat());
    let seam = at_mk(&a, &f, &n)
        .and_then(|t| t.all_intro("n", Type::nat()))
        .and_then(|t| t.all_intro("f", Type::fun(Type::nat(), a)))
        .expect("stream_env: at.mk seam");
    e.define_lemma("at.mk", seam);
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

crate::cov_theory! {
    /// stream lemmas ported to `stream.cov`, over `core` + the `streamprim` env.
    pub mod cov from "stream.cov" {
        import "core" = crate::script::Env::core();
        import "streamprim" = crate::init::stream::stream_env();
        "const.at"   => pub fn const_at_cov;
        "head.const" => pub fn head_const_cov;
        "tail.at"    => pub fn tail_at_cov;
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
        assert!(thm.hyps().is_empty());
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
    fn ext_from_pointwise() {
        // From a *hypothesis-free* pointwise equation `streamAt s n =
        // streamAt s n` (reflexivity, `n` free but not in hyps) conclude
        // s = s — exercising the extensionality machinery end-to-end.
        let s = Term::free("s", stream(alpha()));
        let n = Term::free("n", Type::nat());
        let pointwise = covalence_core::Thm::refl(at(&alpha(), &s, &n)).unwrap(); // ⊢ streamAt s n = streamAt s n
        let thm = ext(&alpha(), &s, &s, "n", pointwise).unwrap();
        assert!(thm.hyps().is_empty());
        let (lhs, rhs) = thm.concl().as_eq().unwrap();
        assert_eq!(lhs, &s);
        assert_eq!(rhs, &s);
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
    fn stream_cov_matches_rust() {
        // Every ported stream lemma must state exactly what the Rust proof states.
        assert_eq!(cov::const_at_cov().concl(), super::const_at_thm().concl());
        assert_eq!(
            cov::head_const_cov().concl(),
            super::head_const_thm().concl()
        );
        assert_eq!(cov::tail_at_cov().concl(), super::tail_at_thm().concl());
    }
}
