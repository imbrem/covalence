//! # `covalence-hol-eval` — the UNTRUSTED reduction driver (zero TCB)
//!
//! THE public API for closed-form literal computation, over the **cert
//! path**: recognize a
//! concrete literal redex ([`Term`] pattern-matching — untrusted), extract
//! the op selector + native argument values, and re-derive the equation
//! through the admitted per-family certificate rules exported by
//! [`covalence_core::seam`] (each computing via the enumerable
//! `covalence-pure-eval` `CanonRule`s), landing back as an ordinary
//! [`Thm`] via [`Thm::from_pure`].
//!
//! Everything here only *composes* already-gated mints (`apply` / `canon` /
//! the ungated equality calculus / the base `eq_mp` / `from_pure`); it can
//! fail, but it cannot forge — the trust story lives entirely in
//! `covalence-core`'s manifest (`docs/deps/core-manifest.txt`) and
//! `covalence-pure-eval`'s (`docs/deps/builtins-manifest.txt`).
//!
//! Surface (semantics pinned by `tests/audit_reduce.rs`, the S8 port of the
//! retired in-kernel audit suite):
//!
//! - [`reduce`] / [`reduce_with`] — single-step closed-form computation
//!   `⊢ t = result` (the `_with` twin keeps the `TrustedCons` sharing seam).
//! - [`prove_true`] — `⊢ t` for a `t` that single-step reduces to `T`.
//! - [`delta`] — definitional unfolding passthrough (still
//!   [`Thm::unfold_term_spec`] until the `defs/` catalogue re-homes).
//! - [`nat_add_thm`] — the S4 toHOL slice driver (symbolic-tier certificate
//!   reified through the admitted toHOL rules and transported with the base
//!   `eq_mp`), kept as the exemplar of the never-materialize pipeline.
//! - [`lit`] — the literal build/recognize facade ([`mk_nat`]/[`as_nat`]/…):
//!   the single peripheral chokepoint that moves when the kernel literal
//!   variants die.

#![forbid(unsafe_code)]

use covalence_core::seam::{
    BytesCert, CoercionCert, CoreLang, CoreProp, FixedWidthCert, IntArithCert, Lit, LitEqCert,
    NatArithCert, PrimFamily, SuccCert, prim_family,
};
use covalence_core::{Error, Result, Term, TermKind, Thm, TrustedCons};
use covalence_pure::{Rule, apply};

pub mod lit;
mod tohol;

pub use lit::{as_blob, as_int, as_nat, kind_name, mk_blob, mk_int, mk_nat};
pub use tohol::nat_add_thm;

/// Unwind an application spine: `((f a) b) c ↦ (f, [a, b, c])`.
fn unwind_app(t: &Term) -> (Term, Vec<Term>) {
    let mut args = Vec::new();
    let mut cursor = t.clone();
    while let TermKind::App(f, x) = cursor.kind() {
        args.push(x.clone());
        let next = f.clone();
        cursor = next;
    }
    args.reverse();
    (cursor, args)
}

/// Apply an admitted `CoreProp`-concluding rule and land it as a [`Thm`].
fn mint<R: Rule<CoreLang, Concl = CoreProp>>(rule: R, input: R::Input) -> Option<Thm> {
    let landed = apply(CoreLang, rule, input).ok()?;
    Thm::from_pure(landed).ok()
}

/// Single-step closed-form computation via the cert path: `⊢ t = result`
/// where `t` is a literal operation applied to all-literal arguments
/// (catalogue, conclusions, and refusals pinned by `tests/audit_reduce.rs`
/// and `tests/catalogue.rs`). Returns `None` for any other shape: it does
/// not reduce subterms or follow β/δ chains.
///
/// The catalogue: HOL `=` over two same-kind literals (equality AND
/// disequality), the primitive `succ`, the `nat.*` / `int.*` / `bytes.*`
/// catalogue ops, the nat↔int/bytes coercions, and the fixed-width `uN`/`sN`
/// ops. Conventions: saturating nat `sub`/`pred`; `n / 0 = 0` and
/// `n mod 0 = n`; fixed-width arithmetic wraps mod `2^width`; oversize
/// `pow`/`shl`/`shr` operands refuse.
pub fn reduce(t: &Term) -> Option<Thm> {
    reduce_with(t, &mut ())
}

/// [`reduce`] interning the result conclusion through a caller-supplied
/// [`TrustedCons`] — the sharing seam, letting a reduction driver thread one
/// cons uniformly through `beta_conv` / `reduce` / `trans`. Pure sharing, no
/// soundness role.
pub fn reduce_with<C: TrustedCons + ?Sized>(t: &Term, cons: &mut C) -> Option<Thm> {
    // Mirror the legacy rule's validation: `reduce` matches purely on shape,
    // so an ill-typed application must be refused up front (the cert rules
    // rebuild the redex from the canonical handle, which would silently
    // repair a wrong `=` type annotation instead of mirroring it).
    t.type_of().ok()?;

    let (head, args) = unwind_app(t);
    let thm = match head.kind() {
        // HOL `=` decided on two closed same-kind literals.
        TermKind::Eq(_) if args.len() == 2 => {
            let a = Lit::from_term(&args[0])?;
            let b = Lit::from_term(&args[1])?;
            mint(LitEqCert, (a, b))?
        }
        // The primitive successor.
        TermKind::Succ if args.len() == 1 => match Lit::from_term(&args[0])? {
            Lit::Nat(n) => mint(SuccCert, n)?,
            _ => return None,
        },
        // Catalogue dispatch by canonical handle (empty type args only —
        // the same restriction as the legacy reducer).
        TermKind::Spec(spec, targs) if targs.is_empty() => {
            let lits: Vec<Lit> = args.iter().map(Lit::from_term).collect::<Option<_>>()?;
            let input = (spec.clone(), lits);
            match prim_family(spec)? {
                PrimFamily::NatArith => mint(NatArithCert, input)?,
                PrimFamily::IntArith => mint(IntArithCert, input)?,
                PrimFamily::Bytes => mint(BytesCert, input)?,
                PrimFamily::Coercion => mint(CoercionCert, input)?,
                PrimFamily::FixedWidth => mint(FixedWidthCert, input)?,
            }
        }
        _ => return None,
    };
    let _ = thm.concl().cons_with(cons);
    Some(thm)
}

/// `⊢ T` — derived through the cert path: `LitEqCert` gives
/// `⊢ (T = T) = T`, `refl` gives `⊢ T = T`, and `eq_mp` concludes `⊢ T`.
fn truth() -> Result<Thm> {
    let bridge = mint(LitEqCert, (Lit::Bool(true), Lit::Bool(true))).ok_or(Error::NotReducible)?; // ⊢ (T = T) = T
    let refl = Thm::refl(Term::bool_lit(true))?; // ⊢ T = T
    bridge.eq_mp(refl) // ⊢ T
}

/// Prove `⊢ t` by single-step evaluation: [`reduce`] `t` and, if it lands on
/// the `T` literal, conclude `⊢ t` (via `⊢ T` and `eq_mp` on the symmetric
/// equation). Errors if `t` does not single-step reduce to `T`.
///
/// This is the single-step twin of the recursive
/// `TermExt::prove_true` in `covalence-init` (which normalises first); it
/// decides one-redex closed goals like `⊢ nat.le ⌜3⌝ ⌜5⌝` or `⊢ ⌜4⌝ = ⌜4⌝`.
pub fn prove_true(t: &Term) -> Result<Thm> {
    let conv = reduce(t).ok_or(Error::NotReducible)?; // ⊢ t = v
    let (_, v) = conv.concl().as_eq().ok_or(Error::NotAnEquation)?;
    if v.as_bool() != Some(true) {
        return Err(Error::ConnectiveRule(format!(
            "prove_true: reduced to `{v}`, not `T`"
        )));
    }
    conv.sym()?.eq_mp(truth()?) // ⊢ T = t, ⊢ T ⇒ ⊢ t
}

/// Definitional unfolding passthrough: `⊢ t = body` for a let-style
/// catalogue spec leaf. Still routed to [`Thm::unfold_term_spec`] — sound
/// definitional unfolding tied to `TermKind::Spec`, which survives until the
/// `defs/` catalogue re-homes as ordinary `define`d constants with stored
/// definitional theorems (then this re-routes without callers moving).
pub fn delta(t: &Term) -> Result<Thm> {
    Thm::unfold_term_spec(t.clone())
}
