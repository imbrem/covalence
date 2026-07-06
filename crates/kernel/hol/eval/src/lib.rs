//! # `covalence-hol-eval` — the **eval tier** (`CoreEval`) + reduction drivers
//!
//! This crate owns [`CoreEval`], the language extending
//! [`CoreLang`](covalence_core::seam::CoreLang) with the computation-backed
//! certificate and toHOL rules (stage E2 of
//! `notes/vibes/handoff/defs-out-of-core.md`). It is **no longer zero-TCB**:
//! trust is per-rule via `admits` — the [`rules`] catalogue (golden:
//! `docs/deps/eval-manifest.txt`) and the [`certs`] dispatch it drives are
//! trusted *at the eval tier* (`Thm<CoreEval>` = [`EvalThm`]), while
//! `Thm<CoreLang>` remains the pure-HOL tier with no computation TCB. The
//! *drivers* below (everything that only composes gated mints) stay
//! untrusted: they can fail, but they cannot forge.
//!
//! Surface (semantics pinned by `tests/audit_reduce.rs`, the S8 port of the
//! retired in-kernel audit suite; definition-vs-native consistency per cert
//! family pinned by `tests/pure_hol_units.rs`, the stage-E3 pure-HOL units):
//!
//! - [`CoreEval`] / [`EvalThm`] — the tier and its theorem type.
//! - [`reduce`] / [`reduce_with`] — single-step closed-form computation
//!   `⊢ t = result` (the `_with` twin keeps the `TrustedCons` sharing seam).
//! - [`prove_true`] — `⊢ t` for a `t` that single-step reduces to `T`.
//! - [`delta`] — definitional unfolding passthrough
//!   ([`covalence_core::Thm::unfold_term_spec`] at the eval tier).
//! - [`nat_add_thm`] — the S4 toHOL slice driver (symbolic-tier certificate
//!   reified through the admitted toHOL rules and transported with the base
//!   `eq_mp`), kept as the exemplar of the never-materialize pipeline.
//! - [`nat_add_thm_symbolic`] — the literal-endgame (stage EG1) driver: the
//!   same `NatAddCert`, landed **without reification** as a
//!   `Thm<CoreEval, NatAddEqE>` whose `toHOL` leaves stay native `Nat`s — the
//!   succ-tower is never built (design: `notes/vibes/literal-endgame-design.md`).
//! - [`lit`] — the literal build/recognize facade ([`mk_nat`]/[`as_nat`]/…):
//!   the single peripheral chokepoint that moves when the kernel literal
//!   variants die.

#![forbid(unsafe_code)]

use covalence_core::seam::Lit;
use covalence_core::{Error, Result, Term, TermKind, TrustedCons};
use covalence_pure::{Rule, apply};

pub mod certs;
pub mod defs;
pub mod derived;
mod lang;
pub mod lit;
pub mod rules;
mod tohol;
mod tohol_ops;
mod typed_float;

pub use certs::{PrimFamily, prim_family};
// The HOL term-builder helpers (`hol_eq` / `hol_imp` / `hol_forall` / …)
// still live in core (the staying axiom rules and the D3 type-catalogue
// residue state their conclusions with them); re-exported here so
// downstream imports route through the eval catalogue, the same alias
// route as `defs` — the eventual physical move is then invisible.
pub use covalence_core::hol;
pub use defs::{as_f64_bits, mk_f64};
pub use derived::{DerivedRules, TypeDefExt};
pub use lang::{CoreEval, EvalThm, EvalTypeDef};
pub use lit::{
    as_blob, as_int, as_nat, as_u32, as_u64, kind_name, mk_blob, mk_int, mk_nat, mk_u32, mk_u64,
};
pub use tohol::{nat_add_thm, nat_add_thm_symbolic};
pub use tohol_ops::{
    HolApp, HolAppE, NatAddEqE, NatAddLhsE, ToHolBytes, ToHolBytesE, ToHolF32, ToHolF32E, ToHolF64,
    ToHolF64E, ToHolInt, ToHolIntE, ToHolNat, ToHolNatE,
};

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

/// Apply an admitted `CoreProp`-concluding rule and land it as an [`EvalThm`].
pub(crate) fn mint<R: Rule<CoreEval, Concl = covalence_core::seam::CoreProp>>(
    rule: R,
    input: R::Input,
) -> Option<EvalThm> {
    let landed = apply(CoreEval, rule, input).ok()?;
    EvalThm::from_pure(landed).ok()
}

/// Single-step closed-form computation via the cert path: `⊢ t = result`
/// where `t` is a literal operation applied to all-literal arguments
/// (catalogue, conclusions, and refusals pinned by `tests/audit_reduce.rs`
/// and `tests/catalogue.rs`). Returns `None` for any other shape: it does
/// not reduce subterms or follow β/δ chains.
///
/// The catalogue: HOL `=` over two same-kind literals (equality AND
/// disequality), the primitive `succ`, the `nat.*` / `int.*` / `bytes.*`
/// catalogue ops, the nat↔int/bytes coercions, the fixed-width `uN`/`sN`
/// ops, the bit-level WASM float ops (`f32.addBits`, `f64.leBits`,
/// `u32.truncSatBits.f32`, … — WASM deterministic profile on `u32`/`u64` bit
/// patterns), the typed `f64.*` ops on `f64` literals (`fromBits ⌜bits⌝` —
/// the F2c layer, a composite of gated steps, see [`defs::TypedF64`]), and
/// the coercion round-trip `rep (abs v) = v` on the float newtypes.
/// Conventions: saturating nat `sub`/`pred`; `n / 0 = 0` and
/// `n mod 0 = n`; fixed-width arithmetic wraps mod `2^width`; detectably
/// unrepresentable results refuse (oversize `pow` exponents on a base ≥ 2,
/// oversize `shl` shifts on a non-zero operand; `shr` is total).
pub fn reduce(t: &Term) -> Option<EvalThm> {
    reduce_with(t, &mut ())
}

/// [`reduce`] interning the result conclusion through a caller-supplied
/// [`TrustedCons`] — the sharing seam, letting a reduction driver thread one
/// cons uniformly through `beta_conv` / `reduce` / `trans`. Pure sharing, no
/// soundness role.
pub fn reduce_with<C: TrustedCons + ?Sized>(t: &Term, cons: &mut C) -> Option<EvalThm> {
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
            mint(rules::LitEqCert, (a, b))?
        }
        // The primitive successor.
        TermKind::Succ if args.len() == 1 => match Lit::from_term(&args[0])? {
            Lit::Nat(n) => mint(rules::SuccCert, n)?,
            _ => return None,
        },
        // Catalogue dispatch by canonical handle (empty type args only —
        // the same restriction as the legacy reducer).
        TermKind::Spec(spec, targs) if targs.is_empty() => {
            if let Some(op) = defs::lookup_f64_op(spec) {
                // The typed float layer (F2c): a composite of already-gated
                // steps (δ/β + coercion round-trip + FloatCert), not a rule.
                typed_float::typed_f64_step(op, spec, &args)?
            } else {
                let lits: Vec<Lit> = args.iter().map(Lit::from_term).collect::<Option<_>>()?;
                let input = (spec.clone(), lits);
                match prim_family(spec)? {
                    PrimFamily::NatArith => mint(rules::NatArithCert, input)?,
                    PrimFamily::IntArith => mint(rules::IntArithCert, input)?,
                    PrimFamily::Bytes => mint(rules::BytesCert, input)?,
                    PrimFamily::Coercion => mint(rules::CoercionCert, input)?,
                    PrimFamily::FixedWidth => mint(rules::FixedWidthCert, input)?,
                    PrimFamily::Float => mint(rules::FloatCert, input)?,
                }
            }
        }
        // Coercion round-trip on a float newtype: `⊢ rep (abs v) = v`.
        TermKind::SpecRep(..) if args.len() == 1 => typed_float::collapse_step(&head, &args[0])?,
        _ => return None,
    };
    let _ = thm.concl().cons_with(cons);
    Some(thm)
}

/// `⊢ T` — derived through the cert path: `LitEqCert` gives
/// `⊢ (T = T) = T`, `refl` gives `⊢ T = T`, and `eq_mp` concludes `⊢ T`.
pub(crate) fn truth() -> Result<EvalThm> {
    let bridge =
        mint(rules::LitEqCert, (Lit::Bool(true), Lit::Bool(true))).ok_or(Error::NotReducible)?; // ⊢ (T = T) = T
    let refl = EvalThm::refl(Term::bool_lit(true))?; // ⊢ T = T
    bridge.eq_mp(refl) // ⊢ T
}

/// Prove `⊢ t` by single-step evaluation: [`reduce`] `t` and, if it lands on
/// the `T` literal, conclude `⊢ t` (via `⊢ T` and `eq_mp` on the symmetric
/// equation). Errors if `t` does not single-step reduce to `T`.
///
/// This is the single-step twin of the recursive
/// `TermExt::prove_true` in `covalence-init` (which normalises first); it
/// decides one-redex closed goals like `⊢ nat.le ⌜3⌝ ⌜5⌝` or `⊢ ⌜4⌝ = ⌜4⌝`.
pub fn prove_true(t: &Term) -> Result<EvalThm> {
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
/// catalogue spec leaf, at the eval tier. Still routed to
/// [`covalence_core::Thm::unfold_term_spec`] — sound definitional unfolding
/// tied to `TermKind::Spec`, which survives until the `defs/` catalogue
/// re-homes as ordinary `define`d constants with stored definitional
/// theorems (then this re-routes without callers moving).
pub fn delta(t: &Term) -> Result<EvalThm> {
    EvalThm::unfold_term_spec(t.clone())
}
