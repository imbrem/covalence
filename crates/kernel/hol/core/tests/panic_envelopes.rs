//! Panic-envelope pins for the deliberately-panicking helpers in trusted
//! substitution code (stage P2, item 3 of the kernel property campaign).
//!
//! `subst::shift_by` / `shift_with` panic on Bound-index underflow and
//! overflow — a designed fail-stop: silently wrapping an index would let
//! an unsound term propagate, so soundness rests on every trusted caller
//! establishing the precondition first.
//!
//! ## Trusted (`src/`, non-test) caller audit — keep in sync
//!
//! - `subst.rs::inst_typed` / `inst_opt` (the `open` machinery) and
//!   `subst.rs::subst_free`: `shift_with(u, depth as i64, 0, _)` with
//!   `depth ≥ 0` — underflow impossible; overflow requires the
//!   *substituted term itself* to carry a free (ill-scoped) `Bound`
//!   within `depth` of `u32::MAX`, and then fail-stops (pinned below).
//! - `thm/rules.rs::EtaConv`: the ONLY negative-delta caller
//!   (`shift_by(f, -1, 0)`), guarded by `uses_bound_outer(f, 0)` — the
//!   exact underflow precondition. Property-tested below: `eta_conv`
//!   never panics, on eta-shaped or fully arbitrary input.
//!
//! Theorem-level rules cannot reach the overflow fail-stop either:
//! every rule type-checks its term inputs first, and `type_of` rejects
//! ill-scoped terms (`Error::NotClosed` on a free `Bound`) before any
//! shift runs — property-tested below on `beta_conv` (the rule whose
//! `open` call shifts by binder depth).
//!
//! ## Bug found by these properties (fixed in `src/thm/rules.rs`)
//!
//! `Thm::beta_conv` violated `hol::hol_eq`'s pre-validation contract:
//! it type-checked only the *argument* of the redex, so an ill-typed or
//! ill-scoped abstraction BODY (e.g. `(λx:nat. #5) 0` or
//! `(λx:nat. (0 0)) 0`) sailed past the checks and **panicked** inside
//! `hol_eq`'s `expect` — a panic reachable from the safe pub kernel API
//! with attacker-supplied terms (untrusted proof scripts drive
//! `beta_conv`). A fail-stop, not a soundness hole (`build` re-validates
//! every conclusion), fixed by validating the whole redex
//! (`app.type_of()?`) before substituting — a strict domain narrowing.
//! `beta_conv_never_panics` below is the regression property.
//!
//! The underflow panic message itself is already pinned in
//! `audit_subst.rs`; the overflow twin is pinned here.

use covalence_core::subst::{open, shift_by};
use covalence_core::{Term, Type};
use covalence_proptest::proptest::prelude::*;

/// The pure tier (`Thm<CoreLang>`) — these are core-rule tests.
type Thm = covalence_core::Thm;

// ===========================================================================
// Generator: small raw terms — possibly open, possibly ill-typed (the full
// syntactic domain the rules must survive), with leaves that let the Ok
// paths fire too.
// ===========================================================================

fn arb_ty() -> impl Strategy<Value = Type> {
    prop_oneof![
        Just(Type::nat()),
        Just(Type::bool()),
        Just(Type::fun(Type::nat(), Type::nat())),
    ]
}

fn arb_term() -> impl Strategy<Value = Term> {
    let leaf = prop_oneof![
        (0u32..4).prop_map(Term::bound),
        // near-overflow indices: the adversarial corner of the envelope
        Just(Term::bound(u32::MAX)),
        Just(Term::bound(u32::MAX - 1)),
        Just(Term::free("x", Type::nat())),
        Just(Term::free("g", Type::fun(Type::nat(), Type::nat()))),
        any::<bool>().prop_map(Term::bool_lit),
        any::<u8>().prop_map(Term::u8_lit),
        Just(Term::succ()),
    ];
    leaf.prop_recursive(4, 16, 2, |inner| {
        prop_oneof![
            3 => (inner.clone(), inner.clone()).prop_map(|(f, x)| Term::app(f, x)),
            2 => (arb_ty(), inner).prop_map(|(ty, b)| Term::abs(ty, b)),
        ]
    })
}

// ===========================================================================
// The guarded negative-delta caller: eta_conv
// ===========================================================================

proptest! {
    /// `eta_conv` never panics on eta-*shaped* input: `λx:nat. f x` for
    /// arbitrary `f` — including bodies that use `Bound(0)` (which the
    /// `uses_bound_outer` guard must refuse BEFORE the down-shift) and
    /// bodies carrying near-`u32::MAX` indices.
    #[test]
    fn eta_conv_never_panics_on_eta_shapes(f in arb_term()) {
        let abs = Term::abs(Type::nat(), Term::app(f, Term::bound(0)));
        let _ = Thm::eta_conv(abs); // Ok or clean Err — never a panic
    }

    /// ... and on fully arbitrary terms (shape rejection is clean too).
    #[test]
    fn eta_conv_never_panics_at_all(t in arb_term()) {
        let _ = Thm::eta_conv(t);
    }

    /// The positive-delta `open` caller behind a kernel rule: `beta_conv`
    /// type-checks before substituting, so ill-scoped arguments (free
    /// `Bound(u32::MAX)` under a binder — the overflow recipe) get a clean
    /// `Err`, never the shift fail-stop.
    #[test]
    fn beta_conv_never_panics(body in arb_term(), arg in arb_term()) {
        let app = Term::app(Term::abs(Type::nat(), body.clone()), arg.clone());
        let _ = Thm::beta_conv(app);
        // arbitrary (non-redex) terms are rejected cleanly too
        let _ = Thm::beta_conv(body);
    }
}

/// A successful eta step really strips the binder: sanity that the Ok path
/// is exercised by the generator's vocabulary (`g : nat → nat`).
#[test]
fn eta_conv_ok_path_smoke() {
    let g = Term::free("g", Type::fun(Type::nat(), Type::nat()));
    let abs = Term::abs(Type::nat(), Term::app(g.clone(), Term::bound(0)));
    let thm: Thm = Thm::eta_conv(abs).expect("η: λx. g x = g");
    let (_lhs, rhs) = thm.concl().as_eq().expect("eta concl is an equation");
    assert_eq!(rhs, &g);
}

// ===========================================================================
// The fail-stop boundary itself (raw subst utilities, not reachable
// through the theorem rules — see the module docs)
// ===========================================================================

/// Overflow twin of `audit_subst.rs`'s underflow pin: pushing a `Bound`
/// past `u32::MAX` aborts loudly instead of wrapping.
#[test]
#[should_panic(expected = "exceeds u32::MAX")]
fn shift_by_overflow_panics_cleanly() {
    let _ = shift_by(&Term::bound(u32::MAX), 1, 0);
}

/// The same fail-stop through `open`: substituting a term that carries an
/// ill-scoped near-`u32::MAX` free `Bound` under one binder shifts it past
/// the ceiling — the raw utility aborts (theorem rules reject such input
/// at type-check instead).
#[test]
#[should_panic(expected = "exceeds u32::MAX")]
fn open_shift_overflow_panics_cleanly() {
    // body = λy:nat. #1 — the outer hole sits under one binder, so the
    // substituted term is shifted by 1.
    let body = Term::abs(Type::nat(), Term::bound(1));
    let _ = open(&body, &Term::bound(u32::MAX));
}

/// Inside the envelope the same shape is fine: `u32::MAX − 1` shifts to
/// exactly `u32::MAX` without panicking.
#[test]
fn open_shift_at_ceiling_is_panic_free() {
    let body = Term::abs(Type::nat(), Term::bound(1));
    let opened = open(&body, &Term::bound(u32::MAX - 1));
    assert_eq!(opened, Term::abs(Type::nat(), Term::bound(u32::MAX)));
}
