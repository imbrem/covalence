//! The `toHOL` denotation ops: HOL terms as a **base sort** (`covalence-pure`
//! expressions of sort [`Term`]), with native values entering under
//! uninterpreted `toHOL` leaves.
//!
//! The maintainer's key move (notes/vibes/pure-hol-and-build-plan.md): the
//! canonical HOL term for a native value is **never materialized**. `toHOL n`
//! *denotes* the numeral `S(S(…(Z)…))` without building it; a megabyte
//! bytestring under [`ToHolBytes`] denotes its `cons`-tower for free. The HOL
//! term formers ([`HolApp`], …) are base ops on the `Term` sort too, so
//! partially-symbolic terms like `S (toHOL 4)` are ordinary base expressions.
//!
//! Trust story:
//! - [`ToHolNat`] / [`ToHolInt`] / [`ToHolBytes`] are **uninterpreted** ops
//!   (no [`CanonRule`]): writing `App<ToHolNat, _>` is inert and always sound.
//!   Their *meaning* is pinned only by admitted rules — the unfolding-equation
//!   and certificate rules in `thm::rules` (`ToHolNatVal`, `NatAddCert`, …).
//! - [`HolApp`] is an [`Op`] **and** a [`CanonRule`] whose `eval` is the raw,
//!   untyped [`Term::app`]. Reducing it via [`covalence_pure::canon`] is gated
//!   on its `TypeId` being admitted; `CoreLang` admits it (it is enumerated in
//!   `CORE_MANIFEST`). Soundness: `App<HolApp, Val((f, x))> = Val(f x)` holds
//!   by literal denotation — `HolApp` *means* HOL application, and the
//!   equation's two sides are the same term value by construction.

use covalence_pure::{App, CanonRule, Op, Val};
use covalence_types::{Bytes, Int, Nat};

use crate::term::Term;

/// `toHOL : Nat → Term` — the uninterpreted denotation of a native natural as
/// its canonical HOL numeral. Never evaluated (no [`CanonRule`]); its defining
/// properties arrive only as admitted rules.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct ToHolNat;

impl Op for ToHolNat {
    type In = Nat;
    type Out = Term;
}

/// `toHOL : Int → Term` — uninterpreted (see [`ToHolNat`]).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct ToHolInt;

impl Op for ToHolInt {
    type In = Int;
    type Out = Term;
}

/// `toHOL : Bytes → Term` — uninterpreted (see [`ToHolNat`]).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct ToHolBytes;

impl Op for ToHolBytes {
    type In = Bytes;
    type Out = Term;
}

/// HOL application as a base op on the `Term` sort: `(f, x) ↦ f x`.
///
/// The [`CanonRule`] eval is the **raw, untyped** [`Term::app`] — no type
/// check, exactly the constructor. Sound by literal denotation: on ground
/// `Val` arguments the minted equation's right-hand side *is* the application
/// node the left-hand side denotes. (An ill-typed application is a perfectly
/// good `Term` value; it simply never type-checks into an `IsThm` sequent.)
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct HolApp;

impl Op for HolApp {
    type In = (Term, Term);
    type Out = Term;
}

impl CanonRule for HolApp {
    fn eval(&self, (f, x): &Self::In) -> Term {
        Term::app(f.clone(), x.clone())
    }
}

// ---------------------------------------------------------------------------
// Expression-shape aliases for the nat.add slice (used by the `NatAddCert`
// rule's conclusion type and by the reification driver, which must agree on
// the exact nesting so `eq_mp`'s structural match succeeds).
// ---------------------------------------------------------------------------

/// A `toHOL`-denoted natural: `App<ToHolNat, Val<Nat>>`.
pub type ToHolNatE = App<ToHolNat, Val<Nat>>;

/// A `toHOL`-denoted integer: `App<ToHolInt, Val<Int>>`.
pub type ToHolIntE = App<ToHolInt, Val<Int>>;

/// A `toHOL`-denoted bytestring: `App<ToHolBytes, Val<Bytes>>`.
pub type ToHolBytesE = App<ToHolBytes, Val<Bytes>>;

/// A symbolic HOL application `f x` at the base layer.
pub type HolAppE<F, X> = App<HolApp, (F, X)>;

/// The symbolic HOL term `nat.add (toHOL a) (toHOL b)` (the `Val<Term>` leaf
/// is the `defs::nat_add` constant).
pub type NatAddLhsE = HolAppE<HolAppE<Val<Term>, ToHolNatE>, ToHolNatE>;

/// The symbolic HOL equation `nat.add (toHOL a) (toHOL b) = toHOL (a + b)`
/// (the outer `Val<Term>` leaf is HOL `=` at `nat`).
pub type NatAddEqE = HolAppE<HolAppE<Val<Term>, NatAddLhsE>, ToHolNatE>;

/// Build the [`NatAddEqE`] expression for concrete `a`, `b`, `sum` — shared by
/// `NatAddCert::decide` and (implicitly, node by node) the reification driver.
pub(crate) fn nat_add_eq_expr(a: Nat, b: Nat, sum: Nat) -> NatAddEqE {
    let add = Val(crate::defs::nat_add());
    let eq = Val(Term::eq_op(crate::term::Type::nat()));
    let lhs = App(
        HolApp,
        (
            App(HolApp, (add, App(ToHolNat, Val(a)))),
            App(ToHolNat, Val(b)),
        ),
    );
    App(HolApp, (App(HolApp, (eq, lhs)), App(ToHolNat, Val(sum))))
}
