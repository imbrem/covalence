//! `int := (nat × nat) / ~` (Grothendieck construction), plus
//! term-level int arithmetic / comparison / coercion.
//!
//! A pair `(a, b) : nat × nat` represents the integer `a − b`, and
//! `(a, b) ~ (c, d) ⟺ a + d = c + b`. The type is the quotient of
//! `prod nat nat` by that relation; the carrier of the quotient is
//! `(prod nat nat) → bool` (an equivalence class is the *set* of pairs
//! it contains). We bridge class ↔ representative with the spec
//! abstraction/representation coercions:
//!
//! ```text
//!     repPair x ≔ ε(λp. rep x p)            -- some pair in x's class
//!     mkInt p   ≔ abs (λq. p ~ q)           -- the int whose class is [p]
//! ```
//!
//! Each arithmetic op picks representatives, computes on the nat
//! components, and re-quotients — the standard Grothendieck formulas:
//!
//! ```text
//!     succ (a−b) = (a+1) − b          neg (a−b) = b − a
//!     (a−b)+(c−d) = (a+c) − (b+d)     (a−b)−(c−d) = (a+d) − (b+c)
//!     (a−b)·(c−d) = (a·c+b·d) − (a·d+b·c)
//!     (a−b) ≤ (c−d) ⟺ a+d ≤ c+b
//! ```
//!
//! Integer *literals* stay the builtin `TermKind::Int`; closed-form
//! reduction continues to go through the certificate path (handle
//! `ptr_eq`), independent of these bodies. The bodies make the open
//! ops *provable* (`covalence-hol` derives the defining equations);
//! they do not change reduction.
//!
//! `intDiv`/`intMod` are defined by composing the sign/magnitude ops
//! (`intSgn`/`intAbs`/`intMul`/`intSub`, `natDiv`, `natToInt`) rather than
//! via the Grothendieck pairs — truncating division toward zero with
//! `x / 0 = 0` and `x mod 0 = x`. Because those sub-ops reduce on
//! literals, these bodies reduce too, so the certificate reductions
//! must agree with them (see the section comment on the definitions).

use std::sync::LazyLock;

use crate::hol;
use crate::term::{Term, Type};

use super::canonical::Canonical;
use super::nat::nat_add;
use super::prod::{fst, prod, snd};
use super::spec::TypeSpec;

// ============================================================================
// `int` as a derived TypeSpec — the Grothendieck construction
// ============================================================================

/// `nat × nat` — the representative-pair carrier.
fn nn_pair() -> Type {
    prod(Type::nat(), Type::nat())
}

/// `fst p` at `(nat, nat)`.
fn fst_nn(p: Term) -> Term {
    Term::app(fst(Type::nat(), Type::nat()), p)
}
/// `snd p` at `(nat, nat)`.
fn snd_nn(p: Term) -> Term {
    Term::app(snd(Type::nat(), Type::nat()), p)
}
/// `a + b` on nat.
fn add(a: Term, b: Term) -> Term {
    Term::app(Term::app(nat_add(), a), b)
}

/// `λp q. fst p + snd q = fst q + snd p` — the Grothendieck relation
/// `(a, b) ~ (c, d) ⟺ a + d = c + b`.
fn int_rel() -> Term {
    let pair_ty = nn_pair();
    let p = Term::free("p", pair_ty.clone());
    let q = Term::free("q", pair_ty.clone());
    let lhs = add(fst_nn(p.clone()), snd_nn(q.clone()));
    let rhs = add(fst_nn(q), snd_nn(p));
    let eq = hol::hol_eq(lhs, rhs);
    hol::pub_abs("p", pair_ty.clone(), hol::pub_abs("q", pair_ty, eq))
}

/// `int := (nat × nat) / ~`, where `(a, b)` represents `a − b` and
/// `(a, b) ~ (c, d) ⟺ a + d = c + b`. The type of integer literals
/// (`TermKind::Int`).
pub fn int_ty_spec() -> TypeSpec {
    static LAZY: LazyLock<TypeSpec> =
        LazyLock::new(|| TypeSpec::quot(Canonical::Int, nn_pair(), int_rel()));
    LAZY.clone()
}
