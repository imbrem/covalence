//! HOL term constructors over the kernel **primitives** — `defs`-free.
//!
//! Everything here builds terms from primitive kernel atoms only (`=` /
//! `TermKind::Eq`, `Abs`, the `Nat` literal zero): building terms mints
//! nothing, so the module is `pub`. Consumed by `thm/` (the inference
//! rules build their equation conclusions with [`hol_eq`] /
//! [`hol_eq_at`]), by `defs/*.rs`'s spec carriers (which need
//! [`pub_abs`] and [`zero`]), and downstream.
//!
//! The **defined-connective** builders (`hol_imp` / `hol_and` /
//! `hol_or` / `hol_not` / `hol_exists` / `hol_forall` / `forall_at`)
//! are NOT here (stage A3): they apply `defs::logic`'s catalogue specs,
//! so they live next to those definitions — `pub(crate)` in
//! `crate::defs::logic` for the D3 residue bodies and the two staying
//! connective-built rules, and publicly in `covalence-hol-eval::hol`
//! (the untrusted home) for everyone else.

use covalence_types::Nat;

use crate::subst::close_var;
use crate::term::Var;
use crate::term::{Term, Type};

/// HOL `=` at `α → α → bool` — the primitive `TermKind::Eq`.
fn eq_at(alpha: Type) -> Term {
    Term::eq_op(alpha)
}

/// HOL `lhs = rhs : bool`, types inferred from `lhs`.
///
/// **Panics** if `lhs` is not well-typed (an open term, an ill-typed
/// application, etc.). Callers in inference-rule paths must
/// pre-validate `lhs.type_of()?` before invoking — see e.g.
/// [`crate::Thm::mk_comb`]. Callers in trusted spec-build paths
/// (`defs/*.rs`'s LazyLock initialisers) construct `lhs` from
/// fully-typed atoms, so the panic is unreachable there.
pub fn hol_eq(lhs: Term, rhs: Term) -> Term {
    let alpha = lhs.type_of().expect("hol::hol_eq: lhs must be well-typed");
    hol_eq_at(alpha, lhs, rhs)
}

/// HOL `lhs = rhs : bool` with the element type `alpha` supplied by the
/// caller — no `type_of` walk. Use this in inference-rule paths that
/// already know `alpha` (e.g. it can be read straight off an input
/// theorem's `Eq(alpha)` node). The result is still fully re-validated by
/// [`crate::Thm`]'s `build`, so a wrong `alpha` is rejected, never
/// trusted — this is purely a way to avoid recomputing what we already
/// know.
pub fn hol_eq_at(alpha: Type, lhs: Term, rhs: Term) -> Term {
    Term::app(Term::app(eq_at(alpha), lhs), rhs)
}

/// `λx:α. body[x]` — kernel abstraction that closes the named free
/// var into `Bound(0)` first. Exposed to `defs/` for building
/// predicate lambdas inside `TypeSpec.tm`.
pub fn pub_abs(hint: &str, alpha: Type, body: Term) -> Term {
    let v = Var::new(hint, alpha.clone());
    Term::abs(alpha, close_var(&body, &v))
}

/// `0 : nat` — the transitional `Nat` literal zero (see
/// [`Term::zero`] for the primitive `Zero` leaf; the two are bridged
/// at the eval tier).
pub fn zero() -> Term {
    Term::nat_lit(Nat::zero())
}
