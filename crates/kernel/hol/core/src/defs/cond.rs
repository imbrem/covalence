//! `cond : bool → 'a → 'a → 'a` — the Boolean conditional
//! (`if b then x else y`).
//!
//! A **let-style** definition, the HOL Light `COND` (`bool.ml`):
//!
//! ```text
//!     cond ≡ λt x y. ε z. (t = T ⟹ z = x) ∧ (t = F ⟹ z = y)
//! ```
//!
//! From this, the reduction equations
//!
//! ```text
//!     cond T x y  =  x
//!     cond F x y  =  y
//! ```
//!
//! are **derived** (not postulated) downstream in
//! `covalence-hol`'s `init::cond` via the choice axiom
//! [`crate::Thm::select_ax`] — the same way HOL Light proves
//! `COND_CLAUSES`. At the kernel level `cond` unfolds to its body
//! through [`crate::Thm::unfold_term_spec`] like any other defined
//! constant; the certificate path has no `cond`-specific rule (the
//! branches are arbitrary terms, not literals), so it is δ-unfolded
//! explicitly.

use std::sync::LazyLock;

use crate::hol;
use crate::term::{Term, Type};

use super::canonical::Canonical;
use super::spec::TermSpec;

/// `λt x y. ε z. (t = T ⟹ z = x) ∧ (t = F ⟹ z = y)` — the HOL Light
/// `COND` body, polymorphic in `α = tfree("a")`.
fn cond_body() -> Term {
    let alpha = Type::tfree("a");
    let t = Term::free("t", Type::bool());
    let x = Term::free("x", alpha.clone());
    let y = Term::free("y", alpha.clone());
    let z = Term::free("z", alpha.clone());

    // (t = T ⟹ z = x) ∧ (t = F ⟹ z = y)
    let t_true = hol::hol_eq(t.clone(), Term::bool_lit(true));
    let t_false = hol::hol_eq(t.clone(), Term::bool_lit(false));
    let z_is_x = hol::hol_eq(z.clone(), x.clone());
    let z_is_y = hol::hol_eq(z.clone(), y.clone());
    let conj = hol::hol_and(hol::hol_imp(t_true, z_is_x), hol::hol_imp(t_false, z_is_y));

    // ε z:α. conj
    let pred = hol::pub_abs("z", alpha.clone(), conj);
    let eps = Term::app(Term::select_op(alpha.clone()), pred);

    // λt x y. eps
    hol::pub_abs(
        "t",
        Type::bool(),
        hol::pub_abs("x", alpha.clone(), hol::pub_abs("y", alpha, eps)),
    )
}

/// `cond : bool → 'a → 'a → 'a` — the Boolean conditional, a let-style
/// definition (body via `cond_body`). Its defining equation is
/// available through [`crate::Thm::unfold_term_spec`].
pub fn cond_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let body = cond_body();
        let ty = body
            .type_of()
            .expect("cond_spec: body must type-check to bool → α → α → α");
        TermSpec::new(Canonical::Cond, Some(ty), Some(body))
    });
    LAZY.clone()
}

/// `cond α : bool → α → α → α`.
pub fn cond(alpha: Type) -> Term {
    Term::term_spec(cond_spec(), vec![alpha])
}

impl Term {
    /// `cond c tt ff : α` — the boolean conditional [`cond`] applied,
    /// with `α` inferred from `tt`. Convenience builder for writing
    /// case-split definitions.
    ///
    /// **Panics** if `tt` is not well-typed (an open / ill-typed term).
    /// Callers in trusted spec-build paths pass fully-typed `tt`, so the
    /// panic is unreachable there; out-of-band callers should
    /// pre-validate with `tt.type_of()`.
    pub fn cond(c: Term, tt: Term, ff: Term) -> Term {
        let alpha = tt
            .type_of()
            .expect("Term::cond: `tt` must be well-typed to infer the result type");
        let op = cond(alpha);
        Term::app(Term::app(Term::app(op, c), tt), ff)
    }
}
