//! `streamIterate` / `streamNth` — stream convenience ops (moved from
//! the core `defs/` catalogue; the `stream` TYPE spec and the residual
//! `stream_at`/`stream_mk`/`stream_head`/`stream_tail`/`stream_const`/
//! `finite` ops are D3 residue in `covalence_core::defs::stream`).

use covalence_core::hol;
use covalence_core::term::{Term, Type};

use crate::defs::{Canonical, iter, stream, stream_at, stream_mk};

/// Body of `streamIterate := λx:α. λf:α→α. stream_mk (λn:nat. iter n f x)`.
fn stream_iterate_body() -> Term {
    let alpha = Type::tfree("a");
    let alpha_to_alpha = Type::fun(alpha.clone(), alpha.clone());
    let x = Term::free("x", alpha.clone());
    let f = Term::free("f", alpha_to_alpha.clone());
    let n = Term::free("n", Type::nat());

    // iter n f x
    let iter_at_alpha = iter(alpha.clone());
    let app1 = Term::app(iter_at_alpha, n.clone());
    let app2 = Term::app(app1, f.clone());
    let iter_body = Term::app(app2, x.clone());

    // stream_mk (λn. iter n f x)
    let lam_n = hol::pub_abs("n", Type::nat(), iter_body);
    let body = Term::app(stream_mk(alpha.clone()), lam_n);

    let lam_f = hol::pub_abs("f", alpha_to_alpha, body);
    hol::pub_abs("x", alpha, lam_f)
}

poly_let_term! {
    /// `streamIterate : 'a → ('a → 'a) → stream 'a` —
    /// `λx f. stream_mk (λn. iter n f x)`. The stream
    /// `x, f x, f (f x), …`.
    stream_iterate_spec, stream_iterate(alpha), Canonical::StreamIterate, stream_iterate_body()
}

// `streamNth` was originally the function-application bridge;
// now that role is filled by `stream_at` directly. `streamNth n s`
// reduces to `stream_at s n` (arg-flipped). We keep it as a
// convenience wrapper.

/// Body of `streamNth := λn:nat. λs:stream α. stream_at s n`.
fn stream_nth_body() -> Term {
    let alpha = Type::tfree("a");
    let stream_a = stream(alpha.clone());
    let n = Term::free("n", Type::nat());
    let s = Term::free("s", stream_a.clone());
    let body = Term::app(Term::app(stream_at(alpha), s.clone()), n.clone());
    let lam_s = hol::pub_abs("s", stream_a, body);
    hol::pub_abs("n", Type::nat(), lam_s)
}

poly_let_term! {
    /// `streamNth : nat → stream 'a → 'a` —
    /// `λn s. stream_at s n`. Convenience wrapper for
    /// `stream_at` with arguments flipped.
    stream_nth_spec, stream_nth(alpha), Canonical::StreamNth, stream_nth_body()
}
