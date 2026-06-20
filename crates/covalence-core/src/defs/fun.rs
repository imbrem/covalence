//! Point-free ("pointless") programming utilities — the basic
//! function combinators `id`, `const`, `compose`, `flip`.
//!
//! These are ordinary let-style definitions (`λ`-bodies over the
//! kernel atoms), polymorphic in the obvious type variables. They give
//! call sites and other definitions a combinator vocabulary instead of
//! spelling out the lambdas each time — e.g. `mk (const F)` for the
//! empty set, `compose g f` for `g ∘ f`.
//!
//! (The term accessor for `fun.const` is spelled [`konst`] because
//! `const` is a Rust keyword; the catalogue label is still
//! `"fun.const"`.)

use crate::hol;
use crate::term::{Term, Type};

use super::canonical::Canonical;

fn id_body() -> Term {
    // λx:'a. x
    let alpha = Type::tfree("a");
    let x = Term::free("x", alpha.clone());
    hol::pub_abs("x", alpha, x)
}

poly_let_term! {
    /// `fun.id : 'a → 'a` ≡ `λx. x` — the identity function.
    id_spec, id(alpha), Canonical::Id, id_body()
}

fn konst_body() -> Term {
    // λx:'a. λ_:'b. x
    let alpha = Type::tfree("a");
    let beta = Type::tfree("b");
    let x = Term::free("x", alpha.clone());
    let ignore_y = Term::abs(beta, x);
    hol::pub_abs("x", alpha, ignore_y)
}

poly_let_term! {
    /// `fun.const : 'a → 'b → 'a` ≡ `λx _. x` — the constant function
    /// (ignores its second argument).
    konst_spec, konst(alpha, beta), Canonical::Const, konst_body()
}

fn compose_body() -> Term {
    // λg:('b→'c). λf:('a→'b). λx:'a. g (f x)
    let alpha = Type::tfree("a");
    let beta = Type::tfree("b");
    let gamma = Type::tfree("c");
    let g_ty = Type::fun(beta.clone(), gamma);
    let f_ty = Type::fun(alpha.clone(), beta);
    let g = Term::free("g", g_ty.clone());
    let f = Term::free("f", f_ty.clone());
    let x = Term::free("x", alpha.clone());
    let gfx = Term::app(g, Term::app(f, x));
    let lam_x = hol::pub_abs("x", alpha, gfx);
    let lam_f = hol::pub_abs("f", f_ty, lam_x);
    hol::pub_abs("g", g_ty, lam_f)
}

poly_let_term! {
    /// `fun.compose : ('b → 'c) → ('a → 'b) → 'a → 'c` ≡
    /// `λg f x. g (f x)` — function composition `g ∘ f`.
    compose_spec, compose(alpha, beta, gamma), Canonical::Compose, compose_body()
}

fn flip_body() -> Term {
    // λf:('a→'b→'c). λy:'b. λx:'a. f x y
    let alpha = Type::tfree("a");
    let beta = Type::tfree("b");
    let gamma = Type::tfree("c");
    let f_ty = Type::fun(alpha.clone(), Type::fun(beta.clone(), gamma));
    let f = Term::free("f", f_ty.clone());
    let x = Term::free("x", alpha.clone());
    let y = Term::free("y", beta.clone());
    let fxy = Term::app(Term::app(f, x), y);
    let lam_x = hol::pub_abs("x", alpha, fxy);
    let lam_y = hol::pub_abs("y", beta, lam_x);
    hol::pub_abs("f", f_ty, lam_y)
}

poly_let_term! {
    /// `fun.flip : ('a → 'b → 'c) → 'b → 'a → 'c` ≡ `λf y x. f x y` —
    /// swap the first two arguments of a binary function.
    flip_spec, flip(alpha, beta, gamma), Canonical::Flip, flip_body()
}
