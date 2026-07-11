//! **The typed-backend flagship: the abstract monad, lowered to real HOL.**
//!
//! `examples/monad_typed.hs` writes the plain-HOL monad shape of
//! `crates/kernel/hol/init/src/init/monad.rs` in the dialect — `ret`/`bind` as
//! typed free variables over a carrier type variable, `map` *defined* from them
//! — and this test lowers it into genuine, well-typed HOL `Term`s **through the
//! `covalence-hol-api` traits** (`Hol` + `Nat`), then asserts:
//!
//! 1. the lowered `map` definition equals the reference `map_op` term
//!    (`\f. \x. bind x (\y. ret (f y))`), and
//! 2. the `map f (ret a) = ret (f a)` law, lowered as a HOL proposition, has
//!    exactly the shape monad.rs's `monad_map_ret` concludes with.
//!
//! Crucially, **both** the dialect-lowered terms and the reference terms are
//! built entirely through the trait surface — the concrete kernel is named only
//! once, where the test picks `NativeHol` as the `H`. Swapping the TCB (a
//! different `Hol + Nat` impl) leaves the dialect source and this lowering
//! untouched; only the chosen `H` changes.
#![cfg(feature = "hol-typed")]

use covalence_haskell::parse::parse_module;
use covalence_haskell::typed::{Env, lower_decl_in, lower_expr, resolve_ty};
use covalence_hol_api::{Hol, Nat, NativeHol, Term};

const MONAD_TYPED: &str = include_str!("../examples/monad_typed.hs");

/// The abstract element / carrier type variables, through the trait.
fn elem(h: &NativeHol) -> covalence_hol_api::Type {
    h.tvar("a")
}
fn carrier(h: &NativeHol) -> covalence_hol_api::Type {
    h.tvar("mcar")
}

/// `ret : a -> mcar`, `bind : mcar -> (a -> mcar) -> mcar` — the abstract monad
/// operations as free variables, exactly as monad.rs seeds them.
fn ret_var(h: &NativeHol) -> Term {
    let ty = h.fun_ty(elem(h), carrier(h));
    h.var("ret", ty)
}
fn bind_var(h: &NativeHol) -> Term {
    let ty = h.fun_ty(
        carrier(h),
        h.fun_ty(h.fun_ty(elem(h), carrier(h)), carrier(h)),
    );
    h.var("bind", ty)
}

/// An ambient env binding `ret` / `bind` to their abstract types — the "monad
/// signature" a definition of `map` reads free.
fn monad_env(h: &NativeHol) -> Env<NativeHol> {
    let mut env = Env::new();
    env.bind("ret", h.fun_ty(elem(h), carrier(h)));
    env.bind(
        "bind",
        h.fun_ty(
            carrier(h),
            h.fun_ty(h.fun_ty(elem(h), carrier(h)), carrier(h)),
        ),
    );
    env
}

/// The reference `map_op` term — `\f:(a->a). \x:mcar. bind x (\y:a. ret (f y))`
/// — built directly through the traits (the shape monad.rs's `map_op` builds).
fn reference_map_op(h: &NativeHol) -> Term {
    let f = h.var("f", h.fun_ty(elem(h), elem(h)));
    let x = h.var("x", carrier(h));
    let y = h.var("y", elem(h));
    // \y:a. ret (f y)
    let ret_f_y = h.app(ret_var(h), h.app(f.clone(), y).unwrap()).unwrap();
    let kern = h.lam("y", elem(h), ret_f_y);
    // bind x kern
    let body = h.app(h.app(bind_var(h), x).unwrap(), kern).unwrap();
    // \f. \x. body
    let lam_x = h.lam("x", carrier(h), body);
    h.lam("f", h.fun_ty(elem(h), elem(h)), lam_x)
}

/// The dialect module parses, and its `map` definition lowers — through the
/// traits — to exactly the reference `map_op` term.
#[test]
fn map_definition_lowers_to_map_op() {
    let h = NativeHol;
    let module = parse_module(MONAD_TYPED).expect("dialect module parses");

    let map_decl = module
        .iter()
        .find(|d| d.name == "map")
        .expect("has a `map` definition");
    // Sanity: the parser attached the signature.
    assert!(map_decl.sig.is_some(), "map has a type signature");

    let (name, term) = lower_decl_in(&h, &monad_env(&h), map_decl).expect("map lowers");
    assert_eq!(name, "map");
    assert_eq!(
        term,
        reference_map_op(&h),
        "lowered map == reference map_op"
    );

    // It is a genuine, well-typed HOL term: `(a -> a) -> mcar -> mcar`.
    let want_ty = h.fun_ty(
        h.fun_ty(elem(&h), elem(&h)),
        h.fun_ty(carrier(&h), carrier(&h)),
    );
    assert_eq!(h.type_of(&term).expect("map is typed"), want_ty);
}

/// The `mapKernel` definition lowers to `\f. \y. ret (f y)` — the continuation
/// `map` binds with.
#[test]
fn map_kernel_lowers() {
    let h = NativeHol;
    let module = parse_module(MONAD_TYPED).expect("parses");
    let decl = module
        .iter()
        .find(|d| d.name == "mapKernel")
        .expect("has mapKernel");
    let (_, term) = lower_decl_in(&h, &monad_env(&h), decl).expect("lowers");

    let f = h.var("f", h.fun_ty(elem(&h), elem(&h)));
    let y = h.var("y", elem(&h));
    let ret_f_y = h.app(ret_var(&h), h.app(f, y).unwrap()).unwrap();
    let kern = h.lam("y", elem(&h), ret_f_y);
    let want = h.lam("f", h.fun_ty(elem(&h), elem(&h)), kern);
    assert_eq!(term, want);
}

/// The monad-map LAW — `map f (ret a) = ret (f a)` — lowered as a HOL
/// proposition through the traits, with `map` the (signature-typed) operation.
/// It is a well-typed `bool` term of exactly the monad-map-law shape.
#[test]
fn map_law_statement_lowers_to_a_hol_proposition() {
    let h = NativeHol;

    // Bind the theory operations (ret/bind) AND the map operation, then lower
    // the law as a dialect equation expression.
    let mut env = monad_env(&h);
    env.bind(
        "map",
        h.fun_ty(
            h.fun_ty(elem(&h), elem(&h)),
            h.fun_ty(carrier(&h), carrier(&h)),
        ),
    );
    env.bind("f", h.fun_ty(elem(&h), elem(&h)));
    env.bind("a", elem(&h));

    // The dialect source for the law statement.
    let law_src = "map f (ret a) == ret (f a)";
    let law_expr = covalence_haskell::parse::parse_expr(law_src).expect("law parses");
    let law = lower_expr(&h, &env, &law_expr).expect("law lowers");

    // It is a proposition (type `bool`).
    assert_eq!(h.type_of(&law).expect("typed"), h.bool_ty());

    // Shape: `Eq( (map f) (ret a), ret (f a) )`.
    let map_op = h.var(
        "map",
        h.fun_ty(
            h.fun_ty(elem(&h), elem(&h)),
            h.fun_ty(carrier(&h), carrier(&h)),
        ),
    );
    let f = h.var("f", h.fun_ty(elem(&h), elem(&h)));
    let a = h.var("a", elem(&h));
    let lhs = h
        .app(
            h.app(map_op, f.clone()).unwrap(),
            h.app(ret_var(&h), a.clone()).unwrap(),
        )
        .unwrap();
    let rhs = h.app(ret_var(&h), h.app(f, a).unwrap()).unwrap();
    let want = h.eq(lhs, rhs).unwrap();
    assert_eq!(law, want, "law statement is the monad-map-law equation");
}

/// The type surface resolves through the traits: variables → `tvar`, `nat`/
/// `bool` → the base types, arrows → `fun_ty`; an applied constructor is
/// (honestly) unsupported until a theory trait supplies it.
#[test]
fn type_resolution_through_the_traits() {
    use covalence_haskell::ast::Ty;
    let h = NativeHol;

    assert_eq!(resolve_ty(&h, &Ty::var("a")).unwrap(), h.tvar("a"));
    assert_eq!(resolve_ty(&h, &Ty::base("nat")).unwrap(), Nat::nat_ty(&h));
    assert_eq!(resolve_ty(&h, &Ty::base("bool")).unwrap(), h.bool_ty());
    assert_eq!(
        resolve_ty(&h, &Ty::fun(Ty::base("nat"), Ty::base("bool"))).unwrap(),
        h.fun_ty(Nat::nat_ty(&h), h.bool_ty())
    );
    // `option a` has no theory trait yet — unsupported, not a silent miss.
    assert!(resolve_ty(&h, &Ty::con("option", vec![Ty::var("a")])).is_err());
}

/// A `nat`-typed definition lowers arithmetic through the `Nat` trait: `\x. x +
/// 1` over `nat` builds `Nat::add x (Nat::lit 1)`.
#[test]
fn nat_arithmetic_lowers_through_the_nat_trait() {
    let h = NativeHol;
    let module = parse_module("inc :: nat -> nat\ninc x = x + 1").expect("parses");
    let (name, term) = lower_decl_in(&h, &Env::new(), &module[0]).expect("lowers");
    assert_eq!(name, "inc");

    let x = h.var("x", Nat::nat_ty(&h));
    let body = Nat::add(&h, x, Nat::lit(&h, 1)).unwrap();
    let want = h.lam("x", Nat::nat_ty(&h), body);
    assert_eq!(term, want);
    // Well-typed `nat -> nat`.
    assert_eq!(
        h.type_of(&term).unwrap(),
        h.fun_ty(Nat::nat_ty(&h), Nat::nat_ty(&h))
    );
}
