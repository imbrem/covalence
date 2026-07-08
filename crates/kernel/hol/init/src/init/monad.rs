//! A **general theory of monads**, and its instantiation for the `option`
//! and `list` monads — the "Haskell theory instantiated for concrete types"
//! payoff: prove a derived law *once* from the abstract monad laws, then get
//! it for free on each concrete monad by discharging that monad's proved law.
//!
//! ## The abstraction
//!
//! A monad is modelled by two free-variable operations over an (abstract)
//! carrier type `m` and element type `α`:
//!
//! - `ret  : α → m`                    (return / unit)
//! - `bind : m → (α → m) → m`          (>>=)
//!
//! with **map** *defined* on top of them:
//!
//! - `map f x ≔ bind x (λx. ret (f x))`   (`map : (α → α) → m → m`)
//!
//! The carrier `m` is a plain HOL **type variable** (standard HOL has no
//! type-constructor variables), so the abstraction is single-typed: `ret`,
//! `bind`, `map` all live over one carrier. Concrete monads instantiate `m`
//! to `option α` / `list α` via [`Thm::inst_tfree`] and `ret`/`bind` to their
//! operations via [`Thm::inst`].
//!
//! ## The general theorem — [`monad_map_ret`]
//!
//! From the **left-identity** law alone, taken as an assumed hypothesis
//!
//! ```text
//! H_lid : ∀x k. bind (ret x) k = k x
//! ```
//!
//! we derive, *conditionally on `H_lid`*,
//!
//! ```text
//! monad_map_ret : {H_lid} ⊢ map f (ret a) = ret (f a)
//! ```
//!
//! by instantiating `H_lid` at `x ≔ a`, `k ≔ (λx. ret (f x))` and β-reducing:
//! `map f (ret a) = bind (ret a) (λx. ret (f x)) = (λx. ret (f x)) a =
//! ret (f a)`. The single hypothesis `H_lid` is exactly the abstract law the
//! theorem is conditional on — nothing else is assumed.
//!
//! ## The instances
//!
//! Each concrete monad *proves its own* left-identity (hypothesis-free), then
//! [`Thm::inst_tfree`] / [`Thm::inst`]s [`monad_map_ret`] at its operations and
//! discharges `H_lid` with that proof — yielding a **hypothesis-free** map law
//! on the concrete type:
//!
//! - **option** (`ret ≔ some`, `bind ≔ option_bind`, no induction — pure case
//!   analysis via [`case_some`](crate::init::option::case_some)):
//!   [`option_left_id`] then [`option_map_ret`]: `⊢ option_map f (some a) =
//!   some (f a)`.
//! - **list** (`ret ≔ singleton`, `bind ≔ concatMap` = `foldr (λx acc. cat
//!   (k x) acc) nil`): [`list_left_id`] reduces to the **append-nil** law
//!   `cat (k x) nil = k x` ([`cat_nil_r`](crate::init::list::cov::cat_nil_r_cov)),
//!   then [`list_map_ret`]: `⊢ list_map f (singleton a) = singleton (f a)`.

use covalence_core::{Result, Term, Type, subst};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::defs::{
    cons, list, list_cat, list_foldr, nil, none, option, option_case, some,
};
use covalence_hol_eval::derived::DerivedRules;

use crate::init::ext::{TermExt, ThmExt};

// ============================================================================
// The abstract monad signature — free type variables + free operations.
// ============================================================================

/// The element type variable `α`.
fn elem() -> Type {
    Type::tfree("a")
}

/// The abstract monad carrier type variable `m` (instantiated per monad).
fn carrier() -> Type {
    Type::tfree("mcar")
}

/// `bind : m → (α → m) → m`.
fn bind_ty(el: &Type, car: &Type) -> Type {
    Type::fun(
        car.clone(),
        Type::fun(Type::fun(el.clone(), car.clone()), car.clone()),
    )
}

/// `λx:α. ret (f x)` — the map kernel (`f : α → α`, `ret : α → m`).
fn ret_of_f(ret: &Term, f: &Term, el: &Type) -> Term {
    let x = Term::free("x", el.clone());
    let body = Term::app(ret.clone(), Term::app(f.clone(), x.clone()));
    Term::abs(el.clone(), subst::close(&body, "x"))
}

/// `map ≔ λf:(α→α). λx:m. bind x (λy. ret (f y))` — the monadic map built
/// from `ret` / `bind`.
fn map_op(ret: &Term, bind: &Term, el: &Type, car: &Type) -> Term {
    let f = Term::free("f", Type::fun(el.clone(), el.clone()));
    let x = Term::free("x", car.clone());
    let kern = ret_of_f(ret, &f, el); // λy. ret (f y), with `f` free
    let body = Term::app(Term::app(bind.clone(), x.clone()), kern);
    let lam_x = Term::abs(car.clone(), subst::close(&body, "x"));
    Term::abs(Type::fun(el.clone(), el.clone()), subst::close(&lam_x, "f"))
}

/// `∀x k. bind (ret x) k = k x` — the left-identity law, over the given
/// `ret` / `bind` and element / carrier types.
fn left_id_law(ret: &Term, bind: &Term, el: &Type, car: &Type) -> Result<Term> {
    let x = Term::free("x", el.clone());
    let k_ty = Type::fun(el.clone(), car.clone());
    let k = Term::free("k", k_ty.clone());
    let lhs = Term::app(
        Term::app(bind.clone(), Term::app(ret.clone(), x.clone())),
        k.clone(),
    );
    let rhs = Term::app(k.clone(), x.clone());
    lhs.equals(rhs)?.forall("k", k_ty)?.forall("x", el.clone())
}

// ============================================================================
// The general theorem.
// ============================================================================

cached_thm! {
    /// `{H_lid} ⊢ map f (ret a) = ret (f a)` — the general derived monad-map
    /// law, over the **abstract** monad (`ret`, `bind` free variables; carrier
    /// `m` a free type variable), conditional on left-identity `H_lid`. See the
    /// [module docs](self) for the derivation. The one hypothesis is exactly
    /// `H_lid`; instances discharge it with their own proved left-identity.
    pub fn monad_map_ret() -> Result<Thm> {
        let (el, car) = (elem(), carrier());
        let ret = Term::free("ret", Type::fun(el.clone(), car.clone()));
        let bind = Term::free("bind", bind_ty(&el, &car));
        let f = Term::free("f", Type::fun(el.clone(), el.clone()));
        let a = Term::free("a", el.clone());

        // Assume left-identity, then instantiate it at x ≔ a, k ≔ λy. ret (f y).
        let hlid = left_id_law(&ret, &bind, &el, &car)?;
        let kern = ret_of_f(&ret, &f, &el);
        let inst = Thm::assume(hlid)?
            .all_elim(a.clone())?
            .all_elim(kern)?; // {H_lid} ⊢ bind (ret a) (λy. ret (f y)) = (λy. ret (f y)) a

        // map f (ret a) β-reduces to `bind (ret a) (λy. ret (f y))`.
        let map = map_op(&ret, &bind, &el, &car);
        let map_lhs = Term::app(Term::app(map, f), Term::app(ret, a));
        let map_beta = map_lhs.reduce()?; // ⊢ map f (ret a) = bind (ret a) (λy. ret (f y))

        // Chain, then β-reduce the RHS `(λy. ret (f y)) a` to `ret (f a)`.
        map_beta.trans(inst)?.rhs_conv(|t| t.reduce())
    }
}

/// Discharge the single left-identity hypothesis of an instantiated
/// [`monad_map_ret`] with a proof of it. `proof : ⊢ H_lid` must match the
/// theorem's hypothesis exactly; `imp_intro` then removes it and `imp_elim`
/// closes it, so the result is hypothesis-free (asserted by the tests).
fn discharge(inst_thm: Thm, proof: Thm) -> Result<Thm> {
    let hyp = proof.concl().clone();
    inst_thm.imp_intro(&hyp)?.imp_elim(proof)
}

// ============================================================================
// OPTION monad — ret ≔ some, bind ≔ option_bind. No induction.
// ============================================================================

/// `option_bind ≔ λm:option α. λk:(α→option α). option_case none k m` — the
/// option monad's bind (`m >>= k`).
fn option_bind(alpha: &Type) -> Term {
    let opt = option(alpha.clone());
    let m = Term::free("m", opt.clone());
    let k = Term::free("k", Type::fun(alpha.clone(), opt.clone()));
    let body = Term::app(
        Term::app(
            Term::app(option_case(alpha.clone(), opt.clone()), none(alpha.clone())),
            k.clone(),
        ),
        m.clone(),
    );
    let lam_k = Term::abs(
        Type::fun(alpha.clone(), opt.clone()),
        subst::close(&body, "k"),
    );
    Term::abs(opt, subst::close(&lam_k, "m"))
}

/// `⊢ ∀x k. option_bind (some x) k = k x` — the option monad's **left
/// identity**, hypothesis-free (by β + [`case_some`](crate::init::option::case_some);
/// no induction).
pub fn option_left_id(alpha: &Type) -> Result<Thm> {
    let opt = option(alpha.clone());
    let k_ty = Type::fun(alpha.clone(), opt.clone());
    let x = Term::free("x", alpha.clone());
    let k = Term::free("k", k_ty.clone());
    let bind = option_bind(alpha);

    let some_x = Term::app(some(alpha.clone()), x.clone());
    let t = Term::app(Term::app(bind, some_x), k.clone()); // option_bind (some x) k
    // β: option_bind (some x) k = option_case none k (some x).
    let beta = t.reduce()?;
    // option_case none k (some x) = k x.
    let cs = crate::init::option::case_some(alpha, &opt, &none(alpha.clone()), &k, &x)?;
    beta.trans(cs)? // ⊢ option_bind (some x) k = k x
        .all_intro("k", k_ty)?
        .all_intro("x", alpha.clone())
}

cached_thm! {
    /// `⊢ option_map f (some a) = some (f a)` — **hypothesis-free**. Obtained
    /// by instantiating the general [`monad_map_ret`] at `ret ≔ some`,
    /// `bind ≔ option_bind` and discharging `H_lid` with [`option_left_id`].
    /// Here `option_map f = λm. option_bind m (λx. some (f x))`.
    pub fn option_map_ret() -> Result<Thm> {
        let a = elem();
        let inst = monad_map_ret()
            .inst_tfree("mcar", option(a.clone()))?
            .inst("ret", some(a.clone()))?
            .inst("bind", option_bind(&a))?;
        discharge(inst, option_left_id(&a)?)
    }
}

// ============================================================================
// LIST monad — ret ≔ singleton, bind ≔ concatMap. Left-id needs append-nil.
// ============================================================================

/// `singleton ≔ λv:α. cons v nil` — the list monad's return.
fn singleton(alpha: &Type) -> Term {
    let v = Term::free("v", alpha.clone());
    let body = Term::app(
        Term::app(cons(alpha.clone()), v.clone()),
        nil(alpha.clone()),
    );
    Term::abs(alpha.clone(), subst::close(&body, "v"))
}

/// `λy:α. λacc:list α. cat (k y) acc` — the `concatMap` fold step for the
/// given continuation `k`.
fn concat_step(alpha: &Type, k: &Term) -> Term {
    let la = list(alpha.clone());
    let y = Term::free("y", alpha.clone());
    let acc = Term::free("acc", la.clone());
    let body = Term::app(
        Term::app(list_cat(alpha.clone()), Term::app(k.clone(), y.clone())),
        acc.clone(),
    );
    let lam_acc = Term::abs(la.clone(), subst::close(&body, "acc"));
    Term::abs(alpha.clone(), subst::close(&lam_acc, "y"))
}

/// `list_bind ≔ λxs:list α. λk:(α→list α). foldr (λy acc. cat (k y) acc) nil
/// xs` — the list monad's bind (concat-map / `xs >>= k`).
fn list_bind(alpha: &Type) -> Term {
    let la = list(alpha.clone());
    let k_ty = Type::fun(alpha.clone(), la.clone());
    let xs = Term::free("xs", la.clone());
    let k = Term::free("k", k_ty.clone());
    let step = concat_step(alpha, &k);
    let body = Term::app(
        Term::app(
            Term::app(list_foldr(alpha.clone(), la.clone()), step),
            nil(alpha.clone()),
        ),
        xs.clone(),
    );
    let lam_k = Term::abs(k_ty, subst::close(&body, "k"));
    Term::abs(la, subst::close(&lam_k, "xs"))
}

/// `⊢ ∀x k. list_bind (singleton x) k = k x` — the list monad's **left
/// identity**, hypothesis-free. `list_bind (singleton x) k` unfolds (foldr
/// over the one-element list) to `cat (k x) nil`, which the append-nil law
/// [`cat_nil_r`](crate::init::list::cov::cat_nil_r_cov) collapses to `k x`.
pub fn list_left_id(alpha: &Type) -> Result<Thm> {
    let la = list(alpha.clone());
    let k_ty = Type::fun(alpha.clone(), la.clone());
    let x = Term::free("x", alpha.clone());
    let k = Term::free("k", k_ty.clone());
    let step = concat_step(alpha, &k);
    let nil_a = nil(alpha.clone());

    let sing_x = Term::app(singleton(alpha), x.clone());
    let t = Term::app(Term::app(list_bind(alpha), sing_x), k.clone()); // list_bind (singleton x) k
    // β: list_bind (singleton x) k = foldr step nil (cons x nil).
    let beta = t.reduce()?;
    // foldr step nil (cons x nil) = step x (foldr step nil nil).
    let fc = crate::init::list_recursion::foldr_cons(alpha, &la, &step, &nil_a, &x, &nil_a)?;
    // foldr step nil nil = nil, congruenced under `step x`.
    let fn_nil = crate::init::list_recursion::foldr_nil(alpha, &la, &step, &nil_a)?;
    let cong = fn_nil.cong_arg(Term::app(step.clone(), x.clone()))?; // step x (foldr…) = step x nil
    // ⊢ list_bind (singleton x) k = step x nil, then β: step x nil = cat (k x) nil.
    let to_cat = crate::init::eq::trans_chain([beta, fc, cong])?.rhs_conv(|u| u.reduce())?;
    // cat (k x) nil = k x  (append-nil / right unit).
    let cat_nil_r = crate::init::list::cov::cat_nil_r_cov()
        .inst_tfree("a", alpha.clone())?
        .all_elim(Term::app(k.clone(), x.clone()))?;
    to_cat
        .trans(cat_nil_r)? // ⊢ list_bind (singleton x) k = k x
        .all_intro("k", k_ty)?
        .all_intro("x", alpha.clone())
}

cached_thm! {
    /// `⊢ list_map f (singleton a) = singleton (f a)` — **hypothesis-free**.
    /// Obtained by instantiating the general [`monad_map_ret`] at
    /// `ret ≔ singleton`, `bind ≔ list_bind` (concat-map) and discharging
    /// `H_lid` with [`list_left_id`]. Here `list_map f = λm. list_bind m
    /// (λx. singleton (f x))`.
    pub fn list_map_ret() -> Result<Thm> {
        let a = elem();
        let inst = monad_map_ret()
            .inst_tfree("mcar", list(a.clone()))?
            .inst("ret", singleton(&a))?
            .inst("bind", list_bind(&a))?;
        discharge(inst, list_left_id(&a)?)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The general theorem carries **exactly** its one abstract hypothesis
    /// `H_lid` and has the expected `map f (ret a) = ret (f a)` conclusion.
    #[test]
    fn monad_map_ret_is_conditional_on_left_id() {
        let (el, car) = (elem(), carrier());
        let ret = Term::free("ret", Type::fun(el.clone(), car.clone()));
        let bind = Term::free("bind", bind_ty(&el, &car));
        let f = Term::free("f", Type::fun(el.clone(), el.clone()));
        let a = Term::free("a", el.clone());

        let thm = monad_map_ret();

        // Exactly one hypothesis, and it is the left-identity law.
        let hlid = left_id_law(&ret, &bind, &el, &car).unwrap();
        assert_eq!(thm.hyps().len(), 1, "one hypothesis: the abstract law");
        assert_eq!(thm.hyps().iter().next().unwrap(), &hlid);

        // Conclusion: map f (ret a) = ret (f a).
        let map = map_op(&ret, &bind, &el, &car);
        let lhs = Term::app(Term::app(map, f.clone()), Term::app(ret.clone(), a.clone()));
        let rhs = Term::app(ret, Term::app(f, a));
        assert_eq!(thm.concl(), &lhs.equals(rhs).unwrap());
    }

    /// The concrete left-identity laws are genuine (hypothesis-free).
    #[test]
    fn concrete_left_ids_are_genuine() {
        assert!(option_left_id(&elem()).unwrap().hyps().is_empty());
        assert!(list_left_id(&elem()).unwrap().hyps().is_empty());
    }

    /// `option_map_ret` is hypothesis-free with conclusion
    /// `option_map f (some a) = some (f a)`.
    #[test]
    fn option_map_ret_is_genuine() {
        let a = elem();
        let thm = option_map_ret();
        assert!(
            thm.hyps().is_empty(),
            "option instance must discharge H_lid"
        );

        let f = Term::free("f", Type::fun(a.clone(), a.clone()));
        let av = Term::free("a", a.clone());
        let map = map_op(&some(a.clone()), &option_bind(&a), &a, &option(a.clone()));
        let lhs = Term::app(
            Term::app(map, f.clone()),
            Term::app(some(a.clone()), av.clone()),
        );
        let rhs = Term::app(some(a.clone()), Term::app(f, av));
        assert_eq!(thm.concl(), &lhs.equals(rhs).unwrap());
    }

    /// `list_map_ret` is hypothesis-free with conclusion
    /// `list_map f (singleton a) = singleton (f a)`.
    #[test]
    fn list_map_ret_is_genuine() {
        let a = elem();
        let thm = list_map_ret();
        assert!(thm.hyps().is_empty(), "list instance must discharge H_lid");

        let f = Term::free("f", Type::fun(a.clone(), a.clone()));
        let av = Term::free("a", a.clone());
        let map = map_op(&singleton(&a), &list_bind(&a), &a, &list(a.clone()));
        let lhs = Term::app(
            Term::app(map, f.clone()),
            Term::app(singleton(&a), av.clone()),
        );
        let rhs = Term::app(singleton(&a), Term::app(f, av));
        assert_eq!(thm.concl(), &lhs.equals(rhs).unwrap());
    }
}
