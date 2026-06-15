//! `rel 'a 'b` + relation properties (preord, pord, per, part).

use std::sync::LazyLock;

use crate::hol;
use crate::term::{Term, Type};

use super::canonical::Canonical;
use super::spec::TypeSpec;

/// `rel 'a 'b := 'a → 'b → bool`.
pub fn rel_spec() -> TypeSpec {
    static LAZY: LazyLock<TypeSpec> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        let beta = Type::tfree("b");
        let carrier = Type::fun(alpha, Type::fun(beta, Type::bool()));
        TypeSpec::newtype(Canonical::Rel, carrier)
    });
    LAZY.clone()
}
pub fn rel(alpha: Type, beta: Type) -> Type {
    Type::spec(rel_spec(), vec![alpha, beta])
}

// ============================================================================
// The `abs`/`rep` bridge, named: `rel.mk` and `rel.holds`. Every term
// op below funnels through these two (the only place the raw `abs`/`rep`
// coercions appear), mirroring `set.mk`/`set.mem`.
// ============================================================================

fn rel_mk_body() -> Term {
    // λp:(α→β→bool). abs p
    let alpha = Type::tfree("a");
    let beta = Type::tfree("b");
    let p_ty = Type::fun(alpha.clone(), Type::fun(beta.clone(), Type::bool()));
    let p = Term::free("p", p_ty.clone());
    let wrapped = Term::app(Term::spec_abs(rel_spec(), vec![alpha, beta]), p);
    hol::pub_abs("p", p_ty, wrapped)
}

poly_let_term! {
    /// `rel.mk : ('a → 'b → bool) → rel 'a 'b` ≡ `λp. abs p` — wrap a
    /// two-place predicate into a relation.
    rel_mk_spec, rel_mk(alpha, beta), Canonical::RelMk, rel_mk_body()
}

fn rel_holds_body() -> Term {
    // λr:rel α β. λx:α. λy:β. (rep r) x y
    let alpha = Type::tfree("a");
    let beta = Type::tfree("b");
    let r_ty = rel(alpha.clone(), beta.clone());
    let r = Term::free("r", r_ty.clone());
    let x = Term::free("x", alpha.clone());
    let y = Term::free("y", beta.clone());
    let rep = Term::spec_rep(rel_spec(), vec![alpha.clone(), beta.clone()]);
    let applied = Term::app(Term::app(Term::app(rep, r), x), y);
    let lam_y = hol::pub_abs("y", beta, applied);
    let lam_x = hol::pub_abs("x", alpha, lam_y);
    hol::pub_abs("r", r_ty, lam_x)
}

poly_let_term! {
    /// `rel.holds : rel 'a 'b → 'a → 'b → bool` ≡ `λr x y. (rep r) x y`
    /// — does relation `r` relate `x` to `y`.
    rel_holds_spec, rel_holds(alpha, beta), Canonical::RelHolds, rel_holds_body()
}

/// `rel.holds[α,β] r x y` — builder over the [`rel_holds`] constant.
fn holds(alpha: &Type, beta: &Type, r: &Term, x: &Term, y: &Term) -> Term {
    let h = rel_holds(alpha.clone(), beta.clone());
    Term::app(Term::app(Term::app(h, r.clone()), x.clone()), y.clone())
}

/// `rel.mk[α,β] (λ<na>:α. λ<nb>:β. body)` — wrap a `bool`-body (open in
/// the free vars `<na>:α`, `<nb>:β`) into a `rel α β`. Builder over the
/// [`rel_mk`] constant.
fn mk(alpha: &Type, beta: &Type, na: &str, nb: &str, body: Term) -> Term {
    let lam = hol::pub_abs(na, alpha.clone(), hol::pub_abs(nb, beta.clone(), body));
    Term::app(rel_mk(alpha.clone(), beta.clone()), lam)
}

// ============================================================================
// Point-free relation utilities: id / compose / converse.
// ============================================================================

fn rel_id_body() -> Term {
    // mk (λx y. x = y)
    let alpha = Type::tfree("a");
    let x = Term::free("x", alpha.clone());
    let y = Term::free("y", alpha.clone());
    mk(&alpha, &alpha, "x", "y", hol::hol_eq(x, y))
}

poly_let_term! {
    /// `rel.id : rel 'a 'a` ≡ `mk (λx y. x = y)` — the identity
    /// (equality) relation.
    rel_id_spec, rel_id(alpha), Canonical::RelId, rel_id_body()
}

fn rel_compose_body() -> Term {
    // λs r. mk (λx z. ∃y. holds r x y ∧ holds s y z)
    let alpha = Type::tfree("a");
    let beta = Type::tfree("b");
    let gamma = Type::tfree("c");
    let r_ty = rel(alpha.clone(), beta.clone()); // r : rel a b
    let s_ty = rel(beta.clone(), gamma.clone()); // s : rel b c
    let s = Term::free("s", s_ty.clone());
    let r = Term::free("r", r_ty.clone());
    let x = Term::free("x", alpha.clone());
    let y = Term::free("y", beta.clone());
    let z = Term::free("z", gamma.clone());
    let conj = hol::hol_and(
        holds(&alpha, &beta, &r, &x, &y),
        holds(&beta, &gamma, &s, &y, &z),
    );
    let exists_y = hol::hol_exists("y", beta, conj);
    let composed = mk(&alpha, &gamma, "x", "z", exists_y); // rel a c
    let lam_r = hol::pub_abs("r", r_ty, composed);
    hol::pub_abs("s", s_ty, lam_r)
}

poly_let_term! {
    /// `rel.compose : rel 'b 'c → rel 'a 'b → rel 'a 'c` ≡
    /// `λs r. mk (λx z. ∃y. holds r x y ∧ holds s y z)` — relational
    /// composition `s ∘ r`.
    rel_compose_spec, rel_compose(alpha, beta, gamma), Canonical::RelCompose, rel_compose_body()
}

fn rel_converse_body() -> Term {
    // λr. mk (λy x. holds r x y)
    let alpha = Type::tfree("a");
    let beta = Type::tfree("b");
    let r_ty = rel(alpha.clone(), beta.clone());
    let r = Term::free("r", r_ty.clone());
    let x = Term::free("x", alpha.clone());
    let y = Term::free("y", beta.clone());
    let body = holds(&alpha, &beta, &r, &x, &y);
    let conv = mk(&beta, &alpha, "y", "x", body); // rel b a
    hol::pub_abs("r", r_ty, conv)
}

poly_let_term! {
    /// `rel.converse : rel 'a 'b → rel 'b 'a` ≡
    /// `λr. mk (λy x. holds r x y)` — the converse relation.
    rel_converse_spec, rel_converse(alpha, beta), Canonical::RelConverse, rel_converse_body()
}

// ============================================================================
// Functionality: deterministic / total / isFunction, and the
// function↔relation bridge toFun / graph.
// ============================================================================

fn rel_deterministic_body() -> Term {
    // λr. ∀x y y'. holds r x y ⟹ holds r x y' ⟹ y = y'
    let alpha = Type::tfree("a");
    let beta = Type::tfree("b");
    let r_ty = rel(alpha.clone(), beta.clone());
    let r = Term::free("r", r_ty.clone());
    let x = Term::free("x", alpha.clone());
    let y = Term::free("y", beta.clone());
    let y2 = Term::free("y2", beta.clone());
    let imp = hol::hol_imp(
        holds(&alpha, &beta, &r, &x, &y),
        hol::hol_imp(
            holds(&alpha, &beta, &r, &x, &y2),
            hol::hol_eq(y.clone(), y2.clone()),
        ),
    );
    let all = hol::hol_forall(
        "x",
        alpha,
        hol::hol_forall("y", beta.clone(), hol::hol_forall("y2", beta, imp)),
    );
    hol::pub_abs("r", r_ty, all)
}

poly_let_term! {
    /// `rel.deterministic : rel 'a 'b → bool` ≡
    /// `λr. ∀x y y'. holds r x y ⟹ holds r x y' ⟹ y = y'` —
    /// single-valuedness.
    rel_deterministic_spec, rel_deterministic(alpha, beta),
    Canonical::RelDeterministic, rel_deterministic_body()
}

fn rel_total_body() -> Term {
    // λr. ∀x. ∃y. holds r x y
    let alpha = Type::tfree("a");
    let beta = Type::tfree("b");
    let r_ty = rel(alpha.clone(), beta.clone());
    let r = Term::free("r", r_ty.clone());
    let x = Term::free("x", alpha.clone());
    let y = Term::free("y", beta.clone());
    let r_xy = holds(&alpha, &beta, &r, &x, &y);
    let exists_y = hol::hol_exists("y", beta, r_xy);
    let all_x = hol::hol_forall("x", alpha, exists_y);
    hol::pub_abs("r", r_ty, all_x)
}

poly_let_term! {
    /// `rel.total : rel 'a 'b → bool` ≡ `λr. ∀x. ∃y. holds r x y` —
    /// every input has at least one image.
    rel_total_spec, rel_total(alpha, beta), Canonical::RelTotal, rel_total_body()
}

fn rel_is_function_body() -> Term {
    // λr. deterministic r ∧ total r
    let alpha = Type::tfree("a");
    let beta = Type::tfree("b");
    let r_ty = rel(alpha.clone(), beta.clone());
    let r = Term::free("r", r_ty.clone());
    let det = Term::app(rel_deterministic(alpha.clone(), beta.clone()), r.clone());
    let tot = Term::app(rel_total(alpha.clone(), beta.clone()), r.clone());
    hol::pub_abs("r", r_ty, hol::hol_and(det, tot))
}

poly_let_term! {
    /// `rel.isFunction : rel 'a 'b → bool` ≡
    /// `λr. deterministic r ∧ total r` — the relation is the graph of a
    /// total function.
    rel_is_function_spec, rel_is_function(alpha, beta),
    Canonical::RelIsFunction, rel_is_function_body()
}

fn rel_to_fun_body() -> Term {
    // λr x. ε y. holds r x y
    let alpha = Type::tfree("a");
    let beta = Type::tfree("b");
    let r_ty = rel(alpha.clone(), beta.clone());
    let r = Term::free("r", r_ty.clone());
    let x = Term::free("x", alpha.clone());
    let y = Term::free("y", beta.clone());
    let pred = hol::pub_abs("y", beta.clone(), holds(&alpha, &beta, &r, &x, &y));
    let eps = Term::app(Term::select_op(beta), pred); // ε y. holds r x y
    let lam_x = hol::pub_abs("x", alpha, eps);
    hol::pub_abs("r", r_ty, lam_x)
}

poly_let_term! {
    /// `rel.toFun : rel 'a 'b → ('a → 'b)` ≡ `λr x. ε y. holds r x y` —
    /// pick a function respecting `r` (the function when `isFunction r`,
    /// ε-junk on inputs with no/ambiguous image).
    rel_to_fun_spec, rel_to_fun(alpha, beta), Canonical::RelToFun, rel_to_fun_body()
}

fn rel_graph_body() -> Term {
    // λf. mk (λx y. f x = y)
    let alpha = Type::tfree("a");
    let beta = Type::tfree("b");
    let f_ty = Type::fun(alpha.clone(), beta.clone());
    let f = Term::free("f", f_ty.clone());
    let x = Term::free("x", alpha.clone());
    let y = Term::free("y", beta.clone());
    let fx_eq_y = hol::hol_eq(Term::app(f.clone(), x.clone()), y.clone());
    let g = mk(&alpha, &beta, "x", "y", fx_eq_y);
    hol::pub_abs("f", f_ty, g)
}

poly_let_term! {
    /// `rel.graph : ('a → 'b) → rel 'a 'b` ≡ `λf. mk (λx y. f x = y)` —
    /// the graph of a function as a relation. Inverse-ish to
    /// [`rel_to_fun`]: `toFun (graph f) = f`, and `graph (toFun r) = r`
    /// when `isFunction r`.
    rel_graph_spec, rel_graph(alpha, beta), Canonical::RelGraph, rel_graph_body()
}

fn transitive_pred(alpha: Type) -> Term {
    let r_ty = Type::fun(alpha.clone(), Type::fun(alpha.clone(), Type::bool()));
    let r = Term::free("R", r_ty.clone());
    let x = Term::free("x", alpha.clone());
    let y = Term::free("y", alpha.clone());
    let z = Term::free("z", alpha.clone());
    let r_xy = Term::app(Term::app(r.clone(), x.clone()), y.clone());
    let r_yz = Term::app(Term::app(r.clone(), y.clone()), z.clone());
    let r_xz = Term::app(Term::app(r.clone(), x.clone()), z.clone());
    let body = hol::hol_imp(r_xy, hol::hol_imp(r_yz, r_xz));
    let all_z = hol::hol_forall("z", alpha.clone(), body);
    let all_yz = hol::hol_forall("y", alpha.clone(), all_z);
    let all_xyz = hol::hol_forall("x", alpha.clone(), all_yz);
    hol::pub_abs("R", r_ty, all_xyz)
}

fn reflexive_pred(alpha: Type) -> Term {
    let r_ty = Type::fun(alpha.clone(), Type::fun(alpha.clone(), Type::bool()));
    let r = Term::free("R", r_ty.clone());
    let x = Term::free("x", alpha.clone());
    let r_xx = Term::app(Term::app(r.clone(), x.clone()), x);
    let body = hol::hol_forall("x", alpha.clone(), r_xx);
    hol::pub_abs("R", r_ty, body)
}

fn symmetric_pred(alpha: Type) -> Term {
    let r_ty = Type::fun(alpha.clone(), Type::fun(alpha.clone(), Type::bool()));
    let r = Term::free("R", r_ty.clone());
    let x = Term::free("x", alpha.clone());
    let y = Term::free("y", alpha.clone());
    let r_xy = Term::app(Term::app(r.clone(), x.clone()), y.clone());
    let r_yx = Term::app(Term::app(r.clone(), y.clone()), x.clone());
    let body = hol::hol_imp(r_xy, r_yx);
    let all_y = hol::hol_forall("y", alpha.clone(), body);
    let all_xy = hol::hol_forall("x", alpha.clone(), all_y);
    hol::pub_abs("R", r_ty, all_xy)
}

fn antisymmetric_pred(alpha: Type) -> Term {
    let r_ty = Type::fun(alpha.clone(), Type::fun(alpha.clone(), Type::bool()));
    let r = Term::free("R", r_ty.clone());
    let x = Term::free("x", alpha.clone());
    let y = Term::free("y", alpha.clone());
    let r_xy = Term::app(Term::app(r.clone(), x.clone()), y.clone());
    let r_yx = Term::app(Term::app(r.clone(), y.clone()), x.clone());
    let x_eq_y = hol::hol_eq(x.clone(), y.clone());
    let body = hol::hol_imp(r_xy, hol::hol_imp(r_yx, x_eq_y));
    let all_y = hol::hol_forall("y", alpha.clone(), body);
    let all_xy = hol::hol_forall("x", alpha.clone(), all_y);
    hol::pub_abs("R", r_ty, all_xy)
}

fn combine_props(alpha: Type, props: &[fn(Type) -> Term]) -> Term {
    let r_ty = Type::fun(alpha.clone(), Type::fun(alpha.clone(), Type::bool()));
    let r = Term::free("R", r_ty.clone());
    let mut applications: Vec<Term> = props
        .iter()
        .map(|p| Term::app(p(alpha.clone()), r.clone()))
        .collect();
    let mut result = applications.remove(0);
    for next in applications {
        result = hol::hol_and(result, next);
    }
    hol::pub_abs("R", r_ty, result)
}

fn rel_property_spec(symbol: Canonical, props: &[fn(Type) -> Term]) -> TypeSpec {
    let alpha = Type::tfree("a");
    let carrier = Type::fun(alpha.clone(), Type::fun(alpha.clone(), Type::bool()));
    TypeSpec::subtype(symbol, carrier, combine_props(alpha, props))
}

/// `preord 'a := rel 'a 'a where (transitive ∧ reflexive)`.
pub fn preord_spec() -> TypeSpec {
    static LAZY: LazyLock<TypeSpec> =
        LazyLock::new(|| rel_property_spec(Canonical::Preord, &[transitive_pred, reflexive_pred]));
    LAZY.clone()
}
pub fn preord(alpha: Type) -> Type {
    Type::spec(preord_spec(), vec![alpha])
}

/// `pord 'a := rel 'a 'a where (transitive ∧ reflexive ∧ antisymmetric)`.
pub fn pord_spec() -> TypeSpec {
    static LAZY: LazyLock<TypeSpec> = LazyLock::new(|| {
        rel_property_spec(
            Canonical::Pord,
            &[transitive_pred, reflexive_pred, antisymmetric_pred],
        )
    });
    LAZY.clone()
}
pub fn pord(alpha: Type) -> Type {
    Type::spec(pord_spec(), vec![alpha])
}

/// `per 'a := rel 'a 'a where (transitive ∧ symmetric)`.
pub fn per_spec() -> TypeSpec {
    static LAZY: LazyLock<TypeSpec> =
        LazyLock::new(|| rel_property_spec(Canonical::Per, &[transitive_pred, symmetric_pred]));
    LAZY.clone()
}
pub fn per(alpha: Type) -> Type {
    Type::spec(per_spec(), vec![alpha])
}

/// `part 'a := rel 'a 'a where (transitive ∧ symmetric ∧ reflexive)`.
pub fn part_spec() -> TypeSpec {
    static LAZY: LazyLock<TypeSpec> = LazyLock::new(|| {
        rel_property_spec(
            Canonical::Part,
            &[transitive_pred, symmetric_pred, reflexive_pred],
        )
    });
    LAZY.clone()
}
pub fn part(alpha: Type) -> Type {
    Type::spec(part_spec(), vec![alpha])
}
