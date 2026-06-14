//! `set 'a := 'a → bool` + set operations.
//!
//! `set α` is a `newtype` over the carrier `α → bool`. The two
//! coercions are named as catalogue constants:
//! [`set_mk`] (`set.mk : (α→bool) → set α`, the `abs` wrapper) and
//! [`set_mem`] (`set.mem : α → set α → bool`, membership via `rep`).
//! Every other operation funnels through these two, so they are the
//! only place the raw `abs`/`rep` coercions appear — which is also the
//! single seam to teach a future literal-backed `set` builtin (the
//! way `bytes` is accelerated today via [`crate::builtins`]).
//!
//! `set.empty`/`set.singleton`/`set.insert` are the constructors;
//! `set.union`/`set.intersect`/`set.diff`/`set.subset`/`set.isEmpty`
//! are defined pointwise on membership; `set.flatten` is the union of
//! a set of sets; `set.all`/`set.any` are the big conjunction/
//! disjunction over a `set bool`; `list.elems` is "appears at some
//! index".
//!
//! Finiteness and cardinality bridge through `list.elems`: `set.finite
//! s` holds iff `s` is the element-set of some list, `set.card s` is
//! the minimal length of such a covering list (= the count of distinct
//! elements; junk `ε` on infinite sets), and `set.card? s` guards that
//! with `set.finite` to return `none` for infinite sets.

use std::sync::LazyLock;

use crate::hol;
use crate::term::{Term, Type};

use super::canonical::Canonical;
use super::list::{list, list_index, list_length};
use super::nat::nat_le;
use super::option::{none, some};
use super::spec::{TermSpec, TypeSpec};

/// `set 'a := 'a → bool` — predicate-style sets.
pub fn set_spec() -> TypeSpec {
    static LAZY: LazyLock<TypeSpec> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        let carrier = Type::fun(alpha, Type::bool());
        TypeSpec::newtype(Canonical::Set, carrier)
    });
    LAZY.clone()
}
pub fn set(alpha: Type) -> Type {
    Type::spec(set_spec(), vec![alpha])
}

// ============================================================================
// The `abs`/`rep` bridge, named: `set.mk` and `set.mem`.
// ============================================================================

fn set_mk_body() -> Term {
    let alpha = Type::tfree("a");
    let pred_ty = Type::fun(alpha.clone(), Type::bool());
    let p = Term::free("p", pred_ty.clone());
    let wrapped = Term::app(Term::spec_abs(set_spec(), vec![alpha]), p);
    hol::pub_abs("p", pred_ty, wrapped)
}

poly_let_term! {
    /// `set.mk : ('a → bool) → set 'a` ≡ `λp. abs p` — wrap a
    /// membership predicate into a set.
    set_mk_spec, set_mk(alpha), Canonical::SetMk, set_mk_body()
}

fn set_mem_body() -> Term {
    let alpha = Type::tfree("a");
    let sa = set(alpha.clone());
    let x = Term::free("x", alpha.clone());
    let s = Term::free("s", sa.clone());
    let rep = Term::spec_rep(set_spec(), vec![alpha.clone()]);
    let rep_s_x = Term::app(Term::app(rep, s.clone()), x.clone());
    let lam_s = hol::pub_abs("s", sa, rep_s_x);
    hol::pub_abs("x", alpha, lam_s)
}

poly_let_term! {
    /// `set.mem : 'a → set 'a → bool` ≡ `λx s. (rep s) x` —
    /// membership.
    set_mem_spec, set_mem(alpha), Canonical::SetMem, set_mem_body()
}

/// `set.mem[α] x s` — membership of `x : α` in `s : set α`, as a
/// `bool` (builder over the [`set_mem`] constant).
fn mem(alpha: &Type, x: &Term, s: &Term) -> Term {
    Term::app(Term::app(set_mem(alpha.clone()), x.clone()), s.clone())
}

/// `set.mk[α] (λ<var>:α. body)` — wrap a `bool`-body (open in the free
/// var `<var> : α`) into a `set α` (builder over the [`set_mk`]
/// constant).
fn mk(alpha: &Type, var: &str, body: Term) -> Term {
    let pred = hol::pub_abs(var, alpha.clone(), body);
    Term::app(set_mk(alpha.clone()), pred)
}

// ============================================================================
// Constructors: empty / singleton / insert.
// ============================================================================

fn set_empty_body() -> Term {
    // mk (λx. F)
    let alpha = Type::tfree("a");
    mk(&alpha, "x", Term::bool_lit(false))
}

poly_let_term! {
    /// `set.empty : set 'a` ≡ `mk (λx. F)` — the empty set.
    set_empty_spec, set_empty(alpha), Canonical::SetEmpty, set_empty_body()
}

fn set_singleton_body() -> Term {
    // λa. mk (λx. x = a)
    let alpha = Type::tfree("a");
    let a = Term::free("a", alpha.clone());
    let x = Term::free("x", alpha.clone());
    let collected = mk(&alpha, "x", hol::hol_eq(x, a.clone()));
    hol::pub_abs("a", alpha, collected)
}

poly_let_term! {
    /// `set.singleton : 'a → set 'a` ≡ `λa. mk (λx. x = a)`.
    set_singleton_spec, set_singleton(alpha), Canonical::SetSingleton, set_singleton_body()
}

fn set_insert_body() -> Term {
    // λa s. mk (λx. x = a ∨ mem x s)
    let alpha = Type::tfree("a");
    let sa = set(alpha.clone());
    let a = Term::free("a", alpha.clone());
    let s = Term::free("s", sa.clone());
    let x = Term::free("x", alpha.clone());
    let body = hol::hol_or(hol::hol_eq(x.clone(), a.clone()), mem(&alpha, &x, &s));
    let collected = mk(&alpha, "x", body);
    let lam_s = hol::pub_abs("s", sa, collected);
    hol::pub_abs("a", alpha, lam_s)
}

poly_let_term! {
    /// `set.insert : 'a → set 'a → set 'a` ≡
    /// `λa s. mk (λx. x = a ∨ mem x s)`.
    set_insert_spec, set_insert(alpha), Canonical::SetInsert, set_insert_body()
}

// ============================================================================
// Binary set operations (pointwise on membership).
// ============================================================================

/// Build a binary `set α → set α → set α` (or `… → bool`) body whose
/// per-element behaviour is `combine (mem x s) (mem x t)`.
fn binop_body(combine: fn(Term, Term) -> Term, wrap: bool) -> Term {
    let alpha = Type::tfree("a");
    let sa = set(alpha.clone());
    let s = Term::free("s", sa.clone());
    let t = Term::free("t", sa.clone());
    let x = Term::free("x", alpha.clone());
    let elem = combine(mem(&alpha, &x, &s), mem(&alpha, &x, &t));
    let inner = if wrap {
        // pointwise: mk (λx. (mem x s) ⋄ (mem x t))
        mk(&alpha, "x", elem)
    } else {
        // relational: ∀x. (mem x s) ⋄ (mem x t) — a bool, no wrapping
        hol::hol_forall("x", alpha.clone(), elem)
    };
    let lam_t = hol::pub_abs("t", sa.clone(), inner);
    hol::pub_abs("s", sa, lam_t)
}

fn set_union_body() -> Term {
    binop_body(hol::hol_or, true)
}

poly_let_term! {
    /// `set.union : set 'a → set 'a → set 'a` ≡
    /// `λs t. mk (λx. mem x s ∨ mem x t)`.
    set_union_spec, set_union(alpha), Canonical::SetUnion, set_union_body()
}

fn set_intersect_body() -> Term {
    binop_body(hol::hol_and, true)
}

poly_let_term! {
    /// `set.intersect : set 'a → set 'a → set 'a` ≡
    /// `λs t. mk (λx. mem x s ∧ mem x t)`.
    set_intersect_spec, set_intersect(alpha), Canonical::SetIntersect, set_intersect_body()
}

fn set_diff_body() -> Term {
    binop_body(|s_x, t_x| hol::hol_and(s_x, hol::hol_not(t_x)), true)
}

poly_let_term! {
    /// `set.diff : set 'a → set 'a → set 'a` ≡
    /// `λs t. mk (λx. mem x s ∧ ¬ mem x t)`.
    set_diff_spec, set_diff(alpha), Canonical::SetDiff, set_diff_body()
}

fn set_subset_body() -> Term {
    binop_body(hol::hol_imp, false)
}

poly_let_term! {
    /// `set.subset : set 'a → set 'a → bool` ≡
    /// `λs t. ∀x. mem x s ⟹ mem x t`.
    set_subset_spec, set_subset(alpha), Canonical::SetSubset, set_subset_body()
}

fn set_is_empty_body() -> Term {
    // λs. ∀x. ¬ mem x s
    let alpha = Type::tfree("a");
    let sa = set(alpha.clone());
    let s = Term::free("s", sa.clone());
    let x = Term::free("x", alpha.clone());
    let no_x = hol::hol_not(mem(&alpha, &x, &s));
    let all_x = hol::hol_forall("x", alpha.clone(), no_x);
    hol::pub_abs("s", sa, all_x)
}

poly_let_term! {
    /// `set.isEmpty : set 'a → bool` ≡ `λs. ∀x. ¬ mem x s`.
    set_is_empty_spec, set_is_empty(alpha), Canonical::SetIsEmpty, set_is_empty_body()
}

// ============================================================================
// Flatten / fold.
// ============================================================================

fn set_flatten_body() -> Term {
    let alpha = Type::tfree("a");
    let sa = set(alpha.clone());
    let ssa = set(sa.clone());
    let big = Term::free("S", ssa.clone());
    let s = Term::free("s", sa.clone());
    let x = Term::free("x", alpha.clone());
    // ∃s. mem[set α] s S ∧ mem[α] x s  — "x lies in some member set of S"
    let conj = hol::hol_and(mem(&sa, &s, &big), mem(&alpha, &x, &s));
    let exists_s = hol::hol_exists("s", sa.clone(), conj);
    let collected = mk(&alpha, "x", exists_s);
    hol::pub_abs("S", ssa, collected)
}

poly_let_term! {
    /// `set.flatten : set (set 'a) → set 'a` ≡
    /// `λS. mk (λx. ∃s. mem s S ∧ mem x s)` — union of a set of sets.
    set_flatten_spec, set_flatten(alpha), Canonical::SetFlatten, set_flatten_body()
}

fn set_all_body() -> Term {
    let b_ty = Type::bool();
    let sb = set(b_ty.clone());
    let big = Term::free("S", sb.clone());
    let b = Term::free("b", b_ty.clone());
    // ∀b. mem b S ⟹ b
    let imp = hol::hol_imp(mem(&b_ty, &b, &big), b.clone());
    let all_b = hol::hol_forall("b", b_ty, imp);
    hol::pub_abs("S", sb, all_b)
}

let_term! {
    /// `set.all : set bool → bool` ≡ `λS. ∀b. mem b S ⟹ b` — the big
    /// conjunction over a set of booleans (`T` iff no member is `F`).
    set_all_spec, set_all, Canonical::SetAll, set_all_body()
}

fn set_any_body() -> Term {
    let b_ty = Type::bool();
    let sb = set(b_ty.clone());
    let big = Term::free("S", sb.clone());
    let b = Term::free("b", b_ty.clone());
    // ∃b. mem b S ∧ b
    let conj = hol::hol_and(mem(&b_ty, &b, &big), b.clone());
    let ex_b = hol::hol_exists("b", b_ty, conj);
    hol::pub_abs("S", sb, ex_b)
}

let_term! {
    /// `set.any : set bool → bool` ≡ `λS. ∃b. mem b S ∧ b` — the big
    /// disjunction over a set of booleans (`T` iff some member is `T`).
    set_any_spec, set_any, Canonical::SetAny, set_any_body()
}

// ============================================================================
// Minimum of a `set nat`.
//
// By well-ordering, every non-empty set of naturals has a least
// element. We fix the convention `min ∅ = 0` so the operator is total.
// (`0` also being the least of any set that contains it is harmless:
// callers distinguish the empty case with `set.isEmpty`.)
// ============================================================================

fn set_min_body() -> Term {
    // λs:set nat. cond (isEmpty s) 0 (ε n. mem n s ∧ ∀m. mem m s ⟹ n ≤ m)
    let nat = Type::nat();
    let sn = set(nat.clone());
    let s = Term::free("s", sn.clone());
    let n = Term::free("n", nat.clone());
    let m = Term::free("m", nat.clone());
    let le = Term::app(Term::app(nat_le(), n.clone()), m.clone());
    let minimal = hol::hol_forall("m", nat.clone(), hol::hol_imp(mem(&nat, &m, &s), le));
    // ε n. mem n s ∧ (∀m. mem m s ⟹ n ≤ m)  — the least element
    let least = hol::hol_and(mem(&nat, &n, &s), minimal);
    let eps = Term::app(
        Term::select_op(nat.clone()),
        hol::pub_abs("n", nat.clone(), least),
    );
    let is_empty = Term::app(set_is_empty(nat), s.clone());
    let chosen = Term::cond(is_empty, hol::zero(), eps);
    hol::pub_abs("s", sn, chosen)
}

/// `set.min : set nat → nat` ≡
/// `λs. cond (isEmpty s) 0 (ε n. mem n s ∧ ∀m. mem m s ⟹ n ≤ m)` —
/// the least element of a set of naturals (`0` for the empty set, by
/// convention).
pub fn set_min_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let body = set_min_body();
        let ty = Type::fun(set(Type::nat()), Type::nat());
        TermSpec::new(Canonical::SetMin, Some(ty), Some(body))
    });
    LAZY.clone()
}
pub fn set_min() -> Term {
    Term::term_spec(set_min_spec(), vec![])
}

// ============================================================================
// Finiteness and cardinality (via the `list` bridge `list.elems`).
//
// A set is *finite* exactly when it is the element-set of some list.
// Its *cardinality* is then the minimal length of such a covering list:
// a minimal cover has no duplicates, so its length is the count of
// distinct elements — i.e. `min` of the set of covering lengths.
// `card` is total (`0` on infinite sets, where no list covers);
// `card?` guards with `finite` and returns `none` past the finite case.
// ============================================================================

/// `∃l:list α. list.elems l = s ∧ list.length l = n` — "some list of
/// length `n` has exactly the elements of `s`" (open in `s`, `n`).
fn covers(alpha: &Type, s: &Term, n: &Term) -> Term {
    let la = list(alpha.clone());
    let l = Term::free("l", la.clone());
    let elems_l = Term::app(list_elems(alpha.clone()), l.clone());
    let len_l = Term::app(list_length(alpha.clone()), l.clone());
    let conj = hol::hol_and(hol::hol_eq(elems_l, s.clone()), hol::hol_eq(len_l, n.clone()));
    hol::hol_exists("l", la, conj)
}

fn set_finite_body() -> Term {
    let alpha = Type::tfree("a");
    let sa = set(alpha.clone());
    let s = Term::free("s", sa.clone());
    let la = list(alpha.clone());
    let l = Term::free("l", la.clone());
    let elems_l = Term::app(list_elems(alpha.clone()), l.clone());
    // ∃l. list.elems l = s
    let exists_l = hol::hol_exists("l", la, hol::hol_eq(elems_l, s.clone()));
    hol::pub_abs("s", sa, exists_l)
}

poly_let_term! {
    /// `set.finite : set 'a → bool` ≡ `λs. ∃l. list.elems l = s` —
    /// the set is the element-set of some (finite) list.
    set_finite_spec, set_finite(alpha), Canonical::SetFinite, set_finite_body()
}

fn set_card_body() -> Term {
    // λs. set.min { n : nat | ∃l. elems l = s ∧ length l = n }
    let alpha = Type::tfree("a");
    let sa = set(alpha.clone());
    let s = Term::free("s", sa.clone());
    let n = Term::free("n", Type::nat());
    // the set of lengths of lists that cover `s`
    let lengths = mk(&Type::nat(), "n", covers(&alpha, &s, &n));
    let card = Term::app(set_min(), lengths);
    hol::pub_abs("s", sa, card)
}

poly_let_term! {
    /// `set.card : set 'a → nat` ≡
    /// `λs. set.min { n | ∃l. elems l = s ∧ length l = n }` — the
    /// minimal length of a list covering `s` (= the number of distinct
    /// elements). `0` on infinite sets (no list covers, so the length
    /// set is empty); use [`set_card_opt`] for the option-returning
    /// form that distinguishes them.
    set_card_spec, set_card(alpha), Canonical::SetCard, set_card_body()
}

fn set_card_opt_body() -> Term {
    let alpha = Type::tfree("a");
    let sa = set(alpha.clone());
    let s = Term::free("s", sa.clone());
    let fin = Term::app(set_finite(alpha.clone()), s.clone());
    let card_s = Term::app(set_card(alpha.clone()), s.clone());
    let some_card = Term::app(some(Type::nat()), card_s);
    let chosen = Term::cond(fin, some_card, none(Type::nat()));
    hol::pub_abs("s", sa, chosen)
}

poly_let_term! {
    /// `set.card? : set 'a → option nat` ≡
    /// `λs. cond (set.finite s) (some (set.card s)) none` — cardinality
    /// as an option, `none` exactly for infinite sets.
    set_card_opt_spec, set_card_opt(alpha), Canonical::SetCardOpt, set_card_opt_body()
}

fn list_elems_body() -> Term {
    let alpha = Type::tfree("a");
    let la = list(alpha.clone());
    let l = Term::free("l", la.clone());
    let x = Term::free("x", alpha.clone());
    let n = Term::free("n", Type::nat());
    // listIndex[α] n l : option α
    let idx = Term::app(Term::app(list_index(alpha.clone()), n.clone()), l.clone());
    let some_x = Term::app(some(alpha.clone()), x.clone());
    // ∃n. listIndex n l = some x  — "x appears in l at some index"
    let appears = hol::hol_eq(idx, some_x);
    let exists_n = hol::hol_exists("n", Type::nat(), appears);
    let collected = mk(&alpha, "x", exists_n);
    hol::pub_abs("l", la, collected)
}

poly_let_term! {
    /// `list.elems : list 'a → set 'a` ≡
    /// `λl. mk (λx. ∃n. listIndex n l = some x)` — the set of elements
    /// appearing at some index of the list.
    list_elems_spec, list_elems(alpha), Canonical::ListElems, list_elems_body()
}

// ============================================================================
// Image / preimage under a function (two type parameters).
// ============================================================================

fn set_image_body() -> Term {
    // λf s. mk (λy. ∃x. mem x s ∧ f x = y)
    let alpha = Type::tfree("a");
    let beta = Type::tfree("b");
    let sa = set(alpha.clone());
    let f_ty = Type::fun(alpha.clone(), beta.clone());
    let f = Term::free("f", f_ty.clone());
    let s = Term::free("s", sa.clone());
    let x = Term::free("x", alpha.clone());
    let y = Term::free("y", beta.clone());
    let fx_eq_y = hol::hol_eq(Term::app(f.clone(), x.clone()), y.clone());
    let conj = hol::hol_and(mem(&alpha, &x, &s), fx_eq_y);
    let exists_x = hol::hol_exists("x", alpha, conj);
    let collected = mk(&beta, "y", exists_x);
    let lam_s = hol::pub_abs("s", sa, collected);
    hol::pub_abs("f", f_ty, lam_s)
}

poly_let_term! {
    /// `set.image : ('a → 'b) → set 'a → set 'b` ≡
    /// `λf s. mk (λy. ∃x. mem x s ∧ f x = y)` — the direct image of `s`
    /// under `f`.
    set_image_spec, set_image(alpha, beta), Canonical::SetImage, set_image_body()
}

fn set_preimage_body() -> Term {
    // λf t. mk (λx. mem (f x) t)
    let alpha = Type::tfree("a");
    let beta = Type::tfree("b");
    let sb = set(beta.clone());
    let f_ty = Type::fun(alpha.clone(), beta.clone());
    let f = Term::free("f", f_ty.clone());
    let t = Term::free("t", sb.clone());
    let x = Term::free("x", alpha.clone());
    let fx = Term::app(f.clone(), x.clone());
    let collected = mk(&alpha, "x", mem(&beta, &fx, &t));
    let lam_t = hol::pub_abs("t", sb, collected);
    hol::pub_abs("f", f_ty, lam_t)
}

poly_let_term! {
    /// `set.preimage : ('a → 'b) → set 'b → set 'a` ≡
    /// `λf t. mk (λx. mem (f x) t)` — the preimage of `t` under `f`.
    set_preimage_spec, set_preimage(alpha, beta), Canonical::SetPreimage, set_preimage_body()
}
