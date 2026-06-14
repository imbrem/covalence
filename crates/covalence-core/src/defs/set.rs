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
//! `set.union`/`set.intersect`/`set.diff`/`set.subset` are defined
//! pointwise on membership; `set.flatten` is the union of a set of
//! sets; `set.all`/`set.any` are the big conjunction/disjunction over
//! a `set bool`; `list.elems` is "appears at some index". `set.card`
//! stays **declaration-only**: a structural cardinality needs a fold
//! over a finiteness witness the kernel does not yet expose (cf. the
//! declaration-only list folds in [`crate::defs::list`]); its type
//! signature is committed and the body is tracked in
//! `docs/roadmap.md`.

use std::sync::LazyLock;

use crate::hol;
use crate::term::{Term, Type};

use super::canonical::Canonical;
use super::list::{list, list_index};
use super::option::some;
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

/// `set.mk[α] (λx:α. body)` — wrap a `bool`-body (open in the free
/// var `x : α`) into a `set α` (builder over the [`set_mk`] constant).
fn mk(alpha: &Type, body: Term) -> Term {
    let pred = hol::pub_abs("x", alpha.clone(), body);
    Term::app(set_mk(alpha.clone()), pred)
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
        mk(&alpha, elem)
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
    let collected = mk(&alpha, exists_s);
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

/// `set.card : set 'a → nat`. **Declaration-only**: see the module
/// docs — a structural cardinality needs a fold over a finiteness
/// witness the kernel does not yet expose.
pub fn set_card_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        let sa = set(alpha);
        TermSpec::new(Canonical::SetCard, Some(Type::fun(sa, Type::nat())), None)
    });
    LAZY.clone()
}
pub fn set_card(alpha: Type) -> Term {
    Term::term_spec(set_card_spec(), vec![alpha])
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
    let collected = mk(&alpha, exists_n);
    hol::pub_abs("l", la, collected)
}

poly_let_term! {
    /// `list.elems : list 'a → set 'a` ≡
    /// `λl. mk (λx. ∃n. listIndex n l = some x)` — the set of elements
    /// appearing at some index of the list.
    list_elems_spec, list_elems(alpha), Canonical::ListElems, list_elems_body()
}
