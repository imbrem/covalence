//! Capture-avoiding substitution and de Bruijn shifting.
//!
//! Locally-nameless convention: `Bound(i)` refers to the i-th enclosing
//! binder (innermost first). `Free` and `Const` carry their type and
//! are unaffected by de Bruijn shifts. `FreshConst` is opaque to
//! substitution over term structure, but its `ty` field participates
//! in type-variable substitution. The operations here are pure syntactic and
//! used by the inference rules in `crate::thm`.

use std::cmp::Ordering;

use std::collections::BTreeMap;

use smol_str::SmolStr;

use crate::term::{FreshLeaf, Term, TermKind, TrustedCons, Type, TypeKind, Var};
use crate::term::{TypeEnv, type_of_in};

// ============================================================================
// Substitution
// ============================================================================
//
// The term-rebuilding operations come in `_with` / plain pairs (see
// `crate::term::cons`): `foo_with(…, cons)` routes every constructed node
// through a caller-supplied `TrustedCons`, and `foo(…)` delegates to
// `foo_with(…, &mut ())` (allocate fresh, no interning). Pass a
// `HashCons` to `_with` to intern the rebuilt structure. Subterms that
// are reused unchanged are shared by `clone`, independent of `cons`.

/// Abstract `Free(name, _)` into `Bound(0)`. Recurses into binders,
/// incrementing the target depth on the way in. Used to build the body
/// of an `Abs`/`All` from a term that mentions a fresh free variable.
pub fn close(t: &Term, name: &str) -> Term {
    close_with(t, name, &mut ())
}

/// [`close`] routing constructed nodes through `cons`.
pub fn close_with<C: TrustedCons + ?Sized>(t: &Term, name: &str, cons: &mut C) -> Term {
    close_at(t, name, 0, cons)
}

fn close_at<C: TrustedCons + ?Sized>(t: &Term, name: &str, depth: u32, cons: &mut C) -> Term {
    // Bloom skip: if `name` provably doesn't occur free here, this subtree
    // is unchanged — reuse it without recursing.
    if !t.free_bloom().contains(name) {
        return t.clone();
    }
    match t.kind() {
        TermKind::Free(v) if v.name() == name => cons.make(TermKind::Bound(depth)),
        TermKind::Bound(_)
        | TermKind::Free(..)
        | TermKind::Const(..)
        | TermKind::Blob(_)
        | TermKind::Nat(_)
        | TermKind::Int(_)
        | TermKind::SmallInt(_)
        | TermKind::Bool(_)
        | TermKind::Eq(_)
        | TermKind::Select(_)
        | TermKind::Spec(_, _)
        | TermKind::SpecAbs(..)
        | TermKind::SpecRep(..)
        | TermKind::FreshConst(..)
        | TermKind::Succ
        | TermKind::Def(_) => t.clone(),
        TermKind::App(f, x) => {
            let f = close_at(f, name, depth, cons);
            let x = close_at(x, name, depth, cons);
            cons.make(TermKind::App(f, x))
        }
        TermKind::Abs(ty, body) => {
            let body = close_at(body, name, depth + 1, cons);
            cons.make(TermKind::Abs(ty.clone(), body))
        }
    }
}

/// Abstract the free variable `var` (identified by name **and** type) into
/// `Bound(0)` — the type-aware [`close`]. A same-named variable at a
/// different type is left alone. Used by the kernel `abs`/`∀`-introduction
/// paths, which receive arbitrary theorem terms that may legitimately
/// carry distinct same-named variables at different types. (The plain
/// name-only [`close`] is kept for construction sites where the name has a
/// single known type.)
pub fn close_var(t: &Term, var: &Var) -> Term {
    close_var_at(t, var, 0)
}

fn close_var_at(t: &Term, var: &Var, depth: u32) -> Term {
    close_var_opt(t, var, depth).unwrap_or_else(|| t.clone())
}

/// Sharing-preserving core of [`close_var_at`] (mirrors [`subst_free_opt`]):
/// `Some(t')` when binding `var` at `depth` *changes* `t`, `None` when it leaves
/// `t` untouched — so the caller reuses the original `Arc` with **no
/// allocation**. The bloom is coarse, so an unchanged subtree can still recurse
/// on a false positive; without this `None` short-circuit every such `App`/`Abs`
/// was needlessly re-allocated. `all_intro` runs `close` over the whole
/// `Closed_L ⟹ d ⌜S⌝` (large `Closed_L`, with `d` only inside its applications)
/// on **every `|-` proof step**, so reusing the unchanged conjuncts instead of
/// rebuilding them is a big win on the lemma-heavy theorems.
fn close_var_opt(t: &Term, var: &Var, depth: u32) -> Option<Term> {
    // Bloom skip: no free var named `var.name()` here ⇒ subtree unchanged.
    if !t.free_bloom().contains(var.name()) {
        return None;
    }
    match t.kind() {
        TermKind::Free(v) if v == var => Some(Term::bound(depth)),
        TermKind::Bound(_)
        | TermKind::Free(..)
        | TermKind::Const(..)
        | TermKind::Blob(_)
        | TermKind::Nat(_)
        | TermKind::Int(_)
        | TermKind::SmallInt(_)
        | TermKind::Bool(_)
        | TermKind::Eq(_)
        | TermKind::Select(_)
        | TermKind::Spec(_, _)
        | TermKind::SpecAbs(..)
        | TermKind::SpecRep(..)
        | TermKind::FreshConst(..)
        | TermKind::Succ
        | TermKind::Def(_) => None,
        TermKind::App(f, x) => {
            let f2 = close_var_opt(f, var, depth);
            let x2 = close_var_opt(x, var, depth);
            if f2.is_none() && x2.is_none() {
                None
            } else {
                Some(Term::app(
                    f2.unwrap_or_else(|| f.clone()),
                    x2.unwrap_or_else(|| x.clone()),
                ))
            }
        }
        TermKind::Abs(bty, body) => {
            close_var_opt(body, var, depth + 1).map(|body| Term::abs(bty.clone(), body))
        }
    }
}

/// Instantiate `Bound(0)` with `u` inside `body` (which is the body of
/// an `Abs`/`All`). The outer binder is consumed: `Bound(i)` for `i ≥ 1`
/// shift down by 1; the replacement `u` shifts up by the binder depth
/// at which the substitution happens. Used in β-reduction and
/// ⋀-elimination.
pub fn open(body: &Term, u: &Term) -> Term {
    open_with(body, u, &mut ())
}

/// [`open`] routing constructed nodes through `cons`.
pub fn open_with<C: TrustedCons + ?Sized>(body: &Term, u: &Term, cons: &mut C) -> Term {
    // Fast path: when `u` is closed and well-typed and we are not interning,
    // substitute *and* compute types in one pass ([`inst_typed`]), stamping
    // each closing `Abs` with its (type-preserving) result type instead of
    // letting `term_info` re-derive it with a separate `type_of_in` walk. The
    // guard `body.bvi() <= 0` means `λ. body` is closed (the only free de
    // Bruijn index is the one being substituted), so no `Bound(i)` ever refers
    // *above* the substituted binder — keeping the binder context exact.
    //
    // `inst_typed` returns `None` when `body` turns out to be ill-typed under
    // the binder — then we fall through to the type-agnostic general path
    // below, exactly as if the guard had failed. (`open` is a `pub` utility,
    // so an ill-typed `body` is reachable from outside the kernel rules; the
    // fast path must never stamp a type derived from an ill-typed tree.)
    if cons.allow_clone()
        && body.bvi() <= 0
        && let Ok(u_ty) = u.ty()
    {
        let u_ty = u_ty.clone();
        let mut env = TypeEnv::new(vec![u_ty.clone()]);
        if let Some((changed, _ty)) = inst_typed(body, u, &u_ty, &mut env, cons) {
            return changed.unwrap_or_else(|| body.clone());
        }
    }
    inst_opt(body, u, 0, cons).unwrap_or_else(|| body.clone())
}

/// Type the *unchanged* subterm `t` in binder context `env`: O(1) from its
/// cached type when closed, else a `type_of_in` walk under `env` (reached only
/// for subterms that are open but free of the substituted index — i.e. they
/// mention an inner binder only). Returns `None` when `t` does not type-check
/// in `env` — the [`inst_typed`] caller then abandons the fast path. Used by
/// [`inst_typed`].
fn type_in_ctx(t: &Term, env: &mut TypeEnv) -> Option<Type> {
    if let Ok(ty) = t.ty() {
        return Some(ty.clone());
    }
    type_of_in(t, env).ok()
}

/// Type-preserving [`inst_opt`] used by the [`open_with`] fast path: substitutes
/// `Bound(env.len()-1) := u` (with `u : u_ty`) **and** returns the type of the
/// result in binder context `env` (`env.bound_ty(i)` is the type of `Bound(i)`,
/// innermost last). Returns `Some((None, ty))` when the subterm is unchanged
/// (caller reuses the `Arc`), `Some((Some(new), ty))` otherwise; `ty` is the
/// result's type. Returns `None` when the subterm does **not** type-check in
/// `env` — the caller must abandon the fast path (fall back to [`inst_opt`])
/// rather than build anything from a type computed off an ill-typed tree.
///
/// `Soundness:` substitution is type-preserving — `u : u_ty` is the type of the
/// binder it replaces — so each rebuilt node has the same type as the original.
/// This computes that type inline, **verifying** (not trusting) well-typedness
/// as it goes: an `App`'s type is its function side's codomain only after
/// checking the function side is an arrow whose domain equals the argument's
/// type (the same check as [`type_of_in`]); unchanged subtrees are typed by
/// [`type_in_ctx`]. Any failure aborts the whole fast path via `None`. On
/// success it stamps closing abstractions via [`Term::abs_with_ty`], doing the
/// work [`type_of_in`] would but fused into the single substitution traversal
/// instead of a second walk per closing `Abs`. (An earlier version *trusted*
/// the input's well-typedness here; a `pub`-reachable ill-typed `body` then
/// stamped a false cached type — a broken `TermInfo::Wf` invariant — or
/// panicked. Verified inline typing restores the invariant on every path.)
fn inst_typed<C: TrustedCons + ?Sized>(
    t: &Term,
    u: &Term,
    u_ty: &Type,
    env: &mut TypeEnv,
    cons: &mut C,
) -> Option<(Option<Term>, Type)> {
    let depth = (env.len() - 1) as u32;
    // Unchanged subtree (no `Bound(i ≥ depth)`): reuse it; its type is cached
    // when closed, else computed under `env`.
    if t.bvi() < depth as i64 {
        return Some((None, type_in_ctx(t, env)?));
    }
    match t.kind() {
        TermKind::Bound(i) => {
            let i = *i;
            match i.cmp(&depth) {
                // `i < depth` was handled by the skip above.
                Ordering::Less => Some((None, env.bound_ty(i as usize))),
                Ordering::Equal => Some((Some(shift_with(u, depth as i64, 0, cons)), u_ty.clone())),
                // `i > depth` cannot occur under the `body.bvi() <= 0` guard.
                Ordering::Greater => Some((
                    Some(cons.make(TermKind::Bound(i - 1))),
                    env.bound_ty((i - 1) as usize),
                )),
            }
        }
        TermKind::App(f, x) => {
            let (f2, f_ty) = inst_typed(f, u, u_ty, env, cons)?;
            let (x2, x_ty) = inst_typed(x, u, u_ty, env, cons)?;
            // Result type = codomain of the function side, *checked* the same
            // way `type_of_in` checks an `App`: the function side must be an
            // arrow and its domain must equal the argument's type. An
            // ill-typed application aborts the fast path.
            let cod = match f_ty.kind() {
                TypeKind::Fun(dom, cod) if *dom == x_ty => cod.clone(),
                _ => return None,
            };
            if f2.is_none() && x2.is_none() {
                Some((None, cod))
            } else {
                let f = f2.unwrap_or_else(|| f.clone());
                let x = x2.unwrap_or_else(|| x.clone());
                Some((Some(cons.make(TermKind::App(f, x))), cod))
            }
        }
        TermKind::Abs(ty, body) => {
            env.push(ty.clone());
            let r = inst_typed(body, u, u_ty, env, cons);
            env.pop();
            let (body2, body_ty) = r?;
            let abs_ty = Type::fun(ty.clone(), body_ty.clone());
            match body2 {
                None => Some((None, abs_ty)),
                Some(body) => Some((Some(Term::abs_with_ty(ty.clone(), body, body_ty)), abs_ty)),
            }
        }
        // Other leaves are closed (`bvi == -1 < depth`) — handled by the skip.
        _ => Some((None, type_in_ctx(t, env)?)),
    }
}

/// The sharing-preserving core of [`open`] / instantiation: returns
/// `Some(t')` when substituting `Bound(depth) := u` (and shifting deeper
/// indices) *changes* `t`, and `None` when it leaves `t` untouched (the
/// caller reuses the original `Arc`).
///
/// **`bvi`-skip:** a subterm whose maximum free de Bruijn index is `<
/// depth` contains no `Bound(i ≥ depth)` — so instantiation is a no-op on
/// it and we return `None` immediately, without recursing. This is the
/// bound-variable twin of the free-variable Bloom skip in
/// [`subst_free_opt`]; both use a summary cached on [`crate::Term`]
/// ([`Term::bvi`] here) to prune whole subtrees.
fn inst_opt<C: TrustedCons + ?Sized>(t: &Term, u: &Term, depth: u32, cons: &mut C) -> Option<Term> {
    // No `Bound(i ≥ depth)` below ⇒ unchanged. (Closed subterms — `bvi ==
    // -1` — are always skipped; so are leaves, including bare `Bound(i)`
    // with `i < depth`.)
    if t.bvi() < depth as i64 {
        return None;
    }
    match t.kind() {
        TermKind::Bound(i) => {
            let i = *i;
            // `i < depth` was handled by the skip above (its `bvi` is `i`).
            match i.cmp(&depth) {
                Ordering::Less => None,
                Ordering::Equal => Some(shift_with(u, depth as i64, 0, cons)),
                Ordering::Greater => Some(cons.make(TermKind::Bound(i - 1))),
            }
        }
        TermKind::App(f, x) => {
            let f2 = inst_opt(f, u, depth, cons);
            let x2 = inst_opt(x, u, depth, cons);
            if f2.is_none() && x2.is_none() {
                None
            } else {
                let f = f2.unwrap_or_else(|| f.clone());
                let x = x2.unwrap_or_else(|| x.clone());
                Some(cons.make(TermKind::App(f, x)))
            }
        }
        TermKind::Abs(ty, body) => inst_opt(body, u, depth + 1, cons)
            .map(|body| cons.make(TermKind::Abs(ty.clone(), body))),
        // Other leaves are closed (`bvi == -1`) and were skipped above.
        _ => None,
    }
}

/// Shift every `Bound(i)` with `i ≥ cutoff` by `delta`.
///
/// Negative `delta` is permitted but only if the caller has
/// established (typically via [`uses_bound_outer`]) that no `Bound(i)`
/// with `i ≥ cutoff` ever needs to drop below zero. The only TCB
/// caller that uses negative `delta` is `Thm::eta_conv`, which checks
/// exactly that precondition before calling.
///
/// On underflow this function **panics** rather than wrapping —
/// soundness depends on the caller's check, and silently producing a
/// `Bound(u32::MAX)` would let the bug propagate.
pub fn shift_by(t: &Term, delta: i64, cutoff: u32) -> Term {
    shift_with(t, delta, cutoff, &mut ())
}

/// [`shift_by`] routing constructed nodes through `cons`.
pub fn shift_with<C: TrustedCons + ?Sized>(
    t: &Term,
    delta: i64,
    cutoff: u32,
    cons: &mut C,
) -> Term {
    if delta == 0 {
        return t.clone();
    }
    shift_inner(t, delta, cutoff, cons)
}

fn shift_inner<C: TrustedCons + ?Sized>(t: &Term, delta: i64, cutoff: u32, cons: &mut C) -> Term {
    // `bvi`-skip: a subterm whose maximum free de Bruijn index is `< cutoff`
    // has no `Bound(i ≥ cutoff)` to shift, so shifting is the identity — reuse
    // it without walking. Crucially this makes shifting a *closed* term (`bvi
    // == -1`, e.g. the closed argument substituted by `open`/`all_elim` at
    // depth > 0) O(1) instead of an O(size) rebuild of an identical tree — the
    // bound-variable twin of the same skip in [`inst_opt`].
    if t.bvi() < cutoff as i64 {
        return t.clone();
    }
    match t.kind() {
        TermKind::Bound(i) => {
            let i = *i;
            if i < cutoff {
                return cons.make(TermKind::Bound(i));
            }
            let new = (i as i64)
                .checked_add(delta)
                .expect("shift_by: i64 overflow in Bound index");
            if new < 0 {
                panic!("shift_by: Bound underflow (i={i}, delta={delta}, cutoff={cutoff})");
            }
            if new > u32::MAX as i64 {
                panic!("shift_by: Bound index exceeds u32::MAX (i={i}, delta={delta})");
            }
            cons.make(TermKind::Bound(new as u32))
        }
        TermKind::Free(..)
        | TermKind::Const(..)
        | TermKind::Blob(_)
        | TermKind::Nat(_)
        | TermKind::Int(_)
        | TermKind::SmallInt(_)
        | TermKind::Bool(_)
        | TermKind::Eq(_)
        | TermKind::Select(_)
        | TermKind::Spec(_, _)
        | TermKind::SpecAbs(..)
        | TermKind::SpecRep(..)
        | TermKind::FreshConst(..)
        | TermKind::Succ
        | TermKind::Def(_) => t.clone(),
        TermKind::App(f, x) => {
            let f = shift_inner(f, delta, cutoff, cons);
            let x = shift_inner(x, delta, cutoff, cons);
            cons.make(TermKind::App(f, x))
        }
        TermKind::Abs(ty, body) => {
            let body = shift_inner(body, delta, cutoff + 1, cons);
            cons.make(TermKind::Abs(ty.clone(), body))
        }
    }
}

/// Substitute the free variable `var` with `r` in `t` — HOL Light
/// `vsubst` for a single variable. A free variable is identified by **both
/// its name and its type** ([`Var`]), so a same-named variable at a
/// different type is distinct and left untouched. `var.ty()` must be `r`'s
/// type. The replacement is shifted up by the current binder depth when
/// crossing binders so any `Bound` references inside `r` continue to refer
/// to the outer environment.
pub fn subst_free(t: &Term, var: &Var, r: &Term) -> Term {
    subst_free_with(t, var, r, &mut ())
}

/// [`subst_free`] routing constructed nodes through `cons`.
pub fn subst_free_with<C: TrustedCons + ?Sized>(
    t: &Term,
    var: &Var,
    r: &Term,
    cons: &mut C,
) -> Term {
    subst_free_at(t, var, r, 0, cons)
}

fn subst_free_at<C: TrustedCons + ?Sized>(
    t: &Term,
    var: &Var,
    r: &Term,
    depth: u32,
    cons: &mut C,
) -> Term {
    subst_free_opt(t, var, r, depth, cons).unwrap_or_else(|| t.clone())
}

/// The sharing-preserving core of [`subst_free_at`]: returns `Some(t')` when
/// substituting `var := r` *changes* `t`, and `None` when it leaves `t`
/// untouched (so the caller reuses the original `Arc` — no allocation). A
/// no-op substitution allocates nothing; a real one rebuilds only the spine
/// from the root down to the substituted leaves.
///
/// The `None` short-circuit is also the hook for a future fast skip: a
/// free-variable summary on `TermInfo` (e.g. a Bloom filter over variable
/// names) could let a subtree that provably lacks `var` return `None`
/// immediately, without recursing.
fn subst_free_opt<C: TrustedCons + ?Sized>(
    t: &Term,
    var: &Var,
    r: &Term,
    depth: u32,
    cons: &mut C,
) -> Option<Term> {
    // Bloom skip: if `var.name()` provably doesn't occur free here, the
    // substitution is a no-op on this subtree — return `None` (the caller
    // reuses the original `Arc`) without recursing.
    if !t.free_bloom().contains(var.name()) {
        return None;
    }
    match t.kind() {
        TermKind::Free(v) if v == var => Some(shift_with(r, depth as i64, 0, cons)),
        TermKind::Bound(_)
        | TermKind::Free(..)
        | TermKind::Const(..)
        | TermKind::Blob(_)
        | TermKind::Nat(_)
        | TermKind::Int(_)
        | TermKind::SmallInt(_)
        | TermKind::Bool(_)
        | TermKind::Eq(_)
        | TermKind::Select(_)
        | TermKind::Spec(_, _)
        | TermKind::SpecAbs(..)
        | TermKind::SpecRep(..)
        | TermKind::FreshConst(..)
        | TermKind::Succ
        | TermKind::Def(_) => None,
        TermKind::App(f, x) => {
            let f2 = subst_free_opt(f, var, r, depth, cons);
            let x2 = subst_free_opt(x, var, r, depth, cons);
            if f2.is_none() && x2.is_none() {
                None
            } else {
                let f = f2.unwrap_or_else(|| f.clone());
                let x = x2.unwrap_or_else(|| x.clone());
                Some(cons.make(TermKind::App(f, x)))
            }
        }
        TermKind::Abs(bty, body) => subst_free_opt(body, var, r, depth + 1, cons)
            .map(|body| cons.make(TermKind::Abs(bty.clone(), body))),
    }
}

// ============================================================================
// Type-variable substitution
// ============================================================================

/// Replace every `TFree(name)` in `ty` with `r`.
pub fn subst_tfree_in_type(ty: &Type, name: &str, r: &Type) -> Type {
    match ty.kind() {
        TypeKind::TFree(n) if n == name => r.clone(),
        TypeKind::TFree(_) | TypeKind::Nat | TypeKind::Bool => ty.clone(),
        TypeKind::Fun(a, b) => Type::fun(
            subst_tfree_in_type(a, name, r),
            subst_tfree_in_type(b, name, r),
        ),
        TypeKind::Tycon(n, args) => Type::tycon(
            n.clone(),
            args.iter()
                .map(|a| subst_tfree_in_type(a, name, r))
                .collect::<Vec<_>>(),
        ),
        // For a `Spec` leaf the args participate in type-var
        // substitution; the spec itself (`Arc`-shared) is untouched.
        // The spec's internal `ty`/`tm` continue to refer to the
        // *spec's* free tvars (in canonical alphabetical order);
        // substituting at this site replaces the args, not the
        // spec's binders.
        TypeKind::Spec(spec, args) => Type::spec(
            spec.clone(),
            args.iter()
                .map(|a| subst_tfree_in_type(a, name, r))
                .collect::<Vec<_>>(),
        ),
        // The `FreshId` identity is preserved; only the type-arg
        // substitution propagates. `τ 'a` after 'a := bytes becomes
        // `τ bytes` with the same constructor identity — exactly
        // what we want for polymorphic typedefs.
        TypeKind::FreshTyCon(leaf) => Type::fresh_tycon(
            leaf.id().clone(),
            leaf.args()
                .iter()
                .map(|a| subst_tfree_in_type(a, name, r))
                .collect::<Vec<_>>(),
        ),
    }
}

/// Simultaneous version of [`subst_tfree_in_type`]: replace each
/// `TFree(n)` by `sub[n]` in a *single* pass. Unlike folding
/// [`subst_tfree_in_type`] over the map's entries, a replacement that
/// itself mentions another substituted name is **not** re-substituted —
/// so `{a:=b, b:=c}` maps `a → b` and `b → c` (a fold would cascade
/// `a → b → c`). This is the correct semantics for instantiating a
/// spec's type variables positionally.
pub fn subst_tfrees_in_type(ty: &Type, sub: &BTreeMap<SmolStr, Type>) -> Type {
    if sub.is_empty() {
        return ty.clone();
    }
    let go = |a: &Type| subst_tfrees_in_type(a, sub);
    match ty.kind() {
        TypeKind::TFree(n) => sub.get(n).cloned().unwrap_or_else(|| ty.clone()),
        TypeKind::Nat | TypeKind::Bool => ty.clone(),
        TypeKind::Fun(a, b) => Type::fun(go(a), go(b)),
        TypeKind::Tycon(n, args) => Type::tycon(n.clone(), args.iter().map(go).collect::<Vec<_>>()),
        TypeKind::Spec(spec, args) => {
            Type::spec(spec.clone(), args.iter().map(go).collect::<Vec<_>>())
        }
        TypeKind::FreshTyCon(leaf) => Type::fresh_tycon(
            leaf.id().clone(),
            leaf.args().iter().map(go).collect::<Vec<_>>(),
        ),
    }
}

/// Simultaneous version of [`subst_tfree_in_term`] over every type
/// annotation in `t` (see [`subst_tfrees_in_type`] for why a single
/// pass matters — it avoids cascading `{a:=b, b:=c}` into `a → c`).
pub fn subst_tfrees_in_term(t: &Term, sub: &BTreeMap<SmolStr, Type>) -> Term {
    subst_tfrees_in_term_with(t, sub, &mut ())
}

/// [`subst_tfrees_in_term`] routing constructed nodes through `cons`.
pub fn subst_tfrees_in_term_with<C: TrustedCons + ?Sized>(
    t: &Term,
    sub: &BTreeMap<SmolStr, Type>,
    cons: &mut C,
) -> Term {
    if sub.is_empty() {
        return t.clone();
    }
    let st = |ty: &Type| subst_tfrees_in_type(ty, sub);
    let kind = match t.kind() {
        TermKind::Bound(i) => TermKind::Bound(*i),
        TermKind::Free(v) => TermKind::Free(Var::new(v.name(), st(v.ty()))),
        TermKind::Const(n, ty) => TermKind::Const(n.clone(), st(ty)),
        TermKind::App(f, x) => {
            let f = subst_tfrees_in_term_with(f, sub, cons);
            let x = subst_tfrees_in_term_with(x, sub, cons);
            TermKind::App(f, x)
        }
        TermKind::Abs(ty, body) => {
            let ty = st(ty);
            let body = subst_tfrees_in_term_with(body, sub, cons);
            TermKind::Abs(ty, body)
        }
        TermKind::Blob(b) => TermKind::Blob(b.clone()),
        TermKind::Nat(n) => TermKind::Nat(n.clone()),
        TermKind::Int(n) => TermKind::Int(n.clone()),
        TermKind::SmallInt(lit) => TermKind::SmallInt(*lit),
        TermKind::Bool(b) => TermKind::Bool(*b),
        TermKind::Eq(alpha) => TermKind::Eq(st(alpha)),
        TermKind::Select(alpha) => TermKind::Select(st(alpha)),
        TermKind::Succ => TermKind::Succ,
        TermKind::Spec(spec, args) => TermKind::Spec(
            spec.clone(),
            args.iter().map(&st).collect::<Vec<_>>().into(),
        ),
        TermKind::SpecAbs(spec, args) => TermKind::SpecAbs(
            spec.clone(),
            args.iter().map(&st).collect::<Vec<_>>().into(),
        ),
        TermKind::SpecRep(spec, args) => TermKind::SpecRep(
            spec.clone(),
            args.iter().map(&st).collect::<Vec<_>>().into(),
        ),
        TermKind::FreshConst(leaf) => {
            TermKind::FreshConst(FreshLeaf::new(leaf.id().clone(), st(leaf.ty())))
        }
        TermKind::Def(d) => {
            TermKind::Def(d.with_instance_type(subst_tfrees_in_type(d.instance_type(), sub)))
        }
    };
    cons.make(kind)
}

/// Replace every `TFree(name)` with `r` in every type annotation inside
/// `t`, including the `ty` field of any `FreshConst` leaf. The identity
/// token itself is opaque and untouched.
pub fn subst_tfree_in_term(t: &Term, name: &str, r: &Type) -> Term {
    subst_tfree_in_term_with(t, name, r, &mut ())
}

/// [`subst_tfree_in_term`] routing constructed nodes through `cons`.
pub fn subst_tfree_in_term_with<C: TrustedCons + ?Sized>(
    t: &Term,
    name: &str,
    r: &Type,
    cons: &mut C,
) -> Term {
    let st = |ty: &Type| subst_tfree_in_type(ty, name, r);
    let kind = match t.kind() {
        TermKind::Bound(i) => TermKind::Bound(*i),
        TermKind::Free(v) => TermKind::Free(Var::new(v.name(), st(v.ty()))),
        TermKind::Const(n, ty) => TermKind::Const(n.clone(), st(ty)),
        TermKind::App(f, x) => {
            let f = subst_tfree_in_term_with(f, name, r, cons);
            let x = subst_tfree_in_term_with(x, name, r, cons);
            TermKind::App(f, x)
        }
        TermKind::Abs(ty, body) => {
            let ty = st(ty);
            let body = subst_tfree_in_term_with(body, name, r, cons);
            TermKind::Abs(ty, body)
        }
        TermKind::Blob(b) => TermKind::Blob(b.clone()),
        TermKind::Nat(n) => TermKind::Nat(n.clone()),
        TermKind::Int(n) => TermKind::Int(n.clone()),
        TermKind::SmallInt(lit) => TermKind::SmallInt(*lit),
        TermKind::Bool(b) => TermKind::Bool(*b),
        TermKind::Eq(alpha) => TermKind::Eq(st(alpha)),
        TermKind::Select(alpha) => TermKind::Select(st(alpha)),
        TermKind::Succ => TermKind::Succ,
        // For a `Spec` leaf the type args participate in type-var
        // substitution; the spec handle (`Arc`-shared) is untouched.
        TermKind::Spec(spec, args) => TermKind::Spec(
            spec.clone(),
            args.iter().map(&st).collect::<Vec<_>>().into(),
        ),
        // `abs`/`rep` coercions carry type args that participate in
        // type-var substitution; the spec handle (`Arc`-shared) is
        // untouched, exactly like `TermKind::Spec`.
        TermKind::SpecAbs(spec, args) => TermKind::SpecAbs(
            spec.clone(),
            args.iter().map(&st).collect::<Vec<_>>().into(),
        ),
        TermKind::SpecRep(spec, args) => TermKind::SpecRep(
            spec.clone(),
            args.iter().map(&st).collect::<Vec<_>>().into(),
        ),
        TermKind::FreshConst(leaf) => {
            TermKind::FreshConst(FreshLeaf::new(leaf.id().clone(), st(leaf.ty())))
        }
        // `Def` carries an `original` Arc identity (the unique
        // `Thm::define` call) plus an `instance_type`. Substitution
        // updates `instance_type` without rebuilding `original`, so
        // the result compares equal to any other `Def` reaching this
        // same instance — the property HOL Light's `INST_TYPE` and
        // polymorphic-constant equality depend on.
        TermKind::Def(d) => {
            TermKind::Def(d.with_instance_type(subst_tfree_in_type(d.instance_type(), name, r)))
        }
    };
    cons.make(kind)
}

// ============================================================================
// Predicates
// ============================================================================

/// A term is closed if every `Bound(i)` is enclosed by at least `i+1`
/// binders. Every term that becomes part of a `Thm` is closed.
pub fn is_closed(t: &Term) -> bool {
    is_closed_at(t, 0)
}

fn is_closed_at(t: &Term, depth: u32) -> bool {
    match t.kind() {
        TermKind::Bound(i) => *i < depth,
        TermKind::Free(..)
        | TermKind::Const(..)
        | TermKind::Blob(_)
        | TermKind::Nat(_)
        | TermKind::Int(_)
        | TermKind::SmallInt(_)
        | TermKind::Bool(_)
        | TermKind::Eq(_)
        | TermKind::Select(_)
        | TermKind::Spec(_, _)
        | TermKind::SpecAbs(..)
        | TermKind::SpecRep(..)
        | TermKind::FreshConst(..)
        | TermKind::Succ
        | TermKind::Def(_) => true,
        TermKind::App(a, b) => is_closed_at(a, depth) && is_closed_at(b, depth),
        TermKind::Abs(_, body) => is_closed_at(body, depth + 1),
    }
}

/// True if `name` appears as a `Free` variable (at any type) anywhere in
/// `t`.
pub fn has_free_var(t: &Term, name: &str) -> bool {
    find_free_type(t, name).is_some()
}

/// True if the free variable `var` — identified by name **and** type —
/// appears anywhere in `t`. Used by the kernel `abs`/`∀`-intro rules to
/// check the variable being bound is not free in the hypotheses.
pub fn has_free_var_typed(t: &Term, var: &Var) -> bool {
    // Bloom skip: no free var named `var.name()` here ⇒ definitely absent.
    if !t.free_bloom().contains(var.name()) {
        return false;
    }
    match t.kind() {
        TermKind::Free(v) => v == var,
        TermKind::App(a, b) => has_free_var_typed(a, var) || has_free_var_typed(b, var),
        TermKind::Abs(_, body) => has_free_var_typed(body, var),
        _ => false,
    }
}

/// First-encountered declared type of a `Free` named `name` in `t`, or
/// `None` if none appears. With free variables identified by `(name,
/// type)`, a single name may in principle occur at several types; this
/// returns the first in traversal order (used only for display / best-
/// effort diagnostics, never for soundness decisions).
pub fn find_free_type(t: &Term, name: &str) -> Option<Type> {
    // Bloom skip: `name` provably absent ⇒ `None` without recursing.
    // (`has_free_var` is `find_free_type(..).is_some()`, so it benefits too.)
    if !t.free_bloom().contains(name) {
        return None;
    }
    match t.kind() {
        TermKind::Free(v) if v.name() == name => Some(v.ty().clone()),
        TermKind::Bound(_)
        | TermKind::Free(..)
        | TermKind::Const(..)
        | TermKind::Blob(_)
        | TermKind::Nat(_)
        | TermKind::Int(_)
        | TermKind::SmallInt(_)
        | TermKind::Bool(_)
        | TermKind::Eq(_)
        | TermKind::Select(_)
        | TermKind::Spec(_, _)
        | TermKind::SpecAbs(..)
        | TermKind::SpecRep(..)
        | TermKind::FreshConst(..)
        | TermKind::Succ
        | TermKind::Def(_) => None,
        TermKind::App(a, b) => find_free_type(a, name).or_else(|| find_free_type(b, name)),
        TermKind::Abs(_, body) => find_free_type(body, name),
    }
}

/// True if `t` mentions `Bound(target)` when read at outer depth 0.
/// Under `n` enclosing binders, we look for `Bound(target + n)`. Used
/// by η-conversion to verify that the binder being eliminated does not
/// occur free in the head.
pub fn uses_bound_outer(t: &Term, target: u32) -> bool {
    uses_bound_at(t, target, 0)
}

fn uses_bound_at(t: &Term, target: u32, depth: u32) -> bool {
    match t.kind() {
        TermKind::Bound(i) => *i == target + depth,
        TermKind::Free(..)
        | TermKind::Const(..)
        | TermKind::Blob(_)
        | TermKind::Nat(_)
        | TermKind::Int(_)
        | TermKind::SmallInt(_)
        | TermKind::Bool(_)
        | TermKind::Eq(_)
        | TermKind::Select(_)
        | TermKind::Spec(_, _)
        | TermKind::SpecAbs(..)
        | TermKind::SpecRep(..)
        | TermKind::FreshConst(..)
        | TermKind::Succ
        | TermKind::Def(_) => false,
        TermKind::App(a, b) => uses_bound_at(a, target, depth) || uses_bound_at(b, target, depth),
        TermKind::Abs(_, body) => uses_bound_at(body, target, depth + 1),
    }
}

/// Collect every free type variable name appearing inside any
/// type annotation in `t` — `Free`/`Const`/`FreshConst` `ty` fields,
/// `Abs`/`All` binder types, and recursively into `Def` bodies.
///
/// Used by `Thm::define` to enforce the soundness invariant that
/// every tvar appearing inside the body's interior also appears in
/// the body's overall type (no "phantom" tvars that would escape
/// substitution-tracking via `instance_type`).
pub fn collect_term_tvars(t: &Term, out: &mut std::collections::BTreeSet<SmolStr>) {
    match t.kind() {
        TermKind::Free(v) => {
            for n in v.ty().free_tvars() {
                out.insert(n);
            }
        }
        TermKind::Const(_, ty) => {
            for n in ty.free_tvars() {
                out.insert(n);
            }
        }
        TermKind::FreshConst(leaf) => {
            for n in leaf.ty().free_tvars() {
                out.insert(n);
            }
        }
        TermKind::Abs(ty, body) => {
            for n in ty.free_tvars() {
                out.insert(n);
            }
            collect_term_tvars(body, out);
        }
        TermKind::App(a, b) => {
            collect_term_tvars(a, out);
            collect_term_tvars(b, out);
        }
        // The logical primitives carry an element type that is part of
        // the term's interior: `Eq(α) : α → α → bool` and
        // `Select(α) : (α → bool) → α`. A tvar appearing only here is
        // still a real interior tvar (notably `Select`/ε denotes a
        // type-dependent value), so it must be collected — otherwise
        // `define`'s phantom-tvar check would miss it.
        TermKind::Eq(alpha) | TermKind::Select(alpha) => {
            for n in alpha.free_tvars() {
                out.insert(n);
            }
        }
        // Derived-spec leaves carry their positional type arguments;
        // collect each.
        TermKind::Spec(_, args) | TermKind::SpecAbs(_, args) | TermKind::SpecRep(_, args) => {
            for arg in args.iter() {
                for n in arg.free_tvars() {
                    out.insert(n);
                }
            }
        }
        TermKind::Bound(_)
        | TermKind::Blob(_)
        | TermKind::Nat(_)
        | TermKind::Int(_)
        | TermKind::SmallInt(_)
        | TermKind::Succ
        | TermKind::Bool(_) => {}
        TermKind::Def(d) => collect_term_tvars(&d.body(), out),
    }
}

// ============================================================================
// One-way type matching
// ============================================================================

/// One-way structural match: treats `TFree(n)` in `pattern` as a
/// schematic variable, and finds a substitution `sub` such that
/// applying `sub` to `pattern` yields `target` (structurally).
/// Returns `Err(())` if no consistent substitution exists.
///
/// Used by `Def::body` to recover the type substitution from
/// `body_type` → `instance_type` when reconstructing the body for
/// utility walks.
// TCB: `Err(())` is the documented "no consistent substitution" signal; a
// dedicated error type would add nothing here.
#[allow(clippy::result_unit_err)]
pub fn match_types(
    pattern: &Type,
    target: &Type,
    sub: &mut BTreeMap<SmolStr, Type>,
) -> Result<(), ()> {
    match (pattern.kind(), target.kind()) {
        (TypeKind::TFree(n), _) => match sub.get(n) {
            Some(existing) if existing == target => Ok(()),
            Some(_) => Err(()),
            None => {
                sub.insert(n.clone(), target.clone());
                Ok(())
            }
        },
        (TypeKind::Nat, TypeKind::Nat) => Ok(()),
        (TypeKind::Bool, TypeKind::Bool) => Ok(()),
        (TypeKind::Fun(pa, pb), TypeKind::Fun(ta, tb)) => {
            match_types(pa, ta, sub)?;
            match_types(pb, tb, sub)
        }
        (TypeKind::Tycon(pn, pa), TypeKind::Tycon(tn, ta)) if pn == tn && pa.len() == ta.len() => {
            for (p, t) in pa.iter().zip(ta) {
                match_types(p, t, sub)?;
            }
            Ok(())
        }
        (TypeKind::FreshTyCon(pl), TypeKind::FreshTyCon(tl))
            if pl.id() == tl.id() && pl.args().len() == tl.args().len() =>
        {
            for (p, t) in pl.args().iter().zip(tl.args()) {
                match_types(p, t, sub)?;
            }
            Ok(())
        }
        // A derived-spec application: the handle is invariant under
        // tvar substitution (only the args change), so the two sides
        // must carry the same spec; recurse into the positional args.
        // Without this arm, `Def::body` would panic recovering the
        // substitution for any `Def` typed at a `Spec` (e.g. `int`,
        // `bytes`, `set 'a`).
        (TypeKind::Spec(ps, pa), TypeKind::Spec(ts, ta)) if ps == ts && pa.len() == ta.len() => {
            for (p, t) in pa.iter().zip(ta) {
                match_types(p, t, sub)?;
            }
            Ok(())
        }
        _ => Err(()),
    }
}
