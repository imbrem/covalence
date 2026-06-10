//! Capture-avoiding substitution and de Bruijn shifting.
//!
//! Locally-nameless convention: `Bound(i)` refers to the i-th enclosing
//! binder (innermost first). `Free` and `Const` carry their type and
//! are unaffected by de Bruijn shifts. `Obs` is opaque to substitution
//! over term structure, but its `ty` field participates in type-
//! variable substitution. The operations here are pure syntactic and
//! used by the inference rules in `crate::thm`.

use std::cmp::Ordering;

use std::collections::BTreeMap;

use smol_str::SmolStr;

use crate::term::{Term, TermKind, Type, TypeKind};

// ============================================================================
// Substitution
// ============================================================================

/// Abstract `Free(name, _)` into `Bound(0)`. Recurses into binders,
/// incrementing the target depth on the way in. Used to build the body
/// of an `Abs`/`All` from a term that mentions a fresh free variable.
pub fn close(t: &Term, name: &str) -> Term {
    close_at(t, name, 0)
}

fn close_at(t: &Term, name: &str, depth: u32) -> Term {
    match t.kind() {
        TermKind::Free(n, _) if n == name => Term::bound(depth),
        TermKind::Bound(_)
        | TermKind::Free(..)
        | TermKind::Const(..)
        | TermKind::Blob(_)
        | TermKind::Nat(_)
        | TermKind::Int(_)
        | TermKind::Bool(_)
        | TermKind::HolOp(_, _)
        | TermKind::Prim(_)
        | TermKind::Obs(..)
        | TermKind::Def(_) => t.clone(),
        TermKind::App(f, x) => Term::app(close_at(f, name, depth), close_at(x, name, depth)),
        TermKind::Abs(hint, ty, body) => {
            Term::abs(hint.clone(), ty.clone(), close_at(body, name, depth + 1))
        }
        TermKind::All(hint, ty, body) => {
            Term::all(hint.clone(), ty.clone(), close_at(body, name, depth + 1))
        }
        TermKind::Imp(a, b) => Term::imp(close_at(a, name, depth), close_at(b, name, depth)),
        TermKind::Eq(a, b) => Term::eq(close_at(a, name, depth), close_at(b, name, depth)),
    }
}

/// Instantiate `Bound(0)` with `u` inside `body` (which is the body of
/// an `Abs`/`All`). The outer binder is consumed: `Bound(i)` for `i ≥ 1`
/// shift down by 1; the replacement `u` shifts up by the binder depth
/// at which the substitution happens. Used in β-reduction and
/// ⋀-elimination.
pub fn open(body: &Term, u: &Term) -> Term {
    inst(body, u, 0)
}

fn inst(t: &Term, u: &Term, depth: u32) -> Term {
    match t.kind() {
        TermKind::Bound(i) => {
            let i = *i;
            match i.cmp(&depth) {
                Ordering::Less => Term::bound(i),
                Ordering::Equal => shift_by(u, depth as i64, 0),
                Ordering::Greater => Term::bound(i - 1),
            }
        }
        TermKind::Free(..)
        | TermKind::Const(..)
        | TermKind::Blob(_)
        | TermKind::Nat(_)
        | TermKind::Int(_)
        | TermKind::Bool(_)
        | TermKind::HolOp(_, _)
        | TermKind::Prim(_)
        | TermKind::Obs(..)
        | TermKind::Def(_) => t.clone(),
        TermKind::App(f, x) => Term::app(inst(f, u, depth), inst(x, u, depth)),
        TermKind::Abs(hint, ty, body) => {
            Term::abs(hint.clone(), ty.clone(), inst(body, u, depth + 1))
        }
        TermKind::All(hint, ty, body) => {
            Term::all(hint.clone(), ty.clone(), inst(body, u, depth + 1))
        }
        TermKind::Imp(a, b) => Term::imp(inst(a, u, depth), inst(b, u, depth)),
        TermKind::Eq(a, b) => Term::eq(inst(a, u, depth), inst(b, u, depth)),
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
    if delta == 0 {
        return t.clone();
    }
    shift_inner(t, delta, cutoff)
}

fn shift_inner(t: &Term, delta: i64, cutoff: u32) -> Term {
    match t.kind() {
        TermKind::Bound(i) => {
            let i = *i;
            if i < cutoff {
                return Term::bound(i);
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
            Term::bound(new as u32)
        }
        TermKind::Free(..)
        | TermKind::Const(..)
        | TermKind::Blob(_)
        | TermKind::Nat(_)
        | TermKind::Int(_)
        | TermKind::Bool(_)
        | TermKind::HolOp(_, _)
        | TermKind::Prim(_)
        | TermKind::Obs(..)
        | TermKind::Def(_) => t.clone(),
        TermKind::App(f, x) => {
            Term::app(shift_inner(f, delta, cutoff), shift_inner(x, delta, cutoff))
        }
        TermKind::Abs(hint, ty, body) => Term::abs(
            hint.clone(),
            ty.clone(),
            shift_inner(body, delta, cutoff + 1),
        ),
        TermKind::All(hint, ty, body) => Term::all(
            hint.clone(),
            ty.clone(),
            shift_inner(body, delta, cutoff + 1),
        ),
        TermKind::Imp(a, b) => {
            Term::imp(shift_inner(a, delta, cutoff), shift_inner(b, delta, cutoff))
        }
        TermKind::Eq(a, b) => {
            Term::eq(shift_inner(a, delta, cutoff), shift_inner(b, delta, cutoff))
        }
    }
}

/// Substitute every `Free(name, _)` with `r` in `t`. The replacement is
/// shifted up by the current binder depth when crossing binders so
/// that any `Bound` references inside `r` continue to refer to the
/// outer environment.
pub fn subst_free(t: &Term, name: &str, r: &Term) -> Term {
    subst_free_at(t, name, r, 0)
}

fn subst_free_at(t: &Term, name: &str, r: &Term, depth: u32) -> Term {
    match t.kind() {
        TermKind::Free(n, _) if n == name => shift_by(r, depth as i64, 0),
        TermKind::Bound(_)
        | TermKind::Free(..)
        | TermKind::Const(..)
        | TermKind::Blob(_)
        | TermKind::Nat(_)
        | TermKind::Int(_)
        | TermKind::Bool(_)
        | TermKind::HolOp(_, _)
        | TermKind::Prim(_)
        | TermKind::Obs(..)
        | TermKind::Def(_) => t.clone(),
        TermKind::App(f, x) => Term::app(
            subst_free_at(f, name, r, depth),
            subst_free_at(x, name, r, depth),
        ),
        TermKind::Abs(hint, ty, body) => Term::abs(
            hint.clone(),
            ty.clone(),
            subst_free_at(body, name, r, depth + 1),
        ),
        TermKind::All(hint, ty, body) => Term::all(
            hint.clone(),
            ty.clone(),
            subst_free_at(body, name, r, depth + 1),
        ),
        TermKind::Imp(a, b) => Term::imp(
            subst_free_at(a, name, r, depth),
            subst_free_at(b, name, r, depth),
        ),
        TermKind::Eq(a, b) => Term::eq(
            subst_free_at(a, name, r, depth),
            subst_free_at(b, name, r, depth),
        ),
    }
}

// ============================================================================
// Type-variable substitution
// ============================================================================

/// Replace every `TFree(name)` in `ty` with `r`.
pub fn subst_tfree_in_type(ty: &Type, name: &str, r: &Type) -> Type {
    match ty.kind() {
        TypeKind::TFree(n) if n == name => r.clone(),
        TypeKind::TFree(_)
        | TypeKind::Prop
        | TypeKind::Bytes
        | TypeKind::Nat
        | TypeKind::Int
        | TypeKind::Unit => ty.clone(),
        TypeKind::Fun(a, b) => Type::fun(
            subst_tfree_in_type(a, name, r),
            subst_tfree_in_type(b, name, r),
        ),
        TypeKind::Tycon(n, args) => Type::tycon(
            n.clone(),
            args.iter()
                .map(|a| subst_tfree_in_type(a, name, r))
                .collect(),
        ),
        // The observer Arc identity is preserved; only the type-arg
        // substitution propagates. `list 'a` after 'a := bytes becomes
        // `list bytes` with the same constructor identity — exactly
        // what we want for polymorphic typedefs.
        TypeKind::TyConObs(observer, hint, args) => Type::tycon_obs_from_dyn(
            observer.clone(),
            hint.clone(),
            args.iter().map(|a| subst_tfree_in_type(a, name, r)).collect(),
        ),
    }
}

/// Replace every `TFree(name)` with `r` in every type annotation inside
/// `t`, including the `ty` field of any `Obs` leaf. The observer value
/// itself is opaque and untouched.
pub fn subst_tfree_in_term(t: &Term, name: &str, r: &Type) -> Term {
    let st = |ty: &Type| subst_tfree_in_type(ty, name, r);
    let sub = |x: &Term| subst_tfree_in_term(x, name, r);
    match t.kind() {
        TermKind::Bound(i) => Term::bound(*i),
        TermKind::Free(n, ty) => Term::free(n.clone(), st(ty)),
        TermKind::Const(n, ty) => Term::const_(n.clone(), st(ty)),
        TermKind::App(f, x) => Term::app(sub(f), sub(x)),
        TermKind::Abs(hint, ty, body) => Term::abs(hint.clone(), st(ty), sub(body)),
        TermKind::All(hint, ty, body) => Term::all(hint.clone(), st(ty), sub(body)),
        TermKind::Imp(a, b) => Term::imp(sub(a), sub(b)),
        TermKind::Eq(a, b) => Term::eq(sub(a), sub(b)),
        TermKind::Blob(b) => Term::blob(b.clone()),
        TermKind::Nat(n) => Term::nat_lit(n.clone()),
        TermKind::Int(n) => Term::int_lit(n.clone()),
        TermKind::Bool(b) => Term::bool_lit(*b),
        TermKind::Prim(p) => Term::prim(*p),
        TermKind::HolOp(op, ty) => Term::hol_op(*op, st(ty)),
        TermKind::Obs(observer, ty) => Term::obs_from_dyn(observer.clone(), st(ty)),
        // `Def` carries an `original` Arc identity (the unique
        // `Thm::define` call) plus an `instance_type`. Substitution
        // updates `instance_type` without rebuilding `original`, so
        // the result compares equal to any other `Def` reaching this
        // same instance — the property HOL Light's `INST_TYPE` and
        // polymorphic-constant equality depend on.
        TermKind::Def(d) => {
            Term::def(d.with_instance_type(subst_tfree_in_type(d.instance_type(), name, r)))
        }
    }
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
        | TermKind::Bool(_)
        | TermKind::HolOp(_, _)
        | TermKind::Prim(_)
        | TermKind::Obs(..)
        | TermKind::Def(_) => true,
        TermKind::App(a, b) | TermKind::Imp(a, b) | TermKind::Eq(a, b) => {
            is_closed_at(a, depth) && is_closed_at(b, depth)
        }
        TermKind::Abs(_, _, body) | TermKind::All(_, _, body) => is_closed_at(body, depth + 1),
    }
}

/// True if `name` appears as a `Free` variable anywhere in `t`.
pub fn has_free_var(t: &Term, name: &str) -> bool {
    find_free_type(t, name).is_some()
}

/// First-encountered declared type of `Free(name)` in `t`, or `None`
/// if no `Free` with that name appears. Because every theorem
/// enforces cross-term `Free` consistency at construction, this is
/// the *only* type the variable can have within that theorem.
pub fn find_free_type(t: &Term, name: &str) -> Option<Type> {
    match t.kind() {
        TermKind::Free(n, ty) if n == name => Some(ty.clone()),
        TermKind::Bound(_)
        | TermKind::Free(..)
        | TermKind::Const(..)
        | TermKind::Blob(_)
        | TermKind::Nat(_)
        | TermKind::Int(_)
        | TermKind::Bool(_)
        | TermKind::HolOp(_, _)
        | TermKind::Prim(_)
        | TermKind::Obs(..)
        | TermKind::Def(_) => None,
        TermKind::App(a, b) | TermKind::Imp(a, b) | TermKind::Eq(a, b) => {
            find_free_type(a, name).or_else(|| find_free_type(b, name))
        }
        TermKind::Abs(_, _, body) | TermKind::All(_, _, body) => find_free_type(body, name),
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
        | TermKind::Bool(_)
        | TermKind::HolOp(_, _)
        | TermKind::Prim(_)
        | TermKind::Obs(..)
        | TermKind::Def(_) => false,
        TermKind::App(a, b) | TermKind::Imp(a, b) | TermKind::Eq(a, b) => {
            uses_bound_at(a, target, depth) || uses_bound_at(b, target, depth)
        }
        TermKind::Abs(_, _, body) | TermKind::All(_, _, body) => {
            uses_bound_at(body, target, depth + 1)
        }
    }
}

/// Collect every free type variable name appearing inside any
/// type annotation in `t` — `Free`/`Const`/`Obs` `ty` fields,
/// `Abs`/`All` binder types, and recursively into `Def` bodies.
///
/// Used by `Thm::define` to enforce the soundness invariant that
/// every tvar appearing inside the body's interior also appears in
/// the body's overall type (no "phantom" tvars that would escape
/// substitution-tracking via `instance_type`).
pub fn collect_term_tvars(t: &Term, out: &mut std::collections::BTreeSet<SmolStr>) {
    match t.kind() {
        TermKind::Free(_, ty) | TermKind::Const(_, ty) | TermKind::Obs(_, ty) => {
            for n in ty.free_tvars() {
                out.insert(n);
            }
        }
        TermKind::Abs(_, ty, body) | TermKind::All(_, ty, body) => {
            for n in ty.free_tvars() {
                out.insert(n);
            }
            collect_term_tvars(body, out);
        }
        TermKind::App(a, b) | TermKind::Imp(a, b) | TermKind::Eq(a, b) => {
            collect_term_tvars(a, out);
            collect_term_tvars(b, out);
        }
        TermKind::Bound(_)
        | TermKind::Blob(_)
        | TermKind::Nat(_)
        | TermKind::Int(_)
        | TermKind::Bool(_)
        | TermKind::HolOp(_, _)
        | TermKind::Prim(_) => {}
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
/// utility walks (`has_no_obs`, etc.).
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
        (TypeKind::Prop, TypeKind::Prop)
        | (TypeKind::Bytes, TypeKind::Bytes)
        | (TypeKind::Nat, TypeKind::Nat)
        | (TypeKind::Int, TypeKind::Int) => Ok(()),
        (TypeKind::Fun(pa, pb), TypeKind::Fun(ta, tb)) => {
            match_types(pa, ta, sub)?;
            match_types(pb, tb, sub)
        }
        (TypeKind::Tycon(pn, pa), TypeKind::Tycon(tn, ta))
            if pn == tn && pa.len() == ta.len() =>
        {
            for (p, t) in pa.iter().zip(ta) {
                match_types(p, t, sub)?;
            }
            Ok(())
        }
        (TypeKind::TyConObs(po, _, pa), TypeKind::TyConObs(to, _, ta))
            if po.ptr_id() == to.ptr_id() && pa.len() == ta.len() =>
        {
            for (p, t) in pa.iter().zip(ta) {
                match_types(p, t, sub)?;
            }
            Ok(())
        }
        _ => Err(()),
    }
}
