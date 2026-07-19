//! **SpecTec type → HOL type** (leg B, the type foundation).
//!
//! Renders a SpecTec `SpecTecTyp` (and a whole `SpecTecDef::Typ`) to a genuine
//! HOL [`Type`] over the [`crate::init`] catalogue: `bool`/`nat`/`int` primitives,
//! tuples → right-nested `prod`, `X*`/`X?` → `list`/`option`, named **alias** types
//! chased through a [`TypeCtx`], **struct** types → `prod` of their fields, and
//! **non-recursive variant** types → a coproduct-of-payloads via the generic
//! datatype backend ([`crate::init::inductive::VariantBackend`]). This is what
//! [`super::denote`] needs to type metavariables from the spec, and the first step
//! toward typing SpecTec functions and relations.
//!
//! Recursive variants render via the impredicative [`ChurchBackend`] `Φ⟨'r⟩`
//! (self-references → a result type variable), and **parametric** types `T(A…)`
//! instantiate by resolving `T`'s body with its type parameters bound (value/`exp`
//! parameters don't affect the HOL type). A `Scope` threads the self-reference
//! name and the type-parameter bindings.
//!
//! **Type families by case analysis** (multiple [`SpecTecInst`]s — `num_`,
//! `unop_`, `vcvtop__`, …) dispatch on their arguments: each instance carries
//! argument *patterns* (`num_(Inn) = iN(…)` vs `num_(Fnn) = fN(…)`), and
//! [`resolve_parametric`] selects the instance those patterns match — by the
//! argument's `Sub`-coercion source type, its metavariable's type (SpecTec names
//! metavariables after their type, `numtype_1 : numtype`), or a concrete `Case`
//! tag looked up in the case sets. When the argument does **not** determine the
//! instance (a supertype metavariable like `unop_(numtype)`), variant-bodied
//! families render as the **union variant** of all candidate instances' cases (in
//! instance order) — a type-level over-approximation in the same faithfulness
//! class as the dropped case-refinement premises below; alias-bodied families
//! must then agree on one HOL type.
//!
//! Separately, [`CaseCatalogue`] is the **total reified case catalogue**: for
//! *every* variant `Typ` (all of them — parametric, multi-instance, recursive,
//! mutually-recursive alike) the ordered case tags and symbolic payload *shapes*,
//! keyed by `(type name, case key)`. It is pure AST processing (no HOL
//! rendering), never fails, and is what ground `Uncase`/`Proj` evaluation gates
//! on.
//!
//! Building a `Type` cannot be unsound (it grows no `Thm`), so this is a plain
//! total-where-possible renderer. Still deferred (typed error), on the bundled
//! WASM 3.0 spec:
//!
//! - the 9-type **mutually-recursive** SCC (`typeuse`/`heaptype`/`valtype`/
//!   `storagetype`/`resulttype`/`fieldtype`/`comptype`/`subtype`/`rectype`) — a
//!   sibling reference cycles (the self-mapping only covers a type's own name);
//!   blocks 53 types incl. `instr`/`module`/`store`;
//! - **parametric cases** (non-empty `qs`): `fN`/`fNmag`/`ishape` (+ inherited
//!   `f32`/`f64`) — the float representations;
//! - `text`/`rat`/`real` and non-numeric value-indexed subtleties.
//!
//! Faithfulness caveat (not a rendering failure): case/field **refinement
//! premises** (`prs`, 56 across 29 spec types) are erased — e.g. `byte` renders
//! as an unconstrained `nat` without its `< 256` side condition. Rendered types
//! over-approximate; nothing derives theorems from them. See the generated open-work index.

use std::collections::{BTreeMap, BTreeSet};

use covalence_core::{Error, Result, Type};
use covalence_spectec::ast::{
    SpecTecArg, SpecTecDef, SpecTecDefTyp, SpecTecExp, SpecTecInst, SpecTecIter, SpecTecNumTyp,
    SpecTecParam, SpecTecTyp, SpecTecTypBind, SpecTecTypCase, SpecTecTypField,
};

use crate::init::inductive::{
    ChurchBackend, CoprodBackend, VCtor, Variant, VariantBackend, self_ty_var,
};
use crate::init::{list, option, prod};

fn syntax_err(msg: impl Into<String>) -> Error {
    Error::ConnectiveRule(format!("spectec syntax: {}", msg.into()))
}

/// A resolver for named SpecTec types (for chasing `Var` aliases). Built from a
/// definition list (the whole spec), flattening `rec` groups.
pub struct TypeCtx<'a> {
    by_name: BTreeMap<&'a str, &'a SpecTecDef>,
}

impl<'a> TypeCtx<'a> {
    /// Index every `Typ` definition in `defs` by name.
    pub fn new(defs: &'a [SpecTecDef]) -> Self {
        let mut by_name = BTreeMap::new();
        fn go<'a>(d: &'a SpecTecDef, m: &mut BTreeMap<&'a str, &'a SpecTecDef>) {
            match d {
                SpecTecDef::Typ { x, .. } => {
                    m.insert(x.as_str(), d);
                }
                SpecTecDef::Rec { ds } => ds.iter().for_each(|x| go(x, m)),
                _ => {}
            }
        }
        defs.iter().for_each(|d| go(d, &mut by_name));
        TypeCtx { by_name }
    }

    fn lookup(&self, name: &str) -> Option<&'a SpecTecDef> {
        self.by_name.get(name).copied()
    }
}

/// A resolution scope: the datatype currently being defined (so a recursive
/// self-reference maps to [`self_ty_var`]) and the **type-parameter bindings** in
/// effect (so parametric instantiation `T(A)` resolves `T`'s body with its params
/// bound). Threaded by shared reference; new scopes are cheap clones.
#[derive(Clone, Default)]
struct Scope {
    /// The variant whose payload we're resolving; a `Var` to it → `self_ty_var`.
    self_name: Option<String>,
    /// Type-parameter name → resolved HOL type.
    tenv: BTreeMap<String, Type>,
}

impl Scope {
    /// Same parameter bindings, resolving variant `name`'s payloads (self-mapping).
    fn under_variant(&self, name: &str) -> Scope {
        Scope {
            self_name: Some(name.to_owned()),
            tenv: self.tenv.clone(),
        }
    }
    /// Same parameter bindings, no self-mapping (alias/struct bodies).
    fn no_self(&self) -> Scope {
        Scope {
            self_name: None,
            tenv: self.tenv.clone(),
        }
    }
}

/// Render a SpecTec type to a HOL [`Type`], chasing named aliases through `ctx`.
pub fn resolve_typ(t: &SpecTecTyp, ctx: &TypeCtx) -> Result<Type> {
    resolve_typ_d(t, ctx, &mut Vec::new(), &Scope::default())
}

/// Render the type a `SpecTecDef::Typ` denotes. Errors on parametric definitions
/// (they need arguments — instantiate via a `Var` application instead).
pub fn resolve_def(def: &SpecTecDef, ctx: &TypeCtx) -> Result<Type> {
    let SpecTecDef::Typ { x, .. } = def else {
        return Err(syntax_err("definition is not a `typ`"));
    };
    resolve_named(x, ctx, &mut Vec::new())
}

fn resolve_typ_d<'a>(
    t: &'a SpecTecTyp,
    ctx: &TypeCtx<'a>,
    visited: &mut Vec<&'a str>,
    scope: &Scope,
) -> Result<Type> {
    match t {
        SpecTecTyp::Bool => Ok(Type::bool()),
        SpecTecTyp::Num(SpecTecNumTyp::Nat) => Ok(Type::nat()),
        SpecTecTyp::Num(SpecTecNumTyp::Int) => Ok(Type::int()),
        SpecTecTyp::Num(nt) => Err(syntax_err(format!("numeric type {nt:?} not modelled yet"))),
        SpecTecTyp::Text => Err(syntax_err("text type not modelled yet")),
        SpecTecTyp::Tup { ets } => resolve_tuple(ets, ctx, visited, scope),
        SpecTecTyp::Iter { t1, it } => {
            let mut ty = resolve_typ_d(t1, ctx, visited, scope)?;
            for step in it {
                ty = match step {
                    SpecTecIter::Opt => option::option(ty),
                    SpecTecIter::List | SpecTecIter::List1 | SpecTecIter::ListN { .. } => {
                        list::list(ty)
                    }
                };
            }
            Ok(ty)
        }
        SpecTecTyp::Var { x, as1 } => resolve_var(x, as1, ctx, visited, scope),
    }
}

/// A tuple type `(t₀, …, tₙ)` → right-nested `prod` (`[]` = `unit`, singleton =
/// the element itself).
fn resolve_tuple<'a>(
    ets: &'a [SpecTecTypBind],
    ctx: &TypeCtx<'a>,
    visited: &mut Vec<&'a str>,
    scope: &Scope,
) -> Result<Type> {
    match ets {
        [] => Ok(Type::unit()),
        [SpecTecTypBind::Bind { typ, .. }] => resolve_typ_d(typ, ctx, visited, scope),
        [SpecTecTypBind::Bind { typ, .. }, rest @ ..] => {
            let head = resolve_typ_d(typ, ctx, visited, scope)?;
            let tail = resolve_tuple(rest, ctx, visited, scope)?;
            Ok(prod::prod(head, tail))
        }
    }
}

/// A type reference `x` or application `x(a…)`.
fn resolve_var<'a>(
    x: &'a str,
    as1: &'a [SpecTecArg],
    ctx: &TypeCtx<'a>,
    visited: &mut Vec<&'a str>,
    scope: &Scope,
) -> Result<Type> {
    if as1.is_empty() {
        // A recursive self-reference inside the current variant's payload.
        if scope.self_name.as_deref() == Some(x) {
            return Ok(self_ty_var());
        }
        // A bound type parameter.
        if let Some(ty) = scope.tenv.get(x) {
            return Ok(ty.clone());
        }
        return resolve_named(x, ctx, visited);
    }
    resolve_parametric(x, as1, ctx, visited, scope)
}

/// Instantiate a parametric type `name(a…)`: bind its type parameters to the
/// resolved type arguments (value/`exp` parameters are irrelevant to the HOL type
/// and ignored) and resolve its body under those bindings. A **multi-instance**
/// family dispatches on the arguments (see [`dispatch_instances`]).
fn resolve_parametric<'a>(
    name: &'a str,
    as1: &'a [SpecTecArg],
    ctx: &TypeCtx<'a>,
    visited: &mut Vec<&'a str>,
    scope: &Scope,
) -> Result<Type> {
    let def = ctx
        .lookup(name)
        .ok_or_else(|| syntax_err(format!("unknown type `{name}`")))?;
    let SpecTecDef::Typ { ps, insts, .. } = def else {
        return Err(syntax_err(format!("`{name}` is not a type")));
    };
    if ps.len() != as1.len() {
        return Err(syntax_err(format!(
            "`{name}`: wrong number of type arguments"
        )));
    }
    // Bind type parameters to their resolved arguments (in the *caller's* scope).
    let mut tenv = BTreeMap::new();
    for (p, a) in ps.iter().zip(as1) {
        match p {
            SpecTecParam::Typ { x: pname } => match a {
                SpecTecArg::Typ { t } => {
                    tenv.insert(pname.clone(), resolve_typ_d(t, ctx, visited, scope)?);
                }
                _ => {
                    return Err(syntax_err(format!(
                        "`{name}`: type parameter needs a type arg"
                    )));
                }
            },
            // A value parameter (e.g. the width `N` of `uN(N)`): the HOL type does
            // not depend on it, so nothing to bind.
            SpecTecParam::Exp { .. } => {}
            _ => {
                return Err(syntax_err(format!(
                    "`{name}`: def/grammar parameter not modelled"
                )));
            }
        }
    }
    let base = Scope {
        self_name: None,
        tenv,
    };
    match insts.as_slice() {
        [] => Err(syntax_err(format!("`{name}` has zero instances"))),
        [SpecTecInst::Inst { dt, .. }] => enter(name, dt, ctx, visited, &base),
        _ => dispatch_instances(name, insts, as1, ctx, visited, &base),
    }
}

/// How well an instance's argument patterns fit the supplied arguments.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PatMatch {
    /// The arguments definitely belong to this instance.
    Yes,
    /// Cannot tell (e.g. a metavariable of the *supertype* — `unop_(numtype)`).
    Maybe,
    /// The arguments definitely do not belong to this instance.
    No,
}

impl PatMatch {
    /// Conjunction over pattern components: any `No` refutes; all `Yes` confirms.
    fn and(self, other: PatMatch) -> PatMatch {
        use PatMatch::*;
        match (self, other) {
            (No, _) | (_, No) => No,
            (Yes, Yes) => Yes,
            _ => Maybe,
        }
    }
}

/// **Instance dispatch** for a type family by case analysis (`insts.len() > 1`):
/// select the [`SpecTecInst`] whose argument patterns match `as1`.
///
/// - Exactly one instance matches positively ([`PatMatch::Yes`]) → resolve its
///   body (so `num_(I32)` = the `Inn` instance = `iN(…)`).
/// - No instance is even possible → a typed error (correct refusal).
/// - Otherwise (the argument leaves several instances open) → the **union** of
///   the candidates: variant-bodied instances join into one variant whose cases
///   are all candidates' cases *in instance order* (matching the ordinals of
///   [`CaseCatalogue`] / [`variant_of`]); non-variant candidates must all render
///   to the *same* HOL type. The union is a type-level over-approximation (see
///   the module docs) — it can only make a rendered type bigger, never forge a
///   theorem.
fn dispatch_instances<'a>(
    name: &'a str,
    insts: &'a [SpecTecInst],
    as1: &'a [SpecTecArg],
    ctx: &TypeCtx<'a>,
    visited: &mut Vec<&'a str>,
    base: &Scope,
) -> Result<Type> {
    let mut yes = Vec::new();
    let mut open = Vec::new(); // Yes ∪ Maybe, in instance order
    for inst in insts {
        let SpecTecInst::Inst { ps: ips, as_, .. } = inst;
        match match_args(as_, as1, ips, ctx) {
            PatMatch::Yes => {
                yes.push(inst);
                open.push(inst);
            }
            PatMatch::Maybe => open.push(inst),
            PatMatch::No => {}
        }
    }
    if let [SpecTecInst::Inst { dt, .. }] = yes.as_slice() {
        return enter(name, dt, ctx, visited, base);
    }
    match open.as_slice() {
        [] => Err(syntax_err(format!(
            "`{name}`: no instance matches the arguments"
        ))),
        [SpecTecInst::Inst { dt, .. }] => enter(name, dt, ctx, visited, base),
        _ => join_instances(name, &open, ctx, visited, base),
    }
}

/// The union type of several candidate instances (see [`dispatch_instances`]).
fn join_instances<'a>(
    name: &'a str,
    cands: &[&'a SpecTecInst],
    ctx: &TypeCtx<'a>,
    visited: &mut Vec<&'a str>,
    base: &Scope,
) -> Result<Type> {
    if visited.contains(&name) {
        return Err(syntax_err(format!("cyclic type `{name}`")));
    }
    visited.push(name);
    let r = join_instances_d(name, cands, ctx, visited, base);
    visited.pop();
    r
}

fn join_instances_d<'a>(
    name: &'a str,
    cands: &[&'a SpecTecInst],
    ctx: &TypeCtx<'a>,
    visited: &mut Vec<&'a str>,
    base: &Scope,
) -> Result<Type> {
    // All variant-bodied → the union variant (cases concatenated in instance order).
    if cands
        .iter()
        .all(|SpecTecInst::Inst { dt, .. }| matches!(dt, SpecTecDefTyp::Variant { .. }))
    {
        let mut ctors = Vec::new();
        for SpecTecInst::Inst { dt, .. } in cands {
            let SpecTecDefTyp::Variant { tcs } = dt else {
                unreachable!()
            };
            ctors.extend(build_variant(name, tcs, ctx, visited, base)?.ctors);
        }
        let v = Variant::new(ctors);
        return if is_recursive(&v) {
            ChurchBackend.ty(&v)
        } else {
            CoprodBackend.ty(&v)
        };
    }
    // Otherwise every candidate must render to the same HOL type.
    let mut tys = Vec::with_capacity(cands.len());
    for SpecTecInst::Inst { dt, .. } in cands {
        tys.push(body_type(name, dt, ctx, visited, base)?);
    }
    let first = tys[0].clone();
    if tys.iter().all(|t| *t == first) {
        Ok(first)
    } else {
        Err(syntax_err(format!(
            "`{name}`: ambiguous instances render to different HOL types"
        )))
    }
}

/// Match an instance's argument patterns against the supplied arguments,
/// component-wise. `ips` are the instance's own parameters (its pattern
/// variables — a bare pattern variable is a wildcard).
fn match_args(
    pats: &[SpecTecArg],
    args: &[SpecTecArg],
    ips: &[SpecTecParam],
    ctx: &TypeCtx,
) -> PatMatch {
    if pats.len() != args.len() {
        return PatMatch::No;
    }
    let pvars: BTreeSet<&str> = ips
        .iter()
        .filter_map(|p| match p {
            SpecTecParam::Exp { x, .. } | SpecTecParam::Typ { x } => Some(x.as_str()),
            _ => None,
        })
        .collect();
    pats.iter()
        .zip(args)
        .map(|(p, a)| match (p, a) {
            (SpecTecArg::Exp { e: pe }, SpecTecArg::Exp { e: ae }) => {
                match_exp(pe, ae, &pvars, ctx)
            }
            // Type-level patterns don't occur in the bundled spec; stay open.
            (SpecTecArg::Typ { .. }, SpecTecArg::Typ { .. }) => PatMatch::Maybe,
            _ => PatMatch::No,
        })
        .fold(PatMatch::Yes, PatMatch::and)
}

/// Match one expression pattern against an argument expression.
fn match_exp(
    pat: &SpecTecExp,
    arg: &SpecTecExp,
    pvars: &BTreeSet<&str>,
    ctx: &TypeCtx,
) -> PatMatch {
    use SpecTecExp as E;
    match pat {
        // An upcast pattern `x <: T` (e.g. `num_(Inn)`'s `Inn <: numtype`):
        // dispatch on whether the argument's values lie in `T`.
        E::Sub { t1, .. } => match typ_name(t1) {
            Some(t) => arg_in_type(arg, t, ctx),
            None => PatMatch::Maybe,
        },
        // A bare pattern variable is a wildcard binder.
        E::Var { id } if pvars.contains(id.as_str()) => PatMatch::Yes,
        E::Var { .. } => PatMatch::Maybe,
        // A constructor pattern (`vunop_`'s `Jnn X dim` shape): the tags must
        // agree, then the payloads match component-wise.
        E::Case { op, e1 } => match arg {
            E::Case { op: aop, e1: ae } => {
                if super::encode::mixop_key(aop) == super::encode::mixop_key(op) {
                    match_exp(e1, ae, pvars, ctx)
                } else {
                    PatMatch::No
                }
            }
            E::Var { id } => match var_type_name(id, ctx) {
                Some(t) => match has_case(&t, &super::encode::mixop_key(op), ctx) {
                    Some(true) | None => PatMatch::Maybe,
                    Some(false) => PatMatch::No,
                },
                None => PatMatch::Maybe,
            },
            E::Sub { t1, .. } => match typ_name(t1) {
                Some(t) => match has_case(t, &super::encode::mixop_key(op), ctx) {
                    Some(true) | None => PatMatch::Maybe,
                    Some(false) => PatMatch::No,
                },
                None => PatMatch::Maybe,
            },
            _ => PatMatch::Maybe,
        },
        E::Tup { es: pes } => match arg {
            E::Tup { es } => {
                if pes.len() != es.len() {
                    return PatMatch::No;
                }
                pes.iter()
                    .zip(es)
                    .map(|(p, a)| match_exp(p, a, pvars, ctx))
                    .fold(PatMatch::Yes, PatMatch::and)
            }
            _ => PatMatch::Maybe,
        },
        _ => PatMatch::Maybe,
    }
}

/// Whether the values `arg` can take lie in the named type `t`.
fn arg_in_type(arg: &SpecTecExp, t: &str, ctx: &TypeCtx) -> PatMatch {
    use SpecTecExp as E;
    match arg {
        E::Sub { t1, .. } => match typ_name(t1) {
            Some(u) => relate(u, t, ctx),
            None => PatMatch::Maybe,
        },
        E::Var { id } => match var_type_name(id, ctx) {
            Some(u) => relate(&u, t, ctx),
            None => PatMatch::Maybe,
        },
        E::Case { op, .. } => match has_case(t, &super::encode::mixop_key(op), ctx) {
            Some(true) => PatMatch::Yes,
            Some(false) => PatMatch::No,
            None => PatMatch::Maybe,
        },
        _ => PatMatch::Maybe,
    }
}

/// Relate a value statically of type `u` to the guard type `t`, by case-set
/// inclusion: `u ⊆ t` → definitely in, disjoint → definitely out, overlap or
/// unknown → indeterminate.
fn relate(u: &str, t: &str, ctx: &TypeCtx) -> PatMatch {
    if u == t {
        return PatMatch::Yes;
    }
    match (case_key_set(u, ctx), case_key_set(t, ctx)) {
        (Some(ku), Some(kt)) => {
            if ku.is_subset(&kt) {
                PatMatch::Yes
            } else if ku.is_disjoint(&kt) {
                PatMatch::No
            } else {
                PatMatch::Maybe
            }
        }
        _ => PatMatch::Maybe,
    }
}

/// Whether the named type has a case with the given key (`None` = can't tell —
/// the name isn't a variant we can see through).
fn has_case(name: &str, key: &str, ctx: &TypeCtx) -> Option<bool> {
    case_key_set(name, ctx).map(|ks| ks.contains(key))
}

/// The set of case keys of a named **variant** type (over *all* its instances),
/// chasing nullary aliases; `None` for anything else.
fn case_key_set(name: &str, ctx: &TypeCtx) -> Option<BTreeSet<String>> {
    fn go(name: &str, ctx: &TypeCtx, seen: &mut Vec<String>) -> Option<BTreeSet<String>> {
        if seen.iter().any(|s| s == name) {
            return None;
        }
        seen.push(name.to_owned());
        let SpecTecDef::Typ { insts, .. } = ctx.lookup(name)? else {
            return None;
        };
        let mut keys = BTreeSet::new();
        for SpecTecInst::Inst { dt, .. } in insts {
            match dt {
                SpecTecDefTyp::Variant { tcs } => {
                    for SpecTecTypCase::Field { op, .. } in tcs {
                        keys.insert(super::encode::mixop_key(op));
                    }
                }
                SpecTecDefTyp::Alias {
                    typ: SpecTecTyp::Var { x, as1 },
                } if as1.is_empty() => {
                    keys.extend(go(x, ctx, seen)?);
                }
                _ => return None,
            }
        }
        Some(keys)
    }
    go(name, ctx, &mut Vec::new())
}

/// The name of a `Var` type (`None` for structural types).
fn typ_name(t: &SpecTecTyp) -> Option<&str> {
    match t {
        SpecTecTyp::Var { x, as1 } if as1.is_empty() => Some(x),
        _ => None,
    }
}

/// The type a SpecTec metavariable ranges over, by the naming convention
/// (`numtype_1 : numtype`, `Inn' : Inn`): the id itself if it names a type, else
/// the id with a trailing prime/`_<digits>` suffix stripped.
fn var_type_name(id: &str, ctx: &TypeCtx) -> Option<String> {
    let base = id.trim_end_matches('\'');
    if ctx.lookup(base).is_some() {
        return Some(base.to_owned());
    }
    if let Some((head, tail)) = base.rsplit_once('_')
        && !tail.is_empty()
        && tail.chars().all(|c| c.is_ascii_digit())
        && ctx.lookup(head).is_some()
    {
        return Some(head.to_owned());
    }
    None
}

/// Resolve a nullary named type reference (chasing its definition).
fn resolve_named<'a>(name: &'a str, ctx: &TypeCtx<'a>, visited: &mut Vec<&'a str>) -> Result<Type> {
    let def = ctx
        .lookup(name)
        .ok_or_else(|| syntax_err(format!("unknown type `{name}`")))?;
    let SpecTecDef::Typ { ps, insts, .. } = def else {
        return Err(syntax_err(format!("`{name}` is not a type")));
    };
    if !ps.is_empty() {
        return Err(syntax_err(format!(
            "parametric type `{name}` used without arguments"
        )));
    }
    let [SpecTecInst::Inst { dt, .. }] = insts.as_slice() else {
        return Err(syntax_err(format!("`{name}` has multiple/zero instances")));
    };
    enter(name, dt, ctx, visited, &Scope::default())
}

/// Resolve a definition body under `base` (its parameter bindings), guarding the
/// name against cycles. Aliases/structs resolve without self-mapping (a recursive
/// alias/record is deferred); variants get the self-mapping via [`resolve_variant`].
fn enter<'a>(
    name: &'a str,
    dt: &'a SpecTecDefTyp,
    ctx: &TypeCtx<'a>,
    visited: &mut Vec<&'a str>,
    base: &Scope,
) -> Result<Type> {
    if visited.contains(&name) {
        return Err(syntax_err(format!("cyclic type `{name}`")));
    }
    visited.push(name);
    let r = body_type(name, dt, ctx, visited, base);
    visited.pop();
    r
}

/// Resolve a definition body (no cycle guard — [`enter`] / [`join_instances`]
/// guard the name first).
fn body_type<'a>(
    name: &'a str,
    dt: &'a SpecTecDefTyp,
    ctx: &TypeCtx<'a>,
    visited: &mut Vec<&'a str>,
    base: &Scope,
) -> Result<Type> {
    match dt {
        SpecTecDefTyp::Alias { typ } => resolve_typ_d(typ, ctx, visited, &base.no_self()),
        SpecTecDefTyp::Struct { tfs } => resolve_struct(tfs, ctx, visited, &base.no_self()),
        SpecTecDefTyp::Variant { tcs } => resolve_variant(name, tcs, ctx, visited, base),
    }
}

/// A record type → the right-nested `prod` of its field types (`{}` = `unit`).
fn resolve_struct<'a>(
    tfs: &'a [SpecTecTypField],
    ctx: &TypeCtx<'a>,
    visited: &mut Vec<&'a str>,
    scope: &Scope,
) -> Result<Type> {
    match tfs {
        [] => Ok(Type::unit()),
        [SpecTecTypField::Field { t, qs, .. }] => {
            reject_parametric_field(qs)?;
            resolve_typ_d(t, ctx, visited, scope)
        }
        [SpecTecTypField::Field { t, qs, .. }, rest @ ..] => {
            reject_parametric_field(qs)?;
            let head = resolve_typ_d(t, ctx, visited, scope)?;
            let tail = resolve_struct(rest, ctx, visited, scope)?;
            Ok(prod::prod(head, tail))
        }
    }
}

/// A variant type → a coproduct-of-payloads (non-recursive, [`CoprodBackend`]) or,
/// if any payload references `name` (a recursive occurrence, now `self_ty_var`),
/// the impredicative [`ChurchBackend`] `Φ⟨'r⟩`.
fn resolve_variant<'a>(
    name: &'a str,
    tcs: &'a [SpecTecTypCase],
    ctx: &TypeCtx<'a>,
    visited: &mut Vec<&'a str>,
    base: &Scope,
) -> Result<Type> {
    let v = build_variant(name, tcs, ctx, visited, base)?;
    if is_recursive(&v) {
        ChurchBackend.ty(&v)
    } else {
        CoprodBackend.ty(&v)
    }
}

/// Whether any constructor payload mentions the self type variable.
fn is_recursive(v: &Variant) -> bool {
    v.is_recursive()
}

/// The generic [`Variant`] description a variant's cases denote (constructor name
/// = case mixop key, payload = resolved case type, self-references → `self_ty_var`).
fn build_variant<'a>(
    name: &'a str,
    tcs: &'a [SpecTecTypCase],
    ctx: &TypeCtx<'a>,
    visited: &mut Vec<&'a str>,
    base: &Scope,
) -> Result<Variant> {
    if tcs.is_empty() {
        return Err(syntax_err("empty variant has no type"));
    }
    let payload_scope = base.under_variant(name);
    let mut ctors = Vec::with_capacity(tcs.len());
    for SpecTecTypCase::Field { op, t, qs, .. } in tcs {
        reject_parametric_field(qs)?;
        let payload = resolve_typ_d(t, ctx, visited, &payload_scope)?;
        ctors.push(VCtor::new(super::encode::mixop_key(op), payload));
    }
    Ok(Variant::new(ctors))
}

/// Resolve a top-level `SpecTecDef::Typ` **variant** definition to its generic
/// [`Variant`] description (the constructors + payload types). Used by
/// [`super::denote`] to build constructor terms for `case` expressions.
///
/// Value (`exp`) parameters are allowed — they never affect the HOL payloads —
/// so this covers value-indexed variants (`uN(N)`) and multi-instance families
/// (`unop_`): a family yields the **union** variant, its instances' cases
/// concatenated in instance order (the same ordinals as [`CaseCatalogue`] and
/// the ambiguous-argument join in [`resolve_parametric`]). Errors on type
/// parameters (no payload binding available standalone) and non-variant bodies.
pub fn variant_of(def: &SpecTecDef, ctx: &TypeCtx) -> Result<Variant> {
    let SpecTecDef::Typ { x, ps, insts } = def else {
        return Err(syntax_err("definition is not a `typ`"));
    };
    if ps.iter().any(|p| !matches!(p, SpecTecParam::Exp { .. })) {
        return Err(syntax_err(format!(
            "type-parametric type `{x}` not modelled yet"
        )));
    }
    if insts.is_empty() {
        return Err(syntax_err(format!("`{x}` has zero instances")));
    }
    let mut ctors = Vec::new();
    for SpecTecInst::Inst { ps: ips, dt, .. } in insts {
        if ips.iter().any(|p| !matches!(p, SpecTecParam::Exp { .. })) {
            return Err(syntax_err(format!(
                "type-parametric type `{x}` not modelled yet"
            )));
        }
        let SpecTecDefTyp::Variant { tcs } = dt else {
            return Err(syntax_err(format!("`{x}` is not a variant")));
        };
        let mut visited = vec![x.as_str()];
        ctors.extend(build_variant(x, tcs, ctx, &mut visited, &Scope::default())?.ctors);
    }
    Ok(Variant::new(ctors))
}

// ===========================================================================
// The total reified case catalogue (pure AST — no HOL rendering)
// ===========================================================================

/// The symbolic **payload shape** of a variant case: one compact symbolic type
/// per tuple component of the payload (a non-tuple payload is one component; a
/// nullary case has none). Pure AST data — building it never touches HOL, so it
/// is total over the whole spec. This is what ground `Uncase`/`Proj` evaluation
/// gates on: tag agreement + projection arity, no datatype rendering required.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CaseShape {
    /// One symbolic type per payload tuple component (e.g. `["blocktype",
    /// "list(instr)"]` for `instr`'s `BLOCK`).
    pub children: Vec<String>,
}

impl CaseShape {
    /// The payload tuple arity (`0` for a nullary case).
    pub fn arity(&self) -> usize {
        self.children.len()
    }
}

/// One catalogued case: its ordinal among its type's cases (over *all*
/// instances, in instance order — matching [`variant_of`]'s constructor
/// indices) and its payload shape.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CaseInfo {
    pub index: usize,
    pub shape: CaseShape,
}

/// The **total reified case catalogue**: every case of every variant `Typ`
/// definition in a spec — parametric, multi-instance, recursive and
/// mutually-recursive alike — keyed by `(type name, case key)`, plus the
/// ordered tag list per type and the bare-key → owning-types index (bare case
/// keys are ambiguous 16 ways in the bundled WASM 3.0 spec; the pair key is
/// what disambiguates them).
///
/// Construction is pure AST processing and **never fails**. A case key that
/// appears *twice within one type* (e.g. `binop_`'s `ADD`, once per instance)
/// is recorded in the tag list but its `(type, key)` lookup yields `None` —
/// the constructor is genuinely ambiguous there, and a consumer gating on the
/// catalogue must refuse rather than guess.
#[derive(Debug, Clone, Default)]
pub struct CaseCatalogue {
    /// `(type name, case key)` → the case, or `None` if the key occurs more
    /// than once in that type (ambiguous — refuse).
    cases: BTreeMap<(String, String), Option<CaseInfo>>,
    /// Type name → its case keys, ordered (all instances, instance order;
    /// duplicates kept).
    by_type: BTreeMap<String, Vec<String>>,
    /// Bare case key → the variant type names defining it.
    owners: BTreeMap<String, BTreeSet<String>>,
}

impl CaseCatalogue {
    /// Catalogue every variant `Typ` in `defs` (descending into `rec` groups).
    /// Total: never fails, skips nothing.
    pub fn new(defs: &[SpecTecDef]) -> Self {
        let mut cat = CaseCatalogue::default();
        fn go(d: &SpecTecDef, cat: &mut CaseCatalogue) {
            match d {
                SpecTecDef::Typ { x, insts, .. } => cat.add_typ(x, insts),
                SpecTecDef::Rec { ds } => ds.iter().for_each(|d| go(d, cat)),
                _ => {}
            }
        }
        defs.iter().for_each(|d| go(d, &mut cat));
        cat
    }

    fn add_typ(&mut self, name: &str, insts: &[SpecTecInst]) {
        let mut index = 0usize;
        for SpecTecInst::Inst { dt, .. } in insts {
            let SpecTecDefTyp::Variant { tcs } = dt else {
                continue;
            };
            for SpecTecTypCase::Field { op, t, .. } in tcs {
                let key = super::encode::mixop_key(op);
                let info = CaseInfo {
                    index,
                    shape: payload_shape(t),
                };
                self.cases
                    .entry((name.to_owned(), key.clone()))
                    .and_modify(|e| *e = None) // second occurrence → ambiguous
                    .or_insert(Some(info));
                self.by_type
                    .entry(name.to_owned())
                    .or_default()
                    .push(key.clone());
                self.owners.entry(key).or_default().insert(name.to_owned());
                index += 1;
            }
        }
    }

    /// Look a case up by `(type name, case key)`. `None` if the type/case is
    /// unknown **or** the key is ambiguous within the type.
    pub fn case(&self, ty: &str, key: &str) -> Option<&CaseInfo> {
        self.cases.get(&(ty.to_owned(), key.to_owned()))?.as_ref()
    }

    /// The ordered case keys of a variant type (`None` if `ty` has no cases).
    pub fn cases_of(&self, ty: &str) -> Option<&[String]> {
        self.by_type.get(ty).map(Vec::as_slice)
    }

    /// The variant types defining a bare case key.
    pub fn owners_of(&self, key: &str) -> impl Iterator<Item = &str> {
        self.owners
            .get(key)
            .into_iter()
            .flatten()
            .map(String::as_str)
    }

    /// The unique variant type owning a bare case key, if unambiguous.
    pub fn unique_owner(&self, key: &str) -> Option<&str> {
        let owners = self.owners.get(key)?;
        match owners.len() {
            1 => owners.first().map(String::as_str),
            _ => None,
        }
    }

    /// Whether `ty` is a catalogued variant type.
    pub fn is_variant(&self, ty: &str) -> bool {
        self.by_type.contains_key(ty)
    }

    /// The number of catalogued variant types.
    pub fn n_variants(&self) -> usize {
        self.by_type.len()
    }
}

/// The shape of a case payload: its tuple components, symbolically.
fn payload_shape(t: &SpecTecTyp) -> CaseShape {
    let children = match t {
        SpecTecTyp::Tup { ets } => ets
            .iter()
            .map(|SpecTecTypBind::Bind { typ, .. }| sym_typ(typ))
            .collect(),
        other => vec![sym_typ(other)],
    };
    CaseShape { children }
}

/// A compact, symbolic (non-HOL) rendering of a SpecTec type, for payload
/// shapes: named types keep their (applied) names, iteration becomes
/// `list(…)`/`opt(…)`, tuples parenthesize.
fn sym_typ(t: &SpecTecTyp) -> String {
    match t {
        SpecTecTyp::Bool => "bool".into(),
        SpecTecTyp::Num(SpecTecNumTyp::Nat) => "nat".into(),
        SpecTecTyp::Num(SpecTecNumTyp::Int) => "int".into(),
        SpecTecTyp::Num(SpecTecNumTyp::Rat) => "rat".into(),
        SpecTecTyp::Num(SpecTecNumTyp::Real) => "real".into(),
        SpecTecTyp::Text => "text".into(),
        SpecTecTyp::Var { x, as1 } => {
            if as1.is_empty() {
                x.clone()
            } else {
                let args: Vec<String> = as1.iter().map(sym_arg).collect();
                format!("{x}({})", args.join(", "))
            }
        }
        SpecTecTyp::Tup { ets } => {
            let parts: Vec<String> = ets
                .iter()
                .map(|SpecTecTypBind::Bind { typ, .. }| sym_typ(typ))
                .collect();
            format!("({})", parts.join(", "))
        }
        SpecTecTyp::Iter { t1, it } => {
            let mut s = sym_typ(t1);
            for step in it {
                s = match step {
                    SpecTecIter::Opt => format!("opt({s})"),
                    SpecTecIter::List | SpecTecIter::List1 | SpecTecIter::ListN { .. } => {
                        format!("list({s})")
                    }
                };
            }
            s
        }
    }
}

/// A compact symbolic rendering of a type-application argument.
fn sym_arg(a: &SpecTecArg) -> String {
    match a {
        SpecTecArg::Exp { e } => sym_exp(e),
        SpecTecArg::Typ { t } => sym_typ(t),
        SpecTecArg::Def { x } => x.clone(),
        SpecTecArg::Gram { .. } => "_".into(),
    }
}

fn sym_exp(e: &SpecTecExp) -> String {
    use SpecTecExp as E;
    match e {
        E::Var { id } => id.clone(),
        E::Num { n } => format!("{n:?}"),
        E::Bool { b } => b.to_string(),
        E::Case { op, e1 } => format!("{}{}", super::encode::mixop_key(op), sym_exp(e1)),
        E::Tup { es } => {
            let parts: Vec<String> = es.iter().map(sym_exp).collect();
            format!("({})", parts.join(", "))
        }
        E::Sub { e1, .. } => sym_exp(e1),
        _ => "_".into(),
    }
}

fn reject_parametric_field(qs: &[SpecTecParam]) -> Result<()> {
    if qs.is_empty() {
        Ok(())
    } else {
        Err(syntax_err("parametric field/case not modelled yet"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_spectec::ast::{MixOp, SpecTecInst, SpecTecParam};

    fn alias(name: &str, typ: SpecTecTyp) -> SpecTecDef {
        SpecTecDef::Typ {
            x: name.into(),
            ps: vec![],
            insts: vec![SpecTecInst::Inst {
                ps: vec![],
                as_: vec![],
                dt: SpecTecDefTyp::Alias { typ },
            }],
        }
    }
    fn num(nt: SpecTecNumTyp) -> SpecTecTyp {
        SpecTecTyp::Num(nt)
    }
    fn var(x: &str) -> SpecTecTyp {
        SpecTecTyp::Var {
            x: x.into(),
            as1: vec![],
        }
    }

    #[test]
    fn primitives_render() {
        let ctx = TypeCtx::new(&[]);
        assert_eq!(resolve_typ(&SpecTecTyp::Bool, &ctx).unwrap(), Type::bool());
        assert_eq!(
            resolve_typ(&num(SpecTecNumTyp::Nat), &ctx).unwrap(),
            Type::nat()
        );
        assert_eq!(
            resolve_typ(&num(SpecTecNumTyp::Int), &ctx).unwrap(),
            Type::int()
        );
    }

    #[test]
    fn list_and_option_render() {
        let ctx = TypeCtx::new(&[]);
        let bytes = SpecTecTyp::Iter {
            t1: Box::new(num(SpecTecNumTyp::Nat)),
            it: vec![SpecTecIter::List],
        };
        assert_eq!(resolve_typ(&bytes, &ctx).unwrap(), list::list(Type::nat()));
        let opt = SpecTecTyp::Iter {
            t1: Box::new(SpecTecTyp::Bool),
            it: vec![SpecTecIter::Opt],
        };
        assert_eq!(
            resolve_typ(&opt, &ctx).unwrap(),
            option::option(Type::bool())
        );
    }

    #[test]
    fn alias_chains_resolve() {
        // byte = nat ; word = (byte, byte)
        let defs = vec![
            alias("byte", num(SpecTecNumTyp::Nat)),
            alias(
                "word",
                SpecTecTyp::Tup {
                    ets: vec![
                        SpecTecTypBind::Bind {
                            id: "a".into(),
                            typ: var("byte"),
                        },
                        SpecTecTypBind::Bind {
                            id: "b".into(),
                            typ: var("byte"),
                        },
                    ],
                },
            ),
        ];
        let ctx = TypeCtx::new(&defs);
        assert_eq!(resolve_def(&defs[0], &ctx).unwrap(), Type::nat());
        assert_eq!(
            resolve_def(&defs[1], &ctx).unwrap(),
            prod::prod(Type::nat(), Type::nat())
        );
    }

    #[test]
    fn cyclic_alias_errors_not_loops() {
        let defs = vec![alias("a", var("b")), alias("b", var("a"))];
        let ctx = TypeCtx::new(&defs);
        assert!(resolve_def(&defs[0], &ctx).is_err());
    }

    fn variant_case(name: &str, t: SpecTecTyp) -> SpecTecTypCase {
        SpecTecTypCase::Field {
            op: MixOp::new(vec![name.into()]),
            t,
            qs: vec![],
            prs: vec![],
        }
    }
    fn variant_def(name: &str, cases: Vec<SpecTecTypCase>) -> SpecTecDef {
        SpecTecDef::Typ {
            x: name.into(),
            ps: vec![],
            insts: vec![SpecTecInst::Inst {
                ps: vec![],
                as_: vec![],
                dt: SpecTecDefTyp::Variant { tcs: cases },
            }],
        }
    }
    fn unit_ty() -> SpecTecTyp {
        SpecTecTyp::Tup { ets: vec![] }
    }

    /// A non-recursive variant renders to a coproduct-of-payloads.
    #[test]
    fn nonrecursive_variant_renders_to_coprod() {
        use crate::init::coprod::coprod;
        // numtype = I32 | I64 | F32  (three nullary cases)
        let def = variant_def(
            "numtype",
            vec![
                variant_case("I32", unit_ty()),
                variant_case("I64", unit_ty()),
                variant_case("F32", unit_ty()),
            ],
        );
        let ctx = TypeCtx::new(std::slice::from_ref(&def));
        assert_eq!(
            resolve_def(&def, &ctx).unwrap(),
            coprod(Type::unit(), coprod(Type::unit(), Type::unit()))
        );
    }

    /// A recursive variant renders to the impredicative Church type `Φ⟨'r⟩`
    /// (self-references → the result var), not looped on.
    #[test]
    fn recursive_variant_renders_to_church_type() {
        // tree = LEAF | NODE tree   (NODE's payload references `tree`)
        let def = variant_def(
            "tree",
            vec![
                variant_case("LEAF", unit_ty()),
                variant_case("NODE", var("tree")),
            ],
        );
        let ctx = TypeCtx::new(std::slice::from_ref(&def));
        let r = self_ty_var();
        // Φ = (unit → r) → (r → r) → r
        let expected = Type::fun(
            Type::fun(Type::unit(), r.clone()),
            Type::fun(Type::fun(r.clone(), r.clone()), r.clone()),
        );
        assert_eq!(resolve_def(&def, &ctx).unwrap(), expected);
    }

    /// A recursive occurrence *under a list* (`instr*`-style) renders too: the
    /// self reference becomes `list r`.
    #[test]
    fn recursion_under_list_renders() {
        let def = variant_def(
            "seq",
            vec![
                variant_case("NIL", unit_ty()),
                variant_case(
                    "MORE",
                    SpecTecTyp::Iter {
                        t1: Box::new(var("seq")),
                        it: vec![SpecTecIter::List],
                    },
                ),
            ],
        );
        let ctx = TypeCtx::new(std::slice::from_ref(&def));
        let r = self_ty_var();
        // Φ = (unit → r) → (list r → r) → r
        let expected = Type::fun(
            Type::fun(Type::unit(), r.clone()),
            Type::fun(Type::fun(list::list(r.clone()), r.clone()), r.clone()),
        );
        assert_eq!(resolve_def(&def, &ctx).unwrap(), expected);
    }

    /// A parametric type applied to a type argument instantiates its body:
    /// `myvec(bool) = bool*` → `list bool`.
    #[test]
    fn parametric_type_application_instantiates() {
        // myvec(X) = X*
        let myvec = SpecTecDef::Typ {
            x: "myvec".into(),
            ps: vec![SpecTecParam::Typ { x: "X".into() }],
            insts: vec![SpecTecInst::Inst {
                ps: vec![],
                as_: vec![],
                dt: SpecTecDefTyp::Alias {
                    typ: SpecTecTyp::Iter {
                        t1: Box::new(var("X")),
                        it: vec![SpecTecIter::List],
                    },
                },
            }],
        };
        // pairs = myvec(bool)
        let pairs = alias(
            "pairs",
            SpecTecTyp::Var {
                x: "myvec".into(),
                as1: vec![SpecTecArg::Typ {
                    t: SpecTecTyp::Bool,
                }],
            },
        );
        let defs = vec![myvec, pairs];
        let ctx = TypeCtx::new(&defs);
        assert_eq!(
            resolve_def(&defs[1], &ctx).unwrap(),
            list::list(Type::bool())
        );
    }

    /// A parametric type used *without* arguments is an error (needs instantiation).
    #[test]
    fn bare_parametric_type_errors() {
        let parametric = SpecTecDef::Typ {
            x: "vec".into(),
            ps: vec![SpecTecParam::Typ { x: "X".into() }],
            insts: vec![],
        };
        let ctx = TypeCtx::new(&[]);
        assert!(resolve_def(&parametric, &ctx).is_err());
    }

    // ==== multi-instance dispatch ====

    /// `Inn = I32 | I64`, `Fnn = F32 | F64`, `numtype = I32 | I64 | F32 | F64`.
    fn subtype_defs() -> Vec<SpecTecDef> {
        vec![
            variant_def(
                "Inn",
                vec![
                    variant_case("I32", unit_ty()),
                    variant_case("I64", unit_ty()),
                ],
            ),
            variant_def(
                "Fnn",
                vec![
                    variant_case("F32", unit_ty()),
                    variant_case("F64", unit_ty()),
                ],
            ),
            variant_def(
                "numtype",
                vec![
                    variant_case("I32", unit_ty()),
                    variant_case("I64", unit_ty()),
                    variant_case("F32", unit_ty()),
                    variant_case("F64", unit_ty()),
                ],
            ),
        ]
    }

    /// An instance with the `x <: sub_ty` upcast pattern (the `num_(Inn)` shape).
    fn sub_pattern_inst(
        pvar: &str,
        sub_ty: &str,
        super_ty: &str,
        dt: SpecTecDefTyp,
    ) -> SpecTecInst {
        SpecTecInst::Inst {
            ps: vec![SpecTecParam::Exp {
                x: pvar.into(),
                t: var(sub_ty),
            }],
            as_: vec![SpecTecArg::Exp {
                e: SpecTecExp::Sub {
                    t1: var(sub_ty),
                    t2: var(super_ty),
                    e1: Box::new(SpecTecExp::Var { id: pvar.into() }),
                },
            }],
            dt,
        }
    }

    /// `fam(Inn) = nat ; fam(Fnn) = bool` — an alias-bodied family (`num_` shape).
    fn alias_family() -> Vec<SpecTecDef> {
        let mut defs = subtype_defs();
        defs.push(SpecTecDef::Typ {
            x: "fam".into(),
            ps: vec![SpecTecParam::Exp {
                x: "numtype".into(),
                t: var("numtype"),
            }],
            insts: vec![
                sub_pattern_inst(
                    "Inn",
                    "Inn",
                    "numtype",
                    SpecTecDefTyp::Alias {
                        typ: num(SpecTecNumTyp::Nat),
                    },
                ),
                sub_pattern_inst(
                    "Fnn",
                    "Fnn",
                    "numtype",
                    SpecTecDefTyp::Alias {
                        typ: SpecTecTyp::Bool,
                    },
                ),
            ],
        });
        defs
    }

    fn apply_exp(name: &str, e: SpecTecExp) -> SpecTecTyp {
        SpecTecTyp::Var {
            x: name.into(),
            as1: vec![SpecTecArg::Exp { e }],
        }
    }
    fn case_exp(name: &str) -> SpecTecExp {
        SpecTecExp::Case {
            op: MixOp::new(vec![name.into()]),
            e1: Box::new(SpecTecExp::Tup { es: vec![] }),
        }
    }
    fn var_exp(id: &str) -> SpecTecExp {
        SpecTecExp::Var { id: id.into() }
    }

    /// A concrete `Case` argument selects the instance whose subtype owns the
    /// tag: `fam(I32)` = the `Inn` instance = `nat`, `fam(F64)` = `bool`.
    #[test]
    fn dispatch_selects_by_case_tag() {
        let defs = alias_family();
        let ctx = TypeCtx::new(&defs);
        let t = resolve_typ(&apply_exp("fam", case_exp("I32")), &ctx).unwrap();
        assert_eq!(t, Type::nat());
        let t = resolve_typ(&apply_exp("fam", case_exp("F64")), &ctx).unwrap();
        assert_eq!(t, Type::bool());
    }

    /// A metavariable named after the subtype selects its instance (SpecTec
    /// names metavariables after their type: `Inn_1 : Inn`).
    #[test]
    fn dispatch_selects_by_metavariable_type() {
        let defs = alias_family();
        let ctx = TypeCtx::new(&defs);
        assert_eq!(
            resolve_typ(&apply_exp("fam", var_exp("Inn")), &ctx).unwrap(),
            Type::nat()
        );
        assert_eq!(
            resolve_typ(&apply_exp("fam", var_exp("Fnn_2")), &ctx).unwrap(),
            Type::bool()
        );
    }

    /// A supertype metavariable (`fam(numtype)`) leaves both alias-bodied
    /// instances open; they render to different HOL types → a typed error, and
    /// an unknown tag (`fam(X9)`) positively matches no instance → a typed error.
    #[test]
    fn dispatch_ambiguous_alias_and_no_match_error() {
        let defs = alias_family();
        let ctx = TypeCtx::new(&defs);
        assert!(resolve_typ(&apply_exp("fam", var_exp("numtype")), &ctx).is_err());
        assert!(resolve_typ(&apply_exp("fam", case_exp("X9")), &ctx).is_err());
    }

    /// A variant-bodied family under an indeterminate argument joins into the
    /// union variant (cases concatenated in instance order) — the `unop_` shape.
    #[test]
    fn dispatch_joins_variant_instances() {
        use crate::init::coprod::coprod;
        let mut defs = subtype_defs();
        defs.push(SpecTecDef::Typ {
            x: "op_".into(),
            ps: vec![SpecTecParam::Exp {
                x: "numtype".into(),
                t: var("numtype"),
            }],
            insts: vec![
                sub_pattern_inst(
                    "Inn",
                    "Inn",
                    "numtype",
                    SpecTecDefTyp::Variant {
                        tcs: vec![variant_case("CLZ", unit_ty())],
                    },
                ),
                sub_pattern_inst(
                    "Fnn",
                    "Fnn",
                    "numtype",
                    SpecTecDefTyp::Variant {
                        tcs: vec![
                            variant_case("ABS", unit_ty()),
                            variant_case("NEG", num(SpecTecNumTyp::Nat)),
                        ],
                    },
                ),
            ],
        });
        let ctx = TypeCtx::new(&defs);
        // Indeterminate → CLZ | ABS | NEG = unit ⊕ (unit ⊕ nat).
        assert_eq!(
            resolve_typ(&apply_exp("op_", var_exp("numtype")), &ctx).unwrap(),
            coprod(Type::unit(), coprod(Type::unit(), Type::nat()))
        );
        // Determinate → just the matching instance.
        assert_eq!(
            resolve_typ(&apply_exp("op_", var_exp("Inn_1")), &ctx).unwrap(),
            Type::unit()
        );
        // The union variant is also what `variant_of` reifies for the family.
        let fam = defs.last().unwrap();
        let v = variant_of(fam, &ctx).unwrap();
        let names: Vec<&str> = v.ctors.iter().map(|c| c.name.as_str()).collect();
        assert_eq!(names, ["CLZ", "ABS", "NEG"]);
    }

    // ==== the total reified case catalogue ====

    /// The catalogue is total: recursive, mutually-recursive and parametric
    /// variants are all catalogued (none of which fully render to HOL).
    #[test]
    fn catalogue_is_total_over_unrenderable_variants() {
        let defs = vec![
            // mutually recursive pair — resolve_def cycles on both.
            variant_def("even", vec![variant_case("E", var("odd"))]),
            variant_def("odd", vec![variant_case("O", var("even"))]),
            // type-parametric variant — variant_of refuses it.
            SpecTecDef::Typ {
                x: "box".into(),
                ps: vec![SpecTecParam::Typ { x: "X".into() }],
                insts: vec![SpecTecInst::Inst {
                    ps: vec![],
                    as_: vec![],
                    dt: SpecTecDefTyp::Variant {
                        tcs: vec![variant_case("BOX", var("X"))],
                    },
                }],
            },
        ];
        let cat = CaseCatalogue::new(&defs);
        assert_eq!(cat.n_variants(), 3);
        assert!(cat.is_variant("even") && cat.is_variant("box"));
        let e = cat.case("even", "E").unwrap();
        assert_eq!((e.index, e.shape.arity()), (0, 1));
        assert_eq!(e.shape.children, ["odd"]);
        assert_eq!(cat.case("box", "BOX").unwrap().shape.children, ["X"]);
    }

    /// `(type, case)` keys disambiguate shared mnemonics; bare-key owners are
    /// still discoverable; a duplicate key *within* one type refuses.
    #[test]
    fn catalogue_disambiguates_and_refuses_duplicates() {
        let mut defs = subtype_defs();
        // A family whose two instances both define `ADD` (the `binop_` shape).
        defs.push(SpecTecDef::Typ {
            x: "bop_".into(),
            ps: vec![SpecTecParam::Exp {
                x: "numtype".into(),
                t: var("numtype"),
            }],
            insts: vec![
                sub_pattern_inst(
                    "Inn",
                    "Inn",
                    "numtype",
                    SpecTecDefTyp::Variant {
                        tcs: vec![variant_case("ADD", unit_ty())],
                    },
                ),
                sub_pattern_inst(
                    "Fnn",
                    "Fnn",
                    "numtype",
                    SpecTecDefTyp::Variant {
                        tcs: vec![variant_case("ADD", unit_ty())],
                    },
                ),
            ],
        });
        let cat = CaseCatalogue::new(&defs);
        // `I32` is defined by Inn *and* numtype: bare key ambiguous, pair key not.
        assert_eq!(cat.unique_owner("I32"), None);
        assert_eq!(cat.owners_of("I32").count(), 2);
        assert_eq!(cat.case("Inn", "I32").unwrap().index, 0);
        assert_eq!(cat.case("numtype", "F32").unwrap().index, 2);
        // `ADD` twice within `bop_` → the pair lookup refuses (None), but the
        // ordered tag list keeps both occurrences.
        assert_eq!(cat.case("bop_", "ADD"), None);
        assert_eq!(cat.cases_of("bop_").unwrap(), ["ADD", "ADD"]);
        // Unknown case/type lookups are None, not errors.
        assert_eq!(cat.case("Inn", "NOPE"), None);
        assert_eq!(cat.case("nosuch", "I32"), None);
    }
}
