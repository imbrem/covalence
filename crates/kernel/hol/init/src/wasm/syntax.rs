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
//! (self-references → a result type variable). Mutually-recursive components
//! use the corresponding simultaneous Church signature: one distinct result
//! carrier per generative variant and all component handlers in stable order;
//! structural aliases are normalized first rather than turned into fictitious
//! constructors. **Parametric** types `T(A…)` instantiate by resolving `T`'s
//! body with its type parameters bound (value/`exp` parameters don't affect the
//! HOL type). A `Scope` threads these recursive carriers and type bindings.
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
//! - **parametric cases** (non-empty `qs`): `fN`/`fNmag`/`ishape` (+ inherited
//!   `f32`/`f64`) — the float representations;
//! - `text`/`rat`/`real` and non-numeric value-indexed subtleties.
//!
//! Faithfulness caveat (not a rendering failure): this carrier-only module does
//! not interpret case/field **refinement premises** (`prs`, 56 across 29 spec
//! types). Consumers needing semantic membership must use
//! [`super::sort::RefinementAwareTypeResolver`], which currently lowers the
//! exact singleton-value fragment (`bit`, `byte`, `char`, and `dim`) and marks
//! every other refined closure unresolved. See the generated open-work index.

use std::collections::{BTreeMap, BTreeSet};

use covalence_core::{Error, Result, Type};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::derived::DerivedRules;
use covalence_spectec::ast::{
    SpecTecArg, SpecTecDef, SpecTecDefTyp, SpecTecExp, SpecTecInst, SpecTecIter, SpecTecNumTyp,
    SpecTecParam, SpecTecTyp, SpecTecTypBind, SpecTecTypCase, SpecTecTypField,
};

use super::type_family::{TypeFamilies, TypeFamilySource};
use crate::init::eq::beta_nf;
use crate::init::ext::TermExt;
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
    /// Non-trivial mutually-recursive components, indexed by every member.
    /// Components are sorted by [`TypeFamilies`] and therefore give the
    /// simultaneous Church renderer a source-independent, stable handler order.
    mutual_by_name: BTreeMap<&'a str, Vec<&'a str>>,
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
        let families = TypeFamilies::new(defs);
        let mut mutual_by_name = BTreeMap::new();
        for component in families
            .strongly_connected_components()
            .into_iter()
            .filter(|component| component.len() > 1)
        {
            for &member in &component {
                mutual_by_name.insert(member, component.clone());
            }
        }
        TypeCtx {
            by_name,
            mutual_by_name,
        }
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
    /// Result carriers and normalized structural aliases of a simultaneous
    /// Church encoding. Unlike the single recursive `cov$self`, one distinct
    /// variable per generative SCC member preserves every sibling edge; aliases
    /// retain their exact structural definitions.
    mutual: BTreeMap<String, Type>,
    /// All members of the component. A member absent from `mutual` is a
    /// structural synonym still being normalized, not a name to recursively
    /// re-enter through `resolve_named`.
    mutual_members: BTreeSet<String>,
}

impl Scope {
    /// Same parameter bindings, resolving variant `name`'s payloads (self-mapping).
    fn under_variant(&self, name: &str) -> Scope {
        Scope {
            self_name: Some(name.to_owned()),
            tenv: self.tenv.clone(),
            mutual: self.mutual.clone(),
            mutual_members: self.mutual_members.clone(),
        }
    }
    /// Same parameter bindings, no self-mapping (alias/struct bodies).
    fn no_self(&self) -> Scope {
        Scope {
            self_name: None,
            tenv: self.tenv.clone(),
            mutual: self.mutual.clone(),
            mutual_members: self.mutual_members.clone(),
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
        if let Some(ty) = scope.mutual.get(x) {
            return Ok(ty.clone());
        }
        if scope.mutual_members.contains(x) {
            return Err(syntax_err(format!(
                "mutual structural synonym `{x}` is not normalized yet"
            )));
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
        mutual: scope.mutual.clone(),
        mutual_members: scope.mutual_members.clone(),
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
    if let Some(component) = ctx.mutual_by_name.get(name) {
        return resolve_mutual_named(name, component, ctx);
    }
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

/// Simultaneous Church signature for one member of a mutually-recursive SCC.
///
/// For generative equations `Tᵢ = Fᵢ(T₀, …, Tₙ)`, assign a distinct result
/// carrier `rᵢ` to every variant member and render
///
/// `Tᵢ := handlers(F₀(r) → r₀, …, Fₙ(r) → rₙ) → rᵢ`.
///
/// A variant contributes one handler per constructor. Alias and struct members
/// are normalized to their exact structural bodies first: they do **not**
/// acquire a fictitious constructor merely because Tarjan includes them in the
/// same dependency SCC. This is the standard simultaneous generalisation of
/// the existing unary [`ChurchBackend`] type. The signature below supplies
/// handler-injection constructors and their checked β laws, while keeping
/// source-datatype freeness as explicit obligations. It is exact about source
/// constructor order, payload shape and every recursive edge. Unsupported
/// binders/refinements are refused rather than erased.
/// One handler-injection constructor in a simultaneous Church signature.
#[derive(Debug, Clone)]
pub struct MutualChurchConstructor {
    owner: String,
    name: String,
    payload: Type,
    term: covalence_core::Term,
    handler_index: usize,
}

impl MutualChurchConstructor {
    pub fn owner(&self) -> &str {
        &self.owner
    }
    pub fn name(&self) -> &str {
        &self.name
    }
    pub fn payload_type(&self) -> &Type {
        &self.payload
    }
    pub fn term(&self) -> &covalence_core::Term {
        &self.term
    }
}

/// A freeness law that an exact mutual-datatype backend must discharge.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MutualFreenessObligation {
    Injective { constructor: usize },
    Distinct { left: usize, right: usize },
}

/// One edge in the universal path domain used to carve a closed mutual
/// datatype.  Constructor and recursive-slot indices are source-order stable.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct MutualPathStep {
    pub constructor: usize,
    pub recursive_slot: usize,
    pub target_member: usize,
}

/// Exact term-level signature of one mutually-recursive SCC.
///
/// Constructors are handler injections over the already-folded payload
/// carriers. Their computation laws are pure β and kernel checked. This does
/// not claim source-datatype freeness: every injectivity/distinctness law is
/// retained explicitly in [`Self::freeness_obligations`].
// TODO(cov:kernel.hol.init.src.wasm.church-types-are-polymorphic-term-free, severe): Seal simultaneous Church signatures as closed recursive carriers; open rank-1 signatures now have constructors, β laws, and checked observations only.
// TODO(cov:kernel.hol.init.src.wasm.constructor-freeness-lemmas-not-threaded, severe): On a closed carrier, discharge 41 injectivity/183 distinctness laws (10 recursive payloads hit rank-1 reconstruction) and thread them into denotation.
#[derive(Debug, Clone)]
pub struct MutualChurchSignature {
    members: Vec<String>,
    carriers: BTreeMap<String, Type>,
    handler_types: Vec<Type>,
    constructors: Vec<MutualChurchConstructor>,
}

impl MutualChurchSignature {
    /// Finite path alphabet for a carved realization of this signature.
    ///
    /// A slot is one occurrence of a mutual result carrier in a constructor
    /// payload. Occurrences are enumerated left-to-right through the HOL type
    /// tree; no occurrence is collapsed merely because two have equal types.
    pub fn path_alphabet(&self) -> Vec<MutualPathStep> {
        fn occurrences(ty: &Type, members: &[String], out: &mut Vec<usize>) {
            use covalence_core::TypeKind;
            match ty.kind() {
                TypeKind::TFree(name) => {
                    if let Some(member) = members
                        .iter()
                        .position(|member| name.as_str() == format!("cov$mutual${member}"))
                    {
                        out.push(member);
                    }
                }
                TypeKind::Fun(domain, codomain) => {
                    occurrences(domain, members, out);
                    occurrences(codomain, members, out);
                }
                TypeKind::Tycon(_, arguments) | TypeKind::Spec(_, arguments) => {
                    for argument in arguments.iter() {
                        occurrences(argument, members, out);
                    }
                }
                TypeKind::FreshTyCon(leaf) => {
                    for argument in leaf.args().iter() {
                        occurrences(argument, members, out);
                    }
                }
                TypeKind::Nat | TypeKind::Bool => {}
            }
        }

        let mut alphabet = Vec::new();
        for (constructor, ctor) in self.constructors.iter().enumerate() {
            let mut targets = Vec::new();
            occurrences(&ctor.payload, &self.members, &mut targets);
            alphabet.extend(targets.into_iter().enumerate().map(
                |(recursive_slot, target_member)| MutualPathStep {
                    constructor,
                    recursive_slot,
                    target_member,
                },
            ));
        }
        alphabet
    }

    /// Common constructor-label carrier for the universal path model.
    ///
    /// It retains every complete constructor payload in source order. The
    /// later carved layer may replace recursive sub-values by child paths, but
    /// this neutral descriptor never erases non-recursive payload information.
    pub fn common_label_carrier(&self) -> Result<Type> {
        fn fold(payloads: &[Type]) -> Result<Type> {
            match payloads {
                [] => Err(syntax_err("mutual signature has no constructor label")),
                [payload] => Ok(payload.clone()),
                [head, tail @ ..] => Ok(crate::init::coprod::coprod(head.clone(), fold(tail)?)),
            }
        }
        fold(
            &self
                .constructors
                .iter()
                .map(|constructor| constructor.payload.clone())
                .collect::<Vec<_>>(),
        )
    }

    /// Constructor payload with every recursive child replaced by `unit`.
    ///
    /// Functor shape is retained by type substitution: for example
    /// `list fieldtype` becomes `list unit`, preserving the runtime list
    /// length needed to validate child-index path steps.
    pub fn carved_payload_skeleton(&self, constructor: usize) -> Result<Type> {
        let constructor = self
            .constructors
            .get(constructor)
            .ok_or_else(|| syntax_err("mutual constructor index out of range"))?;
        Ok(self
            .members
            .iter()
            .fold(constructor.payload.clone(), |payload, member| {
                covalence_core::subst::subst_tfree_in_type(
                    &payload,
                    &format!("cov$mutual${member}"),
                    &Type::unit(),
                )
            }))
    }

    /// Closed common label carrier for the carved path model.
    pub fn carved_label_carrier(&self) -> Result<Type> {
        fn fold(payloads: &[Type]) -> Result<Type> {
            match payloads {
                [] => Err(syntax_err("mutual signature has no constructor label")),
                [payload] => Ok(payload.clone()),
                [head, tail @ ..] => Ok(crate::init::coprod::coprod(head.clone(), fold(tail)?)),
            }
        }
        fold(
            &(0..self.constructors.len())
                .map(|constructor| self.carved_payload_skeleton(constructor))
                .collect::<Result<Vec<_>>>()?,
        )
    }

    /// Runtime path edge:
    /// `(constructor-index, recursive-slot-index, traversal-indices)`.
    ///
    /// The final list is empty for direct/product/option children and contains
    /// one or more natural indices when the recursive occurrence lies beneath
    /// list functors. This is unbounded, unlike the finite type-occurrence
    /// alphabet returned by [`Self::path_alphabet`].
    pub fn runtime_path_step_carrier(&self) -> Type {
        covalence_hol_eval::defs::prod(
            Type::nat(),
            covalence_hol_eval::defs::prod(Type::nat(), crate::init::list::list(Type::nat())),
        )
    }

    pub fn carved_path_carrier(&self) -> Type {
        crate::init::list::list(self.runtime_path_step_carrier())
    }

    /// Universal path-table domain `U := path → label`.
    pub fn carved_universal_domain_carrier(&self) -> Result<Type> {
        Ok(Type::fun(
            self.carved_path_carrier(),
            self.carved_label_carrier()?,
        ))
    }

    /// Constructor payload at the universal-domain approximation `F(U)`.
    ///
    /// Every mutual member is replaced by the same closed path-table domain;
    /// all surrounding products, lists, options, and external fields remain
    /// unchanged. This is the typed input to a U-level constructor. Its root
    /// label is obtained by functor-mapping recursive children to `unit`, and
    /// its non-root equations route to the selected child table.
    pub fn carved_universal_payload(&self, constructor: usize) -> Result<Type> {
        let constructor = self
            .constructors
            .get(constructor)
            .ok_or_else(|| syntax_err("mutual constructor index out of range"))?;
        let universal = self.carved_universal_domain_carrier()?;
        Ok(self
            .members
            .iter()
            .fold(constructor.payload.clone(), |payload, member| {
                covalence_core::subst::subst_tfree_in_type(
                    &payload,
                    &format!("cov$mutual${member}"),
                    &universal,
                )
            }))
    }

    fn erase_universal_children(
        &self,
        source: &Type,
        input: &Type,
        output: &Type,
        value: covalence_core::Term,
    ) -> Result<covalence_core::Term> {
        use crate::init::ext::TermExt;
        use covalence_core::TypeKind;

        if let TypeKind::TFree(name) = source.kind()
            && self
                .members
                .iter()
                .any(|member| name.as_str() == format!("cov$mutual${member}"))
        {
            if input != &self.carved_universal_domain_carrier()? || output != &Type::unit() {
                return Err(syntax_err("recursive U child has wrong erased type"));
            }
            return Ok(covalence_hol_eval::defs::unit_nil());
        }
        if source.free_tvars().iter().all(|name| {
            !self
                .members
                .iter()
                .any(|member| name.as_str() == format!("cov$mutual${member}"))
        }) {
            if input != output || value.type_of()? != *input {
                return Err(syntax_err("external payload changed during root erasure"));
            }
            return Ok(value);
        }
        let (
            TypeKind::Spec(_, source_args),
            TypeKind::Spec(_, input_args),
            TypeKind::Spec(_, output_args),
        ) = (source.kind(), input.kind(), output.kind())
        else {
            return Err(syntax_err(
                "recursive root payload occurs outside product/list/option",
            ));
        };
        if source_args.len() == 2
            && input_args.len() == 2
            && output_args.len() == 2
            && source
                == &covalence_hol_eval::defs::prod(source_args[0].clone(), source_args[1].clone())
        {
            let left = covalence_hol_eval::defs::fst(input_args[0].clone(), input_args[1].clone())
                .apply(value.clone())?;
            let right = covalence_hol_eval::defs::snd(input_args[0].clone(), input_args[1].clone())
                .apply(value)?;
            return covalence_hol_eval::defs::pair(output_args[0].clone(), output_args[1].clone())
                .apply(self.erase_universal_children(
                    &source_args[0],
                    &input_args[0],
                    &output_args[0],
                    left,
                )?)?
                .apply(self.erase_universal_children(
                    &source_args[1],
                    &input_args[1],
                    &output_args[1],
                    right,
                )?);
        }
        if source_args.len() == 1
            && input_args.len() == 1
            && output_args.len() == 1
            && source == &crate::init::list::list(source_args[0].clone())
        {
            let item_name = "cov$mutual$erase$item";
            let item = covalence_core::Term::free(item_name, input_args[0].clone());
            let mapped = self.erase_universal_children(
                &source_args[0],
                &input_args[0],
                &output_args[0],
                item,
            )?;
            let mapper = covalence_core::Term::abs(
                input_args[0].clone(),
                covalence_core::subst::close(&mapped, item_name),
            );
            return covalence_hol_eval::defs::list_map(
                input_args[0].clone(),
                output_args[0].clone(),
            )
            .apply(mapper)?
            .apply(value);
        }
        if source_args.len() == 1
            && input_args.len() == 1
            && output_args.len() == 1
            && source == &crate::init::option::option(source_args[0].clone())
        {
            let item_name = "cov$mutual$erase$item";
            let item = covalence_core::Term::free(item_name, input_args[0].clone());
            let mapped = self.erase_universal_children(
                &source_args[0],
                &input_args[0],
                &output_args[0],
                item,
            )?;
            let some_mapper = covalence_core::Term::abs(
                input_args[0].clone(),
                covalence_core::subst::close(
                    &covalence_hol_eval::defs::some(output_args[0].clone()).apply(mapped)?,
                    item_name,
                ),
            );
            return covalence_hol_eval::defs::option_case(
                input_args[0].clone(),
                crate::init::option::option(output_args[0].clone()),
            )
            .apply(covalence_hol_eval::defs::none(output_args[0].clone()))?
            .apply(some_mapper)?
            .apply(value);
        }
        Err(syntax_err("unrecognised recursive root payload functor"))
    }

    /// Root label produced by U-level constructor `constructor`.
    pub fn carved_root_label(
        &self,
        constructor: usize,
        payload: covalence_core::Term,
    ) -> Result<covalence_core::Term> {
        fn fold(payloads: &[Type]) -> Result<Type> {
            match payloads {
                [] => Err(syntax_err("mutual signature has no constructor label")),
                [payload] => Ok(payload.clone()),
                [head, tail @ ..] => Ok(crate::init::coprod::coprod(head.clone(), fold(tail)?)),
            }
        }
        fn inject(
            payloads: &[Type],
            index: usize,
            value: covalence_core::Term,
        ) -> Result<covalence_core::Term> {
            match payloads {
                [] => Err(syntax_err("mutual constructor index out of range")),
                [_] if index == 0 => Ok(value),
                [head, tail @ ..] if index == 0 => {
                    crate::init::coprod::inl(head.clone(), fold(tail)?).apply(value)
                }
                [head, tail @ ..] => crate::init::coprod::inr(head.clone(), fold(tail)?)
                    .apply(inject(tail, index - 1, value)?),
            }
        }
        let source = &self
            .constructors
            .get(constructor)
            .ok_or_else(|| syntax_err("mutual constructor index out of range"))?
            .payload;
        let input = self.carved_universal_payload(constructor)?;
        if payload.type_of()? != input {
            return Err(syntax_err("wrong U-level constructor payload"));
        }
        let output = self.carved_payload_skeleton(constructor)?;
        let erased = self.erase_universal_children(source, &input, &output, payload)?;
        let payloads = (0..self.constructors.len())
            .map(|index| self.carved_payload_skeleton(index))
            .collect::<Result<Vec<_>>>()?;
        inject(&payloads, constructor, erased)
    }

    /// Exact partial child router for the first carved WASM constructors.
    ///
    /// The result is `option U`: out-of-range list indices remain `None`.
    /// Unsupported constructor/slot/index shapes are refused while the
    /// generic payload-functor router is completed.
    pub fn carved_route_child(
        &self,
        constructor: usize,
        payload: covalence_core::Term,
        recursive_slot: usize,
        list_index: Option<covalence_core::Term>,
    ) -> Result<covalence_core::Term> {
        use crate::init::ext::TermExt;

        let universal = self.carved_universal_domain_carrier()?;
        let expected = self.carved_universal_payload(constructor)?;
        if payload.type_of()? != expected {
            return Err(syntax_err("wrong U-level routing payload"));
        }
        if constructor == 1 {
            if recursive_slot != 0 {
                return Err(syntax_err("recursive slot index out of range"));
            }
            if list_index.is_some() {
                return Err(syntax_err(
                    "direct recursive slot does not take a list index",
                ));
            }
            if expected != universal {
                return Err(syntax_err("constructor 1 child is not direct U"));
            }
            return covalence_hol_eval::defs::some(universal).apply(payload);
        }
        if matches!(constructor, 3 | 18 | 26 | 32 | 39) {
            if recursive_slot != 0 {
                return Err(syntax_err("recursive slot index out of range"));
            }
            if list_index.is_some() {
                return Err(syntax_err(
                    "direct recursive slot does not take a list index",
                ));
            }
            let covalence_core::TypeKind::Spec(_, arguments) = expected.kind() else {
                return Err(syntax_err("constructor 3 payload is not a product"));
            };
            if arguments.len() != 2 {
                return Err(syntax_err("constructor 3 payload is not binary"));
            }
            let child = if matches!(constructor, 18 | 32) {
                covalence_hol_eval::defs::fst(arguments[0].clone(), arguments[1].clone())
                    .apply(payload)?
            } else {
                covalence_hol_eval::defs::snd(arguments[0].clone(), arguments[1].clone())
                    .apply(payload)?
            };
            if child.type_of()? != universal {
                return Err(syntax_err("constructor 3 child is not direct U"));
            }
            return covalence_hol_eval::defs::some(universal).apply(child);
        }
        if constructor == 30 && recursive_slot == 1 {
            if list_index.is_some() {
                return Err(syntax_err(
                    "direct recursive slot does not take a list index",
                ));
            }
            let covalence_core::TypeKind::Spec(_, outer) = expected.kind() else {
                return Err(syntax_err("constructor 30 payload is not a product"));
            };
            if outer.len() != 2 {
                return Err(syntax_err("constructor 30 outer payload is not binary"));
            }
            let tail =
                covalence_hol_eval::defs::snd(outer[0].clone(), outer[1].clone()).apply(payload)?;
            let covalence_core::TypeKind::Spec(_, inner) = outer[1].kind() else {
                return Err(syntax_err("constructor 30 tail is not a product"));
            };
            if inner.len() != 2 {
                return Err(syntax_err("constructor 30 tail is not binary"));
            }
            let child =
                covalence_hol_eval::defs::snd(inner[0].clone(), inner[1].clone()).apply(tail)?;
            if child.type_of()? != universal {
                return Err(syntax_err("constructor 30 direct child is not U"));
            }
            return covalence_hol_eval::defs::some(universal).apply(child);
        }
        let index =
            list_index.ok_or_else(|| syntax_err("list-valued recursive slot needs an index"))?;
        if index.type_of()? != Type::nat() {
            return Err(syntax_err("recursive list index is not nat"));
        }
        let children = match constructor {
            0 | 20 if recursive_slot == 0 => payload,
            2 if recursive_slot < 2 => {
                let covalence_core::TypeKind::Spec(_, arguments) = expected.kind() else {
                    return Err(syntax_err("two-slot payload is not a product"));
                };
                if arguments.len() != 2 {
                    return Err(syntax_err("two-slot payload is not a binary product"));
                }
                if recursive_slot == 0 {
                    covalence_hol_eval::defs::fst(arguments[0].clone(), arguments[1].clone())
                        .apply(payload)?
                } else {
                    covalence_hol_eval::defs::snd(arguments[0].clone(), arguments[1].clone())
                        .apply(payload)?
                }
            }
            30 if recursive_slot == 0 => {
                let covalence_core::TypeKind::Spec(_, outer) = expected.kind() else {
                    return Err(syntax_err("constructor 30 payload is not a product"));
                };
                if outer.len() != 2 {
                    return Err(syntax_err("constructor 30 outer payload is not binary"));
                }
                let tail = covalence_hol_eval::defs::snd(outer[0].clone(), outer[1].clone())
                    .apply(payload)?;
                let covalence_core::TypeKind::Spec(_, inner) = outer[1].kind() else {
                    return Err(syntax_err("constructor 30 tail is not a product"));
                };
                covalence_hol_eval::defs::fst(inner[0].clone(), inner[1].clone()).apply(tail)?
            }
            0 | 2 | 20 | 30 => {
                return Err(syntax_err("recursive slot index out of range"));
            }
            _ => {
                return Err(syntax_err(
                    "constructor is outside the exact routed fragment",
                ));
            }
        };
        covalence_hol_eval::defs::list_index(universal)
            .apply(index)?
            .apply(children)
    }

    /// Source-order recursive constructors whose payload router is complete.
    pub fn carved_routed_recursive_constructors(&self) -> &'static [usize] {
        &[0, 1, 2, 3, 18, 20, 26, 30, 32, 39]
    }

    /// First simultaneous Wf closure clause: every in-bounds child of
    /// constructor 0's `list U` payload routes to `Some child` and that child
    /// satisfies `child_wf`.
    ///
    /// `option.case false child_wf route` is deliberately false at `None`, so
    /// a missing route cannot discharge the implication's consequent.
    pub fn carved_ctor0_wf_clause(
        &self,
        child_wf: covalence_core::Term,
        payload: covalence_core::Term,
    ) -> Result<covalence_core::Term> {
        use crate::init::ext::TermExt;

        let universal = self.carved_universal_domain_carrier()?;
        if child_wf.type_of()? != Type::fun(universal.clone(), Type::bool()) {
            return Err(syntax_err("child Wf predicate has the wrong carrier"));
        }
        let payload_ty = crate::init::list::list(universal.clone());
        if payload.type_of()? != payload_ty {
            return Err(syntax_err("constructor 0 Wf payload is not list U"));
        }
        let index_name = "cov$mutual$wf$index";
        let index = covalence_core::Term::free(index_name, Type::nat());
        let route = self.carved_route_child(0, payload.clone(), 0, Some(index.clone()))?;
        let routed_wf = covalence_hol_eval::defs::option_case(universal.clone(), Type::bool())
            .apply(covalence_hol_eval::mk_bool(false))?
            .apply(child_wf)?
            .apply(route)?;
        let length = covalence_hol_eval::defs::list_length(universal).apply(payload)?;
        let in_bounds = crate::init::nat::nat_lt()
            .apply(index.clone())?
            .apply(length)?;
        in_bounds.imp(routed_wf)?.forall(index_name, Type::nat())
    }

    /// Wf closure for constructor 1's direct recursive child.
    pub fn carved_ctor1_wf_clause(
        &self,
        child_wf: covalence_core::Term,
        payload: covalence_core::Term,
    ) -> Result<covalence_core::Term> {
        use crate::init::ext::TermExt;

        let universal = self.carved_universal_domain_carrier()?;
        if child_wf.type_of()? != Type::fun(universal.clone(), Type::bool()) {
            return Err(syntax_err("child Wf predicate has the wrong carrier"));
        }
        if payload.type_of()? != universal {
            return Err(syntax_err("constructor 1 Wf payload has wrong carrier"));
        }
        let route = self.carved_route_child(1, payload, 0, None)?;
        let routed_wf = covalence_hol_eval::defs::option_case(universal.clone(), Type::bool())
            .apply(covalence_hol_eval::mk_bool(false))?
            .apply(child_wf)?
            .apply(route)?;
        Ok(routed_wf)
    }

    /// Simultaneous Wf closure for constructor 2's two independent `list U`
    /// recursive slots.
    pub fn carved_ctor2_wf_clause(
        &self,
        left_wf: covalence_core::Term,
        right_wf: covalence_core::Term,
        payload: covalence_core::Term,
    ) -> Result<covalence_core::Term> {
        use crate::init::ext::TermExt;

        let universal = self.carved_universal_domain_carrier()?;
        let predicate_ty = Type::fun(universal.clone(), Type::bool());
        if left_wf.type_of()? != predicate_ty || right_wf.type_of()? != predicate_ty {
            return Err(syntax_err(
                "constructor 2 child Wf predicate has wrong carrier",
            ));
        }
        let expected = self.carved_universal_payload(2)?;
        if payload.type_of()? != expected {
            return Err(syntax_err("constructor 2 Wf payload has wrong carrier"));
        }
        let covalence_core::TypeKind::Spec(_, arguments) = expected.kind() else {
            return Err(syntax_err("constructor 2 Wf payload is not a product"));
        };
        if arguments.len() != 2 {
            return Err(syntax_err("constructor 2 Wf payload is not binary"));
        }
        let predicates = [left_wf, right_wf];
        let mut clauses = Vec::new();
        for slot in 0..2 {
            let index_name = format!("cov$mutual$wf$index${slot}");
            let index = covalence_core::Term::free(&index_name, Type::nat());
            let route = self.carved_route_child(2, payload.clone(), slot, Some(index.clone()))?;
            let routed_wf = covalence_hol_eval::defs::option_case(universal.clone(), Type::bool())
                .apply(covalence_hol_eval::mk_bool(false))?
                .apply(predicates[slot].clone())?
                .apply(route)?;
            let children = if slot == 0 {
                covalence_hol_eval::defs::fst(arguments[0].clone(), arguments[1].clone())
                    .apply(payload.clone())?
            } else {
                covalence_hol_eval::defs::snd(arguments[0].clone(), arguments[1].clone())
                    .apply(payload.clone())?
            };
            let length =
                covalence_hol_eval::defs::list_length(universal.clone()).apply(children)?;
            let in_bounds = crate::init::nat::nat_lt()
                .apply(index.clone())?
                .apply(length)?;
            clauses.push(in_bounds.imp(routed_wf)?.forall(&index_name, Type::nat())?);
        }
        clauses[0].clone().and(clauses[1].clone())
    }

    /// Wf closure for constructor 3's direct recursive child.
    pub fn carved_ctor3_wf_clause(
        &self,
        child_wf: covalence_core::Term,
        payload: covalence_core::Term,
    ) -> Result<covalence_core::Term> {
        use crate::init::ext::TermExt;

        let universal = self.carved_universal_domain_carrier()?;
        if child_wf.type_of()? != Type::fun(universal.clone(), Type::bool()) {
            return Err(syntax_err(
                "constructor 3 child Wf predicate has wrong carrier",
            ));
        }
        if payload.type_of()? != self.carved_universal_payload(3)? {
            return Err(syntax_err("constructor 3 Wf payload has wrong carrier"));
        }
        let child = self.carved_route_child(3, payload, 0, None)?;
        covalence_hol_eval::defs::option_case(universal, Type::bool())
            .apply(covalence_hol_eval::mk_bool(false))?
            .apply(child_wf)?
            .apply(child)
    }

    /// Wf closure for the direct-child binary-product cluster.
    pub fn carved_direct_product_wf_clause(
        &self,
        constructor: usize,
        child_wf: covalence_core::Term,
        payload: covalence_core::Term,
    ) -> Result<covalence_core::Term> {
        use crate::init::ext::TermExt;

        if !matches!(constructor, 18 | 26 | 32 | 39) {
            return Err(syntax_err(
                "constructor is outside direct-product Wf cluster",
            ));
        }
        let universal = self.carved_universal_domain_carrier()?;
        if child_wf.type_of()? != Type::fun(universal.clone(), Type::bool()) {
            return Err(syntax_err(
                "direct-product child Wf predicate has wrong carrier",
            ));
        }
        if payload.type_of()? != self.carved_universal_payload(constructor)? {
            return Err(syntax_err("direct-product Wf payload has wrong carrier"));
        }
        let child = self.carved_route_child(constructor, payload, 0, None)?;
        covalence_hol_eval::defs::option_case(universal, Type::bool())
            .apply(covalence_hol_eval::mk_bool(false))?
            .apply(child_wf)?
            .apply(child)
    }

    /// Wf closure for constructor 20's `list U` payload.
    pub fn carved_ctor20_wf_clause(
        &self,
        child_wf: covalence_core::Term,
        payload: covalence_core::Term,
    ) -> Result<covalence_core::Term> {
        use crate::init::ext::TermExt;

        let universal = self.carved_universal_domain_carrier()?;
        if child_wf.type_of()? != Type::fun(universal.clone(), Type::bool()) {
            return Err(syntax_err(
                "constructor 20 child Wf predicate has wrong carrier",
            ));
        }
        if payload.type_of()? != crate::init::list::list(universal.clone()) {
            return Err(syntax_err("constructor 20 Wf payload is not list U"));
        }
        let index_name = "cov$mutual$wf$index$20";
        let index = covalence_core::Term::free(index_name, Type::nat());
        let route = self.carved_route_child(20, payload.clone(), 0, Some(index.clone()))?;
        let routed_wf = covalence_hol_eval::defs::option_case(universal.clone(), Type::bool())
            .apply(covalence_hol_eval::mk_bool(false))?
            .apply(child_wf)?
            .apply(route)?;
        let length = covalence_hol_eval::defs::list_length(universal).apply(payload)?;
        let in_bounds = crate::init::nat::nat_lt()
            .apply(index.clone())?
            .apply(length)?;
        in_bounds.imp(routed_wf)?.forall(index_name, Type::nat())
    }

    /// Wf closure for constructor 30's indexed list child and direct child.
    pub fn carved_ctor30_wf_clause(
        &self,
        list_wf: covalence_core::Term,
        direct_wf: covalence_core::Term,
        payload: covalence_core::Term,
    ) -> Result<covalence_core::Term> {
        use crate::init::ext::TermExt;

        let universal = self.carved_universal_domain_carrier()?;
        let predicate_ty = Type::fun(universal.clone(), Type::bool());
        if list_wf.type_of()? != predicate_ty || direct_wf.type_of()? != predicate_ty {
            return Err(syntax_err(
                "constructor 30 child Wf predicate has wrong carrier",
            ));
        }
        let expected = self.carved_universal_payload(30)?;
        if payload.type_of()? != expected {
            return Err(syntax_err("constructor 30 Wf payload has wrong carrier"));
        }
        let covalence_core::TypeKind::Spec(_, outer) = expected.kind() else {
            return Err(syntax_err("constructor 30 payload is not a product"));
        };
        let tail = covalence_hol_eval::defs::snd(outer[0].clone(), outer[1].clone())
            .apply(payload.clone())?;
        let covalence_core::TypeKind::Spec(_, inner) = outer[1].kind() else {
            return Err(syntax_err("constructor 30 tail is not a product"));
        };
        let children =
            covalence_hol_eval::defs::fst(inner[0].clone(), inner[1].clone()).apply(tail)?;
        let index_name = "cov$mutual$wf$index$30";
        let index = covalence_core::Term::free(index_name, Type::nat());
        let list_route = self.carved_route_child(30, payload.clone(), 0, Some(index.clone()))?;
        let routed_list_wf = covalence_hol_eval::defs::option_case(universal.clone(), Type::bool())
            .apply(covalence_hol_eval::mk_bool(false))?
            .apply(list_wf)?
            .apply(list_route)?;
        let length = covalence_hol_eval::defs::list_length(universal.clone()).apply(children)?;
        let bounded = crate::init::nat::nat_lt()
            .apply(index.clone())?
            .apply(length)?
            .imp(routed_list_wf)?
            .forall(index_name, Type::nat())?;
        let direct_route = self.carved_route_child(30, payload, 1, None)?;
        let direct = covalence_hol_eval::defs::option_case(universal, Type::bool())
            .apply(covalence_hol_eval::mk_bool(false))?
            .apply(direct_wf)?
            .apply(direct_route)?;
        bounded.and(direct)
    }

    /// U-level path-table constructor for any of the 41 source constructors.
    ///
    /// Empty paths return the exact injected root label. Non-empty paths are
    /// validated against the constructor tag, recursive slot, and traversal
    /// index shape before routing into the selected child table. Every invalid
    /// path returns a fixed junk label; Wf closure excludes those branches.
    pub fn carved_u_constructor(
        &self,
        constructor: usize,
        payload: covalence_core::Term,
    ) -> Result<covalence_core::Term> {
        use crate::init::ext::TermExt;

        let universal = self.carved_universal_domain_carrier()?;
        let path_ty = self.carved_path_carrier();
        let step_ty = self.runtime_path_step_carrier();
        let label_ty = self.carved_label_carrier()?;
        if payload.type_of()? != self.carved_universal_payload(constructor)? {
            return Err(syntax_err("wrong U-constructor payload"));
        }
        let root = self.carved_root_label(constructor, payload.clone())?;
        let junk = covalence_core::Term::select_op(label_ty.clone()).apply(
            covalence_core::Term::abs(label_ty.clone(), covalence_hol_eval::mk_bool(true)),
        )?;
        let path_name = format!("cov$mutual$u$path${constructor}");
        let path = covalence_core::Term::free(&path_name, path_ty.clone());
        let rest = crate::init::list::tail(step_ty.clone()).apply(path.clone())?;
        let edge_name = format!("cov$mutual$u$edge${constructor}");
        let edge = covalence_core::Term::free(&edge_name, step_ty.clone());
        let covalence_core::TypeKind::Spec(_, edge_args) = step_ty.kind() else {
            return Err(syntax_err("runtime path step is not a product"));
        };
        let edge_constructor =
            covalence_hol_eval::defs::fst(edge_args[0].clone(), edge_args[1].clone())
                .apply(edge.clone())?;
        let edge_tail = covalence_hol_eval::defs::snd(edge_args[0].clone(), edge_args[1].clone())
            .apply(edge.clone())?;
        let covalence_core::TypeKind::Spec(_, tail_args) = edge_args[1].kind() else {
            return Err(syntax_err("runtime path tail is not a product"));
        };
        let edge_slot = covalence_hol_eval::defs::fst(tail_args[0].clone(), tail_args[1].clone())
            .apply(edge_tail.clone())?;
        let indices = covalence_hol_eval::defs::snd(tail_args[0].clone(), tail_args[1].clone())
            .apply(edge_tail)?;

        let child_name = format!("cov$mutual$u$child${constructor}");
        let child = covalence_core::Term::free(&child_name, universal.clone());
        let child_label = child.clone().apply(rest)?;
        let child_handler = covalence_core::Term::abs(
            universal.clone(),
            covalence_core::subst::close(&child_label, &child_name),
        );
        let slots = self
            .path_alphabet()
            .into_iter()
            .filter(|step| step.constructor == constructor)
            .collect::<Vec<_>>();
        let mut routed = junk.clone();
        for slot in slots.iter().rev() {
            let indexed = matches!(
                (constructor, slot.recursive_slot),
                (0, 0) | (2, 0) | (2, 1) | (20, 0) | (30, 0)
            );
            let selected = if indexed {
                let index_option = covalence_hol_eval::defs::list_index(Type::nat())
                    .apply(covalence_hol_eval::mk_nat(0u64))?
                    .apply(indices.clone())?;
                let index_name =
                    format!("cov$mutual$u$index${constructor}${}", slot.recursive_slot);
                let index = covalence_core::Term::free(&index_name, Type::nat());
                let route = self.carved_route_child(
                    constructor,
                    payload.clone(),
                    slot.recursive_slot,
                    Some(index.clone()),
                )?;
                let route_label =
                    covalence_hol_eval::defs::option_case(universal.clone(), label_ty.clone())
                        .apply(junk.clone())?
                        .apply(child_handler.clone())?
                        .apply(route)?;
                let index_handler = covalence_core::Term::abs(
                    Type::nat(),
                    covalence_core::subst::close(&route_label, &index_name),
                );
                covalence_hol_eval::defs::option_case(Type::nat(), label_ty.clone())
                    .apply(junk.clone())?
                    .apply(index_handler)?
                    .apply(index_option)?
            } else {
                let route = self.carved_route_child(
                    constructor,
                    payload.clone(),
                    slot.recursive_slot,
                    None,
                )?;
                let route_label =
                    covalence_hol_eval::defs::option_case(universal.clone(), label_ty.clone())
                        .apply(junk.clone())?
                        .apply(child_handler.clone())?
                        .apply(route)?;
                let no_indices = indices
                    .clone()
                    .equals(crate::init::list::nil(Type::nat()))?;
                covalence_hol_eval::defs::cond(label_ty.clone())
                    .apply(no_indices)?
                    .apply(route_label)?
                    .apply(junk.clone())?
            };
            let is_slot = edge_slot
                .clone()
                .equals(covalence_hol_eval::mk_nat(slot.recursive_slot as u64))?;
            routed = covalence_hol_eval::defs::cond(label_ty.clone())
                .apply(is_slot)?
                .apply(selected)?
                .apply(routed)?;
        }
        let is_constructor =
            edge_constructor.equals(covalence_hol_eval::mk_nat(constructor as u64))?;
        let edge_result = covalence_hol_eval::defs::cond(label_ty.clone())
            .apply(is_constructor)?
            .apply(routed)?
            .apply(junk.clone())?;
        let edge_handler = covalence_core::Term::abs(
            step_ty.clone(),
            covalence_core::subst::close(&edge_result, &edge_name),
        );
        let body = covalence_hol_eval::defs::option_case(step_ty, label_ty)
            .apply(root)?
            .apply(edge_handler)?
            .apply(crate::init::list::head(self.runtime_path_step_carrier()).apply(path)?)?;
        let term =
            covalence_core::Term::abs(path_ty, covalence_core::subst::close(&body, &path_name));
        if term.type_of()? != universal {
            return Err(syntax_err("U constructor path table has wrong carrier"));
        }
        Ok(term)
    }

    /// Hypothesis-free root computation:
    /// `⊢ carved_u_constructor i payload [] = carved_root_label i payload`.
    pub fn carved_u_root_equation(
        &self,
        constructor: usize,
        payload: covalence_core::Term,
    ) -> Result<Thm> {
        use crate::init::ext::ThmExt;

        let step_ty = self.runtime_path_step_carrier();
        let label_ty = self.carved_label_carrier()?;
        let root = self.carved_root_label(constructor, payload.clone())?;
        let lhs = self
            .carved_u_constructor(constructor, payload)?
            .apply(crate::init::list::nil(step_ty.clone()))?;
        let beta = crate::init::eq::beta_nf(lhs);
        let Some((_, normal)) = beta.concl().as_eq() else {
            return Err(syntax_err("U root β-normalisation is not equality"));
        };
        let Some((case_function, head_nil_term)) = normal.as_app() else {
            return Err(syntax_err("U root normal form is not option elimination"));
        };
        let Some((case_with_default, handler)) = case_function.as_app() else {
            return Err(syntax_err("U root option elimination has no handler"));
        };
        let Some((_, default)) = case_with_default.as_app() else {
            return Err(syntax_err("U root option elimination has no default"));
        };
        if default != &root {
            return Err(syntax_err("U root option default is not root label"));
        }
        let head_nil = crate::init::list::head_nil(&step_ty)?;
        if head_nil.concl().as_eq().map(|(left, _)| left) != Some(head_nil_term) {
            return Err(syntax_err("U root normal form did not expose head nil"));
        }
        let rewrite = head_nil.cong_arg(case_function.clone())?;
        let compute = crate::init::option::case_none(&step_ty, &label_ty, default, handler)?;
        let theorem = beta.trans(rewrite)?.trans(compute)?;
        if !theorem.hyps().is_empty() || theorem.concl().as_eq().map(|(_, r)| r) != Some(&root) {
            return Err(syntax_err("U root equation failed its checked shape"));
        }
        Ok(theorem)
    }

    /// Simultaneous impredicative least-closure predicate over the closed
    /// universal domain for one member of the mutual SCC.
    pub fn carved_simultaneous_wf_predicate(&self, member: &str) -> Result<covalence_core::Term> {
        use crate::init::ext::TermExt;

        let member_index = self
            .members
            .iter()
            .position(|candidate| candidate == member)
            .ok_or_else(|| syntax_err("member is outside mutual signature"))?;
        let universal = self.carved_universal_domain_carrier()?;
        let predicate_ty = Type::fun(universal.clone(), Type::bool());
        let predicate_names = self
            .members
            .iter()
            .map(|member| format!("cov$mutual$carved$wf${member}"))
            .collect::<Vec<_>>();
        let predicates = predicate_names
            .iter()
            .map(|name| covalence_core::Term::free(name, predicate_ty.clone()))
            .collect::<Vec<_>>();
        let alphabet = self.path_alphabet();
        let mut closures = Vec::new();
        for constructor in 0..self.constructors.len() {
            let payload_ty = self.carved_universal_payload(constructor)?;
            let payload_name = format!("cov$mutual$carved$payload${constructor}");
            let payload = covalence_core::Term::free(&payload_name, payload_ty.clone());
            let slots = alphabet
                .iter()
                .filter(|step| step.constructor == constructor)
                .collect::<Vec<_>>();
            let guard = match slots.as_slice() {
                [] => covalence_hol_eval::mk_bool(true),
                [slot] => {
                    let child_wf = predicates[slot.target_member].clone();
                    match constructor {
                        0 => self.carved_ctor0_wf_clause(child_wf, payload.clone())?,
                        1 => self.carved_ctor1_wf_clause(child_wf, payload.clone())?,
                        3 => self.carved_ctor3_wf_clause(child_wf, payload.clone())?,
                        18 | 26 | 32 | 39 => self.carved_direct_product_wf_clause(
                            constructor,
                            child_wf,
                            payload.clone(),
                        )?,
                        20 => self.carved_ctor20_wf_clause(child_wf, payload.clone())?,
                        _ => {
                            return Err(syntax_err(
                                "single-slot constructor lacks exact Wf clause",
                            ));
                        }
                    }
                }
                [left, right] if constructor == 2 => self.carved_ctor2_wf_clause(
                    predicates[left.target_member].clone(),
                    predicates[right.target_member].clone(),
                    payload.clone(),
                )?,
                [left, right] if constructor == 30 => self.carved_ctor30_wf_clause(
                    predicates[left.target_member].clone(),
                    predicates[right.target_member].clone(),
                    payload.clone(),
                )?,
                _ => return Err(syntax_err("constructor recursive-slot census drifted")),
            };
            let owner = self
                .members
                .iter()
                .position(|member| member == self.constructors[constructor].owner())
                .ok_or_else(|| syntax_err("constructor owner is outside mutual signature"))?;
            let introduced = predicates[owner]
                .clone()
                .apply(self.carved_u_constructor(constructor, payload)?)?;
            closures.push(guard.imp(introduced)?.forall(&payload_name, payload_ty)?);
        }
        let value_name = format!("cov$mutual$carved$value${member}");
        let value = covalence_core::Term::free(&value_name, universal.clone());
        let mut body = predicates[member_index].clone().apply(value)?;
        for closure in closures.iter().rev() {
            body = closure.clone().imp(body)?;
        }
        for (name, _) in predicate_names.iter().zip(predicates.iter()).rev() {
            body = body.forall(name, predicate_ty.clone())?;
        }
        let predicate = covalence_core::Term::abs(
            universal.clone(),
            covalence_core::subst::close(&body, &value_name),
        );
        if predicate.type_of()? != Type::fun(universal, Type::bool()) {
            return Err(syntax_err("carved simultaneous Wf predicate is ill-typed"));
        }
        Ok(predicate)
    }

    fn payload_wf_observation(
        &self,
        source: &Type,
        observed: &Type,
        value: covalence_core::Term,
    ) -> Result<covalence_core::Term> {
        use crate::init::ext::TermExt;
        use covalence_core::TypeKind;

        if let TypeKind::TFree(name) = source.kind()
            && self
                .members
                .iter()
                .any(|member| name.as_str() == format!("cov$mutual${member}"))
        {
            if observed != &Type::bool() || value.type_of()? != Type::bool() {
                return Err(syntax_err("recursive slot did not observe as bool"));
            }
            return Ok(value);
        }
        if source.free_tvars().iter().all(|name| {
            !self
                .members
                .iter()
                .any(|member| name.as_str() == format!("cov$mutual${member}"))
        }) {
            return Ok(covalence_hol_eval::mk_bool(true));
        }

        let (TypeKind::Spec(_, source_args), TypeKind::Spec(_, observed_args)) =
            (source.kind(), observed.kind())
        else {
            return Err(syntax_err(
                "recursive payload occurs outside product/list/option",
            ));
        };
        if source_args.len() == 2
            && observed_args.len() == 2
            && source
                == &covalence_hol_eval::defs::prod(source_args[0].clone(), source_args[1].clone())
            && observed
                == &covalence_hol_eval::defs::prod(
                    observed_args[0].clone(),
                    observed_args[1].clone(),
                )
        {
            let left =
                covalence_hol_eval::defs::fst(observed_args[0].clone(), observed_args[1].clone())
                    .apply(value.clone())?;
            let right =
                covalence_hol_eval::defs::snd(observed_args[0].clone(), observed_args[1].clone())
                    .apply(value)?;
            return self
                .payload_wf_observation(&source_args[0], &observed_args[0], left)?
                .and(self.payload_wf_observation(&source_args[1], &observed_args[1], right)?);
        }
        if source_args.len() == 1
            && observed_args.len() == 1
            && source == &crate::init::list::list(source_args[0].clone())
            && observed == &crate::init::list::list(observed_args[0].clone())
        {
            let item = covalence_core::Term::free("cov$mutual$wf$item", observed_args[0].clone());
            let body = self.payload_wf_observation(&source_args[0], &observed_args[0], item)?;
            let predicate = covalence_core::Term::abs(
                observed_args[0].clone(),
                covalence_core::subst::close(&body, "cov$mutual$wf$item"),
            );
            return crate::init::nat_parse::list_all(&observed_args[0], &predicate).apply(value);
        }
        if source_args.len() == 1
            && observed_args.len() == 1
            && source == &crate::init::option::option(source_args[0].clone())
            && observed == &crate::init::option::option(observed_args[0].clone())
        {
            let item = covalence_core::Term::free("cov$mutual$wf$item", observed_args[0].clone());
            let body = self.payload_wf_observation(&source_args[0], &observed_args[0], item)?;
            let some_handler = covalence_core::Term::abs(
                observed_args[0].clone(),
                covalence_core::subst::close(&body, "cov$mutual$wf$item"),
            );
            return covalence_hol_eval::defs::option_case(observed_args[0].clone(), Type::bool())
                .apply(covalence_hol_eval::mk_bool(true))?
                .apply(some_handler)?
                .apply(value);
        }
        Err(syntax_err(
            "recursive payload occurs in an unrecognised type functor",
        ))
    }

    /// The simultaneous structural-closure predicate at the boolean
    /// observation instance of one open Church member.
    ///
    /// Every mutual result occurrence is observed as `bool`; constructor
    /// handlers conjoin exactly the recursive slots, lifting through products,
    /// lists and options. The returned predicate is fully kernel-typechecked,
    /// but is deliberately not a closed-carrier `Wf`: boolean observation
    /// forgets recursive child identity and therefore cannot support sealing
    /// or recursive constructor injectivity.
    pub fn simultaneous_wf_observation_predicate(
        &self,
        member: &str,
    ) -> Result<covalence_core::Term> {
        use crate::init::ext::TermExt;

        let open_carrier = self
            .carrier(member)
            .ok_or_else(|| syntax_err("member is outside mutual signature"))?
            .clone();
        let carrier = self
            .members
            .iter()
            .fold(open_carrier.clone(), |ty, result_member| {
                covalence_core::subst::subst_tfree_in_type(
                    &ty,
                    &format!("cov$mutual${result_member}"),
                    &Type::bool(),
                )
            });
        let value_name = format!("cov$mutual$wf${member}");
        let value = covalence_core::Term::free(&value_name, carrier.clone());
        let mut observed_value = value;
        for (constructor, handler_type) in self.constructors.iter().zip(self.handler_types.iter()) {
            let observed_handler =
                self.members
                    .iter()
                    .fold(handler_type.clone(), |ty, result_member| {
                        covalence_core::subst::subst_tfree_in_type(
                            &ty,
                            &format!("cov$mutual${result_member}"),
                            &Type::bool(),
                        )
                    });
            let covalence_core::TypeKind::Fun(observed_payload, observed_result) =
                observed_handler.kind().clone()
            else {
                return Err(syntax_err("observed mutual handler is not a function"));
            };
            if observed_result != Type::bool() {
                return Err(syntax_err("observed mutual handler result is not bool"));
            }
            let payload_name = format!("cov$mutual$wf$payload${}", constructor.name);
            let payload = covalence_core::Term::free(&payload_name, observed_payload.clone());
            let body =
                self.payload_wf_observation(&constructor.payload, &observed_payload, payload)?;
            let handler = covalence_core::Term::abs(
                observed_payload,
                covalence_core::subst::close(&body, &payload_name),
            );
            observed_value = observed_value.apply(handler)?;
        }
        let mut source_result = open_carrier;
        for _ in &self.handler_types {
            let covalence_core::TypeKind::Fun(_, result) = source_result.kind().clone() else {
                return Err(syntax_err("mutual carrier has too few handlers"));
            };
            source_result = result;
        }
        let observed_result = observed_value.type_of()?;
        let observed_value =
            self.payload_wf_observation(&source_result, &observed_result, observed_value)?;
        let predicate = covalence_core::Term::abs(
            carrier.clone(),
            covalence_core::subst::close(&observed_value, &value_name),
        );
        if predicate.type_of()? != Type::fun(carrier, Type::bool()) {
            return Err(syntax_err("simultaneous Wf predicate is ill-typed"));
        }
        Ok(predicate)
    }

    fn payload_mentions_result_carrier(&self, constructor: usize) -> Result<bool> {
        let payload = &self
            .constructors
            .get(constructor)
            .ok_or_else(|| syntax_err("mutual constructor index out of range"))?
            .payload;
        let variables = payload.free_tvars();
        Ok(self
            .members
            .iter()
            .any(|member| variables.contains(&format!("cov$mutual${member}").into())))
    }

    fn at_observation(
        &self,
        term: &covalence_core::Term,
        observation: &Type,
    ) -> covalence_core::Term {
        self.members.iter().fold(term.clone(), |term, member| {
            covalence_core::subst::subst_tfree_in_term(
                &term,
                &format!("cov$mutual${member}"),
                observation,
            )
        })
    }

    pub fn members(&self) -> &[String] {
        &self.members
    }

    pub fn carrier(&self, member: &str) -> Option<&Type> {
        self.carriers.get(member)
    }

    pub fn constructors(&self) -> &[MutualChurchConstructor] {
        &self.constructors
    }

    pub fn handler_types(&self) -> &[Type] {
        &self.handler_types
    }

    pub fn freeness_obligations(&self) -> Vec<MutualFreenessObligation> {
        let mut out = self
            .constructors
            .iter()
            .enumerate()
            .map(|(constructor, _)| MutualFreenessObligation::Injective { constructor })
            .collect::<Vec<_>>();
        for left in 0..self.constructors.len() {
            for right in left + 1..self.constructors.len() {
                if self.constructors[left].owner == self.constructors[right].owner {
                    out.push(MutualFreenessObligation::Distinct { left, right });
                }
            }
        }
        out
    }

    /// Payload type of `constructor` at the common boolean observation
    /// instance used by [`Self::observational_distinct`].
    pub fn boolean_observation_payload_type(&self, constructor: usize) -> Result<Type> {
        let ctor = self
            .constructors
            .get(constructor)
            .ok_or_else(|| syntax_err("mutual constructor index out of range"))?;
        Ok(self
            .at_observation(
                &covalence_core::Term::free("__payload_ty", ctor.payload.clone()),
                &Type::bool(),
            )
            .type_of()?)
    }

    /// Whether the constructor payload is external to the recursive result
    /// carriers and can therefore be recovered by a projection observation.
    pub fn supports_observational_injectivity(&self, constructor: usize) -> Result<bool> {
        Ok(!self.payload_mentions_result_carrier(constructor)?)
    }

    /// Prove projection-observation injectivity for a non-recursive payload.
    ///
    /// The conclusion is
    /// `Cᵢ[payload] x = Cᵢ[payload] y ⟹ x = y`, with every simultaneous
    /// result carrier instantiated to the payload type. Recursive payloads are
    /// refused: recovering them is exactly the rank-1 reconstruction wall.
    pub fn observational_injective(
        &self,
        constructor: usize,
        left: covalence_core::Term,
        right: covalence_core::Term,
    ) -> Result<Thm> {
        let ctor = self
            .constructors
            .get(constructor)
            .ok_or_else(|| syntax_err("mutual constructor index out of range"))?;
        if self.payload_mentions_result_carrier(constructor)? {
            return Err(syntax_err(
                "recursive payload cannot be recovered by a rank-1 observation",
            ));
        }
        if left.type_of()? != ctor.payload || right.type_of()? != ctor.payload {
            return Err(syntax_err("wrong constructor payload type"));
        }
        let observation = ctor.payload.clone();
        let mut lhs = self
            .at_observation(&ctor.term, &observation)
            .apply(left.clone())?;
        let mut rhs = self
            .at_observation(&ctor.term, &observation)
            .apply(right.clone())?;
        let arbitrary = covalence_core::Term::app(
            covalence_core::Term::select_op(observation.clone()),
            covalence_core::Term::abs(observation.clone(), covalence_hol_eval::mk_bool(true)),
        );
        for (i, handler) in self.handler_types.iter().enumerate() {
            let observed = self.members.iter().fold(handler.clone(), |ty, member| {
                covalence_core::subst::subst_tfree_in_type(
                    &ty,
                    &format!("cov$mutual${member}"),
                    &observation,
                )
            });
            let covalence_core::TypeKind::Fun(payload, result) = observed.kind().clone() else {
                return Err(syntax_err("mutual handler is not a function"));
            };
            if result != observation {
                return Err(syntax_err("projection handler has wrong result"));
            }
            let handler = if i == ctor.handler_index {
                if payload != observation {
                    return Err(syntax_err(
                        "selected projection payload changed under observation",
                    ));
                }
                let value = covalence_core::Term::free("__projection", payload.clone());
                covalence_core::Term::abs(
                    payload,
                    covalence_core::subst::close(&value, "__projection"),
                )
            } else {
                covalence_core::Term::abs(payload, arbitrary.clone())
            };
            lhs = lhs.apply(handler.clone())?;
            rhs = rhs.apply(handler)?;
        }
        let equation = lhs.equals(rhs)?;
        let assumed = Thm::assume(equation.clone())?;
        let Some((l, r)) = assumed.concl().as_eq() else {
            return Err(syntax_err("projection assumption is not equality"));
        };
        let l_beta = beta_nf(l.clone());
        let r_beta = beta_nf(r.clone());
        let recovered = l_beta.sym()?.trans(assumed)?.trans(r_beta)?;
        let left_beta = beta_nf(left);
        let right_beta = beta_nf(right);
        left_beta
            .trans(recovered)?
            .trans(right_beta.sym()?)?
            .imp_intro(&equation)
    }

    /// Prove distinctness at the boolean observation instance.
    ///
    /// This is the exact rank-1 Church observation law:
    /// `¬(Cᵢ[bool] x = Cⱼ[bool] y)`. It is checked and useful for folds, but
    /// deliberately does not discharge the source-carrier distinctness
    /// obligation: the open simultaneous signature is not a closed recursive
    /// datatype.
    pub fn observational_distinct(
        &self,
        left: usize,
        right: usize,
        left_payload: covalence_core::Term,
        right_payload: covalence_core::Term,
    ) -> Result<Thm> {
        let left_ctor = self
            .constructors
            .get(left)
            .ok_or_else(|| syntax_err("mutual constructor index out of range"))?;
        let right_ctor = self
            .constructors
            .get(right)
            .ok_or_else(|| syntax_err("mutual constructor index out of range"))?;
        if left == right || left_ctor.owner != right_ctor.owner {
            return Err(syntax_err(
                "observational distinctness requires different constructors of one owner",
            ));
        }
        if left_payload.type_of()? != self.boolean_observation_payload_type(left)?
            || right_payload.type_of()? != self.boolean_observation_payload_type(right)?
        {
            return Err(syntax_err("wrong boolean-observation payload type"));
        }

        let bool_ty = Type::bool();
        let mut lhs = self
            .at_observation(&left_ctor.term, &bool_ty)
            .apply(left_payload)?;
        let mut rhs = self
            .at_observation(&right_ctor.term, &bool_ty)
            .apply(right_payload)?;
        let mut handlers = Vec::with_capacity(self.handler_types.len());
        for (i, handler) in self.handler_types.iter().enumerate() {
            let observed = self.members.iter().fold(handler.clone(), |ty, member| {
                covalence_core::subst::subst_tfree_in_type(
                    &ty,
                    &format!("cov$mutual${member}"),
                    &bool_ty,
                )
            });
            let covalence_core::TypeKind::Fun(payload, result) = observed.kind().clone() else {
                return Err(syntax_err("mutual handler is not a function"));
            };
            if result != bool_ty {
                return Err(syntax_err(
                    "boolean observation handler has non-bool result",
                ));
            }
            handlers.push(covalence_core::Term::abs(
                payload,
                covalence_hol_eval::mk_bool(i == left),
            ));
        }
        for handler in &handlers {
            lhs = lhs.apply(handler.clone())?;
            rhs = rhs.apply(handler.clone())?;
        }
        let equation = lhs.equals(rhs)?;
        let mut observed = Thm::assume(equation.clone())?;
        // The handlers were already applied above; normalisation exposes their
        // distinct boolean tags directly.
        let Some((l, r)) = observed.concl().as_eq() else {
            return Err(syntax_err("observation assumption is not equality"));
        };
        let l_beta = beta_nf(l.clone());
        let r_beta = beta_nf(r.clone());
        observed = l_beta.sym()?.trans(observed)?.trans(r_beta)?;
        let Some((l, r)) = observed.concl().as_eq() else {
            return Err(syntax_err("observation did not yield equality"));
        };
        if *l != covalence_hol_eval::mk_bool(true) || *r != covalence_hol_eval::mk_bool(false) {
            return Err(syntax_err("constructor tags did not separate"));
        }
        observed
            .eq_mp(crate::init::logic::truth())?
            .imp_intro(&equation)?
            .not_intro()
    }

    /// Prove the handler-injection computation equation
    /// `Cᵢ payload handlers = handlers[i] payload` by β-normalisation.
    pub fn computation(
        &self,
        constructor: usize,
        payload: covalence_core::Term,
        handlers: &[covalence_core::Term],
    ) -> Result<Thm> {
        let ctor = self
            .constructors
            .get(constructor)
            .ok_or_else(|| syntax_err("mutual constructor index out of range"))?;
        if handlers.len() != self.handler_types.len() {
            return Err(syntax_err("wrong mutual handler count"));
        }
        for (actual, expected) in handlers.iter().zip(&self.handler_types) {
            if actual.type_of()? != *expected {
                return Err(syntax_err("wrong mutual handler type"));
            }
        }
        if payload.type_of()? != ctor.payload {
            return Err(syntax_err("wrong mutual constructor payload type"));
        }
        let mut lhs = ctor.term.clone().apply(payload.clone())?;
        for handler in handlers {
            lhs = lhs.apply(handler.clone())?;
        }
        let rhs = handlers[ctor.handler_index].clone().apply(payload)?;
        let lhs_beta = beta_nf(lhs);
        let rhs_beta = beta_nf(rhs);
        let Some((_, lhs_nf)) = lhs_beta.concl().as_eq() else {
            return Err(syntax_err("β-normalisation did not produce equality"));
        };
        let Some((_, rhs_nf)) = rhs_beta.concl().as_eq() else {
            return Err(syntax_err("β-normalisation did not produce equality"));
        };
        if lhs_nf != rhs_nf {
            return Err(syntax_err(
                "mutual constructor did not reduce to selected handler",
            ));
        }
        lhs_beta.trans(rhs_beta.sym()?)
    }
}

/// Build the term-level simultaneous Church signature containing `member`.
pub fn mutual_church_signature(member: &str, ctx: &TypeCtx<'_>) -> Result<MutualChurchSignature> {
    let component = ctx
        .mutual_by_name
        .get(member)
        .ok_or_else(|| syntax_err(format!("`{member}` is not in a mutual type SCC")))?;
    build_mutual_church_signature(component, ctx)
}

fn resolve_mutual_named<'a>(
    target: &str,
    component: &[&'a str],
    ctx: &TypeCtx<'a>,
) -> Result<Type> {
    build_mutual_church_signature(component, ctx)?
        .carrier(target)
        .cloned()
        .ok_or_else(|| syntax_err(format!("`{target}` is not in its mutual component")))
}

fn build_mutual_church_signature<'a>(
    component: &[&'a str],
    ctx: &TypeCtx<'a>,
) -> Result<MutualChurchSignature> {
    let mutual_members: BTreeSet<String> =
        component.iter().map(|name| (*name).to_owned()).collect();
    let mut mutual = BTreeMap::new();
    let mut structural = BTreeSet::new();
    for &member in component {
        let SpecTecDef::Typ { insts, .. } = ctx
            .lookup(member)
            .ok_or_else(|| syntax_err(format!("unknown mutual type `{member}`")))?
        else {
            return Err(syntax_err(format!("`{member}` is not a type")));
        };
        if insts
            .iter()
            .all(|SpecTecInst::Inst { dt, .. }| matches!(dt, SpecTecDefTyp::Variant { .. }))
        {
            mutual.insert(
                member.to_owned(),
                Type::tfree(format!("cov$mutual${member}")),
            );
        } else {
            structural.insert(member);
        }
    }
    if mutual.is_empty() {
        return Err(syntax_err(
            "mutual component has no variant constructor (pure structural cycle)",
        ));
    }

    // Normalize aliases/records after replacing every genuinely generative
    // variant by its distinct result carrier. Repeated passes are a small,
    // deterministic topological evaluator; no-progress means the structural
    // subgraph itself cycles and must be refused.
    while !structural.is_empty() {
        let mut progress = Vec::new();
        for &member in &structural {
            let SpecTecDef::Typ { ps, insts, .. } = ctx.lookup(member).unwrap() else {
                unreachable!()
            };
            if !ps.is_empty() {
                return Err(syntax_err(format!(
                    "mutual type `{member}` has unsupported family parameters"
                )));
            }
            let [
                SpecTecInst::Inst {
                    ps: instance_params,
                    dt,
                    ..
                },
            ] = insts.as_slice()
            else {
                return Err(syntax_err(format!(
                    "structural mutual type `{member}` has multiple/zero instances"
                )));
            };
            if !instance_params.is_empty() {
                return Err(syntax_err(format!(
                    "mutual type `{member}` has unsupported instance parameters"
                )));
            }
            let scope = Scope {
                self_name: None,
                tenv: BTreeMap::new(),
                mutual: mutual.clone(),
                mutual_members: mutual_members.clone(),
            };
            let mut visited = Vec::new();
            let rendered = match dt {
                SpecTecDefTyp::Alias { typ } => resolve_typ_d(typ, ctx, &mut visited, &scope),
                SpecTecDefTyp::Struct { tfs } => {
                    if tfs.iter().any(|field| {
                        let SpecTecTypField::Field { qs, prs, .. } = field;
                        !qs.is_empty() || !prs.is_empty()
                    }) {
                        return Err(syntax_err(format!(
                            "mutual struct `{member}` has field binders/refinements"
                        )));
                    }
                    resolve_struct(tfs, ctx, &mut visited, &scope)
                }
                SpecTecDefTyp::Variant { .. } => unreachable!(),
            };
            if let Ok(ty) = rendered {
                mutual.insert(member.to_owned(), ty);
                progress.push(member);
            }
        }
        if progress.is_empty() {
            return Err(syntax_err(
                "mutual component contains a cyclic structural synonym",
            ));
        }
        for member in progress {
            structural.remove(member);
        }
    }

    let scope = Scope {
        self_name: None,
        tenv: BTreeMap::new(),
        mutual,
        mutual_members,
    };
    let mut handlers = Vec::new();

    for &member in component {
        let def = ctx
            .lookup(member)
            .ok_or_else(|| syntax_err(format!("unknown mutual type `{member}`")))?;
        let SpecTecDef::Typ { ps, insts, .. } = def else {
            return Err(syntax_err(format!("`{member}` is not a type")));
        };
        if !ps.is_empty() {
            return Err(syntax_err(format!(
                "mutual type `{member}` has unsupported family parameters"
            )));
        }
        let result = scope.mutual[member].clone();
        for SpecTecInst::Inst {
            ps: instance_params,
            dt,
            ..
        } in insts
        {
            if !instance_params.is_empty() {
                return Err(syntax_err(format!(
                    "mutual type `{member}` has unsupported instance parameters"
                )));
            }
            let mut visited = Vec::new();
            match dt {
                SpecTecDefTyp::Alias { .. } | SpecTecDefTyp::Struct { .. } => {}
                SpecTecDefTyp::Variant { tcs } => {
                    for SpecTecTypCase::Field { op, t, qs, prs } in tcs {
                        if !qs.is_empty() || !prs.is_empty() {
                            return Err(syntax_err(format!(
                                "mutual variant `{member}` has case binders/refinements"
                            )));
                        }
                        let payload = resolve_typ_d(t, ctx, &mut visited, &scope)?;
                        handlers.push((
                            member.to_owned(),
                            super::encode::mixop_key(op),
                            payload.clone(),
                            Type::fun(payload, result.clone()),
                        ));
                    }
                }
            }
        }
    }

    if handlers.is_empty() {
        return Err(syntax_err("mutual component has no data constructor"));
    }
    let handler_types: Vec<_> = handlers.iter().map(|(_, _, _, ty)| ty.clone()).collect();
    let mut carriers = BTreeMap::new();
    for &member in component {
        let mut encoded = scope.mutual[member].clone();
        for handler in handler_types.iter().rev() {
            encoded = Type::fun(handler.clone(), encoded);
        }
        carriers.insert(member.to_owned(), encoded);
    }
    let handler_names: Vec<_> = (0..handler_types.len())
        .map(|i| format!("cov$mutual$h{i}"))
        .collect();
    let handler_vars: Vec<_> = handler_types
        .iter()
        .enumerate()
        .map(|(i, ty)| covalence_core::Term::free(&handler_names[i], ty.clone()))
        .collect();
    let constructors = handlers
        .iter()
        .enumerate()
        .map(|(i, (owner, name, payload, _))| {
            let value = covalence_core::Term::free("cov$mutual$payload", payload.clone());
            let mut body = handler_vars[i].clone().apply(value.clone())?;
            for j in (0..handler_vars.len()).rev() {
                body = covalence_core::Term::abs(
                    handler_types[j].clone(),
                    covalence_core::subst::close(&body, &handler_names[j]),
                );
            }
            let term = covalence_core::Term::abs(
                payload.clone(),
                covalence_core::subst::close(&body, "cov$mutual$payload"),
            );
            Ok(MutualChurchConstructor {
                owner: owner.clone(),
                name: name.clone(),
                payload: payload.clone(),
                term,
                handler_index: i,
            })
        })
        .collect::<Result<Vec<_>>>()?;
    Ok(MutualChurchSignature {
        members: component.iter().map(|name| (*name).to_owned()).collect(),
        carriers,
        handler_types,
        constructors,
    })
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
    use covalence_core::Term;
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

    #[test]
    fn mutually_recursive_variants_keep_distinct_result_carriers_and_edges() {
        let defs = vec![
            variant_def(
                "even",
                vec![
                    variant_case("ZERO", unit_ty()),
                    variant_case("ES", var("odd")),
                ],
            ),
            variant_def("odd", vec![variant_case("OS", var("even"))]),
        ];
        let ctx = TypeCtx::new(&defs);
        let even = resolve_def(&defs[0], &ctx).unwrap();
        let odd = resolve_def(&defs[1], &ctx).unwrap();
        assert_ne!(even, odd);
        let expected_vars = ["cov$mutual$even", "cov$mutual$odd"];
        assert_eq!(
            even.free_tvars()
                .iter()
                .map(|x| x.as_str())
                .collect::<Vec<_>>(),
            expected_vars
        );
        assert_eq!(
            odd.free_tvars()
                .iter()
                .map(|x| x.as_str())
                .collect::<Vec<_>>(),
            expected_vars
        );
    }

    #[test]
    fn mutual_signature_exposes_checked_handler_injections_and_all_obligations() {
        let defs = vec![
            variant_def(
                "even",
                vec![
                    variant_case("ZERO", unit_ty()),
                    variant_case("ES", var("odd")),
                ],
            ),
            variant_def("odd", vec![variant_case("OS", var("even"))]),
        ];
        let ctx = TypeCtx::new(&defs);
        let signature = mutual_church_signature("even", &ctx).unwrap();
        assert_eq!(signature.members(), ["even", "odd"]);
        assert_eq!(signature.constructors().len(), 3);
        assert_eq!(
            signature
                .constructors()
                .iter()
                .map(|ctor| (ctor.owner(), ctor.name()))
                .collect::<Vec<_>>(),
            [("even", "ZERO"), ("even", "ES"), ("odd", "OS")]
        );

        let handlers: Vec<_> = signature
            .handler_types()
            .iter()
            .enumerate()
            .map(|(i, ty)| Term::free(format!("test_handler_{i}"), ty.clone()))
            .collect();
        for (i, ctor) in signature.constructors().iter().enumerate() {
            assert_eq!(
                ctor.term().type_of().unwrap(),
                Type::fun(
                    ctor.payload_type().clone(),
                    signature.carrier(ctor.owner()).unwrap().clone()
                )
            );
            let payload = Term::free(format!("payload_{i}"), ctor.payload_type().clone());
            let mut lhs = ctor.term().clone().apply(payload.clone()).unwrap();
            for handler in &handlers {
                lhs = lhs.apply(handler.clone()).unwrap();
            }
            let rhs = handlers[i].clone().apply(payload.clone()).unwrap();
            let expected = lhs.equals(rhs).unwrap();
            let computation = signature.computation(i, payload, &handlers).unwrap();
            assert!(computation.hyps().is_empty());
            assert_eq!(computation.concl(), &expected);
        }
        assert_eq!(
            signature.freeness_obligations(),
            [
                MutualFreenessObligation::Injective { constructor: 0 },
                MutualFreenessObligation::Injective { constructor: 1 },
                MutualFreenessObligation::Injective { constructor: 2 },
                MutualFreenessObligation::Distinct { left: 0, right: 1 },
            ]
        );
        let left = Term::free(
            "left_payload",
            signature.boolean_observation_payload_type(0).unwrap(),
        );
        let right = Term::free(
            "right_payload",
            signature.boolean_observation_payload_type(1).unwrap(),
        );
        let distinct = signature.observational_distinct(0, 1, left, right).unwrap();
        assert!(distinct.hyps().is_empty());
        assert!(signature.supports_observational_injectivity(0).unwrap());
        assert!(!signature.supports_observational_injectivity(1).unwrap());
        assert!(!signature.supports_observational_injectivity(2).unwrap());
        let x = Term::free("zero_x", signature.constructors()[0].payload_type().clone());
        let y = Term::free("zero_y", signature.constructors()[0].payload_type().clone());
        let injective = signature.observational_injective(0, x, y).unwrap();
        assert!(injective.hyps().is_empty());
    }

    #[test]
    fn wasm_mutual_signature_constructor_terms_cover_the_pinned_scc() {
        let defs = crate::wasm::spec::wasm_spec();
        let ctx = TypeCtx::new(&defs);
        let signature = mutual_church_signature("valtype", &ctx).unwrap();
        assert_eq!(signature.members().len(), 9);
        assert_eq!(signature.constructors().len(), 41);
        assert_eq!(
            signature.path_alphabet(),
            [
                MutualPathStep {
                    constructor: 0,
                    recursive_slot: 0,
                    target_member: 1,
                },
                MutualPathStep {
                    constructor: 1,
                    recursive_slot: 0,
                    target_member: 1,
                },
                MutualPathStep {
                    constructor: 2,
                    recursive_slot: 0,
                    target_member: 8,
                },
                MutualPathStep {
                    constructor: 2,
                    recursive_slot: 1,
                    target_member: 8,
                },
                MutualPathStep {
                    constructor: 3,
                    recursive_slot: 0,
                    target_member: 5,
                },
                MutualPathStep {
                    constructor: 18,
                    recursive_slot: 0,
                    target_member: 3,
                },
                MutualPathStep {
                    constructor: 20,
                    recursive_slot: 0,
                    target_member: 6,
                },
                MutualPathStep {
                    constructor: 26,
                    recursive_slot: 0,
                    target_member: 2,
                },
                MutualPathStep {
                    constructor: 30,
                    recursive_slot: 0,
                    target_member: 7,
                },
                MutualPathStep {
                    constructor: 30,
                    recursive_slot: 1,
                    target_member: 0,
                },
                MutualPathStep {
                    constructor: 32,
                    recursive_slot: 0,
                    target_member: 3,
                },
                MutualPathStep {
                    constructor: 39,
                    recursive_slot: 0,
                    target_member: 2,
                },
            ]
        );
        let labels = signature.common_label_carrier().unwrap();
        assert_eq!(
            labels
                .free_tvars()
                .into_iter()
                .map(|name| name.to_string())
                .collect::<Vec<_>>(),
            [
                "cov$mutual$comptype",
                "cov$mutual$fieldtype",
                "cov$mutual$heaptype",
                "cov$mutual$rectype",
                "cov$mutual$storagetype",
                "cov$mutual$subtype",
                "cov$mutual$typeuse",
                "cov$mutual$valtype",
            ]
        );
        assert_eq!(
            signature.carved_payload_skeleton(0).unwrap(),
            crate::init::list::list(Type::unit())
        );
        assert!(
            signature
                .carved_payload_skeleton(2)
                .unwrap()
                .free_tvars()
                .is_empty(),
            "the two-slot constructor label must retain shape without children"
        );
        let runtime_step = signature.runtime_path_step_carrier();
        assert_eq!(
            runtime_step,
            covalence_hol_eval::defs::prod(
                Type::nat(),
                covalence_hol_eval::defs::prod(Type::nat(), crate::init::list::list(Type::nat()))
            )
        );
        assert!(
            signature
                .carved_universal_domain_carrier()
                .unwrap()
                .free_tvars()
                .is_empty(),
            "the path-table universal domain must be closed"
        );
        let universal = signature.carved_universal_domain_carrier().unwrap();
        assert_eq!(
            signature.carved_universal_payload(0).unwrap(),
            crate::init::list::list(universal.clone())
        );
        assert_eq!(
            signature.carved_universal_payload(1).unwrap(),
            universal.clone()
        );
        assert_eq!(
            signature.carved_universal_payload(3).unwrap(),
            covalence_hol_eval::defs::prod(
                crate::init::option::option(Type::unit()),
                universal.clone()
            )
        );
        assert_eq!(
            signature.carved_routed_recursive_constructors(),
            [0, 1, 2, 3, 18, 20, 26, 30, 32, 39]
        );
        assert_eq!(
            signature.carved_universal_payload(20).unwrap(),
            crate::init::list::list(universal.clone())
        );
        assert_eq!(
            signature.carved_universal_payload(30).unwrap(),
            covalence_hol_eval::defs::prod(
                crate::init::option::option(Type::unit()),
                covalence_hol_eval::defs::prod(
                    crate::init::list::list(universal.clone()),
                    universal.clone()
                )
            )
        );
        for constructor in [18usize, 32] {
            assert_eq!(
                signature.carved_universal_payload(constructor).unwrap(),
                covalence_hol_eval::defs::prod(universal.clone(), Type::nat())
            );
        }
        for constructor in [26usize, 39] {
            assert_eq!(
                signature.carved_universal_payload(constructor).unwrap(),
                covalence_hol_eval::defs::prod(
                    crate::init::option::option(Type::unit()),
                    universal.clone()
                )
            );
        }
        let ctor0_payload = Term::free(
            "carved_ctor0_payload",
            crate::init::list::list(universal.clone()),
        );
        assert_eq!(
            signature
                .carved_root_label(0, ctor0_payload)
                .unwrap()
                .type_of()
                .unwrap(),
            signature.carved_label_carrier().unwrap()
        );
        fn count_type(ty: &Type, needle: &Type) -> usize {
            use covalence_core::TypeKind;
            if ty == needle {
                return 1;
            }
            match ty.kind() {
                TypeKind::Fun(left, right) => count_type(left, needle) + count_type(right, needle),
                TypeKind::Tycon(_, arguments) | TypeKind::Spec(_, arguments) => arguments
                    .iter()
                    .map(|argument| count_type(argument, needle))
                    .sum(),
                TypeKind::FreshTyCon(leaf) => leaf
                    .args()
                    .iter()
                    .map(|argument| count_type(argument, needle))
                    .sum(),
                TypeKind::TFree(_) | TypeKind::Nat | TypeKind::Bool => 0,
            }
        }
        assert_eq!(
            count_type(&signature.carved_universal_payload(2).unwrap(), &universal),
            2,
            "constructor 2 must retain two independently routable U children"
        );
        let ctor2_payload = Term::free(
            "carved_ctor2_payload",
            signature.carved_universal_payload(2).unwrap(),
        );
        assert_eq!(
            signature
                .carved_root_label(2, ctor2_payload)
                .unwrap()
                .type_of()
                .unwrap(),
            signature.carved_label_carrier().unwrap()
        );
        let child = Term::free("carved_child", universal.clone());
        let rest = Term::free(
            "carved_children",
            crate::init::list::list(universal.clone()),
        );
        let children = crate::init::list::cons(universal.clone())
            .apply(child.clone())
            .unwrap()
            .apply(rest.clone())
            .unwrap();
        let routed = signature
            .carved_route_child(
                0,
                children.clone(),
                0,
                Some(covalence_hol_eval::mk_nat(0u64)),
            )
            .unwrap();
        assert_eq!(
            routed.type_of().unwrap(),
            crate::init::option::option(universal.clone())
        );
        let index_zero = crate::init::list::index_cons_zero(&universal, &child, &rest).unwrap();
        assert_eq!(index_zero.concl().as_eq().unwrap().0, &routed);
        assert!(
            signature
                .carved_route_child(
                    0,
                    children.clone(),
                    1,
                    Some(covalence_hol_eval::mk_nat(0u64))
                )
                .is_err()
        );
        let ctor20_payload = Term::free(
            "carved_ctor20_payload",
            crate::init::list::list(universal.clone()),
        );
        assert_eq!(
            signature
                .carved_ctor20_wf_clause(
                    Term::free(
                        "carved_ctor20_wf",
                        Type::fun(universal.clone(), Type::bool())
                    ),
                    ctor20_payload
                )
                .unwrap()
                .type_of()
                .unwrap(),
            Type::bool()
        );
        let ctor30_payload = Term::free(
            "carved_ctor30_payload",
            signature.carved_universal_payload(30).unwrap(),
        );
        assert_eq!(
            signature
                .carved_ctor30_wf_clause(
                    Term::free(
                        "carved_ctor30_list_wf",
                        Type::fun(universal.clone(), Type::bool())
                    ),
                    Term::free(
                        "carved_ctor30_direct_wf",
                        Type::fun(universal.clone(), Type::bool())
                    ),
                    ctor30_payload.clone()
                )
                .unwrap()
                .type_of()
                .unwrap(),
            Type::bool()
        );
        assert!(
            signature
                .carved_route_child(
                    30,
                    ctor30_payload,
                    1,
                    Some(covalence_hol_eval::mk_nat(0u64))
                )
                .is_err(),
            "constructor 30 direct slot must reject a list index"
        );
        for constructor in 0..signature.constructors().len() {
            let payload = Term::free(
                format!("carved_u_payload_{constructor}"),
                signature.carved_universal_payload(constructor).unwrap(),
            );
            assert_eq!(
                signature
                    .carved_u_constructor(constructor, payload.clone())
                    .unwrap()
                    .type_of()
                    .unwrap(),
                universal
            );
            let root = signature
                .carved_u_root_equation(constructor, payload)
                .unwrap();
            assert!(root.hyps().is_empty());
            assert_eq!(
                root.concl().as_eq().unwrap().1,
                &signature
                    .carved_root_label(
                        constructor,
                        Term::free(
                            format!("carved_u_payload_{constructor}"),
                            signature.carved_universal_payload(constructor).unwrap()
                        )
                    )
                    .unwrap()
            );
        }
        assert!(
            signature
                .carved_u_constructor(0, Term::free("bad_u_payload", Type::nat()))
                .is_err()
        );
        assert!(signature.carved_route_child(0, children, 0, None).is_err());
        let child_wf = Term::free(
            "carved_child_wf",
            Type::fun(universal.clone(), Type::bool()),
        );
        let wf_payload = Term::free(
            "carved_wf_payload",
            crate::init::list::list(universal.clone()),
        );
        assert_eq!(
            signature
                .carved_ctor0_wf_clause(child_wf, wf_payload)
                .unwrap()
                .type_of()
                .unwrap(),
            Type::bool()
        );
        assert!(
            signature
                .carved_ctor0_wf_clause(
                    Term::free("bad_child_wf", Type::fun(Type::nat(), Type::bool())),
                    Term::free("bad_wf_payload", crate::init::list::list(universal.clone()))
                )
                .is_err()
        );
        let ctor1_wf = Term::free(
            "carved_ctor1_wf",
            Type::fun(universal.clone(), Type::bool()),
        );
        let ctor1_payload = Term::free("carved_ctor1_payload", universal.clone());
        assert_eq!(
            signature
                .carved_ctor1_wf_clause(ctor1_wf, ctor1_payload)
                .unwrap()
                .type_of()
                .unwrap(),
            Type::bool()
        );
        let ctor2_wf_payload = Term::free(
            "carved_ctor2_wf_payload",
            signature.carved_universal_payload(2).unwrap(),
        );
        let left_wf = Term::free("carved_left_wf", Type::fun(universal.clone(), Type::bool()));
        let right_wf = Term::free(
            "carved_right_wf",
            Type::fun(universal.clone(), Type::bool()),
        );
        assert_eq!(
            signature
                .carved_ctor2_wf_clause(left_wf, right_wf, ctor2_wf_payload)
                .unwrap()
                .type_of()
                .unwrap(),
            Type::bool()
        );
        assert!(
            signature
                .carved_ctor2_wf_clause(
                    Term::free("bad_left_wf", Type::fun(Type::nat(), Type::bool())),
                    Term::free("good_right_wf", Type::fun(universal.clone(), Type::bool())),
                    Term::free(
                        "bad_ctor2_wf_payload",
                        signature.carved_universal_payload(2).unwrap()
                    )
                )
                .is_err()
        );
        let ctor3_payload = Term::free(
            "carved_ctor3_payload",
            signature.carved_universal_payload(3).unwrap(),
        );
        let ctor3_wf = Term::free(
            "carved_ctor3_wf",
            Type::fun(universal.clone(), Type::bool()),
        );
        assert_eq!(
            signature
                .carved_ctor3_wf_clause(ctor3_wf, ctor3_payload.clone())
                .unwrap()
                .type_of()
                .unwrap(),
            Type::bool()
        );
        assert!(
            signature
                .carved_route_child(3, ctor3_payload, 0, Some(covalence_hol_eval::mk_nat(0u64)))
                .is_err(),
            "direct child must reject a spurious list index"
        );
        for constructor in [18usize, 26, 32, 39] {
            let wf = Term::free(
                format!("carved_direct_wf_{constructor}"),
                Type::fun(universal.clone(), Type::bool()),
            );
            let payload = Term::free(
                format!("carved_direct_payload_{constructor}"),
                signature.carved_universal_payload(constructor).unwrap(),
            );
            assert_eq!(
                signature
                    .carved_direct_product_wf_clause(constructor, wf, payload)
                    .unwrap()
                    .type_of()
                    .unwrap(),
                Type::bool()
            );
        }
        assert!(
            signature
                .carved_direct_product_wf_clause(
                    20,
                    Term::free(
                        "unsupported_direct_wf",
                        Type::fun(universal.clone(), Type::bool())
                    ),
                    Term::free(
                        "unsupported_direct_payload",
                        signature.carved_universal_payload(20).unwrap()
                    )
                )
                .is_err()
        );
        for member in signature.members() {
            assert_eq!(
                signature
                    .carved_simultaneous_wf_predicate(member)
                    .unwrap()
                    .type_of()
                    .unwrap(),
                Type::fun(universal.clone(), Type::bool())
            );
            let predicate = signature
                .simultaneous_wf_observation_predicate(member)
                .unwrap();
            let covalence_core::TypeKind::Fun(_, result) =
                predicate.type_of().unwrap().kind().clone()
            else {
                panic!("Wf observation must be a predicate");
            };
            assert_eq!(result, Type::bool());
        }
        assert!(
            signature
                .carved_simultaneous_wf_predicate("outside")
                .is_err()
        );
        for ctor in signature.constructors() {
            assert_eq!(
                ctor.term().type_of().unwrap(),
                Type::fun(
                    ctor.payload_type().clone(),
                    signature.carrier(ctor.owner()).unwrap().clone()
                )
            );
        }
        let obligations = signature.freeness_obligations();
        assert_eq!(obligations.len(), 224);
        assert_eq!(
            obligations
                .iter()
                .filter(|law| matches!(law, MutualFreenessObligation::Injective { .. }))
                .count(),
            41
        );
        assert_eq!(
            obligations
                .iter()
                .filter(|law| matches!(law, MutualFreenessObligation::Distinct { .. }))
                .count(),
            183
        );
        let mut checked_distinct = 0;
        for obligation in obligations {
            let MutualFreenessObligation::Distinct { left, right } = obligation else {
                continue;
            };
            let left_payload = Term::free(
                format!("obs_left_{left}_{right}"),
                signature.boolean_observation_payload_type(left).unwrap(),
            );
            let right_payload = Term::free(
                format!("obs_right_{left}_{right}"),
                signature.boolean_observation_payload_type(right).unwrap(),
            );
            let theorem = signature
                .observational_distinct(left, right, left_payload, right_payload)
                .unwrap();
            assert!(theorem.hyps().is_empty());
            checked_distinct += 1;
        }
        assert_eq!(checked_distinct, 183);
        let mut checked_injective = 0;
        for constructor in 0..signature.constructors().len() {
            if !signature
                .supports_observational_injectivity(constructor)
                .unwrap()
            {
                continue;
            }
            let payload = signature.constructors()[constructor].payload_type().clone();
            let left = Term::free(format!("inj_left_{constructor}"), payload.clone());
            let right = Term::free(format!("inj_right_{constructor}"), payload);
            let theorem = signature
                .observational_injective(constructor, left, right)
                .unwrap();
            assert!(theorem.hyps().is_empty());
            checked_injective += 1;
        }
        assert_eq!(checked_injective, 31);
    }

    #[test]
    fn real_wasm_mutual_scc_renders_all_nine_members_without_identifying_them() {
        let defs = crate::wasm::spec::wasm_spec();
        let ctx = TypeCtx::new(&defs);
        let names = [
            "comptype",
            "fieldtype",
            "heaptype",
            "rectype",
            "resulttype",
            "storagetype",
            "subtype",
            "typeuse",
            "valtype",
        ];
        let rendered: Vec<_> = names
            .iter()
            .map(|name| resolve_named(name, &ctx, &mut Vec::new()).unwrap())
            .collect();
        let unique: BTreeSet<_> = rendered.iter().collect();
        assert_eq!(unique.len(), names.len());
        let generative = [
            "comptype",
            "fieldtype",
            "heaptype",
            "rectype",
            "storagetype",
            "subtype",
            "typeuse",
            "valtype",
        ];
        for ty in rendered {
            let vars: BTreeSet<_> = ty.free_tvars().into_iter().collect();
            assert_eq!(
                vars,
                generative
                    .iter()
                    .map(|name| format!("cov$mutual${name}").into())
                    .collect()
            );
        }
        assert_eq!(crate::wasm::spec::rendered_types(&defs), (144, 207));
        assert_eq!(crate::wasm::spec::renderable_types(&defs), (170, 207));
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
