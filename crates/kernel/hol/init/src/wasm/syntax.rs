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
//! parameters don't affect the HOL type). A [`Scope`] threads the self-reference
//! name and the type-parameter bindings.
//!
//! Building a `Type` cannot be unsound (it grows no `Thm`), so this is a plain
//! total-where-possible renderer. Still deferred (typed error): mutually-recursive
//! variants (a sibling reference cycles), `text`/`rat`/`real`, and non-numeric
//! value-indexed subtleties. See `SKELETONS.md`.

use std::collections::BTreeMap;

use covalence_core::{Error, Result, Type};
use covalence_spectec::ast::{
    SpecTecArg, SpecTecDef, SpecTecDefTyp, SpecTecInst, SpecTecIter, SpecTecNumTyp, SpecTecParam,
    SpecTecTyp, SpecTecTypBind, SpecTecTypCase, SpecTecTypField,
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
/// and ignored) and resolve its body under those bindings.
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
    let [SpecTecInst::Inst { dt, .. }] = insts.as_slice() else {
        return Err(syntax_err(format!("`{name}` has multiple/zero instances")));
    };
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
    enter(
        name,
        dt,
        ctx,
        visited,
        &Scope {
            self_name: None,
            tenv,
        },
    )
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
    let r = match dt {
        SpecTecDefTyp::Alias { typ } => resolve_typ_d(typ, ctx, visited, &base.no_self()),
        SpecTecDefTyp::Struct { tfs } => resolve_struct(tfs, ctx, visited, &base.no_self()),
        SpecTecDefTyp::Variant { tcs } => resolve_variant(name, tcs, ctx, visited, base),
    };
    visited.pop();
    r
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
    let self_tv = self_ty_var().free_tvars();
    v.ctors
        .iter()
        .any(|c| c.payload.free_tvars().iter().any(|t| self_tv.contains(t)))
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
/// [`Variant`] description (the constructors + payload types). Errors if `def`
/// isn't a non-recursive variant. Used by [`super::denote`] to build constructor
/// terms for `case` expressions.
pub fn variant_of(def: &SpecTecDef, ctx: &TypeCtx) -> Result<Variant> {
    let SpecTecDef::Typ { x, ps, insts } = def else {
        return Err(syntax_err("definition is not a `typ`"));
    };
    if !ps.is_empty() {
        return Err(syntax_err(format!(
            "parametric type `{x}` not modelled yet"
        )));
    }
    let [SpecTecInst::Inst { ps: ips, dt, .. }] = insts.as_slice() else {
        return Err(syntax_err(format!("`{x}` has multiple/zero instances")));
    };
    if !ips.is_empty() {
        return Err(syntax_err(format!(
            "parametric type `{x}` not modelled yet"
        )));
    }
    let SpecTecDefTyp::Variant { tcs } = dt else {
        return Err(syntax_err(format!("`{x}` is not a variant")));
    };
    let mut visited = vec![x.as_str()];
    build_variant(x, tcs, ctx, &mut visited, &Scope::default())
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
}
