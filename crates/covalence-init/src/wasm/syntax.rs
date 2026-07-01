//! **SpecTec type → HOL type** (leg B, the type foundation).
//!
//! Renders a SpecTec `SpecTecTyp` (and a whole `SpecTecDef::Typ`) to a genuine
//! HOL [`Type`] over the [`crate::init`] catalogue: `bool`/`nat`/`int` primitives,
//! tuples → right-nested `prod`, `X*`/`X?` → `list`/`option`, and named
//! **alias** types chased through a [`TypeCtx`]. This is what [`super::denote`]
//! needs to type metavariables that come from the spec, and the first step toward
//! typing SpecTec functions and relations.
//!
//! Building a `Type` cannot be unsound (it grows no `Thm`), so this is a plain
//! total-where-possible renderer: constructs the catalogue doesn't yet model —
//! **variant** and **struct** types (WASM's `valtype`/`instr`/… — these need real
//! inductive datatypes via the `crate::init` engine), parametric types (`vec(X)`),
//! `text`, `rat`/`real` — return a typed error. See `SKELETONS.md`.

use std::collections::BTreeMap;

use covalence_core::{Error, Result, Type};
use covalence_spectec::ast::{
    SpecTecDef, SpecTecDefTyp, SpecTecInst, SpecTecIter, SpecTecNumTyp, SpecTecTyp, SpecTecTypBind,
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

/// Render a SpecTec type to a HOL [`Type`], chasing named aliases through `ctx`.
pub fn resolve_typ(t: &SpecTecTyp, ctx: &TypeCtx) -> Result<Type> {
    resolve_typ_d(t, ctx, &mut Vec::new())
}

/// Render the type a `SpecTecDef::Typ` denotes (a top-level alias). Errors on
/// variant/struct/parametric definitions.
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
) -> Result<Type> {
    match t {
        SpecTecTyp::Bool => Ok(Type::bool()),
        SpecTecTyp::Num(SpecTecNumTyp::Nat) => Ok(Type::nat()),
        SpecTecTyp::Num(SpecTecNumTyp::Int) => Ok(Type::int()),
        SpecTecTyp::Num(nt) => Err(syntax_err(format!("numeric type {nt:?} not modelled yet"))),
        SpecTecTyp::Text => Err(syntax_err("text type not modelled yet")),
        SpecTecTyp::Tup { ets } => resolve_tuple(ets, ctx, visited),
        SpecTecTyp::Iter { t1, it } => {
            let mut ty = resolve_typ_d(t1, ctx, visited)?;
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
        SpecTecTyp::Var { x, as1 } => {
            if !as1.is_empty() {
                return Err(syntax_err(format!(
                    "parametric type `{x}` not modelled yet"
                )));
            }
            resolve_named(x, ctx, visited)
        }
    }
}

/// A tuple type `(t₀, …, tₙ)` → right-nested `prod` (`[]` = `unit`, singleton =
/// the element itself).
fn resolve_tuple<'a>(
    ets: &'a [SpecTecTypBind],
    ctx: &TypeCtx<'a>,
    visited: &mut Vec<&'a str>,
) -> Result<Type> {
    match ets {
        [] => Ok(Type::unit()),
        [SpecTecTypBind::Bind { typ, .. }] => resolve_typ_d(typ, ctx, visited),
        [SpecTecTypBind::Bind { typ, .. }, rest @ ..] => {
            let head = resolve_typ_d(typ, ctx, visited)?;
            let tail = resolve_tuple(rest, ctx, visited)?;
            Ok(prod::prod(head, tail))
        }
    }
}

fn resolve_named<'a>(name: &'a str, ctx: &TypeCtx<'a>, visited: &mut Vec<&'a str>) -> Result<Type> {
    if visited.contains(&name) {
        return Err(syntax_err(format!("cyclic type alias `{name}`")));
    }
    let def = ctx
        .lookup(name)
        .ok_or_else(|| syntax_err(format!("unknown type `{name}`")))?;
    let SpecTecDef::Typ { ps, insts, .. } = def else {
        return Err(syntax_err(format!("`{name}` is not a type")));
    };
    if !ps.is_empty() {
        return Err(syntax_err(format!(
            "parametric type `{name}` not modelled yet"
        )));
    }
    let [SpecTecInst::Inst { ps: ips, dt, .. }] = insts.as_slice() else {
        return Err(syntax_err(format!("`{name}` has multiple/zero instances")));
    };
    if !ips.is_empty() {
        return Err(syntax_err(format!(
            "parametric type `{name}` not modelled yet"
        )));
    }
    match dt {
        SpecTecDefTyp::Alias { typ } => {
            visited.push(name);
            let r = resolve_typ_d(typ, ctx, visited);
            visited.pop();
            r
        }
        SpecTecDefTyp::Struct { .. } => Err(syntax_err(format!(
            "record type `{name}` needs a datatype (not modelled yet)"
        ))),
        SpecTecDefTyp::Variant { .. } => Err(syntax_err(format!(
            "variant type `{name}` needs a datatype (not modelled yet)"
        ))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_spectec::ast::{SpecTecInst, SpecTecParam};

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
    fn variant_and_parametric_error() {
        let variant = SpecTecDef::Typ {
            x: "valtype".into(),
            ps: vec![],
            insts: vec![SpecTecInst::Inst {
                ps: vec![],
                as_: vec![],
                dt: SpecTecDefTyp::Variant { tcs: vec![] },
            }],
        };
        let parametric = SpecTecDef::Typ {
            x: "vec".into(),
            ps: vec![SpecTecParam::Typ { x: "X".into() }],
            insts: vec![],
        };
        let ctx = TypeCtx::new(&[]);
        assert!(resolve_def(&variant, &ctx).is_err());
        assert!(resolve_def(&parametric, &ctx).is_err());
    }
}
