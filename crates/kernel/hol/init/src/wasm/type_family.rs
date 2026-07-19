//! Lossless, non-semantic reification of SpecTec type declarations.
//!
//! This module is the boundary between the upstream AST and future HOL
//! datatype backends.  It deliberately does not choose a carrier or claim that
//! a declaration renders: instance binders, case/field binders, and refinement
//! premises are retained verbatim.  The dependency graph and its strongly
//! connected components are likewise pure source analysis.

use std::collections::{BTreeMap, BTreeSet};

use covalence_spectec::ast::{
    MixOp, SpecTecArg, SpecTecDef, SpecTecDefTyp, SpecTecInst, SpecTecParam, SpecTecPrem,
    SpecTecTyp, SpecTecTypCase, SpecTecTypField,
};

use crate::init::inductive::{CoprodBackend, CoprodVariantTheory, VariantTheoryBackend};

use super::syntax;

/// A lossless view of one struct field.
#[derive(Debug, Clone, Copy)]
pub struct FieldShape<'a> {
    pub label: &'a MixOp,
    pub ty: &'a SpecTecTyp,
    pub params: &'a [SpecTecParam],
    pub refinements: &'a [SpecTecPrem],
}

/// A lossless view of one variant case.
#[derive(Debug, Clone, Copy)]
pub struct CaseShape<'a> {
    pub operator: &'a MixOp,
    pub payload: &'a SpecTecTyp,
    pub params: &'a [SpecTecParam],
    pub refinements: &'a [SpecTecPrem],
}

/// The body of one type-family instance.
#[derive(Debug, Clone)]
pub enum TypeShape<'a> {
    Alias(&'a SpecTecTyp),
    Struct(Vec<FieldShape<'a>>),
    Variant(Vec<CaseShape<'a>>),
}

/// One instance of a (possibly indexed) type family.
#[derive(Debug, Clone)]
pub struct FamilyInstance<'a> {
    pub params: &'a [SpecTecParam],
    pub args: &'a [SpecTecArg],
    pub shape: TypeShape<'a>,
}

/// A top-level SpecTec type family, with every source component preserved.
#[derive(Debug, Clone)]
pub struct TypeFamily<'a> {
    pub name: &'a str,
    pub params: &'a [SpecTecParam],
    pub instances: Vec<FamilyInstance<'a>>,
}

impl<'a> TypeFamily<'a> {
    /// Every case/field refinement premise owned by this family.
    pub fn refinements(&self) -> impl Iterator<Item = &'a SpecTecPrem> + '_ {
        self.instances.iter().flat_map(|instance| {
            let groups: Vec<&'a [SpecTecPrem]> = match &instance.shape {
                TypeShape::Alias(_) => Vec::new(),
                TypeShape::Struct(fields) => fields.iter().map(|field| field.refinements).collect(),
                TypeShape::Variant(cases) => cases.iter().map(|case| case.refinements).collect(),
            };
            groups.into_iter().flatten()
        })
    }

    /// Names of type families referenced by this family's declared types.
    pub fn dependencies(&self) -> BTreeSet<&'a str> {
        let mut out = BTreeSet::new();
        for param in self.params {
            references_param(param, &mut out);
        }
        for instance in &self.instances {
            for param in instance.params {
                references_param(param, &mut out);
            }
            for arg in instance.args {
                references_arg(arg, &mut out);
            }
            match &instance.shape {
                TypeShape::Alias(ty) => references_typ(ty, &mut out),
                TypeShape::Struct(fields) => {
                    for field in fields {
                        references_typ(field.ty, &mut out);
                        for param in field.params {
                            references_param(param, &mut out);
                        }
                    }
                }
                TypeShape::Variant(cases) => {
                    for case in cases {
                        references_typ(case.payload, &mut out);
                        for param in case.params {
                            references_param(param, &mut out);
                        }
                    }
                }
            }
        }
        out
    }
}

/// A lossless catalogue plus deterministic type-dependency analysis.
#[derive(Debug, Clone)]
pub struct TypeFamilies<'a> {
    families: BTreeMap<&'a str, TypeFamily<'a>>,
}

/// High-level source interface consumed by future datatype backends.
pub trait TypeFamilySource<'a> {
    fn family(&self, name: &str) -> Option<&TypeFamily<'a>>;
    fn families<'s>(&'s self) -> impl Iterator<Item = &'s TypeFamily<'a>> + 's
    where
        'a: 's;
    fn dependencies(&self, name: &str) -> Option<BTreeSet<&'a str>>;
    /// Whether `name` and every reachable declared type family are free of
    /// case/field refinement premises.
    fn refinement_free_closure(&self, name: &str) -> Option<bool>;
    fn strongly_connected_components(&self) -> Vec<Vec<&'a str>>;
}

/// Realize one source variant through the existing non-recursive coproduct
/// renderer and expose its kernel-derived constructor theory.
///
/// This is intentionally the same accepted fragment as
/// [`syntax::variant_of`] followed by [`CoprodBackend`], with one additional
/// honesty check: recursive variants are refused rather than presenting their
/// free self-type placeholder as a closed datatype carrier.  Refinement
/// premises remain reified by [`TypeFamilies`] and are not claimed by this
/// representation-level theory.
pub fn coprod_variant_theory(
    def: &SpecTecDef,
    ctx: &syntax::TypeCtx<'_>,
) -> covalence_core::Result<CoprodVariantTheory> {
    let variant = syntax::variant_of(def, ctx)?;
    CoprodBackend.theory(&variant)
}

impl<'a> TypeFamilies<'a> {
    /// Reify every `Typ`, descending through `Rec` groups.
    pub fn new(defs: &'a [SpecTecDef]) -> Self {
        let mut families = BTreeMap::new();
        fn visit<'a>(def: &'a SpecTecDef, out: &mut BTreeMap<&'a str, TypeFamily<'a>>) {
            match def {
                SpecTecDef::Typ { x, ps, insts } => {
                    let instances = insts.iter().map(reify_instance).collect();
                    out.insert(
                        x,
                        TypeFamily {
                            name: x,
                            params: ps,
                            instances,
                        },
                    );
                }
                SpecTecDef::Rec { ds } => {
                    for def in ds {
                        visit(def, out);
                    }
                }
                _ => {}
            }
        }
        for def in defs {
            visit(def, &mut families);
        }
        Self { families }
    }

    /// Number of source type declarations.
    pub fn len(&self) -> usize {
        self.families.len()
    }

    pub fn is_empty(&self) -> bool {
        self.families.is_empty()
    }
}

impl<'a> TypeFamilySource<'a> for TypeFamilies<'a> {
    fn family(&self, name: &str) -> Option<&TypeFamily<'a>> {
        self.families.get(name)
    }

    fn families<'s>(&'s self) -> impl Iterator<Item = &'s TypeFamily<'a>> + 's
    where
        'a: 's,
    {
        self.families.values()
    }

    fn dependencies(&self, name: &str) -> Option<BTreeSet<&'a str>> {
        let family = self.family(name)?;
        Some(
            family
                .dependencies()
                .into_iter()
                .filter(|dependency| self.families.contains_key(dependency))
                .collect(),
        )
    }

    fn refinement_free_closure(&self, name: &str) -> Option<bool> {
        self.family(name)?;
        fn visit<'a>(
            families: &TypeFamilies<'a>,
            name: &str,
            visiting: &mut BTreeSet<String>,
        ) -> bool {
            if !visiting.insert(name.to_owned()) {
                return true;
            }
            let Some(family) = families.family(name) else {
                return true;
            };
            if family.refinements().next().is_some() {
                return false;
            }
            families
                .dependencies(name)
                .unwrap_or_default()
                .into_iter()
                .all(|dependency| visit(families, dependency, visiting))
        }
        Some(visit(self, name, &mut BTreeSet::new()))
    }

    fn strongly_connected_components(&self) -> Vec<Vec<&'a str>> {
        // Tarjan, with BTree iteration and sorted components for stable output.
        struct Tarjan<'a, 'b> {
            graph: &'b TypeFamilies<'a>,
            next: usize,
            indices: BTreeMap<&'a str, usize>,
            lowlinks: BTreeMap<&'a str, usize>,
            stack: Vec<&'a str>,
            on_stack: BTreeSet<&'a str>,
            components: Vec<Vec<&'a str>>,
        }
        impl<'a> Tarjan<'a, '_> {
            fn visit(&mut self, node: &'a str) {
                let index = self.next;
                self.next += 1;
                self.indices.insert(node, index);
                self.lowlinks.insert(node, index);
                self.stack.push(node);
                self.on_stack.insert(node);

                for successor in self.graph.dependencies(node).unwrap_or_default() {
                    if !self.indices.contains_key(successor) {
                        self.visit(successor);
                        let child = self.lowlinks[successor];
                        self.lowlinks
                            .entry(node)
                            .and_modify(|low| *low = (*low).min(child));
                    } else if self.on_stack.contains(successor) {
                        let back = self.indices[successor];
                        self.lowlinks
                            .entry(node)
                            .and_modify(|low| *low = (*low).min(back));
                    }
                }

                if self.lowlinks[node] == self.indices[node] {
                    let mut component = Vec::new();
                    loop {
                        let member = self.stack.pop().expect("Tarjan stack");
                        self.on_stack.remove(member);
                        component.push(member);
                        if member == node {
                            break;
                        }
                    }
                    component.sort_unstable();
                    self.components.push(component);
                }
            }
        }

        let mut tarjan = Tarjan {
            graph: self,
            next: 0,
            indices: BTreeMap::new(),
            lowlinks: BTreeMap::new(),
            stack: Vec::new(),
            on_stack: BTreeSet::new(),
            components: Vec::new(),
        };
        for &name in self.families.keys() {
            if !tarjan.indices.contains_key(name) {
                tarjan.visit(name);
            }
        }
        tarjan.components.sort();
        tarjan.components
    }
}

fn reify_instance(instance: &SpecTecInst) -> FamilyInstance<'_> {
    let SpecTecInst::Inst { ps, as_, dt } = instance;
    let shape = match dt {
        SpecTecDefTyp::Alias { typ } => TypeShape::Alias(typ),
        SpecTecDefTyp::Struct { tfs } => TypeShape::Struct(
            tfs.iter()
                .map(|field| {
                    let SpecTecTypField::Field { at, t, qs, prs } = field;
                    FieldShape {
                        label: at,
                        ty: t,
                        params: qs,
                        refinements: prs,
                    }
                })
                .collect(),
        ),
        SpecTecDefTyp::Variant { tcs } => TypeShape::Variant(
            tcs.iter()
                .map(|case| {
                    let SpecTecTypCase::Field { op, t, qs, prs } = case;
                    CaseShape {
                        operator: op,
                        payload: t,
                        params: qs,
                        refinements: prs,
                    }
                })
                .collect(),
        ),
    };
    FamilyInstance {
        params: ps,
        args: as_,
        shape,
    }
}

fn references_typ<'a>(ty: &'a SpecTecTyp, out: &mut BTreeSet<&'a str>) {
    match ty {
        SpecTecTyp::Var { x, as1 } => {
            out.insert(x);
            for arg in as1 {
                references_arg(arg, out);
            }
        }
        SpecTecTyp::Tup { ets } => {
            for bind in ets {
                let covalence_spectec::ast::SpecTecTypBind::Bind { typ, .. } = bind;
                references_typ(typ, out);
            }
        }
        SpecTecTyp::Iter { t1, .. } => references_typ(t1, out),
        SpecTecTyp::Bool | SpecTecTyp::Num(_) | SpecTecTyp::Text => {}
    }
}

fn references_arg<'a>(arg: &'a SpecTecArg, out: &mut BTreeSet<&'a str>) {
    if let SpecTecArg::Typ { t } = arg {
        references_typ(t, out);
    }
}

fn references_param<'a>(param: &'a SpecTecParam, out: &mut BTreeSet<&'a str>) {
    match param {
        SpecTecParam::Exp { t, .. }
        | SpecTecParam::Def { t, .. }
        | SpecTecParam::Gram { t, .. } => references_typ(t, out),
        SpecTecParam::Typ { .. } => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::init::inductive::VariantTheory;
    use crate::wasm::spec::wasm_spec;

    fn variant_case(name: &str, payload: SpecTecTyp) -> SpecTecTypCase {
        SpecTecTypCase::Field {
            op: MixOp::new(vec![name.into()]),
            t: payload,
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

    #[test]
    fn source_variant_theory_preserves_single_constructor_name_and_carrier() {
        let def = variant_def(
            "boxed_nat",
            vec![variant_case(
                "BOX",
                SpecTecTyp::Num(covalence_spectec::ast::SpecTecNumTyp::Nat),
            )],
        );
        let defs = vec![def];
        let ctx = syntax::TypeCtx::new(&defs);
        let theory = coprod_variant_theory(&defs[0], &ctx).unwrap();

        assert_eq!(theory.carrier(), &covalence_core::Type::nat());
        assert_eq!(theory.constructor_count(), 1);
        assert_eq!(theory.constructor_name(0).unwrap(), "BOX");
        assert_eq!(theory.constructor_named("BOX").unwrap().0, 0);
    }

    #[test]
    fn source_variant_theory_refuses_recursive_family() {
        let def = variant_def(
            "tree",
            vec![
                variant_case("LEAF", SpecTecTyp::Tup { ets: vec![] }),
                variant_case(
                    "NODE",
                    SpecTecTyp::Var {
                        x: "tree".into(),
                        as1: vec![],
                    },
                ),
            ],
        );
        let defs = vec![def];
        let ctx = syntax::TypeCtx::new(&defs);
        assert!(coprod_variant_theory(&defs[0], &ctx).is_err());
    }

    #[test]
    fn real_wasm_mutual_type_scc_is_pinned() {
        let defs = wasm_spec();
        let families = TypeFamilies::new(&defs);
        assert_eq!(families.len(), 207);
        let mutual: Vec<_> = families
            .strongly_connected_components()
            .into_iter()
            .filter(|component| component.len() > 1)
            .collect();
        assert_eq!(
            mutual,
            [vec![
                "comptype",
                "fieldtype",
                "heaptype",
                "rectype",
                "resulttype",
                "storagetype",
                "subtype",
                "typeuse",
                "valtype",
            ]]
        );
    }

    #[test]
    fn real_wasm_refinements_are_retained_losslessly() {
        let defs = wasm_spec();
        let families = TypeFamilies::new(&defs);
        let owners: BTreeSet<_> = families
            .families()
            .filter(|family| family.refinements().next().is_some())
            .map(|family| family.name)
            .collect();
        let refinements = families
            .families()
            .map(|family| family.refinements().count())
            .sum::<usize>();
        assert_eq!(refinements, 56);
        assert_eq!(
            owners,
            BTreeSet::from([
                "bit",
                "bshape",
                "byte",
                "char",
                "cvtop__",
                "dim",
                "fNmag",
                "instr",
                "ishape",
                "list",
                "loadop_",
                "name",
                "relaxed2",
                "relaxed4",
                "sN",
                "shape",
                "storeop_",
                "symdots",
                "sz",
                "uN",
                "unop_",
                "vbinop_",
                "vcvtop__",
                "vextbinop__",
                "vextternop__",
                "vextunop__",
                "vloadop_",
                "vrelop_",
                "vunop_",
            ])
        );
        assert_eq!(families.refinement_free_closure("bit"), Some(false));
        assert_eq!(families.refinement_free_closure("mut"), Some(true));
        assert_eq!(families.refinement_free_closure("not-a-family"), None);
    }
}
