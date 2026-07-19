//! Whole-spec facades for the two top layers of SpecTec support.
//!
//! [`SpecTecSpec`] is the AST-shaped layer: it owns an elaborated SpecTec
//! definition stream and indexes definitions recursively through `rec` groups.
//! [`HolSpec`] is the next layer down: it lowers that stream into the common
//! clause currency used by relations, functions, evaluators, and slices.
//!
//! Keeping the layers distinct makes the support claim precise. A definition
//! being present in [`SpecTecSpec`] means the front end can represent it.
//! A clause being present in [`HolSpec`] means it was translated into a
//! kernel-checked rule set. A rule being in an opaque-free slice such as
//! [`HolSpec::lime`] means its dependency closure is executable by the current
//! derivation engine.

use std::collections::BTreeMap;

use covalence_core::{Error, Result};
use covalence_spectec::ast::SpecTecDef;

use super::RelationEnv;
use crate::wasm::lower::slice::{SliceEnv, SliceSeed, SpecSlice, lime_slice};
use crate::wasm::lower::total::{ClauseMeta, TotalReport, total_spec_clauses};
use crate::wasm::lower::{Clause, rule_set_of};
use crate::wasm::type_family::TypeFamilies;

/// The five definition forms in the elaborated SpecTec AST.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum DefinitionKind {
    Type,
    Relation,
    Function,
    Grammar,
    RecursionGroup,
}

impl DefinitionKind {
    /// Stable, SpecTec-shaped spelling used in diagnostics and inventories.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Type => "typ",
            Self::Relation => "rel",
            Self::Function => "def",
            Self::Grammar => "gram",
            Self::RecursionGroup => "rec",
        }
    }
}

/// A typed borrowed view into a [`SpecTecSpec`]'s flattened definition index.
#[derive(Debug, Clone, Copy)]
pub struct DefinitionRef<'a> {
    kind: DefinitionKind,
    name: Option<&'a str>,
    ast: &'a SpecTecDef,
}

impl<'a> DefinitionRef<'a> {
    pub fn kind(self) -> DefinitionKind {
        self.kind
    }

    /// Definition name, or `None` for an anonymous `rec` grouping node.
    pub fn name(self) -> Option<&'a str> {
        self.name
    }

    pub fn ast(self) -> &'a SpecTecDef {
        self.ast
    }
}

/// An owned elaborated SpecTec AST with a recursive, kind-aware name index.
///
/// The original nesting is retained in [`Self::defs`]; [`Self::definitions`]
/// is a pre-order flattened view that includes `rec` nodes and their children.
/// The name index is kind-aware because different SpecTec namespaces need not
/// be conflated by a high-level consumer.
#[derive(Debug, Clone)]
pub struct SpecTecSpec {
    defs: Vec<SpecTecDef>,
    flat_paths: Vec<Vec<usize>>,
    by_name: BTreeMap<(DefinitionKind, String), Vec<usize>>,
}

impl SpecTecSpec {
    /// Index an elaborated definition stream without changing its AST.
    pub fn new(defs: Vec<SpecTecDef>) -> Self {
        let mut flat_paths = Vec::new();
        collect_paths(&defs, &mut Vec::new(), &mut flat_paths);
        let mut by_name: BTreeMap<(DefinitionKind, String), Vec<usize>> = BTreeMap::new();
        for (flat_idx, path) in flat_paths.iter().enumerate() {
            let def = at_path(&defs, path);
            if let Some(name) = def_name(def) {
                by_name
                    .entry((def_kind(def), name.to_owned()))
                    .or_default()
                    .push(flat_idx);
            }
        }
        Self {
            defs,
            flat_paths,
            by_name,
        }
    }

    /// The bundled, elaborated WebAssembly 3.0 SpecTec AST.
    pub fn wasm3() -> Self {
        Self::new(covalence_spectec::wasm::get_wasm_spectec_ast())
    }

    /// Original top-level definitions, preserving `rec` groups.
    pub fn defs(&self) -> &[SpecTecDef] {
        &self.defs
    }

    /// Lossless type-family view, retaining every source refinement premise
    /// and exposing deterministic dependency/SCC analysis.
    pub fn type_families(&self) -> TypeFamilies<'_> {
        TypeFamilies::new(&self.defs)
    }

    /// Every definition in pre-order, recursively descending through `rec`.
    pub fn definitions(&self) -> impl ExactSizeIterator<Item = DefinitionRef<'_>> {
        self.flat_paths.iter().map(|path| {
            let ast = at_path(&self.defs, path);
            DefinitionRef {
                kind: def_kind(ast),
                name: def_name(ast),
                ast,
            }
        })
    }

    /// All definitions with this `(kind, name)`.
    ///
    /// Returning all matches keeps duplicate declarations visible instead of
    /// silently choosing one. [`Self::unique`] is the stricter convenience.
    pub fn named(
        &self,
        kind: DefinitionKind,
        name: &str,
    ) -> impl ExactSizeIterator<Item = DefinitionRef<'_>> {
        let indices = self
            .by_name
            .get(&(kind, name.to_owned()))
            .map(Vec::as_slice)
            .unwrap_or_default();
        indices.iter().map(move |&i| {
            let ast = at_path(&self.defs, &self.flat_paths[i]);
            DefinitionRef {
                kind,
                name: Some(name_of(ast)),
                ast,
            }
        })
    }

    /// Resolve exactly one definition, rejecting ambiguous duplicate names.
    pub fn unique(&self, kind: DefinitionKind, name: &str) -> Result<DefinitionRef<'_>> {
        let found: Vec<_> = self.named(kind, name).collect();
        match found.as_slice() {
            [one] => Ok(*one),
            [] => Err(Error::ConnectiveRule(format!(
                "spectec spec: unknown {} `{name}`",
                kind.as_str()
            ))),
            _ => Err(Error::ConnectiveRule(format!(
                "spectec spec: ambiguous {} `{name}` ({} definitions)",
                kind.as_str(),
                found.len()
            ))),
        }
    }

    /// Lower one named relation into its small, relation-local environment.
    pub fn relation(&self, name: &str) -> Result<RelationEnv> {
        RelationEnv::relation(self.unique(DefinitionKind::Relation, name)?.ast())
    }

    /// Lower the entire AST into the shared HOL clause layer.
    pub fn lower(self) -> Result<HolSpec> {
        HolSpec::new(self)
    }
}

/// The complete common-clause lowering of one [`SpecTecSpec`].
///
/// This is deliberately not called “executable”: total lowering preserves
/// unsupported premises as opaque, underivable judgements. Use [`Self::lime`]
/// for the current maximally-fireable core, or [`Self::slice`] to state an
/// explicit premise-closed support boundary.
pub struct HolSpec {
    source: SpecTecSpec,
    clauses: Vec<Clause>,
    report: TotalReport,
}

impl HolSpec {
    pub fn new(source: SpecTecSpec) -> Result<Self> {
        let (clauses, report) = total_spec_clauses(source.defs())?;
        Ok(Self {
            source,
            clauses,
            report,
        })
    }

    /// Load and lower the bundled WebAssembly 3.0 specification.
    pub fn wasm3() -> Result<Self> {
        SpecTecSpec::wasm3().lower()
    }

    pub fn source(&self) -> &SpecTecSpec {
        &self.source
    }

    /// Honest whole-lowering census, including opaque/conditional residue.
    pub fn report(&self) -> &TotalReport {
        &self.report
    }

    pub fn clauses(&self) -> &[Clause] {
        &self.clauses
    }

    pub fn metas(&self) -> &[ClauseMeta] {
        &self.report.metas
    }

    /// Build the full rule set. Whole-set kernel operations require
    /// `wasm::lower::total::with_total_stack`.
    pub fn rule_set(&self) -> crate::metalogic::RuleSet<'static> {
        rule_set_of(self.clauses.clone())
    }

    /// Carve an explicit premise-closed subset of the complete lowering.
    pub fn slice(&self, name: impl Into<String>, seeds: &[SliceSeed]) -> Result<SpecSlice> {
        SpecSlice::carve(&self.clauses, self.metas(), name, seeds)
    }

    /// The current maximally-fireable, opaque-free WASM core.
    pub fn lime(&self) -> Result<SpecSlice> {
        lime_slice(&self.clauses, self.metas())
    }

    /// [`Self::lime`] packaged as the high-level derivation environment.
    pub fn lime_env(&self) -> Result<SliceEnv> {
        Ok(SliceEnv::new(self.lime()?))
    }
}

fn collect_paths(defs: &[SpecTecDef], prefix: &mut Vec<usize>, out: &mut Vec<Vec<usize>>) {
    for (i, def) in defs.iter().enumerate() {
        prefix.push(i);
        out.push(prefix.clone());
        if let SpecTecDef::Rec { ds } = def {
            collect_paths(ds, prefix, out);
        }
        prefix.pop();
    }
}

fn at_path<'a>(defs: &'a [SpecTecDef], path: &[usize]) -> &'a SpecTecDef {
    let mut level = defs;
    let mut found = None;
    for &i in path {
        let def = &level[i];
        found = Some(def);
        level = match def {
            SpecTecDef::Rec { ds } => ds,
            _ => &[],
        };
    }
    found.expect("SpecTec definition paths are non-empty")
}

fn def_kind(def: &SpecTecDef) -> DefinitionKind {
    match def {
        SpecTecDef::Typ { .. } => DefinitionKind::Type,
        SpecTecDef::Rel { .. } => DefinitionKind::Relation,
        SpecTecDef::Dec { .. } => DefinitionKind::Function,
        SpecTecDef::Gram { .. } => DefinitionKind::Grammar,
        SpecTecDef::Rec { .. } => DefinitionKind::RecursionGroup,
    }
}

fn def_name(def: &SpecTecDef) -> Option<&str> {
    match def {
        SpecTecDef::Typ { x, .. }
        | SpecTecDef::Rel { x, .. }
        | SpecTecDef::Dec { x, .. }
        | SpecTecDef::Gram { x, .. } => Some(x),
        SpecTecDef::Rec { .. } => None,
    }
}

fn name_of(def: &SpecTecDef) -> &str {
    def_name(def).expect("only named definitions enter the name index")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wasm3_ast_is_recursively_indexed() {
        let spec = SpecTecSpec::wasm3();
        assert!(spec.definitions().len() > spec.defs().len());
        assert_eq!(spec.type_families().len(), 207);
        let step = spec.unique(DefinitionKind::Relation, "Step_pure").unwrap();
        assert_eq!(step.name(), Some("Step_pure"));
        assert!(matches!(step.ast(), SpecTecDef::Rel { .. }));
        // A relation-local env is available for relations whose rules need no
        // whole-spec function/evaluator dependencies.
        assert!(spec.relation("Num_ok").is_ok());
    }

    #[test]
    fn whole_wasm_lowers_and_lime_is_honest() {
        crate::wasm::lower::total::with_total_stack(|| {
            let hol = HolSpec::wasm3().unwrap();
            assert_eq!(hol.clauses().len(), hol.report().total_clauses);
            let lime = hol.lime().unwrap();
            let report = lime.report();
            assert!(report.n_clauses > 0);
            assert_eq!(report.opaque_total(), 0);
            assert_eq!(report.n_clauses, report.n_clauses_clean);
        })
    }
}
