//! Meta-theoretic validation of the interchange as an **ACSet instance**.
//!
//! An ACSet schema is a finitely-presented category (an *olog*): objects are
//! entity tables, morphisms are functional relationships (foreign keys),
//! optionally with **path equations** (commuting diagrams), and an *instance* is
//! a functor `schema → Set` — it populates each object with parts (rows) and each
//! morphism with a **total function** between those parts, respecting the
//! equations. A schema is a (finite-limit / geometric) theory; a valid instance
//! is a model of it. So validating the interchange *structurally* is exactly
//! checking that a [`FactStore`](crate::FactStore) is a valid instance of the
//! interchange schema — a model / constraint-satisfaction check, native to a
//! geometric kernel.
//!
//! [`validate_store`] runs the full interchange check: functoriality (every
//! morphism total, images in range), the schema's path equations, **acyclicity**
//! of the citation DAG (no circular proofs), and the content-address attribute
//! laws (`Fact.cid` equals the hash of its body, and is injective). It does
//! **not** check the logical truth of theorems (that is `kernel_ingest`'s job).
//! A *dangling citation* is a morphism that is not a total function into `Fact`
//! — the functor fails to exist. Referential integrity = proof well-formedness,
//! restated categorically.

use std::collections::{BTreeMap, HashMap};

use crate::cid::Cid;
use crate::codec;
use crate::fact::DerivationFact;

// ===========================================================================
// Generic ACSet core
// ===========================================================================

/// A morphism (foreign key) `dom → cod` between two schema objects.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Hom {
    pub name: &'static str,
    pub dom: &'static str,
    pub cod: &'static str,
}

/// An attribute `dom → cod`, where `cod` is a fixed value type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Attr {
    pub name: &'static str,
    pub dom: &'static str,
    pub cod: &'static str,
}

/// A path equation: two morphism paths (composed left-to-right) that must denote
/// the same function. Both paths share a domain and a codomain.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PathEq {
    pub name: &'static str,
    pub lhs: Vec<&'static str>,
    pub rhs: Vec<&'static str>,
}

/// An ACSet schema: a finitely-presented category (objects, morphisms, path
/// equations) plus attribute types.
#[derive(Debug, Clone)]
pub struct Schema {
    pub objects: Vec<&'static str>,
    pub attr_types: Vec<&'static str>,
    pub homs: Vec<Hom>,
    pub attrs: Vec<Attr>,
    pub equations: Vec<PathEq>,
}

/// Ways a [`Schema`] is itself ill-formed (independent of any instance).
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum SchemaError {
    #[error("duplicate {kind} name `{name}`")]
    DuplicateName {
        kind: &'static str,
        name: &'static str,
    },
    #[error("morphism `{hom}` references undeclared object `{obj}`")]
    UndeclaredObject {
        hom: &'static str,
        obj: &'static str,
    },
    #[error("attribute `{attr}` references undeclared {kind} `{name}`")]
    UndeclaredAttr {
        attr: &'static str,
        kind: &'static str,
        name: &'static str,
    },
    #[error("equation `{eq}` uses unknown morphism `{hom}`")]
    UnknownHom { eq: &'static str, hom: &'static str },
    #[error("equation `{eq}` does not compose: {detail}")]
    BadComposite { eq: &'static str, detail: String },
}

/// Ways an instance fails to be a valid functor of its schema.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum AcsetError {
    #[error("morphism `{hom}` is not total: {got} images for {expected} `{dom}` part(s)")]
    NonTotalHom {
        hom: &'static str,
        dom: &'static str,
        expected: usize,
        got: usize,
    },
    #[error(
        "morphism `{hom}` part {src} maps outside `{cod}`: image {image} ∉ [0,{cod_parts}) \
         — a dangling reference"
    )]
    DanglingHom {
        hom: &'static str,
        cod: &'static str,
        src: usize,
        image: usize,
        cod_parts: usize,
    },
    #[error("attribute `{attr}` is not total: {got} values for {expected} `{dom}` part(s)")]
    NonTotalAttr {
        attr: &'static str,
        dom: &'static str,
        expected: usize,
        got: usize,
    },
    #[error("equation `{eq}` fails at `{dom}` part {src}: lhs ↦ {lhs:?}, rhs ↦ {rhs:?}")]
    EquationViolation {
        eq: &'static str,
        dom: &'static str,
        src: usize,
        lhs: Option<usize>,
        rhs: Option<usize>,
    },
    #[error("citation graph has a cycle through `{obj}` parts {cycle:?} — a circular proof")]
    Cyclic {
        obj: &'static str,
        cycle: Vec<usize>,
    },
    #[error("attribute `{attr}` is not injective: parts {a} and {b} share value `{value}`")]
    NonInjectiveAttr {
        attr: &'static str,
        a: usize,
        b: usize,
        value: String,
    },
    #[error("content-address law: `{part_label}` body hashes to {actual}, not its key")]
    CidMismatch { part_label: String, actual: String },
}

/// An ACSet instance over a [`Schema`]: a functor `schema → Set`.
#[derive(Debug, Clone)]
pub struct Instance {
    schema: Schema,
    nparts: HashMap<&'static str, usize>,
    homs: HashMap<&'static str, Vec<usize>>,
    attrs: HashMap<&'static str, Vec<String>>,
    labels: HashMap<(&'static str, usize), String>,
}

impl Schema {
    /// Look up a morphism by name.
    pub fn hom(&self, name: &str) -> Option<&Hom> {
        self.homs.iter().find(|h| h.name == name)
    }

    /// Domain and codomain of a composite path, or an error describing where it
    /// fails to chain.
    fn path_dom_cod(
        &self,
        eq: &'static str,
        path: &[&'static str],
    ) -> Result<(&'static str, &'static str), SchemaError> {
        let first = self
            .hom(path[0])
            .ok_or(SchemaError::UnknownHom { eq, hom: path[0] })?;
        let dom = first.dom;
        let mut cod = first.cod;
        for &h in &path[1..] {
            let next = self.hom(h).ok_or(SchemaError::UnknownHom { eq, hom: h })?;
            if next.dom != cod {
                return Err(SchemaError::BadComposite {
                    eq,
                    detail: format!("`{h}` has domain `{}`, expected `{cod}`", next.dom),
                });
            }
            cod = next.cod;
        }
        Ok((dom, cod))
    }

    /// Check the schema is itself well-formed: unique names, declared
    /// objects/attribute-types, and well-typed equations.
    pub fn check(&self) -> Result<(), Vec<SchemaError>> {
        let mut errs = Vec::new();
        let dup = |kind,
                   name: &'static str,
                   seen: &mut Vec<&'static str>,
                   errs: &mut Vec<SchemaError>| {
            if seen.contains(&name) {
                errs.push(SchemaError::DuplicateName { kind, name });
            } else {
                seen.push(name);
            }
        };
        let (mut so, mut st, mut sh, mut sa) = (Vec::new(), Vec::new(), Vec::new(), Vec::new());
        for o in &self.objects {
            dup("object", o, &mut so, &mut errs);
        }
        for t in &self.attr_types {
            dup("attr-type", t, &mut st, &mut errs);
        }
        for h in &self.homs {
            dup("morphism", h.name, &mut sh, &mut errs);
            if !self.objects.contains(&h.dom) {
                errs.push(SchemaError::UndeclaredObject {
                    hom: h.name,
                    obj: h.dom,
                });
            }
            if !self.objects.contains(&h.cod) {
                errs.push(SchemaError::UndeclaredObject {
                    hom: h.name,
                    obj: h.cod,
                });
            }
        }
        for a in &self.attrs {
            dup("attribute", a.name, &mut sa, &mut errs);
            if !self.objects.contains(&a.dom) {
                errs.push(SchemaError::UndeclaredAttr {
                    attr: a.name,
                    kind: "object",
                    name: a.dom,
                });
            }
            if !self.attr_types.contains(&a.cod) {
                errs.push(SchemaError::UndeclaredAttr {
                    attr: a.name,
                    kind: "attr-type",
                    name: a.cod,
                });
            }
        }
        for e in &self.equations {
            if e.lhs.is_empty() || e.rhs.is_empty() {
                errs.push(SchemaError::BadComposite {
                    eq: e.name,
                    detail: "empty path".into(),
                });
                continue;
            }
            match (
                self.path_dom_cod(e.name, &e.lhs),
                self.path_dom_cod(e.name, &e.rhs),
            ) {
                (Ok((ld, lc)), Ok((rd, rc))) => {
                    if ld != rd || lc != rc {
                        errs.push(SchemaError::BadComposite {
                            eq: e.name,
                            detail: format!("lhs {ld}→{lc} vs rhs {rd}→{rc}"),
                        });
                    }
                }
                (Err(x), _) | (_, Err(x)) => errs.push(x),
            }
        }
        if errs.is_empty() { Ok(()) } else { Err(errs) }
    }
}

impl Instance {
    /// An empty instance of `schema`.
    pub fn new(schema: Schema) -> Self {
        let nparts = schema.objects.iter().map(|o| (*o, 0)).collect();
        let homs = schema.homs.iter().map(|h| (h.name, Vec::new())).collect();
        let attrs = schema.attrs.iter().map(|a| (a.name, Vec::new())).collect();
        Self {
            schema,
            nparts,
            homs,
            attrs,
            labels: HashMap::new(),
        }
    }

    /// Add one part to `obj`, returning its index.
    pub fn add_part(&mut self, obj: &'static str) -> usize {
        let n = self.nparts.get_mut(obj).expect("object in schema");
        let idx = *n;
        *n += 1;
        idx
    }

    /// Number of parts of `obj`.
    pub fn nparts(&self, obj: &str) -> usize {
        self.nparts.get(obj).copied().unwrap_or(0)
    }

    /// Append the next image for morphism `hom` (callers push in part order).
    pub fn push_hom(&mut self, hom: &'static str, image: usize) {
        self.homs.get_mut(hom).expect("hom in schema").push(image);
    }

    /// Append the next value for attribute `attr` (callers push in part order).
    pub fn push_attr(&mut self, attr: &'static str, value: impl Into<String>) {
        self.attrs
            .get_mut(attr)
            .expect("attr in schema")
            .push(value.into());
    }

    /// Label `(obj, part)` for diagnostics.
    pub fn set_label(&mut self, obj: &'static str, part: usize, label: impl Into<String>) {
        self.labels.insert((obj, part), label.into());
    }

    /// The label set for `(obj, part)`, if any.
    pub fn label(&self, obj: &'static str, part: usize) -> Option<&str> {
        self.labels.get(&(obj, part)).map(String::as_str)
    }

    /// Attribute value column.
    pub fn attr(&self, name: &str) -> &[String] {
        self.attrs.get(name).map(Vec::as_slice).unwrap_or(&[])
    }

    /// The schema this instance is over.
    pub fn schema(&self) -> &Schema {
        &self.schema
    }

    /// Compose a path of morphisms into a partial function on the domain's parts;
    /// an element is `None` where some step's image is out of range (dangling).
    fn compose(&self, path: &[&'static str]) -> (&'static str, &'static str, Vec<Option<usize>>) {
        let first = self.schema.hom(path[0]).expect("hom in schema");
        let dom = first.dom;
        let mut cod = first.cod;
        let mut cur: Vec<Option<usize>> = (0..self.nparts(dom)).map(Some).collect();
        for &h in path {
            let hom = self.schema.hom(h).expect("hom in schema");
            let map = &self.homs[h];
            let ncod = self.nparts(hom.cod);
            cur = cur
                .iter()
                .map(|opt| {
                    opt.and_then(|i| map.get(i).copied())
                        .filter(|&img| img < ncod)
                })
                .collect();
            cod = hom.cod;
        }
        (dom, cod, cur)
    }

    /// Check this assignment is a valid functor of the schema: every morphism and
    /// attribute is a *total* function whose images land in existing parts, and
    /// every path equation holds.
    pub fn validate(&self) -> Result<(), Vec<AcsetError>> {
        let mut errs = Vec::new();
        for h in &self.schema.homs {
            let map = &self.homs[h.name];
            let expected = self.nparts(h.dom);
            if map.len() != expected {
                errs.push(AcsetError::NonTotalHom {
                    hom: h.name,
                    dom: h.dom,
                    expected,
                    got: map.len(),
                });
            }
            let cod_parts = self.nparts(h.cod);
            for (src, &image) in map.iter().enumerate() {
                if image >= cod_parts {
                    errs.push(AcsetError::DanglingHom {
                        hom: h.name,
                        cod: h.cod,
                        src,
                        image,
                        cod_parts,
                    });
                }
            }
        }
        for a in &self.schema.attrs {
            let vals = &self.attrs[a.name];
            let expected = self.nparts(a.dom);
            if vals.len() != expected {
                errs.push(AcsetError::NonTotalAttr {
                    attr: a.name,
                    dom: a.dom,
                    expected,
                    got: vals.len(),
                });
            }
        }
        for e in &self.schema.equations {
            let (dom, _, lhs) = self.compose(&e.lhs);
            let (_, _, rhs) = self.compose(&e.rhs);
            for src in 0..lhs.len().min(rhs.len()) {
                if lhs[src] != rhs[src] {
                    errs.push(AcsetError::EquationViolation {
                        eq: e.name,
                        dom,
                        src,
                        lhs: lhs[src],
                        rhs: rhs[src],
                    });
                }
            }
        }
        if errs.is_empty() { Ok(()) } else { Err(errs) }
    }

    /// Treat the span `(src_hom, dst_hom): edge → V` as a directed graph on the
    /// parts of `V` and check it is acyclic. On a cycle, returns the offending
    /// vertices. Dangling edges (image out of range) are skipped.
    pub fn acyclic_span(
        &self,
        edge: &'static str,
        src_hom: &'static str,
        dst_hom: &'static str,
    ) -> Result<(), AcsetError> {
        let v = self.schema.hom(src_hom).expect("hom").cod;
        let nv = self.nparts(v);
        let (s, d) = (&self.homs[src_hom], &self.homs[dst_hom]);
        let mut adj: Vec<Vec<usize>> = vec![Vec::new(); nv];
        for e in 0..self.nparts(edge) {
            let (from, to) = (s[e], d[e]);
            if from < nv && to < nv {
                adj[from].push(to);
            }
        }
        // 0 = white, 1 = gray (on stack), 2 = black
        let mut color = vec![0u8; nv];
        let mut stack: Vec<usize> = Vec::new();
        fn dfs(
            u: usize,
            adj: &[Vec<usize>],
            color: &mut [u8],
            stack: &mut Vec<usize>,
        ) -> Option<Vec<usize>> {
            color[u] = 1;
            stack.push(u);
            for &w in &adj[u] {
                if color[w] == 1 {
                    let start = stack.iter().position(|&x| x == w).unwrap_or(0);
                    return Some(stack[start..].to_vec());
                }
                if color[w] == 0 {
                    if let Some(c) = dfs(w, adj, color, stack) {
                        return Some(c);
                    }
                }
            }
            stack.pop();
            color[u] = 2;
            None
        }
        for u in 0..nv {
            if color[u] == 0 {
                if let Some(cycle) = dfs(u, &adj, &mut color, &mut stack) {
                    return Err(AcsetError::Cyclic { obj: v, cycle });
                }
            }
        }
        Ok(())
    }

    /// Check an attribute is injective (a mono): distinct parts have distinct
    /// values.
    pub fn attr_injective(&self, attr: &'static str) -> Result<(), AcsetError> {
        let vals = self.attr(attr);
        let mut seen: HashMap<&str, usize> = HashMap::new();
        for (i, v) in vals.iter().enumerate() {
            if let Some(&j) = seen.get(v.as_str()) {
                return Err(AcsetError::NonInjectiveAttr {
                    attr,
                    a: j,
                    b: i,
                    value: v.clone(),
                });
            }
            seen.insert(v, i);
        }
        Ok(())
    }
}

// ===========================================================================
// The interchange schema (an olog) + builder + full validation
// ===========================================================================

/// Object names for the interchange schema.
pub mod ob {
    /// A derivation-fact (a stored envelope).
    pub const FACT: &str = "Fact";
    /// An externally-referenced object (axiom-set, witness, trust-root leaf).
    pub const LEAF: &str = "Leaf";
    /// A fact → fact citation edge (a derivation-fact assumption).
    pub const FACT_CITE: &str = "FactCite";
    /// A fact → leaf citation edge (a scoped trust-root assumption).
    pub const ROOT_CITE: &str = "RootCite";
}

/// The interchange schema. The citation graph (`FactCite`) is required to be
/// acyclic by [`validate_store`]; the schema carries no path equations (it is a
/// free quiver), so the equation machinery is exercised by other schemas.
pub fn interchange_schema() -> Schema {
    Schema {
        objects: vec![ob::FACT, ob::LEAF, ob::FACT_CITE, ob::ROOT_CITE],
        attr_types: vec!["Logic", "Codec", "CidText"],
        homs: vec![
            Hom {
                name: "fact_axioms",
                dom: ob::FACT,
                cod: ob::LEAF,
            },
            Hom {
                name: "fact_deriv",
                dom: ob::FACT,
                cod: ob::LEAF,
            },
            Hom {
                name: "fc_src",
                dom: ob::FACT_CITE,
                cod: ob::FACT,
            },
            Hom {
                name: "fc_dst",
                dom: ob::FACT_CITE,
                cod: ob::FACT,
            },
            Hom {
                name: "rc_src",
                dom: ob::ROOT_CITE,
                cod: ob::FACT,
            },
            Hom {
                name: "rc_dst",
                dom: ob::ROOT_CITE,
                cod: ob::LEAF,
            },
        ],
        attrs: vec![
            Attr {
                name: "fact_logic",
                dom: ob::FACT,
                cod: "Logic",
            },
            Attr {
                name: "fact_codec",
                dom: ob::FACT,
                cod: "Codec",
            },
            Attr {
                name: "fact_cid",
                dom: ob::FACT,
                cod: "CidText",
            },
            Attr {
                name: "leaf_codec",
                dom: ob::LEAF,
                cod: "Codec",
            },
            Attr {
                name: "leaf_cid",
                dom: ob::LEAF,
                cod: "CidText",
            },
        ],
        equations: vec![],
    }
}

/// Build the interchange [`Instance`] for `store` (see module docs). Returns
/// `None` if any stored body fails to decode.
pub fn instance_of(store: &crate::FactStore) -> Option<Instance> {
    let mut facts: Vec<(Cid, DerivationFact)> = store
        .facts()
        .map(|(cid, body)| DerivationFact::decode(body).ok().map(|f| (cid, f)))
        .collect::<Option<_>>()?;
    facts.sort_by_key(|(c, _)| (c.codec, c.digest));
    let fact_index: HashMap<Cid, usize> = facts
        .iter()
        .enumerate()
        .map(|(i, (c, _))| (*c, i))
        .collect();
    let nfacts = facts.len();

    let mut leaf_set: BTreeMap<(u64, [u8; 32]), Cid> = BTreeMap::new();
    for (_, f) in &facts {
        leaf_set.insert((f.axioms.codec, f.axioms.digest), f.axioms);
        leaf_set.insert((f.derivation.codec, f.derivation.digest), f.derivation);
        for a in &f.assumptions {
            if a.codec != codec::DERIVATION_FACT {
                leaf_set.insert((a.codec, a.digest), *a);
            }
        }
    }
    let leaves: Vec<Cid> = leaf_set.into_values().collect();
    let leaf_index: HashMap<Cid, usize> = leaves.iter().enumerate().map(|(i, c)| (*c, i)).collect();

    let mut inst = Instance::new(interchange_schema());

    for (i, (cid, _)) in facts.iter().enumerate() {
        inst.add_part(ob::FACT);
        inst.set_label(ob::FACT, i, cid.to_text());
    }
    for (cid, f) in &facts {
        inst.push_attr("fact_logic", codec::logic::name(f.logic));
        inst.push_attr("fact_codec", codec::name(f.prop_codec));
        inst.push_attr("fact_cid", cid.to_text());
        inst.push_hom("fact_axioms", leaf_index[&f.axioms]);
        inst.push_hom("fact_deriv", leaf_index[&f.derivation]);
    }
    for (i, cid) in leaves.iter().enumerate() {
        inst.add_part(ob::LEAF);
        inst.set_label(ob::LEAF, i, cid.to_text());
        inst.push_attr("leaf_codec", codec::name(cid.codec));
        inst.push_attr("leaf_cid", cid.to_text());
    }
    for (src, (_, f)) in facts.iter().enumerate() {
        for a in &f.assumptions {
            if a.codec == codec::DERIVATION_FACT {
                let dst = fact_index.get(a).copied().unwrap_or(nfacts); // dangling → out of range
                inst.add_part(ob::FACT_CITE);
                inst.push_hom("fc_src", src);
                inst.push_hom("fc_dst", dst);
            } else {
                inst.add_part(ob::ROOT_CITE);
                inst.push_hom("rc_src", src);
                inst.push_hom("rc_dst", leaf_index[a]);
            }
        }
    }
    Some(inst)
}

/// Full structural validation of `store` as an interchange ACSet instance:
/// functoriality + path equations, acyclicity of the citation graph (no circular
/// proofs), and the content-address attribute laws (`fact_cid` injective, and
/// each fact's key equals the hash of its body). `Ok(())` iff the store is a
/// valid instance of the interchange schema. Structural only — not theorem truth.
pub fn validate_store(store: &crate::FactStore) -> Result<(), Vec<AcsetError>> {
    let Some(inst) = instance_of(store) else {
        return Err(vec![AcsetError::NonTotalHom {
            hom: "<decode>",
            dom: ob::FACT,
            expected: store.len(),
            got: 0,
        }]);
    };

    let mut errs = inst.validate().err().unwrap_or_default();

    // No circular proofs: the fact→fact citation graph must be acyclic.
    if let Err(e) = inst.acyclic_span(ob::FACT_CITE, "fc_src", "fc_dst") {
        errs.push(e);
    }

    // Content-addressed keys are unique (fact_cid is a mono).
    if let Err(e) = inst.attr_injective("fact_cid") {
        errs.push(e);
    }

    // Content-address law: each stored key equals the BLAKE3 of its body.
    for (cid, body) in store.facts() {
        let actual = Cid::of(codec::DERIVATION_FACT, body);
        if actual != cid {
            errs.push(AcsetError::CidMismatch {
                part_label: cid.to_text(),
                actual: actual.to_text(),
            });
        }
    }

    if errs.is_empty() { Ok(()) } else { Err(errs) }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{DerivationFact, FactStore, codec};

    fn hol_thm() -> DerivationFact {
        DerivationFact {
            logic: codec::logic::HOL,
            axioms: Cid::of(codec::AXIOM_SET, b"theory:HOL"),
            prop_codec: codec::COV_HOL_THM,
            prop: b"|- x = x".to_vec(),
            assumptions: vec![],
            derivation: Cid::of(codec::MM_DERIVATION, b"derivation:refl"),
        }
    }

    fn coln_seq(imports: Cid) -> DerivationFact {
        DerivationFact {
            logic: codec::logic::GEOMETRIC,
            axioms: Cid::of(codec::AXIOM_SET, b"theory:geom"),
            prop_codec: codec::COLN_GEOM_SEQ,
            prop: b"x:Comm |- comm(x)".to_vec(),
            assumptions: vec![Cid::of(codec::AXIOM_SET, b"assumption:LEM"), imports],
            derivation: Cid::of(codec::MM_DERIVATION, b"derivation:glue"),
        }
    }

    #[test]
    fn interchange_schema_is_well_formed() {
        assert_eq!(interchange_schema().check(), Ok(()));
    }

    #[test]
    fn valid_store_passes_full_validation() {
        let hol = hol_thm();
        let coln = coln_seq(hol.cid());
        let mut store = FactStore::new();
        store.put(&hol);
        store.put(&coln);

        let inst = instance_of(&store).unwrap();
        assert_eq!(inst.nparts(ob::FACT), 2);
        assert_eq!(inst.nparts(ob::FACT_CITE), 1);
        assert_eq!(inst.nparts(ob::ROOT_CITE), 1);
        assert_eq!(validate_store(&store), Ok(()));
    }

    #[test]
    fn dangling_citation_breaks_functoriality() {
        let hol = hol_thm();
        let coln = coln_seq(hol.cid());
        let mut store = FactStore::new();
        store.put(&coln); // cited fact absent
        let errs = validate_store(&store).unwrap_err();
        assert!(
            errs.iter()
                .any(|e| matches!(e, AcsetError::DanglingHom { hom: "fc_dst", .. }))
        );
    }

    #[test]
    fn cid_law_catches_a_corrupted_key() {
        let hol = hol_thm();
        let body = hol.encode();
        let wrong = Cid::of(codec::DERIVATION_FACT, b"not the body");
        let mut store = FactStore::new();
        store.insert_raw(wrong, body); // key disagrees with body
        let errs = validate_store(&store).unwrap_err();
        assert!(
            errs.iter()
                .any(|e| matches!(e, AcsetError::CidMismatch { .. }))
        );
    }

    #[test]
    fn acyclicity_detects_a_cycle() {
        // Toy graph schema: V vertices, E edges with src/dst, on a 2-cycle.
        let schema = Schema {
            objects: vec!["V", "E"],
            attr_types: vec![],
            homs: vec![
                Hom {
                    name: "src",
                    dom: "E",
                    cod: "V",
                },
                Hom {
                    name: "dst",
                    dom: "E",
                    cod: "V",
                },
            ],
            attrs: vec![],
            equations: vec![],
        };
        let mut inst = Instance::new(schema);
        inst.add_part("V");
        inst.add_part("V");
        inst.add_part("E"); // 0 → 1
        inst.push_hom("src", 0);
        inst.push_hom("dst", 1);
        inst.add_part("E"); // 1 → 0
        inst.push_hom("src", 1);
        inst.push_hom("dst", 0);
        assert!(matches!(
            inst.acyclic_span("E", "src", "dst"),
            Err(AcsetError::Cyclic { .. })
        ));
    }

    #[test]
    fn path_equation_is_checked() {
        // Commuting square: f;g == h on a single element.
        let schema = Schema {
            objects: vec!["A", "B", "C"],
            attr_types: vec![],
            homs: vec![
                Hom {
                    name: "f",
                    dom: "A",
                    cod: "B",
                },
                Hom {
                    name: "g",
                    dom: "B",
                    cod: "C",
                },
                Hom {
                    name: "h",
                    dom: "A",
                    cod: "C",
                },
            ],
            attrs: vec![],
            equations: vec![PathEq {
                name: "tri",
                lhs: vec!["f", "g"],
                rhs: vec!["h"],
            }],
        };
        assert_eq!(schema.check(), Ok(()));

        // consistent instance: A0 -f-> B0 -g-> C0, and h(A0) = C0
        let mut ok = Instance::new(schema.clone());
        ok.add_part("A");
        ok.add_part("B");
        ok.add_part("C");
        ok.push_hom("f", 0);
        ok.push_hom("g", 0);
        ok.push_hom("h", 0);
        assert_eq!(ok.validate(), Ok(()));

        // inconsistent: add a second C and point h elsewhere
        let mut bad = Instance::new(schema);
        bad.add_part("A");
        bad.add_part("B");
        bad.add_part("C");
        bad.add_part("C");
        bad.push_hom("f", 0);
        bad.push_hom("g", 0); // f;g (A0) = C0
        bad.push_hom("h", 1); // h(A0) = C1 ≠ C0
        let errs = bad.validate().unwrap_err();
        assert!(
            errs.iter()
                .any(|e| matches!(e, AcsetError::EquationViolation { eq: "tri", .. }))
        );
    }

    #[test]
    fn bad_schema_is_rejected() {
        let s = Schema {
            objects: vec!["A"],
            attr_types: vec![],
            homs: vec![Hom {
                name: "f",
                dom: "A",
                cod: "Nope",
            }],
            attrs: vec![],
            equations: vec![],
        };
        assert!(s.check().is_err());
    }
}
