//! A small, generic **ACSet** (attributed C-set) library.
//!
//! An ACSet schema is a finitely-presented category (an *olog*): objects are
//! entity tables, morphisms are functional relationships, optionally with **path
//! equations** (commuting diagrams), plus attribute types. An *instance* is a
//! functor `schema → Set`: each object gets a set of parts (rows), each morphism
//! a total function between them, respecting the equations.
//!
//! High-level surface:
//! - [`Schema::builder`] — declare objects, morphisms, attributes, equations.
//! - [`Instance`] — order-independent: [`add_part`](Instance::add_part) returns a
//!   typed [`Part`]; [`set_hom`](Instance::set_hom) / [`set_attr`](Instance::set_attr)
//!   fill it in any order; [`follow`](Instance::follow) navigates paths.
//! - [`Instance::validate`] — is this a valid functor? (totality + range +
//!   equations). Plus [`acyclic`](Instance::acyclic) and
//!   [`attr_injective`](Instance::attr_injective) law checks.
//! - [`Instance::pullback`] — Δ functorial data migration along a [`Functor`]
//!   (objects, morphisms, and mapped attributes).
//!
//! Object/morphism/attribute names are `&'static str` (compile-time schemas);
//! attribute values are the typed [`AttrVal`]. See the generated open-work index for what is
//! deferred (Σ/Π migration, dynamic names, a query layer).

use std::collections::HashMap;
use std::fmt;

pub mod datalog;
pub mod lattice;
pub mod query;
pub use datalog::{DatalogError, Program, Rule, Solution};
pub use lattice::{JoinSemilattice, MinDist, lfp};
pub use query::{Match, Query, QueryBuilder, QueryError};

// ===========================================================================
// Errors
// ===========================================================================

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
    #[error("morphism `{hom}` is undefined at `{dom}` part {src} — a partial function")]
    UndefinedHom {
        hom: &'static str,
        dom: &'static str,
        src: usize,
    },
    #[error("morphism `{hom}` part {src} maps outside `{cod}`: {image} ∉ [0,{cod_parts})")]
    DanglingHom {
        hom: &'static str,
        cod: &'static str,
        src: usize,
        image: usize,
        cod_parts: usize,
    },
    #[error("attribute `{attr}` is undefined at `{dom}` part {src}")]
    UndefinedAttr {
        attr: &'static str,
        dom: &'static str,
        src: usize,
    },
    #[error("equation `{eq}` fails at `{dom}` part {src}: lhs ↦ {lhs:?}, rhs ↦ {rhs:?}")]
    EquationViolation {
        eq: &'static str,
        dom: &'static str,
        src: usize,
        lhs: Option<usize>,
        rhs: Option<usize>,
    },
    #[error("graph on `{obj}` has a cycle through parts {cycle:?}")]
    Cyclic {
        obj: &'static str,
        cycle: Vec<usize>,
    },
    #[error("attribute `{attr}` is not injective: parts {a} and {b} share `{value}`")]
    NonInjectiveAttr {
        attr: &'static str,
        a: usize,
        b: usize,
        value: String,
    },
}

/// Ways a [`Functor`] migration fails.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum MigrationError {
    #[error("functor has no image for source object `{obj}`")]
    MissingObject { obj: &'static str },
    #[error("functor has no image for source morphism `{hom}`")]
    MissingHom { hom: &'static str },
    #[error("functor is ill-typed: {detail}")]
    BadFunctor { detail: String },
}

// ===========================================================================
// Schema (an olog)
// ===========================================================================

/// A morphism (foreign key) `dom → cod`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Hom {
    pub name: &'static str,
    pub dom: &'static str,
    pub cod: &'static str,
}

/// An attribute `dom → cod`, where `cod` is a value type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Attr {
    pub name: &'static str,
    pub dom: &'static str,
    pub cod: &'static str,
}

/// A typed attribute value.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum AttrVal {
    Str(String),
    Int(i64),
    Bytes(Vec<u8>),
}

impl From<String> for AttrVal {
    fn from(s: String) -> Self {
        AttrVal::Str(s)
    }
}
impl From<&str> for AttrVal {
    fn from(s: &str) -> Self {
        AttrVal::Str(s.to_owned())
    }
}
impl From<i64> for AttrVal {
    fn from(n: i64) -> Self {
        AttrVal::Int(n)
    }
}
impl From<Vec<u8>> for AttrVal {
    fn from(b: Vec<u8>) -> Self {
        AttrVal::Bytes(b)
    }
}

impl fmt::Display for AttrVal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AttrVal::Str(s) => write!(f, "{s}"),
            AttrVal::Int(n) => write!(f, "{n}"),
            AttrVal::Bytes(b) => {
                write!(f, "0x")?;
                for byte in b {
                    write!(f, "{byte:02x}")?;
                }
                Ok(())
            }
        }
    }
}

/// A path equation: two morphism paths (composed left-to-right) that must
/// denote the same function.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PathEq {
    pub name: &'static str,
    pub lhs: Vec<&'static str>,
    pub rhs: Vec<&'static str>,
}

/// A finitely-presented category plus attribute types. Build via
/// [`Schema::builder`].
#[derive(Debug, Clone, Default)]
pub struct Schema {
    objects: Vec<&'static str>,
    attr_types: Vec<&'static str>,
    homs: Vec<Hom>,
    attrs: Vec<Attr>,
    equations: Vec<PathEq>,
}

/// Fluent builder for a [`Schema`].
#[derive(Debug, Default)]
pub struct SchemaBuilder {
    schema: Schema,
}

impl Schema {
    /// Start a new schema.
    pub fn builder() -> SchemaBuilder {
        SchemaBuilder::default()
    }

    pub fn objects(&self) -> &[&'static str] {
        &self.objects
    }
    pub fn attr_types(&self) -> &[&'static str] {
        &self.attr_types
    }
    pub fn homs(&self) -> &[Hom] {
        &self.homs
    }
    pub fn attrs(&self) -> &[Attr] {
        &self.attrs
    }
    pub fn equations(&self) -> &[PathEq] {
        &self.equations
    }

    /// Look up a morphism by name.
    pub fn hom(&self, name: &str) -> Option<&Hom> {
        self.homs.iter().find(|h| h.name == name)
    }
    /// Look up an attribute by name.
    pub fn attr(&self, name: &str) -> Option<&Attr> {
        self.attrs.iter().find(|a| a.name == name)
    }

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

    /// Check the schema is well-formed: unique names, declared object /
    /// attribute-type references, well-typed equations.
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
            for obj in [h.dom, h.cod] {
                if !self.objects.contains(&obj) {
                    errs.push(SchemaError::UndeclaredObject { hom: h.name, obj });
                }
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

impl SchemaBuilder {
    /// Declare an entity object.
    pub fn object(mut self, name: &'static str) -> Self {
        self.schema.objects.push(name);
        self
    }
    /// Declare an attribute (value) type.
    pub fn attr_type(mut self, name: &'static str) -> Self {
        self.schema.attr_types.push(name);
        self
    }
    /// Declare a morphism `name: dom → cod`.
    pub fn hom(mut self, name: &'static str, dom: &'static str, cod: &'static str) -> Self {
        self.schema.homs.push(Hom { name, dom, cod });
        self
    }
    /// Declare an attribute `name: dom → cod` (cod is an attribute type).
    pub fn attr(mut self, name: &'static str, dom: &'static str, cod: &'static str) -> Self {
        self.schema.attrs.push(Attr { name, dom, cod });
        self
    }
    /// Declare a path equation `lhs == rhs` (paths composed left-to-right).
    pub fn equation(
        mut self,
        name: &'static str,
        lhs: &[&'static str],
        rhs: &[&'static str],
    ) -> Self {
        self.schema.equations.push(PathEq {
            name,
            lhs: lhs.to_vec(),
            rhs: rhs.to_vec(),
        });
        self
    }
    /// Finish building.
    pub fn build(self) -> Schema {
        self.schema
    }
}

// ===========================================================================
// Instance (a functor schema → Set)
// ===========================================================================

/// A typed handle to a part (row) of an object.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Part {
    pub obj: &'static str,
    pub index: usize,
}

/// An ACSet instance over a [`Schema`].
#[derive(Debug, Clone)]
pub struct Instance {
    schema: Schema,
    nparts: HashMap<&'static str, usize>,
    homs: HashMap<&'static str, Vec<Option<usize>>>,
    attrs: HashMap<&'static str, Vec<Option<AttrVal>>>,
    labels: HashMap<Part, String>,
}

impl Instance {
    /// An empty instance of `schema`.
    pub fn new(schema: Schema) -> Self {
        let nparts = schema.objects.iter().map(|o| (*o, 0usize)).collect();
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

    /// The schema this instance is over.
    pub fn schema(&self) -> &Schema {
        &self.schema
    }

    /// Number of parts of `obj`.
    pub fn nparts(&self, obj: &str) -> usize {
        self.nparts.get(obj).copied().unwrap_or(0)
    }

    /// Add one part to `obj`, returning a handle. Morphism/attribute columns
    /// whose domain is `obj` grow with an unset (`None`) slot.
    pub fn add_part(&mut self, obj: &'static str) -> Part {
        let hom_cols: Vec<&'static str> = self
            .schema
            .homs
            .iter()
            .filter(|h| h.dom == obj)
            .map(|h| h.name)
            .collect();
        let attr_cols: Vec<&'static str> = self
            .schema
            .attrs
            .iter()
            .filter(|a| a.dom == obj)
            .map(|a| a.name)
            .collect();
        for n in hom_cols {
            self.homs.get_mut(n).expect("hom column").push(None);
        }
        for n in attr_cols {
            self.attrs.get_mut(n).expect("attr column").push(None);
        }
        let index = *self.nparts.get(obj).unwrap_or(&0);
        self.nparts.insert(obj, index + 1);
        Part { obj, index }
    }

    /// Set `hom(src) = dst`. Panics if the morphism is unknown or `src`/`dst`
    /// do not match its declared domain/codomain (a schema-contract violation).
    pub fn set_hom(&mut self, src: Part, hom: &'static str, dst: Part) {
        let h = self
            .schema
            .hom(hom)
            .unwrap_or_else(|| panic!("unknown morphism `{hom}`"));
        assert_eq!(
            h.dom, src.obj,
            "morphism `{hom}` domain is `{}`, not `{}`",
            h.dom, src.obj
        );
        assert_eq!(
            h.cod, dst.obj,
            "morphism `{hom}` codomain is `{}`, not `{}`",
            h.cod, dst.obj
        );
        self.homs.get_mut(hom).expect("hom column")[src.index] = Some(dst.index);
    }

    /// Set `attr(part) = value`. Panics if the attribute is unknown or its
    /// domain does not match `part`.
    pub fn set_attr(&mut self, part: Part, attr: &'static str, value: impl Into<AttrVal>) {
        let a = self
            .schema
            .attr(attr)
            .unwrap_or_else(|| panic!("unknown attribute `{attr}`"));
        assert_eq!(
            a.dom, part.obj,
            "attribute `{attr}` domain is `{}`, not `{}`",
            a.dom, part.obj
        );
        self.attrs.get_mut(attr).expect("attr column")[part.index] = Some(value.into());
    }

    /// Attach a display label to a part.
    pub fn set_label(&mut self, part: Part, label: impl Into<String>) {
        self.labels.insert(part, label.into());
    }
    /// A part's label, if any.
    pub fn label(&self, part: Part) -> Option<&str> {
        self.labels.get(&part).map(String::as_str)
    }

    /// The target of `hom` at `part`, if set and in range.
    pub fn hom_image(&self, part: Part, hom: &str) -> Option<Part> {
        let h = self.schema.hom(hom)?;
        let img = (*self.homs.get(hom)?.get(part.index)?)?;
        (img < self.nparts(h.cod)).then_some(Part {
            obj: h.cod,
            index: img,
        })
    }

    /// The value of `attr` at `part`, if set.
    pub fn attr_value(&self, part: Part, attr: &str) -> Option<&AttrVal> {
        self.attrs.get(attr)?.get(part.index)?.as_ref()
    }

    /// Iterate every part of `obj`.
    pub fn parts(&self, obj: &'static str) -> impl Iterator<Item = Part> + '_ {
        (0..self.nparts(obj)).map(move |index| Part { obj, index })
    }

    /// Follow a path of morphisms from `start`, returning the endpoint or `None`
    /// if any step is undefined.
    pub fn follow(&self, start: Part, path: &[&'static str]) -> Option<Part> {
        let mut cur = start;
        for &h in path {
            cur = self.hom_image(cur, h)?;
        }
        Some(cur)
    }

    fn compose(&self, path: &[&'static str]) -> (&'static str, Vec<Option<usize>>) {
        let dom = self.schema.hom(path[0]).expect("hom in schema").dom;
        let images = (0..self.nparts(dom))
            .map(|i| {
                self.follow(Part { obj: dom, index: i }, path)
                    .map(|p| p.index)
            })
            .collect();
        (dom, images)
    }

    /// Check this assignment is a valid functor: every morphism/attribute total
    /// and in range, every path equation satisfied.
    pub fn validate(&self) -> Result<(), Vec<AcsetError>> {
        let mut errs = Vec::new();
        for h in &self.schema.homs {
            let col = &self.homs[h.name];
            let cod_parts = self.nparts(h.cod);
            for (src, slot) in col.iter().enumerate() {
                match *slot {
                    None => errs.push(AcsetError::UndefinedHom {
                        hom: h.name,
                        dom: h.dom,
                        src,
                    }),
                    Some(image) if image >= cod_parts => errs.push(AcsetError::DanglingHom {
                        hom: h.name,
                        cod: h.cod,
                        src,
                        image,
                        cod_parts,
                    }),
                    Some(_) => {}
                }
            }
        }
        for a in &self.schema.attrs {
            for (src, slot) in self.attrs[a.name].iter().enumerate() {
                if slot.is_none() {
                    errs.push(AcsetError::UndefinedAttr {
                        attr: a.name,
                        dom: a.dom,
                        src,
                    });
                }
            }
        }
        for e in &self.schema.equations {
            let (dom, lhs) = self.compose(&e.lhs);
            let (_, rhs) = self.compose(&e.rhs);
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
    /// parts of `V` and check it is acyclic. Undefined edges are skipped.
    pub fn acyclic(
        &self,
        edge: &'static str,
        src_hom: &'static str,
        dst_hom: &'static str,
    ) -> Result<(), AcsetError> {
        let v = self.schema.hom(src_hom).expect("hom").cod;
        let nv = self.nparts(v);
        let mut adj: Vec<Vec<usize>> = vec![Vec::new(); nv];
        for e in 0..self.nparts(edge) {
            let edge_part = Part {
                obj: edge,
                index: e,
            };
            if let (Some(s), Some(d)) = (
                self.hom_image(edge_part, src_hom),
                self.hom_image(edge_part, dst_hom),
            ) {
                adj[s.index].push(d.index);
            }
        }
        let mut color = vec![0u8; nv]; // 0 white, 1 gray, 2 black
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
                if color[w] == 0
                    && let Some(c) = dfs(w, adj, color, stack)
                {
                    return Some(c);
                }
            }
            stack.pop();
            color[u] = 2;
            None
        }
        for u in 0..nv {
            if color[u] == 0
                && let Some(cycle) = dfs(u, &adj, &mut color, &mut stack)
            {
                return Err(AcsetError::Cyclic { obj: v, cycle });
            }
        }
        Ok(())
    }

    /// Check an attribute is injective (a mono): distinct parts have distinct
    /// values. Unset values are ignored.
    pub fn attr_injective(&self, attr: &'static str) -> Result<(), AcsetError> {
        let col = self.attrs.get(attr).map(Vec::as_slice).unwrap_or(&[]);
        let mut seen: HashMap<&AttrVal, usize> = HashMap::new();
        for (i, slot) in col.iter().enumerate() {
            if let Some(v) = slot {
                if let Some(&j) = seen.get(v) {
                    return Err(AcsetError::NonInjectiveAttr {
                        attr,
                        a: j,
                        b: i,
                        value: v.to_string(),
                    });
                }
                seen.insert(v, i);
            }
        }
        Ok(())
    }

    /// Δ functorial data migration: pull `self` (a `cod`-instance) back along
    /// `functor: dom → cod` to an instance over `dom_schema`. Each `dom` object's
    /// parts are those of its image; each `dom` morphism is the composite of its
    /// image path; each mapped `dom` attribute copies its image attribute's
    /// values.
    pub fn pullback(
        &self,
        functor: &Functor,
        dom_schema: Schema,
    ) -> Result<Instance, MigrationError> {
        let mut out = Instance::new(dom_schema.clone());
        // Parts: out(d) := self(F d), by identity on indices.
        for &d in dom_schema.objects() {
            let c = functor
                .object(d)
                .ok_or(MigrationError::MissingObject { obj: d })?;
            for i in 0..self.nparts(c) {
                let p = out.add_part(d);
                if let Some(l) = self.label(Part { obj: c, index: i }) {
                    out.set_label(p, l.to_owned());
                }
            }
        }
        // Morphisms: out(h) := self(F h) as a composite.
        for h in dom_schema.homs() {
            let path = functor
                .hom(h.name)
                .ok_or(MigrationError::MissingHom { hom: h.name })?;
            let src_c = functor
                .object(h.dom)
                .ok_or(MigrationError::MissingObject { obj: h.dom })?;
            for i in 0..self.nparts(src_c) {
                if let Some(end) = self.follow(
                    Part {
                        obj: src_c,
                        index: i,
                    },
                    path,
                ) {
                    out.set_hom(
                        Part {
                            obj: h.dom,
                            index: i,
                        },
                        h.name,
                        Part {
                            obj: h.cod,
                            index: end.index,
                        },
                    );
                }
            }
        }
        // Attributes: out(a) := self(F a), copied by index over the mapped object.
        for a in dom_schema.attrs() {
            let Some(c_attr) = functor.attr(a.name) else {
                continue;
            };
            let src_c = functor
                .object(a.dom)
                .ok_or(MigrationError::MissingObject { obj: a.dom })?;
            for i in 0..self.nparts(src_c) {
                if let Some(v) = self.attr_value(
                    Part {
                        obj: src_c,
                        index: i,
                    },
                    c_attr,
                ) {
                    out.set_attr(
                        Part {
                            obj: a.dom,
                            index: i,
                        },
                        a.name,
                        v.clone(),
                    );
                }
            }
        }
        Ok(out)
    }
}

// ===========================================================================
// Functor (for migration)
// ===========================================================================

/// A schema functor `dom → cod`: maps each source object to a target object and
/// each source morphism to a target *path*. Build via [`Functor::builder`].
#[derive(Debug, Clone, Default)]
pub struct Functor {
    objects: Vec<(&'static str, &'static str)>,
    homs: Vec<(&'static str, Vec<&'static str>)>,
    attrs: Vec<(&'static str, &'static str)>,
}

/// Fluent builder for a [`Functor`].
#[derive(Debug, Default)]
pub struct FunctorBuilder {
    functor: Functor,
}

impl Functor {
    pub fn builder() -> FunctorBuilder {
        FunctorBuilder::default()
    }
    /// Image of a source object.
    pub fn object(&self, d: &str) -> Option<&'static str> {
        self.objects.iter().find(|(s, _)| *s == d).map(|(_, t)| *t)
    }
    /// Image (a target path) of a source morphism.
    pub fn hom(&self, d: &str) -> Option<&[&'static str]> {
        self.homs
            .iter()
            .find(|(s, _)| *s == d)
            .map(|(_, p)| p.as_slice())
    }
    /// Image (a target attribute) of a source attribute.
    pub fn attr(&self, d: &str) -> Option<&'static str> {
        self.attrs.iter().find(|(s, _)| *s == d).map(|(_, t)| *t)
    }
}

impl FunctorBuilder {
    /// Map source object `d` to target object `c`.
    pub fn object(mut self, d: &'static str, c: &'static str) -> Self {
        self.functor.objects.push((d, c));
        self
    }
    /// Map source morphism `d` to the target path `path` (composed left-to-right).
    pub fn hom(mut self, d: &'static str, path: &[&'static str]) -> Self {
        self.functor.homs.push((d, path.to_vec()));
        self
    }
    /// Map source attribute `d` to the target attribute `c`.
    pub fn attr(mut self, d: &'static str, c: &'static str) -> Self {
        self.functor.attrs.push((d, c));
        self
    }
    pub fn build(self) -> Functor {
        self.functor
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn graph_schema() -> Schema {
        Schema::builder()
            .object("V")
            .object("E")
            .hom("src", "E", "V")
            .hom("dst", "E", "V")
            .build()
    }

    #[test]
    fn schema_check_ok_and_bad() {
        assert_eq!(graph_schema().check(), Ok(()));
        let bad = Schema::builder().object("A").hom("f", "A", "Nope").build();
        assert!(bad.check().is_err());
    }

    #[test]
    fn instance_build_and_validate() {
        let mut g = Instance::new(graph_schema());
        let v0 = g.add_part("V");
        let v1 = g.add_part("V");
        let e = g.add_part("E");
        g.set_hom(e, "src", v0);
        g.set_hom(e, "dst", v1);
        assert_eq!(g.validate(), Ok(()));
        assert_eq!(g.follow(e, &["dst"]), Some(v1));
    }

    #[test]
    fn missing_hom_is_partial() {
        let mut g = Instance::new(graph_schema());
        g.add_part("V");
        let e = g.add_part("E");
        g.set_hom(e, "src", Part { obj: "V", index: 0 });
        // dst left unset
        let errs = g.validate().unwrap_err();
        assert!(
            errs.iter()
                .any(|e| matches!(e, AcsetError::UndefinedHom { hom: "dst", .. }))
        );
    }

    #[test]
    fn acyclicity() {
        let mut g = Instance::new(graph_schema());
        let v0 = g.add_part("V");
        let v1 = g.add_part("V");
        let e0 = g.add_part("E");
        g.set_hom(e0, "src", v0);
        g.set_hom(e0, "dst", v1);
        assert!(g.acyclic("E", "src", "dst").is_ok());
        let e1 = g.add_part("E");
        g.set_hom(e1, "src", v1);
        g.set_hom(e1, "dst", v0); // 0 → 1 → 0
        assert!(matches!(
            g.acyclic("E", "src", "dst"),
            Err(AcsetError::Cyclic { .. })
        ));
    }

    #[test]
    fn path_equation() {
        let schema = Schema::builder()
            .object("A")
            .object("B")
            .object("C")
            .hom("f", "A", "B")
            .hom("g", "B", "C")
            .hom("h", "A", "C")
            .equation("tri", &["f", "g"], &["h"])
            .build();
        assert_eq!(schema.check(), Ok(()));
        let mut bad = Instance::new(schema);
        let a = bad.add_part("A");
        let b = bad.add_part("B");
        let c0 = bad.add_part("C");
        let c1 = bad.add_part("C");
        bad.set_hom(a, "f", b);
        bad.set_hom(b, "g", c0);
        bad.set_hom(a, "h", c1); // f;g = C0 ≠ C1 = h
        assert!(
            bad.validate()
                .unwrap_err()
                .iter()
                .any(|e| matches!(e, AcsetError::EquationViolation { .. }))
        );
    }

    #[test]
    fn pullback_reverses_a_graph() {
        // Build a graph 0 → 1, then pull back along the edge-reversing functor.
        let mut g = Instance::new(graph_schema());
        let v0 = g.add_part("V");
        let v1 = g.add_part("V");
        let e = g.add_part("E");
        g.set_hom(e, "src", v0);
        g.set_hom(e, "dst", v1);

        // F: graph → graph, identity on objects, src ↦ dst and dst ↦ src.
        let rev = Functor::builder()
            .object("V", "V")
            .object("E", "E")
            .hom("src", &["dst"])
            .hom("dst", &["src"])
            .build();
        let r = g.pullback(&rev, graph_schema()).unwrap();
        assert_eq!(r.validate(), Ok(()));
        // the edge now runs 1 → 0
        assert_eq!(r.follow(Part { obj: "E", index: 0 }, &["src"]), Some(v1));
        assert_eq!(r.follow(Part { obj: "E", index: 0 }, &["dst"]), Some(v0));
    }

    fn tagged_schema() -> Schema {
        Schema::builder()
            .object("P")
            .attr_type("V")
            .attr("tag", "P", "V")
            .build()
    }

    #[test]
    fn typed_attrs_and_injectivity() {
        let mut i = Instance::new(tagged_schema());
        let a = i.add_part("P");
        i.set_attr(a, "tag", 7i64);
        let b = i.add_part("P");
        i.set_attr(b, "tag", "hello");
        assert_eq!(i.attr_value(a, "tag"), Some(&AttrVal::Int(7)));
        assert_eq!(i.validate(), Ok(()));
        assert!(i.attr_injective("tag").is_ok());
        // a duplicate value breaks injectivity
        let c = i.add_part("P");
        i.set_attr(c, "tag", 7i64);
        assert!(matches!(
            i.attr_injective("tag"),
            Err(AcsetError::NonInjectiveAttr { .. })
        ));
    }

    #[test]
    fn pullback_migrates_attributes() {
        let mut c = Instance::new(tagged_schema());
        let p0 = c.add_part("P");
        c.set_attr(p0, "tag", 7i64);
        let p1 = c.add_part("P");
        c.set_attr(p1, "tag", "hello");

        let f = Functor::builder()
            .object("P", "P")
            .attr("tag", "tag")
            .build();
        let d = c.pullback(&f, tagged_schema()).unwrap();
        assert_eq!(d.validate(), Ok(()));
        assert_eq!(
            d.attr_value(Part { obj: "P", index: 0 }, "tag"),
            Some(&AttrVal::Int(7))
        );
        assert_eq!(
            d.attr_value(Part { obj: "P", index: 1 }, "tag"),
            Some(&AttrVal::Str("hello".into()))
        );
        assert_eq!(d.parts("P").count(), 2);
    }
}
