//! Meta-theoretic validation of the interchange as an **ACSet instance**.
//!
//! An ACSet schema is a finitely-presented category (an *olog*): objects are
//! entity tables, morphisms are functional relationships (foreign keys), and an
//! *instance* is a functor `schema → Set` — it populates each object with parts
//! (rows) and each morphism with a **total function** between those parts. A
//! schema is a (finite-limit / geometric) theory; a valid instance is a model of
//! it. So validating the interchange *structurally* is exactly checking that a
//! [`FactStore`](crate::FactStore) is a valid instance of the interchange schema
//! — a model / constraint-satisfaction check, native to a geometric kernel.
//!
//! This validates **structure** (referential integrity of the fact DAG), not the
//! logical truth of theorems (that is `kernel_ingest`'s job) nor the
//! content-address hashes (the [`cid`](crate::cid) layer). A *dangling citation*
//! — a derivation-fact that cites another fact absent from the store — shows up
//! here as a morphism that is **not a total function into `Fact`**: the functor
//! fails to exist. Referential integrity = proof well-formedness, restated
//! categorically.

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

/// An ACSet schema: a finitely-presented category plus attribute types.
/// (Path/commutativity equations are not modelled yet — see SKELETONS.)
#[derive(Debug, Clone)]
pub struct Schema {
    pub objects: Vec<&'static str>,
    pub attr_types: Vec<&'static str>,
    pub homs: Vec<Hom>,
    pub attrs: Vec<Attr>,
}

/// A way an instance fails to be a valid functor of its schema.
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
}

/// An ACSet instance over a [`Schema`]: a functor `schema → Set`.
#[derive(Debug, Clone)]
pub struct Instance {
    schema: Schema,
    nparts: HashMap<&'static str, usize>,
    homs: HashMap<&'static str, Vec<usize>>,
    attrs: HashMap<&'static str, Vec<String>>,
    /// Display labels for `(object, part)` — purely for legible diagnostics.
    labels: HashMap<(&'static str, usize), String>,
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
    pub fn nparts(&self, obj: &'static str) -> usize {
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

    /// Check this assignment is a valid functor of the schema: every morphism and
    /// attribute is a *total* function whose images land in existing parts.
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
        if errs.is_empty() { Ok(()) } else { Err(errs) }
    }

    /// The label set for `(obj, part)`, if any.
    pub fn label(&self, obj: &'static str, part: usize) -> Option<&str> {
        self.labels.get(&(obj, part)).map(String::as_str)
    }

    /// The schema this instance is over.
    pub fn schema(&self) -> &Schema {
        &self.schema
    }
}

// ===========================================================================
// The interchange schema (an olog) + builder from a FactStore
// ===========================================================================

/// Object/attribute names for the interchange schema.
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

/// The interchange schema: `Fact` and `Leaf` entities, with `fact_axioms` /
/// `fact_deriv` foreign keys and the two citation-edge spans `FactCite` /
/// `RootCite`.
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
    }
}

/// Build the interchange [`Instance`] for `store`: `Fact` parts are the stored
/// facts; `Leaf` parts are the distinct non-fact CIDs they reference
/// (axiom-sets, witnesses, trust-root assumptions); citation edges record each
/// fact's assumptions. A derivation-fact assumption whose target is absent from
/// the store becomes a `FactCite` whose `fc_dst` points outside `Fact` — caught
/// by [`Instance::validate`] as a dangling reference.
///
/// Returns `None` if any stored body fails to decode.
pub fn instance_of(store: &crate::FactStore) -> Option<Instance> {
    // Decode all facts; order deterministically by (codec, digest).
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

    // Distinct non-fact CIDs referenced anywhere → Leaf parts (sorted).
    let mut leaf_set: BTreeMap<(u64, [u8; 32]), Cid> = BTreeMap::new();
    let mut note_leaf = |c: Cid| {
        leaf_set.insert((c.codec, c.digest), c);
    };
    for (_, f) in &facts {
        note_leaf(f.axioms);
        note_leaf(f.derivation);
        for a in &f.assumptions {
            if a.codec != codec::DERIVATION_FACT {
                note_leaf(*a);
            }
        }
    }
    let leaves: Vec<Cid> = leaf_set.into_values().collect();
    let leaf_index: HashMap<Cid, usize> = leaves.iter().enumerate().map(|(i, c)| (*c, i)).collect();

    let mut inst = Instance::new(interchange_schema());

    // Fact parts + their attributes and axioms/derivation foreign keys.
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

    // Leaf parts + attributes.
    for (i, cid) in leaves.iter().enumerate() {
        inst.add_part(ob::LEAF);
        inst.set_label(ob::LEAF, i, cid.to_text());
        inst.push_attr("leaf_codec", codec::name(cid.codec));
        inst.push_attr("leaf_cid", cid.to_text());
    }

    // Citation edges, one part per assumption.
    for (src, (_, f)) in facts.iter().enumerate() {
        for a in &f.assumptions {
            if a.codec == codec::DERIVATION_FACT {
                // dangling target → index nfacts, i.e. outside [0, nfacts)
                let dst = fact_index.get(a).copied().unwrap_or(nfacts);
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

/// Validate `store` as an interchange ACSet instance — meta-theoretic
/// (structural) validation of the interchange. `Ok(())` iff it is a valid
/// functor of the interchange schema.
pub fn validate_store(store: &crate::FactStore) -> Result<(), Vec<AcsetError>> {
    match instance_of(store) {
        Some(inst) => inst.validate(),
        None => Err(vec![AcsetError::NonTotalHom {
            hom: "<decode>",
            dom: ob::FACT,
            expected: store.len(),
            got: 0,
        }]),
    }
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
    fn valid_store_is_a_valid_instance() {
        let hol = hol_thm();
        let coln = coln_seq(hol.cid());
        let mut store = FactStore::new();
        store.put(&hol);
        store.put(&coln);

        let inst = instance_of(&store).unwrap();
        // 2 facts; 1 fact→fact citation (coln→hol); 1 fact→leaf citation (LEM).
        assert_eq!(inst.nparts(ob::FACT), 2);
        assert_eq!(inst.nparts(ob::FACT_CITE), 1);
        assert_eq!(inst.nparts(ob::ROOT_CITE), 1);
        assert_eq!(inst.validate(), Ok(()));
    }

    #[test]
    fn dangling_citation_breaks_functoriality() {
        let hol = hol_thm();
        let coln = coln_seq(hol.cid());
        let mut store = FactStore::new();
        store.put(&coln); // hol (the cited fact) deliberately absent

        let errs = validate_store(&store).unwrap_err();
        // the fact→fact citation's fc_dst points outside Fact.
        assert!(
            errs.iter()
                .any(|e| matches!(e, AcsetError::DanglingHom { hom: "fc_dst", .. }))
        );
    }

    #[test]
    fn schema_shape() {
        let s = interchange_schema();
        assert_eq!(s.objects.len(), 4);
        assert_eq!(s.homs.len(), 6);
        // every hom's dom/cod is a declared object
        for h in &s.homs {
            assert!(s.objects.contains(&h.dom) && s.objects.contains(&h.cod));
        }
    }
}
