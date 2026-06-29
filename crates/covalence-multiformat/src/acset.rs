//! The **interchange schema** and its validation, built on the generic
//! [`covalence_acset`] library.
//!
//! The interchange schema is an *olog*: objects `Fact`/`Leaf` with foreign keys
//! and citation-edge spans. A [`FactStore`](crate::FactStore) is an *instance* (a
//! functor `schema → Set`). [`validate_store`] is the full structural check —
//! functoriality + path equations + acyclic citations (no circular proofs) +
//! the content-address laws (`fact_cid` injective, and each key = hash of body).
//! It validates **structure**, not theorem truth (that is `kernel_ingest`). A
//! dangling citation is a morphism left undefined: the functor fails to exist.
//! Since the schema is a geometric theory, this check is native to a geometric
//! (Coln) kernel.

use std::collections::{BTreeMap, HashMap};

use covalence_acset::{AcsetError, Instance, Part, Schema};

use crate::cid::Cid;
use crate::codec;
use crate::fact::DerivationFact;

// Re-export the generic ACSet surface so consumers reach it through this crate.
pub use covalence_acset::{Attr, AttrVal, Functor, Hom, PathEq, SchemaBuilder, SchemaError};

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
/// free quiver).
pub fn interchange_schema() -> Schema {
    Schema::builder()
        .object(ob::FACT)
        .object(ob::LEAF)
        .object(ob::FACT_CITE)
        .object(ob::ROOT_CITE)
        .attr_type("Logic")
        .attr_type("Codec")
        .attr_type("CidText")
        .hom("fact_axioms", ob::FACT, ob::LEAF)
        .hom("fact_deriv", ob::FACT, ob::LEAF)
        .hom("fc_src", ob::FACT_CITE, ob::FACT)
        .hom("fc_dst", ob::FACT_CITE, ob::FACT)
        .hom("rc_src", ob::ROOT_CITE, ob::FACT)
        .hom("rc_dst", ob::ROOT_CITE, ob::LEAF)
        .attr("fact_logic", ob::FACT, "Logic")
        .attr("fact_codec", ob::FACT, "Codec")
        .attr("fact_cid", ob::FACT, "CidText")
        .attr("leaf_codec", ob::LEAF, "Codec")
        .attr("leaf_cid", ob::LEAF, "CidText")
        .build()
}

/// Build the interchange [`Instance`] for `store` (see module docs). Returns
/// `None` if any stored body fails to decode. A derivation-fact assumption whose
/// target is absent from the store leaves `fc_dst` undefined — caught by
/// [`Instance::validate`] as a partial (non-functorial) morphism.
pub fn instance_of(store: &crate::FactStore) -> Option<Instance> {
    let mut facts: Vec<(Cid, DerivationFact)> = store
        .facts()
        .map(|(cid, body)| DerivationFact::decode(body).ok().map(|f| (cid, f)))
        .collect::<Option<_>>()?;
    facts.sort_by_key(|(c, _)| (c.codec, c.digest));

    let mut inst = Instance::new(interchange_schema());

    // Fact parts.
    let mut fact_part: HashMap<Cid, Part> = HashMap::new();
    for (cid, _) in &facts {
        let p = inst.add_part(ob::FACT);
        inst.set_label(p, cid.to_text());
        fact_part.insert(*cid, p);
    }

    // Distinct non-fact CIDs → Leaf parts (sorted for determinism).
    let mut leaf_set: BTreeMap<(u64, [u8; 32]), Cid> = BTreeMap::new();
    for (_, f) in &facts {
        for c in [f.axioms, f.derivation] {
            leaf_set.insert((c.codec, c.digest), c);
        }
        for a in &f.assumptions {
            if a.codec != codec::DERIVATION_FACT {
                leaf_set.insert((a.codec, a.digest), *a);
            }
        }
    }
    let mut leaf_part: HashMap<Cid, Part> = HashMap::new();
    for cid in leaf_set.into_values() {
        let p = inst.add_part(ob::LEAF);
        inst.set_label(p, cid.to_text());
        inst.set_attr(p, "leaf_codec", codec::name(cid.codec));
        inst.set_attr(p, "leaf_cid", cid.to_text());
        leaf_part.insert(cid, p);
    }

    // Fact attributes + axioms/derivation foreign keys.
    for (cid, f) in &facts {
        let fp = fact_part[cid];
        inst.set_attr(fp, "fact_logic", codec::logic::name(f.logic));
        inst.set_attr(fp, "fact_codec", codec::name(f.prop_codec));
        inst.set_attr(fp, "fact_cid", cid.to_text());
        inst.set_hom(fp, "fact_axioms", leaf_part[&f.axioms]);
        inst.set_hom(fp, "fact_deriv", leaf_part[&f.derivation]);
    }

    // Citation edges, one per assumption.
    for (cid, f) in &facts {
        let fp = fact_part[cid];
        for a in &f.assumptions {
            if a.codec == codec::DERIVATION_FACT {
                let e = inst.add_part(ob::FACT_CITE);
                inst.set_hom(e, "fc_src", fp);
                if let Some(&tp) = fact_part.get(a) {
                    inst.set_hom(e, "fc_dst", tp); // else left undefined → caught by validate
                }
            } else {
                let e = inst.add_part(ob::ROOT_CITE);
                inst.set_hom(e, "rc_src", fp);
                inst.set_hom(e, "rc_dst", leaf_part[a]);
            }
        }
    }
    Some(inst)
}

/// A way `validate_store` rejects a store.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum StoreError {
    #[error("not a valid instance: {0}")]
    Acset(#[from] AcsetError),
    #[error("a stored body failed to decode")]
    Decode,
    #[error("content-address law: key `{key}` is not the hash of its body (got {actual})")]
    CidMismatch { key: String, actual: String },
}

/// Full structural validation of `store` as an interchange ACSet instance:
/// functoriality + path equations, acyclicity of the citation graph (no circular
/// proofs), and the content-address laws (`fact_cid` injective, and each key
/// equals the BLAKE3 of its body). `Ok(())` iff the store is a valid instance.
/// Structural only — not theorem truth.
pub fn validate_store(store: &crate::FactStore) -> Result<(), Vec<StoreError>> {
    let Some(inst) = instance_of(store) else {
        return Err(vec![StoreError::Decode]);
    };

    let mut errs: Vec<StoreError> = Vec::new();
    if let Err(es) = inst.validate() {
        errs.extend(es.into_iter().map(StoreError::Acset));
    }
    if let Err(e) = inst.acyclic(ob::FACT_CITE, "fc_src", "fc_dst") {
        errs.push(StoreError::Acset(e));
    }
    if let Err(e) = inst.attr_injective("fact_cid") {
        errs.push(StoreError::Acset(e));
    }
    for (cid, body) in store.facts() {
        let actual = Cid::of(codec::DERIVATION_FACT, body);
        if actual != cid {
            errs.push(StoreError::CidMismatch {
                key: cid.to_text(),
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
    fn dangling_citation_is_partial() {
        let hol = hol_thm();
        let coln = coln_seq(hol.cid());
        let mut store = FactStore::new();
        store.put(&coln); // cited fact absent
        let errs = validate_store(&store).unwrap_err();
        assert!(errs.iter().any(|e| matches!(
            e,
            StoreError::Acset(AcsetError::UndefinedHom { hom: "fc_dst", .. })
        )));
    }

    #[test]
    fn cid_law_catches_a_corrupted_key() {
        let body = hol_thm().encode();
        let wrong = Cid::of(codec::DERIVATION_FACT, b"not the body");
        let mut store = FactStore::new();
        store.insert_raw(wrong, body);
        let errs = validate_store(&store).unwrap_err();
        assert!(
            errs.iter()
                .any(|e| matches!(e, StoreError::CidMismatch { .. }))
        );
    }
}
