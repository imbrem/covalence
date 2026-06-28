//! Meta-theoretic (structural) validation of the interchange as an ACSet.
//!
//! The interchange schema is an *olog*: objects `Fact`/`Leaf` with foreign keys
//! and citation-edge spans. A `FactStore` is an *instance* (a functor
//! `schema → Set`). "Valid interchange" = "valid instance": every morphism is a
//! total function into existing parts. A dangling citation = a morphism that is
//! not a function = the functor fails to exist. This is the geometric-kernel-
//! native reading of the same integrity `FactStore::check` enforces imperatively.
//!
//! Run:  `cargo run -p covalence-multiformat --example acset_validate`

use covalence_multiformat::acset::{instance_of, interchange_schema, ob};
use covalence_multiformat::{Cid, DerivationFact, FactStore, codec};

fn section(title: &str) {
    println!("\n\x1b[1m{title}\x1b[0m");
    println!("{}", "─".repeat(title.chars().count()));
}

fn hol_thm() -> DerivationFact {
    DerivationFact {
        logic: codec::logic::HOL,
        axioms: Cid::of(codec::AXIOM_SET, b"theory:HOL-classical"),
        prop_codec: codec::COV_HOL_THM,
        prop: b"|- x = x".to_vec(),
        assumptions: vec![],
        derivation: Cid::of(codec::MM_DERIVATION, b"derivation:refl"),
    }
}

fn coln_seq(imports: Cid) -> DerivationFact {
    DerivationFact {
        logic: codec::logic::GEOMETRIC,
        axioms: Cid::of(codec::AXIOM_SET, b"theory:geometric-base"),
        prop_codec: codec::COLN_GEOM_SEQ,
        prop: b"x:Comm |- mul-commutes(x)".to_vec(),
        assumptions: vec![
            Cid::of(codec::AXIOM_SET, b"assumption:classical/LEM"),
            imports,
        ],
        derivation: Cid::of(codec::MM_DERIVATION, b"derivation:import+glue"),
    }
}

fn show_validation(store: &FactStore) {
    let inst = instance_of(store).expect("bodies decode");
    println!(
        "  instance parts: Fact={}  Leaf={}  FactCite={}  RootCite={}",
        inst.nparts(ob::FACT),
        inst.nparts(ob::LEAF),
        inst.nparts(ob::FACT_CITE),
        inst.nparts(ob::ROOT_CITE),
    );
    match inst.validate() {
        Ok(()) => println!("  validate: VALID INSTANCE ✓ (the functor schema → Set exists)"),
        Err(errs) => {
            println!("  validate: NOT AN INSTANCE ✗");
            for e in &errs {
                // annotate the dangling source fact with its label
                if let covalence_multiformat::AcsetError::DanglingHom {
                    src, hom: "fc_dst", ..
                } = e
                {
                    let who = inst.label(ob::FACT, *src).unwrap_or("?");
                    println!("    · {e}\n      (citing fact: {who})");
                } else {
                    println!("    · {e}");
                }
            }
        }
    }
}

fn main() {
    println!("covalence-multiformat — interchange as an ACSet (meta-theoretic validation)\n");

    // -- the schema (an olog) ----------------------------------------------
    section("interchange schema (olog): objects, foreign keys, attributes");
    let s = interchange_schema();
    println!("  objects   : {}", s.objects.join(", "));
    println!("  attr types: {}", s.attr_types.join(", "));
    for h in &s.homs {
        println!("  hom       : {:<12} {} → {}", h.name, h.dom, h.cod);
    }
    for a in &s.attrs {
        println!("  attr      : {:<12} {} → {}", a.name, a.dom, a.cod);
    }

    // -- a valid store is a valid instance ---------------------------------
    section("1. a well-formed store IS a valid instance");
    let hol = hol_thm();
    let coln = coln_seq(hol.cid());
    let mut store = FactStore::new();
    store.put(&hol);
    store.put(&coln);
    println!("  store: HOL `x = x`, plus a geometric sequent citing it + LEM.");
    show_validation(&store);

    // -- a dangling citation breaks functoriality --------------------------
    section("2. drop the cited HOL fact — the functor fails to exist");
    let mut broken = FactStore::new();
    broken.put(&coln); // the cited HOL fact is absent
    println!("  store: only the geometric sequent; its HOL citation is missing.");
    show_validation(&broken);

    section("what this validates");
    println!("  structure (referential integrity of the fact DAG), as instance-conformance.");
    println!("  NOT theorem truth (kernel_ingest) nor content hashes (the cid layer).");
    println!("  The schema is a geometric theory — this check is native to Coln's kernel.");
}
