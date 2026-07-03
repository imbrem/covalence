//! covalence ⇄ Coln interchange-format demo, driven through the
//! `covalence-multiformat` library API.
//!
//! Run:  `cargo run -p covalence-multiformat --example coln_bridge`

use covalence_multiformat::{CheckStep, Cid, DerivationFact, FactStore, codec};

fn section(title: &str) {
    println!("\n\x1b[1m{title}\x1b[0m");
    println!("{}", "─".repeat(title.chars().count()));
}

/// A reader that knows ONLY the multiformat structure — not the payload
/// semantics. It verifies the content hash and follows links regardless of
/// whether it understands the logic or the payload codec.
fn inspect(role: &str, body: &[u8], advertised: Cid) {
    println!(
        "  [{role}] reads envelope advertised as {}",
        advertised.to_text()
    );

    let recomputed = Cid::of(codec::DERIVATION_FACT, body);
    let ok = recomputed == advertised;
    println!(
        "      hash check: {} (recomputed {})",
        if ok { "VALID ✓" } else { "TAMPERED ✗" },
        recomputed
    );
    if !ok {
        return;
    }

    let f = DerivationFact::decode(body).expect("valid body");
    println!("      logic       : {}", codec::logic::name(f.logic));
    println!("      axiom-set   : {}", f.axioms);
    if matches!(f.prop_codec, codec::COV_HOL_THM | codec::COLN_GEOM_SEQ) {
        println!(
            "      statement   : [{}] {:?}",
            codec::name(f.prop_codec),
            String::from_utf8_lossy(&f.prop)
        );
    } else {
        println!(
            "      statement   : [{}] <{} bytes, codec opaque to me — skipping, hash still verified>",
            codec::name(f.prop_codec),
            f.prop.len()
        );
    }
    println!(
        "      derivation  : {}  (proof-irrelevant: only existence matters)",
        f.derivation
    );
    if f.assumptions.is_empty() {
        println!("      assumptions : none (proved outright)");
    } else {
        println!(
            "      assumptions : {} scoped hypotheses —",
            f.assumptions.len()
        );
        for a in &f.assumptions {
            println!("                    ↳ {}   {}", a, a.to_text());
        }
    }
}

fn main() {
    println!("covalence ⇄ Coln — multiformat derivation-fact interchange\n");
    println!(
        "wire CID = multibase('f') · multicodec(content-type) · multihash(blake3=0x1e, 32, digest)\n\
         neutral hash = plain BLAKE3 = covalence O256::blob; each side re-keys to its own identity."
    );

    // -- 1. covalence authors a classical HOL theorem -----------------------
    section("1. covalence authors a classical HOL theorem");
    let cov_thm = DerivationFact {
        logic: codec::logic::HOL,
        axioms: Cid::of(codec::AXIOM_SET, b"theory:HOL-classical/opentheory-base"),
        prop_codec: codec::COV_HOL_THM,
        prop: b"|- !p q. (p /\\ q) ==> (q /\\ p)".to_vec(),
        assumptions: vec![],
        derivation: Cid::of(
            codec::MM_DERIVATION,
            b"derivation:and-comm:CONJ;CONJUNCT2;CONJUNCT1",
        ),
    };
    let cov_thm_cid = cov_thm.cid();
    let cov_thm_body = cov_thm.encode();
    println!("  authored fact: {cov_thm_cid}");
    println!("  wire CID     : {}", cov_thm_cid.to_text());
    println!("  body size    : {} bytes", cov_thm_body.len());
    assert_eq!(
        DerivationFact::decode(&cov_thm_body).unwrap().cid(),
        cov_thm_cid
    );
    println!("  roundtrip    : decode → re-encode → identical CID ✓");

    // -- 2. Coln imports it (borrow classical power) ------------------------
    section("2. Coln authors a geometric sequent that BORROWS the HOL theorem");
    let coln_fact = DerivationFact {
        logic: codec::logic::GEOMETRIC,
        axioms: Cid::of(
            codec::AXIOM_SET,
            b"theory:geometric-base/arithmetic-universe",
        ),
        prop_codec: codec::COLN_GEOM_SEQ,
        prop: b"x:Comm |- mul-commutes(x)".to_vec(),
        // the bridge: cite covalence's Thm by CID, plus an explicit classical axiom
        assumptions: vec![
            Cid::of(codec::AXIOM_SET, b"assumption:classical/LEM"),
            cov_thm_cid,
        ],
        derivation: Cid::of(
            codec::MM_DERIVATION,
            b"derivation:import(cov_thm)+geometric-glue",
        ),
    };
    let coln_fact_cid = coln_fact.cid();
    let coln_fact_body = coln_fact.encode();
    println!("  authored fact: {coln_fact_cid}");
    println!("  wire CID     : {}", coln_fact_cid.to_text());
    println!(
        "  imports covalence Thm as scoped hypothesis → {}",
        cov_thm_cid.to_text()
    );

    // -- 3. the other side reads it, multiformat-style ---------------------
    section("3. each side reads the other's fact (self-describing → partial interop)");
    println!("\n  Coln reading the covalence-authored HOL theorem:");
    inspect("coln ", &cov_thm_body, cov_thm_cid);
    println!("\n  covalence reading the Coln-authored geometric sequent:");
    inspect("covln", &coln_fact_body, coln_fact_cid);
    let cited = coln_fact.assumptions.contains(&cov_thm_cid);
    println!(
        "\n  cross-link resolves: Coln's fact cites covalence's exact Thm CID? {}",
        if cited {
            "YES ✓ — the bridge holds"
        } else {
            "no"
        }
    );

    // -- 4. tamper-evidence -------------------------------------------------
    section("4. content-addressing is tamper-evident");
    let mut tampered = cov_thm_body.clone();
    *tampered.last_mut().unwrap() ^= 0x01;
    println!("  flip one bit of the covalence fact body, keep the old CID:");
    inspect("coln ", &tampered, cov_thm_cid);

    // -- 5. the hinge, made literal ----------------------------------------
    section("5. the hinge, made literal");
    println!(
        "  covalence waist : \"∃ derivation D of P under Ax (mod Γ)\"  ==  this DerivationFact\n  \
         Coln database   : \"proof checking is constraint checking\"   ==  does CID(fact) ∈ store?"
    );

    // -- 6. run the hinge ---------------------------------------------------
    section("6. proof-checking AS a constraint query (executed)");
    let mut store = FactStore::new();
    store.put(&cov_thm);
    let coln_in_store = store.put(&coln_fact);
    println!("  store now holds {} facts.\n", store.len());
    println!("  check(Coln sequent) — recurse over citations until trust-roots:");
    let render = &mut |depth: usize, step: CheckStep| {
        let pad = "  ".repeat(depth + 3);
        match step {
            CheckStep::Fact { cid, logic } => {
                println!("{pad}✓ {cid}  [{}]", codec::logic::name(logic))
            }
            CheckStep::TrustRoot(cid) => {
                println!("{pad}• trust-root {cid}  (scoped assumption — leaf)")
            }
        }
    };
    match store.check_traced(coln_in_store, render) {
        Ok(()) => {
            println!("  ⇒ ADMISSIBLE ✓  (every citation resolved across the kernel boundary)")
        }
        Err(e) => println!("  ⇒ REJECTED ✗  {e}"),
    }

    println!("\n  now drop covalence's Thm from the store and re-check the SAME Coln fact:");
    let mut broken = FactStore::new();
    broken.put(&coln_fact);
    match broken.check_traced(coln_in_store, render) {
        Ok(()) => println!("  ⇒ ADMISSIBLE ✓"),
        Err(e) => println!(
            "  ⇒ REJECTED ✗  {e}\n     (referential integrity = proof well-formedness: a dangling citation is an open goal)"
        ),
    }

    section("next layers (not in this demo)");
    println!("  · ed25519-signed envelopes (covalence-sig) — federation / authored Thm exchange");
    println!("  · wire-CID ↦ internal identity (COV_ROOT Name256 / Coln Sedimentree address)");
    println!("  · ACSet-schema-as-geometric-theory soundness-certificate facts");
    println!("  · CAR-style bundles: a fact plus the transitive closure of its witnesses");
}
