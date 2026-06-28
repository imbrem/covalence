//! Option 2: bind the interchange format to the *real* covalence HOL kernel.
//!
//! The `coln_bridge` example simulates both sides in Rust. This one makes the
//! covalence end genuine: an envelope is authored from an actual
//! `covalence-core` `Thm`, and "ingesting" it means **independently
//! reconstructing that theorem in a fresh kernel** and checking the envelope
//! against it — then re-keying the verified neutral wire CID to covalence's
//! internal `Name256`.
//!
//! Run:  `cargo run -p covalence-multiformat --example kernel_ingest`

use covalence_init::hash::{UnitObsHasher, hash_term};
use covalence_init::{HolLightCtx, Term, Thm};
use covalence_multiformat::{Cid, DerivationFact, codec, identity};

fn section(title: &str) {
    println!("\n\x1b[1m{title}\x1b[0m");
    println!("{}", "─".repeat(title.chars().count()));
}

/// Build a genuine kernel theorem: `⊢ (p ∧ q) = (p ∧ q)` via HOL reflexivity.
/// (A real `Thm` value — the only paths to one are the kernel's primitive rules.)
fn build_thm() -> Thm {
    let ctx = HolLightCtx::new();
    let p = Term::free("p", ctx.bool_type());
    let q = Term::free("q", ctx.bool_type());
    let conj = ctx.mk_and(p, q);
    Thm::refl(conj).expect("refl is total on well-typed terms")
}

/// Author an envelope *from* a real theorem: the statement payload is the
/// kernel's own rendering of the conclusion, and the derivation-witness CID is
/// pinned to the conclusion's real `covalence-init` term hash.
fn author(thm: &Thm) -> DerivationFact {
    let concl = thm.concl();
    let term_hash = hash_term(concl, &UnitObsHasher);
    DerivationFact {
        logic: codec::logic::HOL,
        axioms: Cid::of(codec::AXIOM_SET, b"theory:HOL-classical/core"),
        prop_codec: codec::COV_HOL_THM,
        prop: format!("{concl}").into_bytes(),
        assumptions: vec![], // refl: proved outright, no scoped hypotheses
        derivation: Cid::from_digest(codec::MM_DERIVATION, *term_hash.as_bytes()),
    }
}

/// Ingest: accept an envelope only if it round-trips to a genuine kernel `Thm`.
/// Returns the covalence-internal `Name256` the verified object is stored under.
fn ingest(body: &[u8], advertised: Cid) -> Result<covalence_hash::O256, String> {
    // 1. neutral wire integrity.
    if Cid::of(codec::DERIVATION_FACT, body) != advertised {
        return Err("wire hash mismatch".into());
    }
    let fact = DerivationFact::decode(body).map_err(|e| format!("decode: {e}"))?;
    if fact.logic != codec::logic::HOL {
        return Err(format!(
            "not a HOL fact (logic = {})",
            codec::logic::name(fact.logic)
        ));
    }

    // 2. independently reconstruct the theorem in a fresh kernel.
    let thm = build_thm();

    // 3. the envelope's statement must match the kernel's own rendering.
    if format!("{}", thm.concl()).into_bytes() != fact.prop {
        return Err("statement does not match the kernel theorem".into());
    }

    // 4. the witness CID must be pinned to the real term hash.
    let kernel_hash = hash_term(thm.concl(), &UnitObsHasher);
    if fact.derivation != Cid::from_digest(codec::MM_DERIVATION, *kernel_hash.as_bytes()) {
        return Err("derivation witness is not the real term hash".into());
    }

    // verified: re-key the neutral wire id to covalence's internal Name256.
    Ok(identity::covalence_name(&advertised))
}

fn main() {
    println!("covalence-multiformat — binding the wire format to the real HOL kernel\n");

    // -- 1. author an envelope from a genuine kernel theorem ----------------
    section("1. author from a real covalence-core Thm");
    let thm = build_thm();
    println!("  kernel theorem : ⊢ {}", thm.concl());
    println!("  obs-free (HOL) : {}", thm.has_no_obs());
    let term_hash = hash_term(thm.concl(), &UnitObsHasher);
    println!("  term hash      : {term_hash}  (covalence-init hash_term)");

    let fact = author(&thm);
    let wire = fact.cid();
    let body = fact.encode();
    println!("  wire CID       : {}", wire.to_text());
    println!("  internal Name256: {}", wire.covalence_name());
    println!("  (wire = neutral plain BLAKE3; Name256 = COV_ROOT-keyed — domain-separated)");

    // -- 2. ingest it back into the real kernel -----------------------------
    section("2. ingest: accept only if it round-trips to a genuine Thm");
    match ingest(&body, wire) {
        Ok(name) => {
            println!("  ✓ ADMITTED — corresponds to a real kernel theorem");
            println!("    stored under internal Name256 {name}");
        }
        Err(e) => println!("  ✗ REJECTED — {e}"),
    }

    // -- 3. a forged statement is rejected by the kernel --------------------
    section("3. forge the statement — the kernel refuses it");
    let mut forged = fact.clone();
    forged.prop = b"|- (p /\\ q) = (q /\\ p)".to_vec(); // a different (unproven) claim
    let forged_body = forged.encode();
    let forged_wire = forged.cid();
    println!(
        "  forged statement: {:?}",
        String::from_utf8_lossy(&forged.prop)
    );
    match ingest(&forged_body, forged_wire) {
        Ok(name) => println!("  ✓ ADMITTED under {name}  (should not happen!)"),
        Err(e) => println!("  ✗ REJECTED — {e}"),
    }

    section("what's real here / what's still stubbed");
    println!("  real : the Thm, its term hash, the wire CID, the COV_ROOT Name256 mapping.");
    println!("  stub : ingest rebuilds the theorem from a known recipe rather than *parsing*");
    println!("         the prop term and re-checking it through the kernel (needs a term");
    println!("         deserializer). Coln's Sedimentree address mapping is also unmodelled.");
}
