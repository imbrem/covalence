//! Integration test: the interchange envelope round-trips to a *real*
//! `covalence-core` `Thm`. Mirrors the `kernel_ingest` example but as an
//! actual `cargo test` (dev-deps on covalence-init + covalence-sexp).

use covalence_init::hash::{UnitObsHasher, hash_term};
use covalence_init::sexp::{UnitObs, term_from_sexp, term_to_sexp};
use covalence_init::{HolLightCtx, Term, Thm};
use covalence_multiformat::{Cid, DerivationFact, codec, covalence_name};
use covalence_sexp::prettyprint;

/// `⊢ x = x` for a `bool` variable — uses only round-trippable constructors.
fn eq_refl(name: &str) -> Thm {
    let ctx = HolLightCtx::new();
    Thm::refl(Term::free(name, ctx.bool_type())).expect("refl")
}

fn term_bytes(t: &Term) -> Vec<u8> {
    let sx = term_to_sexp(t, &UnitObs).expect("serialise");
    let mut buf = Vec::new();
    prettyprint(&[sx], &mut buf).expect("write");
    buf
}

fn author(thm: &Thm) -> DerivationFact {
    let concl = thm.concl();
    let term_hash = hash_term(concl, &UnitObsHasher);
    DerivationFact {
        logic: codec::logic::HOL,
        axioms: Cid::of(codec::AXIOM_SET, b"theory:HOL-classical/core"),
        prop_codec: codec::COV_HOL_THM,
        prop: term_bytes(concl),
        assumptions: vec![],
        derivation: Cid::from_digest(codec::MM_DERIVATION, *term_hash.as_bytes()),
    }
}

/// Returns the internal Name256 (as text) on success — parse + kernel
/// type-check + hash-pin, exactly as the example's `ingest`.
fn ingest(body: &[u8], advertised: Cid) -> Result<String, String> {
    if Cid::of(codec::DERIVATION_FACT, body) != advertised {
        return Err("wire hash mismatch".into());
    }
    let fact = DerivationFact::decode(body).map_err(|e| format!("decode: {e}"))?;
    if fact.logic != codec::logic::HOL || fact.prop_codec != codec::COV_HOL_THM {
        return Err("not a HOL theorem fact".into());
    }
    let text = std::str::from_utf8(&fact.prop).map_err(|e| format!("utf8: {e}"))?;
    let sxs = covalence_sexp::parse(text).map_err(|e| format!("s-expr: {e:?}"))?;
    let sx = sxs.into_iter().next().ok_or("empty s-expression")?;
    let term = term_from_sexp(&sx, &UnitObs).map_err(|e| format!("term: {e}"))?;
    let ty = term.type_of().map_err(|e| format!("ill-typed: {e}"))?;
    if !ty.is_bool() {
        return Err("conclusion is not a bool proposition".into());
    }
    let hash = hash_term(&term, &UnitObsHasher);
    if fact.derivation != Cid::from_digest(codec::MM_DERIVATION, *hash.as_bytes()) {
        return Err("witness CID is not the hash of the payload term".into());
    }
    Ok(covalence_name(&advertised).to_string())
}

#[test]
fn ingest_admits_a_real_theorem() {
    let thm = eq_refl("x");
    let fact = author(&thm);
    let name = ingest(&fact.encode(), fact.cid()).expect("admitted");
    // the internal Name256 is the COV_ROOT re-keying of the wire CID
    assert_eq!(name, fact.cid().covalence_name().to_string());
}

#[test]
fn ingest_is_general_over_distinct_theorems() {
    let a = author(&eq_refl("x"));
    let b = author(&eq_refl("y"));
    assert_ne!(a.cid(), b.cid());
    assert!(ingest(&a.encode(), a.cid()).is_ok());
    assert!(ingest(&b.encode(), b.cid()).is_ok());
}

#[test]
fn ingest_rejects_a_forged_statement() {
    let fact = author(&eq_refl("x"));
    let ctx = HolLightCtx::new();
    // swap the statement to a different well-typed term, keep the old witness
    let mut forged = fact.clone();
    forged.prop = term_bytes(&Term::free("z", ctx.bool_type()));
    let err = ingest(&forged.encode(), forged.cid()).unwrap_err();
    assert!(err.contains("witness CID"), "unexpected error: {err}");
}

#[test]
fn ingest_rejects_corrupt_payload() {
    let fact = author(&eq_refl("x"));
    let mut bad = fact.clone();
    bad.prop = b"(eq (and p".to_vec(); // unbalanced
    assert!(ingest(&bad.encode(), bad.cid()).is_err());
}
