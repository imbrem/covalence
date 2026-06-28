//! Self-describing, content-addressed interchange format for derivation facts.
//!
//! The minimal wire artifact two provers can exchange — built so covalence
//! (classical HOL) and a peer like Coln (geometric logic) can each read an
//! envelope, **verify its hash, and follow its links even for payloads they
//! cannot interpret**. The hinge: covalence's thin waist reduces every logic to
//! one proof-irrelevant existential ("∃ a derivation `D` with axiom-set `Ax` of
//! `P`"), and Coln's thesis is "proof checking is database constraint checking".
//! A [`DerivationFact`] *is* that existential; [`FactStore::check`] *is* that
//! constraint query.
//!
//! # Why multiformat?
//!
//! covalence's native `O256` is an *opaque* 32-byte hash — the hash function and
//! the payload type are both implicit, known only by convention. That is the
//! wrong property for interop. So the wire identifier ([`Cid`]) is made
//! self-describing:
//!
//! * **multihash**  — the digest carries its hash-function code (BLAKE3 =
//!   `0x1e`) and length, so a reader knows how to re-verify it.
//! * **multicodec** — every payload and the envelope carry a content-type
//!   [`codec`] code, so a reader knows *what* it is and can skip payloads it
//!   cannot interpret while still verifying hashes and following links.
//! * **multibase**  — text form is prefixed (`'f'` = base16-lower).
//!
//! The wire hash is *neutral* plain BLAKE3 (covalence's `O256::blob`), so each
//! system can re-verify and re-key a verified envelope onto its own internal
//! identity (covalence's `COV_ROOT`-keyed `Name256`, Coln's Sedimentree
//! address).
//!
//! # Example
//!
//! ```
//! use covalence_multiformat::{Cid, DerivationFact, FactStore, codec};
//!
//! // covalence authors a classical HOL theorem (proved outright).
//! let hol = DerivationFact {
//!     logic: codec::logic::HOL,
//!     axioms: Cid::of(codec::AXIOM_SET, b"theory:HOL-classical"),
//!     prop_codec: codec::COV_HOL_THM,
//!     prop: b"|- !p q. (p /\\ q) ==> (q /\\ p)".to_vec(),
//!     assumptions: vec![],
//!     derivation: Cid::of(codec::MM_DERIVATION, b"derivation:and-comm"),
//! };
//!
//! // Coln imports it by CID as a scoped hypothesis (borrowing classical power).
//! let coln = DerivationFact {
//!     logic: codec::logic::GEOMETRIC,
//!     axioms: Cid::of(codec::AXIOM_SET, b"theory:geometric-base"),
//!     prop_codec: codec::COLN_GEOM_SEQ,
//!     prop: b"x:Comm |- mul-commutes(x)".to_vec(),
//!     assumptions: vec![Cid::of(codec::AXIOM_SET, b"assumption:LEM"), hol.cid()],
//!     derivation: Cid::of(codec::MM_DERIVATION, b"derivation:import+glue"),
//! };
//!
//! let mut store = FactStore::new();
//! store.put(&hol);
//! let coln_cid = store.put(&coln);
//!
//! // Proof-checking IS the constraint query — and it resolves across kernels.
//! assert!(store.check(coln_cid).is_ok());
//!
//! // Drop the cited HOL theorem and the same fact has a dangling citation.
//! let mut broken = FactStore::new();
//! broken.put(&coln);
//! assert!(broken.check(coln_cid).is_err());
//! ```

pub mod cid;
pub mod codec;
pub mod error;
pub mod fact;
pub mod store;

pub use cid::Cid;
pub use codec::Codec;
pub use error::{CheckError, ParseError};
pub use fact::DerivationFact;
pub use store::{CheckStep, FactStore};

#[cfg(test)]
mod tests {
    use super::*;

    fn hol_thm() -> DerivationFact {
        DerivationFact {
            logic: codec::logic::HOL,
            axioms: Cid::of(codec::AXIOM_SET, b"theory:HOL-classical"),
            prop_codec: codec::COV_HOL_THM,
            prop: b"|- !p q. (p /\\ q) ==> (q /\\ p)".to_vec(),
            assumptions: vec![],
            derivation: Cid::of(codec::MM_DERIVATION, b"derivation:and-comm"),
        }
    }

    fn coln_seq(imports: Cid) -> DerivationFact {
        DerivationFact {
            logic: codec::logic::GEOMETRIC,
            axioms: Cid::of(codec::AXIOM_SET, b"theory:geometric-base"),
            prop_codec: codec::COLN_GEOM_SEQ,
            prop: b"x:Comm |- mul-commutes(x)".to_vec(),
            assumptions: vec![Cid::of(codec::AXIOM_SET, b"assumption:LEM"), imports],
            derivation: Cid::of(codec::MM_DERIVATION, b"derivation:import+glue"),
        }
    }

    #[test]
    fn cid_wire_roundtrip() {
        let c = Cid::of(codec::DERIVATION_FACT, b"hello");
        assert_eq!(Cid::decode(&c.encode()).unwrap(), c);
    }

    #[test]
    fn cid_text_roundtrip() {
        let c = Cid::of(codec::COV_HOL_THM, b"world");
        let t = c.to_text();
        assert!(t.starts_with('f'));
        assert_eq!(Cid::from_text(&t).unwrap(), c);
    }

    #[test]
    fn cid_neutral_hash_matches_blake3_blob() {
        use covalence_hash::ContentHash;
        let c = Cid::of(codec::RAW, b"abc");
        assert_eq!(&c.digest, b"abc".to_id().as_bytes());
    }

    #[test]
    fn cid_rejects_foreign_multihash() {
        // sha2-256 multihash code 0x12 — a reader must reject what it can't verify.
        let mut bad = Vec::new();
        covalence_parse::leb128::encode_u64(codec::RAW, &mut bad);
        covalence_parse::leb128::encode_u64(0x12, &mut bad);
        covalence_parse::leb128::encode_u64(32, &mut bad);
        bad.extend_from_slice(&[0u8; 32]);
        assert_eq!(
            Cid::decode(&bad),
            Err(ParseError::UnsupportedMultihash(0x12))
        );
    }

    #[test]
    fn fact_body_roundtrip() {
        let f = coln_seq(hol_thm().cid());
        let decoded = DerivationFact::decode(&f.encode()).unwrap();
        assert_eq!(decoded, f);
    }

    #[test]
    fn fact_cid_is_deterministic() {
        assert_eq!(hol_thm().cid(), hol_thm().cid());
    }

    #[test]
    fn check_resolves_across_kernels() {
        let hol = hol_thm();
        let coln = coln_seq(hol.cid());
        let mut store = FactStore::new();
        store.put(&hol);
        let coln_cid = store.put(&coln);
        assert_eq!(store.check(coln_cid), Ok(()));
    }

    #[test]
    fn dangling_citation_is_an_open_goal() {
        let hol = hol_thm();
        let coln = coln_seq(hol.cid());
        let mut store = FactStore::new();
        let coln_cid = store.put(&coln); // hol deliberately absent
        assert_eq!(
            store.check(coln_cid),
            Err(CheckError::MissingCitation(hol.cid()))
        );
    }

    #[test]
    fn tampered_body_fails_hash_check() {
        let hol = hol_thm();
        let cid = hol.cid();
        let mut body = hol.encode();
        *body.last_mut().unwrap() ^= 0x01;
        // Re-derive the CID for the tampered bytes: it differs, so a store keyed
        // by the *original* CID would report a hash mismatch on lookup.
        assert_ne!(Cid::of(codec::DERIVATION_FACT, &body), cid);
    }

    #[test]
    fn traced_check_visits_in_order() {
        let hol = hol_thm();
        let coln = coln_seq(hol.cid());
        let mut store = FactStore::new();
        store.put(&hol);
        let coln_cid = store.put(&coln);

        let mut steps = Vec::new();
        store
            .check_traced(coln_cid, &mut |depth, step| {
                let kind = match step {
                    CheckStep::Fact { .. } => "fact",
                    CheckStep::TrustRoot(_) => "root",
                };
                steps.push((depth, kind));
            })
            .unwrap();
        // root coln fact, then its LEM trust-root, then the imported HOL fact.
        assert_eq!(steps, vec![(0, "fact"), (1, "root"), (1, "fact")]);
    }
}
