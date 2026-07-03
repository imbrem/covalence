//! The interchange envelope: a [`DerivationFact`].
//!
//! This reifies the covalence kernel's thin-waist existential —
//! *"∃ a derivation `D` with axiom-set `Ax` of `P`, modulo assumptions Γ"* —
//! as a content-addressed record. The proof witness `D` is referenced by CID
//! and never inspected (proof-irrelevance); checking a fact is a constraint
//! query over a store of such records (see [`crate::FactStore`]).

use covalence_parse::leb128::{decode_u64, encode_u64};

use crate::cid::Cid;
use crate::codec::{self, Codec, logic::Logic};
use crate::error::ParseError;

/// Envelope format version (the first field of every encoded body).
pub const FORMAT_VERSION: u64 = 1;

/// A content-addressed assertion that `prop` is derivable in `logic` from
/// `axioms`, modulo the scoped hypotheses in `assumptions`.
#[derive(Clone, PartialEq, Eq)]
pub struct DerivationFact {
    /// Which logic the statement lives in.
    pub logic: Logic,
    /// CID of the axiom-set / theory object.
    pub axioms: Cid,
    /// Codec of the `prop` payload.
    pub prop_codec: Codec,
    /// The statement `P`, encoded in `prop_codec` (opaque to this crate).
    pub prop: Vec<u8>,
    /// Scoped hypotheses `Γ`: imported foreign theorems, classical principles,
    /// `Con(ZFC)`, … Each is a CID; non-fact codecs are trust-root leaves.
    pub assumptions: Vec<Cid>,
    /// CID of the proof witness `D` (proof-irrelevant: only its existence counts).
    pub derivation: Cid,
}

impl DerivationFact {
    /// Canonical, deterministic body encoding (the bytes the fact's CID hashes).
    pub fn encode(&self) -> Vec<u8> {
        let mut out = Vec::new();
        encode_u64(FORMAT_VERSION, &mut out);
        encode_u64(self.logic, &mut out);
        self.axioms.encode_into(&mut out);
        encode_u64(self.prop_codec, &mut out);
        encode_u64(self.prop.len() as u64, &mut out);
        out.extend_from_slice(&self.prop);
        encode_u64(self.assumptions.len() as u64, &mut out);
        for a in &self.assumptions {
            a.encode_into(&mut out);
        }
        self.derivation.encode_into(&mut out);
        out
    }

    /// The fact's content address (codec [`codec::DERIVATION_FACT`]).
    pub fn cid(&self) -> Cid {
        Cid::of(codec::DERIVATION_FACT, &self.encode())
    }

    /// Decode a body produced by [`DerivationFact::encode`].
    pub fn decode(body: &[u8]) -> Result<DerivationFact, ParseError> {
        let (version, n) = decode_u64(body)?;
        if version != FORMAT_VERSION {
            return Err(ParseError::BadVersion(version));
        }
        let r = &body[n..];
        let (logic, n) = decode_u64(r)?;
        let r = &r[n..];
        let (axioms, r) = Cid::parse(r)?;
        let (prop_codec, n) = decode_u64(r)?;
        let r = &r[n..];
        let (prop_len, n) = decode_u64(r)?;
        let r = &r[n..];
        let prop_len = prop_len as usize;
        if r.len() < prop_len {
            return Err(ParseError::Eof);
        }
        let prop = r[..prop_len].to_vec();
        let mut r = &r[prop_len..];
        let (n_assume, n) = decode_u64(r)?;
        r = &r[n..];
        let mut assumptions = Vec::with_capacity(n_assume as usize);
        for _ in 0..n_assume {
            let (cid, rest) = Cid::parse(r)?;
            assumptions.push(cid);
            r = rest;
        }
        let derivation = Cid::decode(r)?;
        Ok(DerivationFact {
            logic,
            axioms,
            prop_codec,
            prop,
            assumptions,
            derivation,
        })
    }
}

impl std::fmt::Debug for DerivationFact {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("DerivationFact")
            .field("logic", &codec::logic::name(self.logic))
            .field("axioms", &self.axioms)
            .field("prop_codec", &codec::name(self.prop_codec))
            .field("prop_len", &self.prop.len())
            .field("assumptions", &self.assumptions)
            .field("derivation", &self.derivation)
            .finish()
    }
}
