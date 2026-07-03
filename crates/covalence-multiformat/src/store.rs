//! A content-addressed fact store — the "database" in *proof checking is
//! database constraint checking*.

use std::collections::HashMap;

use crate::cid::Cid;
use crate::codec;
use crate::error::CheckError;
use crate::fact::DerivationFact;

/// Maps CIDs to encoded [`DerivationFact`] bodies.
#[derive(Debug, Default, Clone)]
pub struct FactStore {
    facts: HashMap<Cid, Vec<u8>>,
}

impl FactStore {
    /// An empty store.
    pub fn new() -> Self {
        Self::default()
    }

    /// Insert a fact; returns its content address.
    pub fn put(&mut self, fact: &DerivationFact) -> Cid {
        let cid = fact.cid();
        self.facts.insert(cid, fact.encode());
        cid
    }

    /// Insert a pre-addressed `body` under `cid` **without recomputing** the
    /// hash. For store adapters that load already-verified bodies (e.g. from
    /// disk) — and for tests that need to construct an inconsistent store. The
    /// `cid`/`body` agreement is the caller's responsibility; the content-address
    /// law in [`crate::acset::validate_store`] is what catches a mismatch.
    pub fn insert_raw(&mut self, cid: Cid, body: Vec<u8>) {
        self.facts.insert(cid, body);
    }

    /// Number of facts held.
    pub fn len(&self) -> usize {
        self.facts.len()
    }

    /// Whether the store holds no facts.
    pub fn is_empty(&self) -> bool {
        self.facts.is_empty()
    }

    /// Whether a fact with this CID is present.
    pub fn contains(&self, cid: Cid) -> bool {
        self.facts.contains_key(&cid)
    }

    /// The stored body for `cid`, if present.
    pub fn get(&self, cid: Cid) -> Option<&[u8]> {
        self.facts.get(&cid).map(Vec::as_slice)
    }

    /// Iterate `(cid, body)` over every stored fact, in unspecified order.
    pub fn facts(&self) -> impl Iterator<Item = (Cid, &[u8])> {
        self.facts.iter().map(|(c, b)| (*c, b.as_slice()))
    }

    /// Proof-checking *as* a constraint query: `cid` is admissible iff it is
    /// present, its stored body hashes back to it, and — recursively — every
    /// derivation-fact it cites is itself admissible. Assumptions whose codec
    /// is not [`codec::DERIVATION_FACT`] (axiom-sets, classical principles) are
    /// scoped trust-roots: leaves, satisfied by assumption. The multicodec tag
    /// on each CID is what selects recurse-vs-leaf.
    ///
    /// A dangling citation (a cited fact absent from the store) is exactly an
    /// open goal: referential integrity = proof well-formedness.
    pub fn check(&self, cid: Cid) -> Result<(), CheckError> {
        self.check_inner(cid, &mut |_, _| {})
    }

    /// Like [`check`](Self::check) but invokes `visit(depth, step)` at each node
    /// — for tracing/rendering a proof walk.
    pub fn check_traced(
        &self,
        cid: Cid,
        visit: &mut dyn FnMut(usize, CheckStep),
    ) -> Result<(), CheckError> {
        self.check_inner(cid, visit)
    }

    fn check_inner(
        &self,
        cid: Cid,
        visit: &mut dyn FnMut(usize, CheckStep),
    ) -> Result<(), CheckError> {
        self.walk(cid, 0, visit)
    }

    fn walk(
        &self,
        cid: Cid,
        depth: usize,
        visit: &mut dyn FnMut(usize, CheckStep),
    ) -> Result<(), CheckError> {
        // Non-derivation CIDs are scoped trust-roots (the sequent's Γ).
        if cid.codec != codec::DERIVATION_FACT {
            visit(depth, CheckStep::TrustRoot(cid));
            return Ok(());
        }

        // Constraint 1: the cited fact must exist.
        let body = self
            .facts
            .get(&cid)
            .ok_or(CheckError::MissingCitation(cid))?;

        // Constraint 2: its bytes must hash to its advertised CID.
        if Cid::of(codec::DERIVATION_FACT, body) != cid {
            return Err(CheckError::HashMismatch(cid));
        }

        let fact = DerivationFact::decode(body).map_err(|e| CheckError::Malformed(cid, e))?;
        visit(
            depth,
            CheckStep::Fact {
                cid,
                logic: fact.logic,
            },
        );

        // Constraint 3: every cited derivation must itself check (transitively).
        for a in &fact.assumptions {
            self.walk(*a, depth + 1, visit)?;
        }
        Ok(())
    }
}

/// A node visited during [`FactStore::check_traced`].
#[derive(Debug, Clone, Copy)]
pub enum CheckStep {
    /// A derivation-fact that exists and is hash-valid.
    Fact { cid: Cid, logic: u64 },
    /// A scoped trust-root leaf (axiom-set, classical principle, …).
    TrustRoot(Cid),
}
