# Skeletons — covalence-multiformat

## Minor

- **Codecs are unregistered private-use codes.** `codec::{AXIOM_SET, COV_HOL_THM,
  COLN_GEOM_SEQ, MM_DERIVATION, DERIVATION_FACT}` sit in the multicodec
  private-use range (`>= 0x30_0000`). Register real codes before any
  cross-project wire commitment.
- **No signed envelopes.** Federation / authored Thm exchange needs ed25519
  signatures over the body (via `covalence-sig`). Not yet modelled.
- **Multihash is blake3-only.** `Cid::parse` rejects every other multihash code.
  Add SHA-256/etc. when a peer requires it.
- **Ingest does not re-derive the proof.** `examples/kernel_ingest` parses the
  S-expression `prop` payload, kernel-type-checks it, and pins it to the witness
  hash — but does not re-derive the theorem (the waist is proof-irrelevant; doing
  so needs the envelope to carry derivation steps). The Coln Sedimentree-address
  analogue of `identity::covalence_name` is also unmodelled.
- **HOL payload limited to the round-trippable term fragment.** covalence-init's
  `term_from_sexp` parses only a subset of constructors (no `bool-lit` /
  `term-spec` / `nat-lit` / …), so `COV_HOL_THM` payloads are restricted to what
  round-trips (`app`/`eq`/`free`/`abs`/`const`/…). Widening needs those arms in
  covalence-init, or a different term codec.
- **ACSet validation is structure-only and equation-free.** `acset` checks the
  interchange is a valid *instance* (every morphism a total function into
  existing parts = referential integrity). It does NOT yet model schema
  path/commutativity equations, acyclicity of the citation DAG, or attribute
  laws (e.g. `Fact.cid = blake3(body)` — that lives in the `cid` layer). No
  functorial data migration between schemas. Hand-rolled core, not a real ACSet
  library.
- **Payloads are opaque bytes.** `prop` / witness payloads are not typed or
  validated; the `examples/coln_bridge` Coln reader is simulated in Rust, not a
  real Coln decoder. ACSet-schema soundness-certificate facts (carrying a schema
  *as payload*) are future work.
