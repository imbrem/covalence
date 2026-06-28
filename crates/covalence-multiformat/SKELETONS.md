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
- **Kernel ingest rebuilds, doesn't parse.** `examples/kernel_ingest` verifies an
  envelope against a real `covalence-core` `Thm` by reconstructing it from a known
  recipe. Full ingest must *deserialize* the `prop` term and re-check it through
  the kernel (needs a term deserializer). The CID ↦ `COV_ROOT` `Name256` map
  (`identity::covalence_name`) is real; the Coln Sedimentree-address analogue is
  unmodelled.
- **Payloads are opaque bytes.** `prop` / witness payloads are not typed or
  validated; the `examples/coln_bridge` Coln reader is simulated in Rust, not a
  real Coln decoder. ACSet-schema soundness-certificate facts are future work.
