# Skeletons — covalence-hash

## Minor

- **`examples/coln_bridge.rs` is an alpha sketch, not the real interchange.**
  Demonstrates a multiformat (multihash/multicodec/multibase) content-addressed
  `DerivationFact` envelope bridging covalence (HOL) and Coln (geometric), with
  an in-example store executing the "proof-check = constraint query" hinge. Open:
  codecs sit in the multicodec private-use range (unregistered); no signed
  envelopes (federation needs ed25519 via `covalence-sig`); the Coln-side reader
  is simulated in Rust; witnesses are opaque bytes. Promote to a real crate
  (`covalence-multiformat` / `covalence-coln`) with typed payloads + tests before
  relying on it. Context: bridge analysis in chat / `notes/` (Coln comparison).
