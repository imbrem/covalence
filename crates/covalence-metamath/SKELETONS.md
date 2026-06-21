# Skeletons — covalence-metamath

Intentional placeholders and deferred work in this crate. Its scope is now the
**`.mm` format / IO reader** only — the substitution engine moved to
`covalence-hol::metamath` (engine-side deferrals — the `#logic` correspondence
layer, the import-tactic + representation-equivalence metatheorem, and the
structured-tree encoding — live in
[`covalence-hol/src/metamath/SKELETONS.md`](../covalence-hol/src/metamath/SKELETONS.md)).
See the repo [`CLAUDE.md`](../../CLAUDE.md) § Skeletons for the policy.

## Deferred features (north stars) — reader scope

- **Compressed proof format.** Only *normal / uncompressed* proofs are read.
  The parser (`src/parse.rs`, `Parser::read_proof`) **detects** a compressed
  proof (`$= ( labels ) LETTERS $.`) and rejects it with a clear
  `MmError::Parse` ("compressed proof format … not yet supported"). The
  compressed encoding (the `A`–`T` / `U`–`Y` base-20/5 integer scheme, the `Z`
  save marker, and the mandatory-hyp/label-block/heap addressing) is a north
  star, required before `set.mm` can be imported. No incomplete decoder is
  shipped — the gate is the rejection in `read_proof`.

- **`$[ ... $]` file inclusion.** The parser handles a single source string.
  Multi-file databases (`$[ include.mm $]`, with dedup by canonical path) are
  not parsed. This is the only reader feature `set.mm` truly needs beyond the
  compressed format.

- **`set.mm`-scale streaming/incremental parsing.** The reader tokenises an
  entire source string up front — fine for the hand-encoded example theories
  and the `tests/fixtures/demo0.mm` file, not for the ~40 MB `set.mm`.
  Streaming/incremental parsing is deferred until the compressed format lands.
  (The engine-side model performance — symbol interning, statement arenas — is
  tracked on the `covalence-hol::metamath` side.)

- **Canonical `.mm` serializer.** There is no in-crate emitter; the round-trip
  test (`tests/mm_file.rs`) ships a minimal test-local one. A canonical
  serializer is a north star.

## Notes

- No `unsafe` (project rule).
- The reader builds a genuine `covalence_hol::metamath::Database`; verification
  (substitutions, typecodes, and `$d` distinct-variable conditions all
  re-derived and re-checked) is done by the engine. Bad proofs are rejected
  with precise errors — see the end-to-end theory tests in `tests/theories.rs`.
