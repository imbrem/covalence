# Skeletons — covalence-metamath

Intentional placeholders and deferred work in this crate. See the repo
[`CLAUDE.md`](../../CLAUDE.md) § Skeletons for the policy.

## Deferred features (north stars)

- **Compressed proof format.** Only *normal / uncompressed* proofs are checked.
  The parser (`src/parse.rs`, `Parser::read_proof`) **detects** a compressed
  proof (`$= ( labels ) LETTERS $.`) and rejects it with a clear
  `MmError::Parse` ("compressed proof format … not yet supported"). The
  compressed encoding (the `A`–`T` / `U`–`Y` base-20/5 integer scheme, the `Z`
  save marker, and the mandatory-hyp/label-block/heap addressing) is a north
  star, required before `set.mm` can be imported. No incomplete decoder is
  shipped — the gate is the rejection in `read_proof`.

- **`set.mm` scale & performance.** The model uses `String` symbols and `HashMap`
  label/symbol tables with no interning or arenas — fine for the hand-encoded
  example theories (`tests/theories.rs`), not for the ~40 MB `set.mm`. Symbol
  interning, a flat statement arena, and incremental/streaming parsing are
  deferred until the compressed format lands.

- **`$[ ... $]` file inclusion.** The parser handles a single source string.
  Multi-file databases (`$[ include.mm $]`, with dedup by canonical path) are
  not parsed. (A prior flat-string prototype had a `SourceResolver`; the
  `SExpr`-based rewrite drops it pending the compressed-format work, since
  `set.mm` is the only real consumer of includes.)

- **`covalence-hol` import tactic + representation-equivalence metatheorem.**
  The whole point of pillar 2 (`docs/theories-models-and-logics.md` §5.5): a
  `covalence-metamath` → `covalence-hol` bridge that **replays** an (untrusted)
  Metamath proof and **kernel-rechecks** it — the same untrusted-frontend →
  kernel-recheck pattern as `covalence-alethe`. Soundness of the import rests
  on a HOL metatheorem relating the Metamath representation of a theory to our
  locally-nameless syntax (e.g. "Metamath-PA ≡ our PA"). This crate's core is
  deliberately kept independent of `covalence-hol`; the bridge is a future
  crate-dependency edge, not code here.

- **Structured-tree (grammar-parsed) expression encoding.** Expressions are
  encoded as *faithful flat sequences* (`[typecode, sym, sym, ...]` `SExpr`
  lists) — see the crate docs for the rationale. A grammar pass turning those
  flat lists into structured trees (`(-> ph ps)`) would be nicer for the
  metatheory work above, but reintroduces grammar ambiguity and is therefore
  deferred to the bridge layer, where the grammar is part of the (untrusted)
  representation, not the checker.

## Notes

- No `unsafe` (project rule for kernel-liftable surface-language crates).
- The checker performs **genuine** checking: substitutions, typecodes, and `$d`
  distinct-variable conditions are all re-derived and re-verified
  (`src/verify.rs`); bad proofs are rejected with precise errors
  (`tests/theories.rs`).
