# Skeletons — covalence-metamath

Intentional placeholders and deferred work in this crate. Its scope is the
**Metamath substitution engine** (expression model, substitution, frame/database
model, RPN checker) **and** the `.mm` format / IO reader — both now live here,
the lower HOL-free crate. The *consumer-side* bridge deferrals — the `#logic` /
`Derivable_L` correspondence, the import tactic + representation-equivalence
metatheorem — live in `covalence-hol`
([`metalogic/SKELETONS.md`](../covalence-hol/src/metalogic/SKELETONS.md),
[`peano/SKELETONS.md`](../covalence-hol/src/peano/SKELETONS.md)), since they are
HOL-kernel work. See the repo [`CLAUDE.md`](../../CLAUDE.md) § Skeletons for the
policy.

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

- **Canonical `.mm` serializer.** There is no in-crate emitter; the round-trip
  test (`tests/mm_file.rs`) ships a minimal test-local one. A canonical
  serializer is a north star.

## Deferred features (north stars) — engine scope

- **A `Database` trait + pluggable backends.** Today [`Database`](src/database.rs)
  is one concrete in-memory value built by the reader and checked by
  [`verify`](src/verify.rs). The target (the crate-inversion vision) is a
  `Database`/builder **trait** the reader drives, with multiple implementers: the
  in-memory checker here (a HOL-free "sanity check", behind a feature flag) and
  a **HOL-backed** consumer in `covalence-hol` that constructs `⊢ Derivable_…`
  theorems as it reads. Builtin enums for symbol kinds (typecode roles, etc.)
  belong with the trait. **Not built** — the reader still builds the concrete
  `Database` directly.

- **Structured-tree (grammar-parsed) expression encoding.** Expressions are
  encoded as *faithful flat sequences* (`[typecode, sym, sym, ...]` `SExpr`
  lists) — see [`lib.rs`](src/lib.rs) for the rationale. A grammar pass turning
  those flat lists into structured trees (`(-> ph ps)`) would be nicer for the
  metatheory work, but reintroduces grammar ambiguity and is therefore deferred
  to the (untrusted) bridge layer above, where the grammar is part of the
  representation, not the checker.

- **`set.mm` scale & performance.** The model uses `String` symbols and
  `HashMap` label/symbol tables with no interning or arenas — fine for the
  hand-encoded example theories, not for the ~40 MB `set.mm`. Symbol interning,
  a flat statement arena, and incremental construction are deferred.

## Notes

- No `unsafe` (project rule).
- The checker performs **genuine** checking: substitutions, typecodes, and `$d`
  distinct-variable conditions are all re-derived and re-verified
  ([`verify.rs`](src/verify.rs)); the inline unit tests cover the expression and
  substitution core. End-to-end theory tests (good + bad proofs across four
  hand-encoded theories) drive the engine through the reader and live in
  `tests/theories.rs`.
