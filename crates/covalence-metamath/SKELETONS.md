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

## Done (no longer deferred)

- **Compressed proof format.** ✅ The reader parses `$= ( labels ) LETTERS $.`
  into [`Proof::Compressed`](src/database.rs); the decoder/verifier
  ([`verify::decompress_proof`](src/verify.rs)) recovers the `A`–`T` / `U`–`Y`
  base-20/5 integer scheme, the `Z` save markers, and the mandatory-hyp /
  label-block / heap addressing, then runs the same RPN/`$d` machinery. Both
  encodings are tested (`tests/theories.rs`, with and without `Z` saves).

- **`$[ ... $]` file inclusion.** ✅ The `SourceResolver` trait +
  `FileResolver`/`MemoryResolver` + `parse_with_resolver` expand includes at the
  token level with dedup by canonical key (`src/parse.rs`). `parse(&str)` is the
  no-include default. Tested via a two-source `MemoryResolver` end-to-end.

- **The `Database` builder trait.** ✅ [`DatabaseSink`](src/database.rs) is the
  construction API the reader drives; the in-memory `Database` implements it, and
  the parser builds through `&mut impl DatabaseSink`. `SymbolKind` classifies
  `$c`/`$v` declarations. The **HOL-backed sink** (constructing `⊢ Derivable_…`
  theorems as it reads) is the `covalence-hol` follow-on — see below.

- **Distinct-variable (`$d`) checking against the proof's full scope.** ✅ Fixed
  the spurious-rejection bug where `check_disjoints` ([`verify.rs`](src/verify.rs))
  checked generated `$d` obligations against the proving theorem's
  *mandatory-filtered* `frame.disjoints` — too small, because it dropped `$d`
  pairs over dummy/working variables used only inside the proof (this rejected
  `hol.mm`'s `cl`/`clf`). Each [`Assertion`](src/database.rs) now records
  `scope_disjoints`: the **full** in-scope `$d` set over *all* variables;
  `check_disjoints` checks against that. The mandatory-filtered set still
  *propagates* when the assertion is later applied. Genuine `$d` violations are
  still rejected (`tests/theories.rs`: `dv_violation_when_collapsed`,
  `dv_violation_when_obligation_not_declared` still FAIL; `dv_satisfied_when_declared`
  still PASSES).

- **Real-file ingestion (`hol.mm`, `set.mm`).** ✅ The vendored
  `tests/fixtures/hol.mm` (CC0, 151 `$p` theorems, all compressed proofs) parses
  and fully verifies in ~0.04 s (`tests/hol_mm.rs`). Full `set.mm` (~48 MB, not
  vendored) parses in ~0.9 s and verifies **47,394 theorems in ~5 s** in release
  (`tests/set_mm.rs`, `#[ignore]`d, run via `COV_SET_MM=/path cargo test … --
  --ignored`). No grammar / `$d` / compressed-proof / scale failures surfaced —
  the un-interned reader handles full `set.mm` comfortably, so interning (below)
  is a nice-to-have, not a blocker.

## Deferred features (north stars) — reader scope

- **`set.mm`-scale streaming/incremental parsing.** The reader tokenises an
  entire source string up front and `parse` takes a `&str`, so the whole ~48 MB
  `set.mm` must be read into memory first. This is *acceptable today* (full
  parse+verify is ~6 s in release, see "Real-file ingestion" above), but a
  streaming/incremental reader that does not require holding the entire source +
  database in memory is still a north star.

- **Canonical `.mm` serializer.** There is no in-crate emitter; the round-trip
  test (`tests/mm_file.rs`) ships a minimal test-local one. A canonical
  serializer is a north star.

## Deferred features (north stars) — engine scope

- **HOL-backed `DatabaseSink`** — done for the propositional fragment. The
  [`DatabaseSink`](src/database.rs) trait has two implementers: the in-memory
  [`Database`](src/database.rs) (the HOL-free "sanity check" behind the default-on
  `checker` feature) and `covalence-hol`'s `metalogic::mm_sink::HolPropSink`,
  which constructs `⊢ Derivable_Prop ⌜S⌝` as it reads a prop `.mm`. **Remaining:**
  a HOL sink over an *arbitrary* database (the `RuleSet`-from-`Database` /
  schema-database replay, landing `⊢ Derivable_DB ⌜db⌝ ⌜S⌝`) — tracked in
  `covalence-hol`'s `metalogic/SKELETONS.md`.

- **Structured-tree (grammar-parsed) expression encoding.** Expressions are the
  primitive [`Expr`](src/expr.rs) = a typecode `Symbol` + flat `body: Vec<Symbol>`
  — *faithful flat sequences*, see [`lib.rs`](src/lib.rs) for the rationale. A
  grammar pass turning those flat sequences into structured trees (`(-> ph ps)`)
  would be nicer for the metatheory work, but reintroduces grammar ambiguity and
  is therefore deferred to the (untrusted) bridge layer above, where the grammar
  is part of the representation, not the checker.

- **Symbol interning for `set.mm` scale.** [`Symbol`](src/expr.rs) is an owned
  `smol_str::SmolStr`; the database uses `HashMap` label/symbol tables with no
  interning or arenas. Empirically this is *not* a correctness or even a
  practical-speed blocker — full `set.mm` (47,394 theorems) verifies in ~5 s in
  release. Symbol interning (an `Expr` of interned ids), a flat statement arena,
  and incremental construction remain a performance/memory north star (would cut
  allocation and the ~50 MB in-memory `Database` footprint), no longer urgent.

- **`replay_db` over compressed proofs.** [`replay_db`](../covalence-hol/src/metalogic/mm_database.rs)
  (the HOL replay that re-derives `⊢ Derivable_L ⌜S⌝`) accepts only
  [`Proof::Normal`](src/database.rs); it rejects [`Proof::Compressed`](src/database.rs)
  with "decompress to a normal proof first". But **every** `$p` proof in `hol.mm`
  (and the overwhelming majority of `set.mm`) is compressed, so no `hol.mm`
  theorem can currently be replayed into a kernel HOL theorem. The missing piece
  is a **decompress-to-normal** pass — exposing the verifier's `decompress_proof`
  step sequence as an equivalent flat RPN label list (re-expanding `Z`/heap
  backreferences into their producing label subsequence), then feeding that to
  `replay_db` (or teaching `replay_db` to consume `ProofStep`s directly). This is
  the concrete next step for "construct a kernel HOL theorem from real `hol.mm`
  data"; tracked also in `covalence-hol`'s `metalogic/SKELETONS.md`.

## Notes

- No `unsafe` (project rule).
- The checker performs **genuine** checking: substitutions, typecodes, and `$d`
  distinct-variable conditions are all re-derived and re-verified
  ([`verify.rs`](src/verify.rs), behind the default-on `checker` feature); the
  inline unit tests cover the expression and substitution core. End-to-end theory
  tests (good + bad proofs across four hand-encoded theories, plus compressed
  proofs and file inclusion) drive the engine through the reader and live in
  `tests/theories.rs`.
