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

## Deferred features (north stars) — reader scope

- **`set.mm`-scale streaming/incremental parsing.** The reader tokenises an
  entire source string up front — fine for the hand-encoded example theories
  and the `tests/fixtures/demo0.mm` file, not for the ~40 MB `set.mm`.
  Streaming/incremental parsing is deferred until symbol interning lands.

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
  interning or arenas — fine for the hand-encoded example theories, not for the
  ~40 MB `set.mm`. Symbol interning (an `Expr` of interned ids), a flat statement
  arena, and incremental construction are deferred.

## Notes

- No `unsafe` (project rule).
- The checker performs **genuine** checking: substitutions, typecodes, and `$d`
  distinct-variable conditions are all re-derived and re-verified
  ([`verify.rs`](src/verify.rs), behind the default-on `checker` feature); the
  inline unit tests cover the expression and substitution core. End-to-end theory
  tests (good + bad proofs across four hand-encoded theories, plus compressed
  proofs and file inclusion) drive the engine through the reader and live in
  `tests/theories.rs`.
