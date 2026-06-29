---
name: crate-map
description: Catalogue of every covalence-* crate — what each one wraps/provides and which layer it lives in. Consult when deciding which crate to use, where new code belongs, or how the workspace is structured.
disable-model-invocation: true
---

# Crate map

The workspace is many `covalence-*` crates. **Dependency discipline:** all use of
an external library goes through its wrapper crate — never import the underlying
dep directly (so deps are centralized and extensible without touching every
consumer). The layers below mirror the dependency stack (see
`notes/crate-graph.md`) and the in-flight three-layer reorg (`notes/refactor-plan.md`).

## Wrappers (external deps — the leaves)

- **covalence-wasm** — wraps `wat`, `wasmparser`, `wasmprinter`, `wasm-encoder`, optionally `wasmtime` (`runtime` feature; re-exported via `engine::wasmtime`). `ModuleBuilder`, `Val`/`ValType`. (Note: currently also depends on `covalence-core` — a layering wart, see refactor-plan.)
- **covalence-hash** — wraps `blake3`, `sha2`, optionally `gix-hash` (`git` feature). `O256` hash, `HashCtx` (BLAKE3/SHA-256/git), `ContentHash`/`ContentId`, `CovRoot` domain-separated hashing.
- **covalence-sqlite** — wraps `rusqlite`; `open()`/`open_memory()` with WAL + NORMAL sync + busy-timeout pragmas.
- **covalence-rand** — wraps `rand`. All randomness goes through here.
- **covalence-sig** — wraps `ed25519-dalek` (EdDSA). Re-exports pinned `rand_core` 0.6 as `dalek_rand_core` (the one exception to the covalence-rand rule).
- **covalence-parse** — wraps `winnow`; `leb128` module (unsigned LEB128 varints).
- **covalence-sexp** — S-expression parser. Parametric `SExp<A>`; default `SExpr = SExp<Atom>` (`Symbol(SmolStr)` | `Str{format,bytes}`). Layers: `SExpVisitor` (SAX + dialect), `SExpBuilder`/`TreeBuilder`, `SExp`. Dialects: `CovalenceDialect` (`;;`, `(; ;)`, `|...|`), `SmtLibDialect`, `WatDialect`. `parse()`/`parse_smt()`/`parse_wat()`/`parse_with()`; `map()`/`map_ref()`.
- **covalence-types** — `Decision` (sat/unknown/unsat), `Bits`, and (default `int` feature) `Nat`/`Int` arbitrary-precision (wraps `num-bigint`/`num-traits`/`num-integer`), `Sign`, errors. `Nat` subtraction saturates; use `checked_sub`.
- **covalence-sat** — SAT formulas, DIMACS, DRAT proofs, solver traits. Optional `wasm` feature.
- **covalence-smt** — SMT-LIB2 terms, theories, Alethe proofs.
- **covalence-arrow** — wraps `arrow`; `parse_ipc()` (auto file vs stream) → `ArrowInfo`.
- **covalence-parquet** — wraps `parquet`; `parse_file()`, `scan_hive()` (decoupled via `HiveSource`).
- **covalence-spectec** — wraps `cyruscook/spectec_parse` (`ast`/`decode`/`decode_derive`/`wasm`). `wasm::get_wasm_spectec_ast()` returns the WASM 3.0 spec as a SpecTec AST. **Untrusted driver** lowering WASM semantics into HOL.
- **covalence-graph** — ordered, typed, payload-polymorphic graph (`Graph<P>`/`GraphBuilder<P>`, `BytesGraph`), `LabelList`/`KindFlags` overlays, `StringDiagram`, `cov:graph@0.1.0` WIT, pure-Rust `render_svg`. Symmetric premonoidal: insertion order = init order; linear inputs, fan-out outputs.
- **covalence-json** — wraps `serde_json` only (serde itself stays a normal direct dep).
- **covalence-grammar** — grammar/parsing support (used by hol + spectec).

## Storage / content-addressing

- **covalence-store** — content-addressed blob store. `ContentStore`, `BlobStore`, `TaggedStore`/`TaggedBlobStore`, `ObjectStore`/`KeyedObjectStore`, `GitPrefixStore`, `SharedMemoryStore`, `KvStore`, `SqliteStore` (`sqlite` feature). Must stay portable to wasm32-wasip1-threads.
- **covalence-object** — object serialization. `Dir`/`DirBuilder`, `Table`/`TableBuilder` (LEB128 rows), git tree-format conversion.
- **covalence-git** — git-compatible object storage + hashing. `hash_blob`, loose/odb backends, Git LFS.
- **covalence-kv** — key-value store surface (`cov:kv@0.1.0`).
- **covalence-wasm-store** — host-side wasmtime store adapters (kept out of portable covalence-store).
- **covalence-acset** — generic **ACSet** (attributed C-set) library, no covalence deps. `Schema::builder` (olog: objects, morphisms, attributes, path equations) + `check`; `Instance` (order-independent `add_part`→`Part`, `set_hom`/`set_attr`, `follow`) + `validate` (functoriality + equations), `acyclic`, `attr_injective`; `Functor` + `Instance::pullback` (Δ functorial data migration); `AttrVal` typed attributes; `query` (`Query::builder` conjunctive queries — answers = homomorphisms, join-style backtracking); `datalog` (`Program`/`Rule` recursive queries — derived relations to a least fixpoint, e.g. transitive closure; the Datafun seam is `notes/sketches/acset-datalog-datafun.md`). Used by covalence-multiformat.
- **covalence-multiformat** — self-describing, content-addressed *interchange format* (multihash/multicodec/multibase) for derivation facts exchanged with peer provers (e.g. Coln). `Cid` (blake3 multihash, base16 multibase), `codec` content-type registry, `DerivationFact` envelope (reifies the waist existential), `FactStore::check` (proof-checking *as* a constraint query), `identity::covalence_name` (verified wire CID ↦ `COV_ROOT` `Name256`), `acset` (the interchange schema + `validate_store`, built on covalence-acset — structural/meta-theoretic validation of a `FactStore`, native to a geometric kernel). Wire layer only — logical payloads stay opaque; the `kernel_ingest` example (dev-dep on covalence-init) binds an envelope to a real `covalence-core` `Thm`. See `crates/covalence-multiformat/SKELETONS.md`.

## Kernel / TCB (the three-layer stack)

- **covalence-pure** — *base logic, TCB floor* (empty scaffold today). A small constructive first-order logic; `covalence-core` builds on it. See `notes/covalence-pure.md`.
- **covalence-core** — **THE TCB** (safe Rust). HOL-Light-style kernel, locally-nameless `Term`/`Type`. Logical primitives are only `=` (`TermKind::Eq`) and `ε` (`TermKind::Select`); connectives are defined constants in `defs/logic.rs`. HOL Light's 10 primitives + fast derived constructors with `Soundness:` docstrings; `define` + `new_type_definition`; `reduce_prim`/`unfold_term_spec`; `spec_abs`/`spec_rep`. Four non-computational primitive rules: `nat_induct`, `false_elim`, `unit_eq`, `lem`. Observer rules `obs_eq`/`obs_true`/`obs_imp`. `defs/` catalogue. **Read `notes/kernel-design.md` before touching.**
- **covalence-hol** — the thin HOL surface (non-TCB): the builder context `HolLightCtx` + the `HolLightKernel`/`HolLightTerms`/`HolLightTypes` traits + shared `NameId`/`HolError` types. The surface HOL proof consumers (covalence-init, the OpenTheory importer) build against. Depends only on `covalence-core`.
- **covalence-init** — the semi-trusted API over `covalence-core`: the `init/` theory catalogue, `proofs/` tactics, the `script/` `.cov` layer + `project`, `metalogic`/`peano` (Metamath bridge), `models`, `regex`/`spectec` grammars, the algebra theories, `hash`/`sexp`. Depends on `covalence-hol` and re-exports its surface (so `covalence_init::{HolLightCtx,traits,types,Term,…}` resolve).
- **covalence-metamath** — HOL-free Metamath substrate: expression model, substitution, frames, RPN/compressed-proof checker, `.mm` reader, `Database`. `covalence-init` consumes it.
- **covalence-kernel** — *legacy, pending rewire* (arena+egraph+UF, superseded). Target: the TCB-preset integration point + re-export façade (refactor-plan §3).

## Proof-format frontends

- **covalence-alethe** — Alethe (SMT) proof checking → HOL.
- **covalence-egglog** — egglog integration (pinned upstream git rev for the `proof` module).
- **covalence-opentheory** — OpenTheory article import (folds into the new thin covalence-hol).
- **covalence-lean** — Lean export parsing (type-theory seed).
- **covalence-forsp** — Forsp Lisp (drives the repl).

## App / systems

- **covalence** — the `cov` CLI (clap 4 + color-eyre).
- **covalence-repl** — S-expression REPL with kernel integration.
- **covalence-serve** — axum 0.8 HTTP/WebSocket server (REST + REPL WS + optional embedded static frontend).
- **covalence-client** — remote kernel client (sync via ureq, async via hyper).
- **covalence-lsp** — language server (`lsp-server` 0.7 + `lsp-types` 0.97).
- **covalence-proto** — service discovery/config (Unix sockets, JSON descriptors).
- **covalence-python** — PyO3 0.28 bindings (content-addressing/store/WASM/SAT/graph; HOL kernel bindings TBD on covalence-hol).
- **covalence-shell** — thin userspace re-export over kernel + hol (folds into covalence-kernel).
- **covalence-llm** — central chat/LLM API.
- **covalence-fuse** — FUSE mount (`cog` command).
- **covalence-web-kernel** — the kernel compiled to wasm32 for the browser.

## Other

- **covalence-wasm-spec** — multi-variant WASM components naming functions; dual BLAKE3+SHA256 hashes.
- **covalence-core-test-guest**, **covalence-wasm-build-guest** — wasm32 test/build guests.
