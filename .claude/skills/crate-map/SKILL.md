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
`notes/vibes/crate-graph.md`) and the in-flight three-layer reorg (`notes/vibes/refactor-plan.md`).

## Wrappers (external deps — the leaves)

- **covalence-wasm** — wraps `wat`, `wasmparser`, `wasmprinter`, `wasm-encoder`, optionally `wasmtime` (`runtime` feature; re-exported via `engine::wasmtime`). `ModuleBuilder`, `Val`/`ValType`. (Note: currently also depends on `covalence-core` — a layering wart, see refactor-plan.)
- **covalence-hash** — wraps `blake3`, `sha2`, optionally `gix-hash` (`git` feature). `O256` hash, `HashCtx` (BLAKE3/SHA-256/git), `ContentHash`/`ContentId`, `CovRoot` domain-separated hashing.
- **covalence-sqlite** — wraps `rusqlite`; `open()`/`open_memory()` with WAL + NORMAL sync + busy-timeout pragmas.
- **covalence-rand** — wraps `rand`. All randomness goes through here.
- **covalence-crypto-sig** — wraps `ed25519-dalek` (EdDSA). Re-exports pinned `rand_core` 0.6 as `dalek_rand_core` (the one exception to the covalence-rand rule).
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
- **covalence-inductive** (`crates/lang/inductive`) — the logic-agnostic **inductive-types API**: plain-data `InductiveSpec<X>` (simple = single/non-indexed/strictly-positive/first-order), two-tier `Logic`/`LogicOps` abstraction, `InductiveTheory`/`InductiveFacts` bundle (membership-relativized contract, iteration recursor, rule-form schematic theorems, honest `BackendCaps`), `InductiveBackend` seam, generic `conformance` suite. Deps: `smol_str`+`thiserror` only. HOL backends live in `covalence-init::init::inductive::{api,church,engine}` (impredicative Church = any spec incl. the `sexpr` flagship; engine adapter = exact `nat`); a set.mm backend slots in later. Design: `notes/vibes/inductive-api-design.md`.

## Storage / content-addressing

- **covalence-store** — content-addressed blob store. `ContentStore`, `BlobStore`, `TaggedStore`/`TaggedBlobStore`, `ObjectStore`/`KeyedObjectStore`, `GitPrefixStore`, `SharedMemoryStore`, `KvStore`, `SqliteStore` (`sqlite` feature). Must stay portable to wasm32-wasip1-threads.
- **covalence-object** — object serialization. `Dir`/`DirBuilder`, `Table`/`TableBuilder` (LEB128 rows), git tree-format conversion.
- **covalence-git** — git-compatible object storage + hashing. `hash_blob`, loose/odb backends, Git LFS.
- **covalence-kv** — key-value store surface (`cov:kv@0.1.0`).
- **covalence-wasm-store** — host-side wasmtime store adapters (kept out of portable covalence-store).
- **covalence-acset** — generic **ACSet** (attributed C-set) library, no covalence deps. `Schema::builder` (olog: objects, morphisms, attributes, path equations) + `check`; `Instance` (order-independent `add_part`→`Part`, `set_hom`/`set_attr`, `follow`) + `validate` (functoriality + equations), `acyclic`, `attr_injective`; `Functor` + `Instance::pullback` (Δ functorial data migration); `AttrVal` typed attributes; `query` (`Query::builder` conjunctive queries — answers = homomorphisms, join-style backtracking); `datalog` (`Program`/`Rule` recursive queries — derived relations to a least fixpoint, e.g. transitive closure); `lattice` (`JoinSemilattice` + `lfp` = Datafun's `fix`; `MinDist` for min-plus, set/map/bool instances — set-valued *and* lattice-valued recursion through one combinator; the Datafun seam is `notes/vibes/sketches/acset-datalog-datafun.md`). Used by covalence-multiformat.
- **covalence-multiformat** — self-describing, content-addressed *interchange format* (multihash/multicodec/multibase) for derivation facts exchanged with peer provers (e.g. Coln). `Cid` (blake3 multihash, base16 multibase), `codec` content-type registry, `DerivationFact` envelope (reifies the waist existential), `FactStore::check` (proof-checking *as* a constraint query), `identity::covalence_name` (verified wire CID ↦ `COV_ROOT` `Name256`), `acset` (the interchange schema + `validate_store`, built on covalence-acset — structural/meta-theoretic validation of a `FactStore`, native to a geometric kernel). Wire layer only — logical payloads stay opaque; the `kernel_ingest` example (dev-dep on covalence-init) binds an envelope to a real `covalence-core` `Thm`. See `crates/lib/data/multiformat/SKELETONS.md`.

## Kernel / TCB (the three-layer stack)

- **covalence-pure** (`crates/kernel/base`) — closed-world equality kernel (Stage 0 built: `Thm<L,P>` LCF certificate, `Op`/`Expr`/`Eqn`, parameter-free `Language`) — facade over `covalence-pure-trusted`; `covalence-core` builds on it. See `notes/vibes/closed-world-kernel.md`.
- **covalence-pure-trusted** (`crates/kernel/base/trusted`) — the TCB floor: the trusted closed-world kernel internals `covalence-pure` re-exports.
- **covalence-pure-eval** (`crates/kernel/base/eval`) — the `Builtins` base language: every native computation the kernel will ever trust, as per-op `Op`+`CanonRule` ZSTs over `covalence_types` (nat/int/bytes + the `u8`…`s64` fixed-width families), semantics transcribed from `covalence-core`'s `builtins.rs` (incl. the FORCED `n mod 0 = n`, `x/0 = 0`, `x rem 0 = x`), pinned by a differential suite + the MANIFEST golden `docs/deps/builtins-manifest.txt` (regen: `COV_REGEN_GOLDEN=1`). Deps: `covalence-pure` + `covalence-types` ONLY — the `-> covalence-core` edge is BANNED in dep-graph; enters the TCB when core opens the seam (toHOL purge S4).
- **covalence-core** — **the pure-HOL tier of the TCB, together with `covalence-pure(-trusted)`** (safe Rust; `core::Thm<L: HolTier = CoreLang>` is a newtype over `pure::Thm` — see `docs/deps/tcb.json`; `Thm<CoreLang>` carries NO computation axioms). HOL-Light-style kernel, locally-nameless `Term`/`Type`. Logical primitives are only `=` (`TermKind::Eq`) and `ε` (`TermKind::Select`); connectives are defined constants in `defs/logic.rs`. HOL Light's 10 primitives + fast derived constructors with `Soundness:` docstrings (39 rules, golden `docs/deps/core-manifest.txt`); `define` + `new_type_definition`; `unfold_term_spec`; `spec_abs`/`spec_rep`. Four non-computational primitive rules: `nat_induct`, `false_elim`, `unit_eq`, `lem`. `src/defs/` is only the **D3 residue** (literal-leaf type handles + connective builders — dies with the literal leaves; see its `SKELETONS.md`): the term-op catalogue and the cert rules moved to `covalence-hol-eval` (stage E2). **Read `notes/vibes/kernel-design.md` before touching.**
- **covalence-hol-eval** (`crates/kernel/hol/eval`) — **the eval tier**: owns `CoreEval` (a `Language` extending `CoreLang`) + `EvalThm = Thm<CoreEval>`; hosts the per-family computation certificate rules + toHOL rules (`rules.rs`, 14 rules incl. `FloatCert`, golden `docs/deps/eval-manifest.txt`) NEXT TO their `defs/` dispatch tables and the term-op catalogue (the auditability goal — `defs/floats.rs` = the two-layer float architecture: F2b bit-level declarations + the F2c typed `f64.*` let-style wrappers). Trust is per-rule via `admits`; the drivers (`reduce`/`prove_true`/`delta`, the `lit.rs` facade, the `typed_float.rs` composite that reduces typed float ops with NO new rule) stay untrusted. GOTCHA: `reduce`'s normal forms are load-bearing for hand-assembled `trans` chains in covalence-init — never widen its catalogue over existing symbols (new opt-in passes instead; see `init/ball.rs`'s `ball_eval` + `ext::fire_all`). `tests/pure_hol_units.rs` = the definition-vs-native differential per cert family (dev-dep on covalence-init). `core -> hol-eval` and normal `hol-eval -> init` are BANNED dep-graph edges.
- **covalence-hol** — the thin HOL surface (non-TCB): the builder context `HolLightCtx` + the `HolLightKernel`/`HolLightTerms`/`HolLightTypes` traits + shared `NameId`/`HolError` types. The surface HOL proof consumers (covalence-init, the OpenTheory importer) build against. Depends only on `covalence-core`.
- **covalence-init** — the semi-trusted API over the kernel tower (consumes the top tier: its `Thm` alias is `covalence_hol_eval::EvalThm`): the `init/` theory catalogue, `proofs/` tactics, the `script/` `.cov` layer + `project`, `metalogic`/`peano` (Metamath bridge), `models`, `grammar/{regex,spectec}` grammars, the algebra theories, `hash`/`sexp`. Depends on `covalence-hol` and re-exports its surface (so `covalence_init::{HolLightCtx,traits,types,Term,…}` resolve).
- **covalence-metamath** — HOL-free Metamath substrate: expression model, substitution, frames, RPN/compressed-proof checker, `.mm` reader, `Database`. `covalence-init` consumes it.
- **covalence-kernel** — *legacy, pending rewire* (arena+egraph+UF, superseded). Target: the TCB-preset integration point + re-export façade (refactor-plan §3).

## Proof-format frontends

- **covalence-alethe** — Alethe (SMT) proof checking → HOL.
- **covalence-egglog** — egglog integration (pinned upstream git rev for the `proof` module).
- **covalence-opentheory** — OpenTheory article import (folds into the new thin covalence-hol).
- **covalence-lean** — Lean export parsing (type-theory seed). Intentionally has no in-workspace dependents yet: the seed for future Lean (and Dedukti) proof imports. Keep, don't prune.
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
