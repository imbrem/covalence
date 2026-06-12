---
name: architecture
description: Covalence repo layout, dependency graph, and key architectural rules
disable-model-invocation: true
---

> The canonical kernel design lives in
> [`docs/kernel-design.md`](../../../docs/kernel-design.md). Read it
> before touching `covalence-core` or `covalence-hol`.

## Repo Layout

### Kernel + HOL surface

- `crates/covalence-core/` — **TCB** (~3 KLoC). HOL Light kernel
  in safe Rust.
  - `src/term/{observers,types,terms}.rs` — Term/Type/HolOp/Object
    representation, including `validate_hol_op_shape` for canonical
    HolOp instance types.
  - `src/thm.rs` — single opaque `Thm` type. HOL Light's 10
    primitives (refl, trans, mk_comb, abs, beta_conv, assume, eq_mp,
    deduct_antisym, inst, inst_tfree), 8 derived rules (sym,
    cong_app/abs, imp_intro/elim, all_intro/elim, eta_conv), `weaken`,
    `define`, `new_type_definition`, `reduce_prim`,
    `unfold_term_spec`, the observer rules (`obs_eq`/`obs_true`/`obs_imp`),
    and the single kernel axiom `nat_induction`.
  - `src/builtins.rs` — `reduce_prim_term` (literal arithmetic) +
    `reduce_spec` (catalogue dispatch by `TermSpec::ptr_eq`).
  - `src/hol.rs` — HOL connective constructors (`hol_eq`, `hol_imp`,
    `hol_forall`, …) + `nat_induction_term`. No bridge axioms (Pure
    layer deleted).
  - `src/subst.rs` — capture-avoiding `close` / `open` /
    `shift_by` / `subst_free` / `subst_tfree_in_term`.
  - `src/ctx.rs` — hypothesis `Ctx` (BTreeSet wrapped in
    `Option<Arc<…>>`, structurally shared).
  - `src/defs/` — TypeSpec / TermSpec catalogue (semi-trusted): `nat`,
    `int`, `blob`, `set`, `coprod` (`bit`/`u2`/…/`u512`), `prod`
    (`signed1`/`signed2`), `list`, `option`, `result`, `rel`,
    `stream`, `rat`, `real`, `floats`. `int := signed2 nat` and
    `bytes := list u8` are derived TypeSpecs — `Type::int()` and
    `Type::bytes()` return spec'd types; literals stay as
    `TermKind::{Int,Blob,Nat,Bool}` built-ins.
- `crates/covalence-hol/` — **OUTSIDE the TCB.** HOL builder API +
  serialization.
  - `src/hol_light_obs.rs` — `HolLightCtx` zero-sized handle:
    `mk_eq`/`mk_imp`/`mk_forall`/`mk_and`/… term constructors.
  - `src/nat_axioms.rs`, `src/int_axioms.rs` — postulated downstream
    "axioms" via `Thm::assume(body)` (each carries the body as a
    self-hyp). Slated to be replaced by derivations from
    `Thm::nat_induction` + `define`.
  - `src/stdlib/*` — typed-arithmetic stdlib (nat/int/bool/fun/list/
    option/either/bytes/byte/rat/real) over the `covalence-core`
    primitives.
  - `src/hash.rs` — content hashing (BLAKE3-keyed, `T_PROP`/`T_IMP`/
    `T_ALL`/`T_EQ` tag values **reserved** to keep persisted hashes
    stable, NOT reused).
  - `src/sexp.rs` — canonical S-expression syntax.
  - `src/traits.rs`, `src/types.rs` — `HolLightKernel` /
    `HolLightTerms` / `HolLightTypes` traits, `BOOL_TYCON_ID` /
    `EQ_CONST_ID` / `FUN_TYCON_ID` opaque NameIds for OpenTheory.
  - **Gated** (slated for WASM-proof rewrite): `pure_hol.rs`,
    `peano.rs`, `bridge.rs`. They previously implemented Rust-side
    HOL Light proofs over the now-deleted Pure-meta bridge axioms;
    will be rewritten in the WASM proof format.

### Shells, server, REPL, frontends

- `crates/covalence-shell/` — `SyncBackend` / `AsyncBackend` traits +
  in-memory `Kernel` adapter + `Prover` trait. `prover_kernel.rs`
  wraps the **legacy** `covalence-kernel` arena kernel (different from
  `covalence-core`'s Thm — separate codebase, deliberately).
- `crates/covalence-kernel/` — **LEGACY** arena+egraph+UF HOL kernel.
  Slated for rewrite as an orchestration shell over `covalence-core`
  + `covalence-hol` + `covalence-store` + WASM evaluator + tree-store;
  see `docs/design/proposals/stacked-pure-hol/next-stages.md`.
- `crates/covalence-repl/` — S-expression REPL backed by
  `Box<dyn SyncBackend>` and `covalence-wasm`.
- `crates/covalence-serve/` — axum 0.8 HTTP/WebSocket server.
- `crates/covalence-client/` — sync (ureq) + async (hyper) remote
  backend impls.
- `crates/covalence-proto/` — XDG-runtime-dir service discovery.
- `crates/covalence-lsp/` — LSP server library (used by `cov lsp`).
- `crates/covalence-python/` — PyO3 0.28 Python bindings for
  `covalence-core` Term/Type/Thm.
- `crates/covalence-opentheory/` — OpenTheory article interpreter;
  Rust-proof tests gated until `pure_hol` is reinstated on the
  new rule set.
- `crates/covalence/` — `cov` CLI (clap derive). `cov hol check` is
  gated pending the `covalence-hol::pure_hol` rewrite.

### Storage + primitives

- `crates/covalence-store/` — content-addressed blob store traits
  + impls (memory + sqlite).
- `crates/covalence-sqlite/` — low-level SQLite wrapper (rusqlite).
- `crates/covalence-hash/` — `O256`, `IdentityHasher`, optional git
  hashing.
- `crates/covalence-git/` — git-compatible object storage + LFS.

### WASM, parsing, arrow/parquet, signatures, …

- `crates/covalence-wasm/` — WAT↔WASM, programmatic ModuleBuilder,
  component encoder, runtime (wasmtime) re-export behind `runtime`
  feature.
- `crates/covalence-wasm-store/` — host-side wasmtime store
  adapters.
- `crates/covalence-spectec/` — WebAssembly SpecTec AST.
- `crates/covalence-sexp/` — S-expression parser with dialect
  configuration (Covalence/SMT-LIB/WAT).
- `crates/covalence-parse/` — winnow parser combinators + LEB128.
- `crates/covalence-graph/` — ordered typed payload-polymorphic
  graphs + WIT-bridged forms.
- `crates/covalence-arrow/`, `covalence-parquet/` — Arrow IPC and
  Parquet wrappers.
- `crates/covalence-sat/`, `covalence-smt/` — SAT/SMT terms + Alethe
  proofs.
- `crates/covalence-types/` — `Decision`, `Bits`, `Nat`/`Int` shared
  types (wraps `num-bigint`/`num-traits`/`num-integer` behind the
  default `int` feature).
- `crates/covalence-rand/` — `rand` wrapper.
- `crates/covalence-sig/` — ed25519 signatures (pinned `rand_core 0.6`).
- `crates/covalence-llm/` — central LLM/chat API (see
  [LLM-native vision](../../../docs/design/proposals/) for direction).
- `crates/covalence-json/` — serde_json wrapper.

### Frontends

- `apps/covalence-web/` — SvelteKit web app (adapter-static, SPA
  mode). Builds to `build/`, embedded by `covalence-serve`'s
  `static` feature.
- `packages/covalence-ui/` — shared Svelte 5 component scaffold.
- `extensions/covalence-vscode/` — VSCode extension (desktop +
  web). LSP server detection: native `cov` binary preferred, WASM
  fallback.

## Trust graph

```
                  covalence-core           ← TCB (~3 KLoC, safe Rust)
                       │
                       ▼
                  covalence-hol            ← untrusted: HOL builders,
                       │                     hash, sexp, stdlib,
                       │                     downstream postulates
        ┌──────────────┼──────────────┐
        ▼              ▼              ▼
  covalence-shell  covalence-      covalence-
  (prover trait,   opentheory      python
   Kernel adapter) (article        (PyO3
                   interp)         bindings)
        │
        ▼
  covalence-repl, covalence-serve, … (application code)
```

A bug in `covalence-hol` cannot produce a false `Thm`. A bug in
`covalence-shell` or `covalence-opentheory` cannot produce a false
`Thm`. Soundness reduces to `covalence-core`'s rule and axiom set,
reviewed module-by-module per [`docs/kernel-design.md`](../../../docs/kernel-design.md).

## Key invariants

- **Single non-computational axiom: `Thm::nat_induction`.** Every
  other arithmetic / logical fact is derivable from it + the rule
  set + `define`.
- **No `TermKind::Imp/All/Eq`** (Pure meta-variants deleted); no
  `HolOp::Trueprop`; no `TypeKind::Prop`; no `Type::prop()` /
  `is_prop` / `is_formula`. Every formula is `bool`.
- **HolOp instance types are validated** (`type_of_in` rejects
  weird shapes like `Eq : nat → int → bool`).
- **`Thm::assume(body)` is the postulate primitive**: produces
  `{body} ⊢ body` with body as a self-hyp. Downstream consumers use
  this to "axiom-ize" facts that aren't yet derived from
  `nat_induction`; the audit chain is visible in any final theorem.
- **`int := signed2 nat` and `bytes := list u8`** are derived
  TypeSpecs. Literals (`TermKind::Int`, `TermKind::Blob`) stay as
  kernel built-ins — efficient binary representation is the point.
- **TermSpec dispatch is ptr_eq on catalogue handles.** Users can
  construct their own TermSpecs but they won't `ptr_eq` with the
  catalogue, so they don't trigger `reduce_spec` — their reasoning
  goes through `unfold_term_spec` (sound let-binding) instead.
- **The observer system is sound under the parametric ε-model.**
  Each Rust observer type `O` gets its own ε-family, so a bug or
  policy choice in one observer's `obs_eq`/`obs_true`/`obs_imp`
  cannot affect theorems involving another observer type.

## CLI (`cov`)

clap 4 derive + color-eyre. Subcommands (all default-on, target-gated
for native-only deps on wasm):

- `lsp` — `cov lsp` (LSP server)
- `cogit` — `cov cog` (git-compatible VCS ops)
- `serve` — `cov serve` (axum 0.8 HTTP/WebSocket server)
- `repl` — `cov repl` (S-expression REPL with syntax highlighting)
- `hol check` — gated pending the WASM-proof rewrite of
  `covalence-hol::pure_hol`.

## REPL (`cov repl`)

Backend selection at startup:

- `--connect URL` → `SyncHttpBackend` (remote)
- `--standalone` → in-process `Kernel`
- Default → auto-discovery (find running server) → fallback to
  `Kernel`.

Storage: `--store` enables SQLite persistence, `--memory` (default)
in-memory.

S-expression commands (selected):

- `(store "text")`, `(store-url "url")`, `(store-file "path")` —
  hash + store as blob.
- `(read <hash>)`, `(read-wat <hash>)` — print blob.
- `(module ...)`, `(component ...)` — compile WAT, store.
- `(parse-module <hash>)`, `(parse-component <hash>)` — inspect
  imports/exports.
- `(decide <hash>)` — decide if a proposition (WASM component)
  calls `attest()` on startup.
- `(arrow-stats <hash>)`, `(parquet-stats <hash>)` — Arrow IPC /
  Parquet stats (gated by `covalence-repl/arrow` and
  `covalence-repl/parquet` features).
