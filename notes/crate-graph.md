# Internal crate dependency graph

> **Snapshot: 2026-06-25.** Generated from `crates/*/Cargo.toml`
> path-dependencies (internal `covalence-*` edges only). Regenerate with the
> script in [`refactor-plan.md` §5](./refactor-plan.md) — this is a point-in-time
> picture to make the layering legible and spot inversions, not a maintained
> invariant.

Subgraphs are the *proposed* grouping (§5 of the refactor plan), not the current
on-disk layout (everything is flat under `crates/`).

```mermaid
graph LR
  subgraph wrap
    types; parse; sexp; rand; sig; hash; sqlite; json; arrow; parquet; smt; sat; grammar; spectec; wasm-spec
  end
  subgraph base [base / core API]
    store; object; git; kv; graph; wasm; wasm-store
  end
  subgraph kernel [kernel / TCB]
    pure; core; hol; init; metamath; kernel
  end
  subgraph frontend [proof-format frontends]
    opentheory; lean; alethe; egglog; forsp
  end
  subgraph app
    repl; serve; client; lsp; proto; python; shell; llm; fuse; web-kernel
  end
  covalence --> client & fuse & git & hash & hol & lsp & object & opentheory & proto & repl & serve & shell & store & wasm
  alethe --> core & init & sexp & smt & types
  client --> hash & serve & shell & store
  core --> pure & sexp & types
  egglog --> sexp & types
  forsp --> hash & sexp
  fuse --> hash & object & store
  git --> hash & object & sqlite & store
  graph --> hash & parse
  hash --> rand
  hol --> core
  init --> core & grammar & hash & hol & metamath & sexp & spectec & types
  kernel --> hash & init & object & sexp & store
  llm --> proto
  lsp --> sexp & wasm
  metamath --> parse & sexp
  object --> hash & parse
  opentheory --> hol
  parquet --> arrow
  pure --> types
  python --> git & graph & hash & kv & llm & object & repl & sat & serve & sexp & shell & sig & store & wasm & wasm-store
  repl --> arrow & forsp & git & graph & hash & init & object & parquet & shell & wasm
  sat --> parse & types & wasm
  serve --> core & git & hash & init & metamath & object & proto & repl & shell & store
  sexp --> parse
  shell --> hol & kernel
  smt --> sat & sexp & types
  spectec --> grammar
  store --> hash & json & sqlite
  wasm --> core
  wasm-spec --> hash & types & wasm
  wasm-store --> hash & json & store & wasm
  web-kernel --> kernel
```

## Findings

- **The `hol` split landed.** `covalence-hol` is now thin (`hol --> core` only);
  the bulk is `covalence-init` (`init --> core, hol, metamath, grammar, hash,
  sexp, spectec, types`). The old gravity well is gone — `init` is the new hub,
  but it has a clear single inbound layer (`kernel`/`alethe`/`repl`/`serve`),
  with `opentheory`/`shell`/`covalence` on the thin `hol`.
- **Layering inversion: `covalence-wasm → covalence-core`.** A "wrapper" still
  depends on the TCB, so the wrappers aren't a clean leaf layer; `sat`/`lsp`/
  `wasm-store`/`wasm-spec` pull `core` in transitively. Decide whether `wasm`
  belongs in a *core-API* tier or whether the `core` edge can move to
  `covalence-eval`.
- **`covalence-kernel` is the intended re-export hub** but `repl`/`serve`/
  `covalence` still reach past it into `init`/`git`/`store`. The façade refactor
  (plan §3) should funnel these through `kernel`.
- **Clean leaves** (no internal deps): `types`, `parse`, `rand`, `sig`, `sqlite`,
  `json`, `kv`, `arrow`, `grammar`, `lean`, `proto`. `pure` now has one edge
  (`pure --> types`).
