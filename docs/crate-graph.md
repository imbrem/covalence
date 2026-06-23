# Internal crate dependency graph

> Generated from `crates/*/Cargo.toml` path-dependencies (internal
> `covalence-*` edges only). Regenerate with the script in
> [`refactor-plan.md` §5](./refactor-plan.md). A snapshot to make the layering
> legible and to spot inversions. **45 crates.**

Subgraphs are the *proposed* grouping (§5 of the refactor plan), not the current
on-disk layout (everything is flat under `crates/`).

```mermaid
graph LR
  subgraph wrap
    types; parse; sexp; rand; sig; hash; sqlite; json
    arrow; parquet; smt; sat; grammar; spectec; wasm-spec
  end
  subgraph base [base / core API]
    store; object; git; kv; graph; wasm; wasm-store
  end
  subgraph kernel [kernel / TCB]
    pure; core; hol; metamath; kernel
  end
  subgraph frontend [proof-format frontends]
    opentheory; lean; alethe; egglog; forsp
  end
  subgraph app
    covalence; repl; serve; client; lsp; proto; python; shell; llm; fuse; web-kernel
  end

  core --> pure
  core --> sexp & types
  hol --> core & grammar & hash & metamath & sexp & spectec & types
  kernel --> hash & hol & object & sexp & store
  metamath --> parse & sexp
  opentheory --> hol
  alethe --> core & hol & sexp & smt & types
  shell --> hol & kernel
  store --> hash & json & sqlite
  object --> hash & parse
  git --> hash & object & sqlite & store
  graph --> hash & parse
  wasm --> core
  wasm-store --> hash & json & store & wasm
  wasm-spec --> hash & types & wasm
  sat --> parse & types & wasm
  smt --> sat & sexp & types
  spectec --> grammar
  sexp --> parse
  hash --> rand
  parquet --> arrow
  fuse --> hash & object & store
  forsp --> hash & sexp
  egglog --> sexp & types
  llm --> proto
  lsp --> sexp & wasm
  repl --> arrow & forsp & git & graph & hash & hol & object & parquet & shell & wasm
  serve --> core & git & hash & hol & metamath & object & proto & repl & shell & store
  client --> hash & serve & shell & store
  python --> git & graph & hash & kv & llm & object & repl & sat & serve & sexp & shell & sig & store & wasm & wasm-store
  web-kernel --> kernel
  covalence --> client & fuse & git & hash & hol & lsp & object & opentheory & proto & repl & serve & shell & store & wasm
```

## Findings

- **Layering inversion: `covalence-wasm → covalence-core`.** A "wrapper" crate
  depends on the TCB, so the wrappers are *not* a clean leaf layer. `sat`, `lsp`,
  `wasm-store`, `wasm-spec`, `repl` then pull `core` in transitively through
  `wasm`. Decide whether `wasm` belongs in a *core-API* tier (with `store`) or
  whether the `core` edge can be cut (it is likely a small proposition-deciding
  hook that could move to `covalence-eval`).
- **`covalence-kernel` is the intended re-export hub** but currently only `shell`
  and `web-kernel` go through it; `repl`/`serve`/`covalence` reach past it
  straight into `hol`, `git`, `store`, etc. The façade refactor (plan §3) should
  funnel these through `kernel`.
- **`hol` is the gravity well** — 7 internal deps in, and `repl`/`serve`/`alethe`/
  `opentheory`/`shell`/`covalence` all depend on it. Splitting it (plan §3–4) is
  the single highest-leverage move for legibility.
- **Clean leaves** (no internal deps): `types`, `parse`, `rand`, `sig`, `sqlite`,
  `json`, `kv`, `arrow`, `grammar`, `lean`, `proto`, `pure`. These are the safe
  bottom of any grouping.
