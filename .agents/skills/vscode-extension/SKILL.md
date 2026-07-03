---
name: vscode-extension
description: VSCode extension architecture and LSP server details
disable-model-invocation: true
---

## LSP (`cov lsp`)

Supports two file categories:

- **S-expression files** (`.smt`, `.smt2`, `.alethe`, `.cov`) — diagnostics for unclosed/unmatched parens via `covalence-sexp`, formatting via `covalence_sexp::prettyprint()`
- **WAT files** (`.wat`) — diagnostics via `covalence_wasm::validate_wat()` (reports compile errors with line/col)

Also provides `textDocument/formatting` for sexp files. WAT formatting is not yet implemented.

## VSCode extension

The extension supports two LSP transport modes, selected automatically by `src/server.ts`:

**Native mode** (Linux desktop, when `cov` is available):

```
VSCode ← LanguageClient ← stdio ← cov lsp (native binary)
```

**WASM mode** (browser, or native not available):

```
VSCode ← LanguageClient ← @vscode/wasm-wasi-lsp ← WASI Process (cov.wasm) ← lsp-server
```

Detection order: `covalence.server.path` setting → `cov` on PATH (Linux only) → WASM fallback.

The same `src/extension.ts` serves both desktop and web bundles. esbuild aliases `vscode-languageclient/node` → `vscode-languageclient/browser` for the web build.

Supported languages: SMT (`.smt`, `.smt2`), Alethe (`.alethe`), Cov (`.cov`), WAT (`.wat`).

The target triple is set at build time via `crates/app/cov/build.rs` (`COV_TARGET` env var) and passed into `covalence_lsp::run_lsp()` via `LspConfig`. The LSP server reports it in `serverInfo.version` during the initialize handshake.
