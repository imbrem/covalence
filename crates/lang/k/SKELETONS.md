# `covalence-k` — skeletons

Two independent frontends: the **KORE** frontend (`ast`/`parse`/`sexpr`/
`fragment`) over kompile's elaborated IR, and the **`.k`-source** grammar
frontend (`kdef`) over K's surface language. Design: `notes/design/k-frontend.md`.

## KORE frontend

### Severe

- **KORE-JSON + KAST-JSON ingestion missing.** Only textual `definition.kore`
  is parsed; kompile's JSON emissions (and KAST terms) are unconsumed.
- **Claims/reachability layer unconsumed.** `claim` sentences parse and
  render, but the classifier returns `Other` and nothing consumes them. (F0
  single-step lowering of *rewrite* rules lives in `covalence-init::k`.)
- **Alias expansion not implemented.** `alias … where lhs := rhs` is stored
  as data; no substitution of alias applications anywhere.

### Minor

- **`from_sexp` / round-trip missing.** `sexpr` is `to_sexp`-only.
- **Attribute semantics only partially interpreted.** `assoc`/`comm`/`idem`/
  `unit`/constructor attrs are class markers only; their semantics (AC matching,
  unit laws, …) are uninterpreted.
- **Legacy-K dialect untested.** Real dumps (c-semantics, x86-64, older grammar
  vintages) have not been run through the parser.

## `.k`-source grammar frontend (`kdef`)

### Severe

- **Grammar only — no semantics.** `rule`/`context`/`configuration`/`claim`
  sentences are *skipped* (scanned to the next boundary, counted), not parsed.
  Reading K rules (the reduction semantics) from `.k` is a separate, larger job.
- **Regex/token production items unsupported.** `r"…"` items and `syntax
  lexical` declarations error/skip; token sorts come from the `cfg::SortResolver`
  strategy instead (e.g. `KDomains` for `Id`/`Int`/`Bool`). A full lowering would
  parse the `[token]` regexes directly.

### Minor

- **CFG lowering flattens disambiguation.** Priority (`>`) and associativity
  (`[left]`/`left:`) are preserved in the AST but dropped by `kdef::cfg`
  (priorities are parse-time filters over the same context-free language); a
  disambiguating lowering is future work.
- **No layout/whitespace in the lowered CFG.** `kdef::cfg` recognises
  token-adjacent input only; inter-token layout (K's `#Layout`) is unmodelled.
- **Imports not followed.** Only the named module is lowered; `imports` are not
  resolved transitively — undefined sorts fall to the `SortResolver`.
- **Casts and out-of-line `syntax priority`/`syntax left` skipped.** Not needed
  for the tutorial grammars; carried opaquely / skipped.
- **No `.k` ↔ KORE bridge.** The two frontends are independent; the `.k`
  frontend does not kompile to KORE.
