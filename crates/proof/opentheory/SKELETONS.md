# covalence-opentheory — SKELETONS

Open work only. Severe first.

## Severe

- **`defineConstList` not implemented.** `ArticleMachine::cmd_define_const_list`
  still returns `UnknownCommand`. Needed for `list-def`, `option-def`,
  `sum-def`, `stream-def`, `modular-def`, `word-bits-def`, `natural-bits-def`,
  `probability-def` (and hence `base`). Semantics: pop `Thm ({vᵢ = tᵢ} ⊢ φ)`
  and a `List [(Name, Var)]`; define each `cᵢ = tᵢ` (via `new_basic_definition`,
  checking no `tᵢ` mentions any `vⱼ`), then push `List [Const cᵢ]` and
  `Thm (φ[cᵢ/vᵢ])` with the `vᵢ = tᵢ` hyps discharged. Not offline-testable
  until the missing deps below are fetched.

## Minor

- **Online resolver can't version bare package names.** `UrlResolver`
  (`fetch.rs`) only knows a version once an umbrella block registers it, so a
  bare top-level name or a bare `requires:` in a `.thy` (`natural` needs
  `bool`, …) fails with "no version known". *Versioned* names fetch, cache, and
  verify fine (e.g. `bool-def-1.11`). Fix: fetch the repo's package/version
  index (or accept a name→version map). This is the only thing blocking
  `bun run opentheory` (online) from verifying the whole stdlib; offline
  (`--offline`) verifies 20 packages / 428 theorems today.

- **Vendored offline corpus is incomplete.** `assets/opentheory/gilith/std/`
  is missing a few base packages (`natural-order-def`, `natural-dest-def`,
  `natural-numeral-def`), so `natural`/`list`/`base`/`real` etc. cannot be
  checked offline. Every offline failure is this resolver error — none is a
  verification failure. Vendor the missing packages (they fetch by versioned
  name) or use the online path once the resolver above is fixed.

- **Interpretation files (`.int`) parsed but not applied**
  (`resolve.rs::apply_interpretation`). Umbrella packages that rename
  types/constants across a dependency (e.g. `word`→`byte`) will report
  spurious assumptions until deep NameId renaming of theorem terms lands.

- **`cov hol check` / `cov hol pkg` CLI** not yet wired (still the exit-2
  stub in `crates/app/cov/src/cmd/hol.rs`), and the `bun run opentheory`
  download+cache+verify-all benchmark script is not yet written.
