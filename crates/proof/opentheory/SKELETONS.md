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

- **Vendored offline corpus is incomplete.** `assets/opentheory/gilith/std/`
  is missing some packages (e.g. `natural-order-def`), so `natural` (umbrella),
  `list-def`, and `base` cannot be checked offline. The downloading benchmark
  (`bun run opentheory`, once wired) fetches the full set.

- **Interpretation files (`.int`) parsed but not applied**
  (`resolve.rs::apply_interpretation`). Umbrella packages that rename
  types/constants across a dependency (e.g. `word`→`byte`) will report
  spurious assumptions until deep NameId renaming of theorem terms lands.

- **`cov hol check` / `cov hol pkg` CLI** not yet wired (still the exit-2
  stub in `crates/app/cov/src/cmd/hol.rs`), and the `bun run opentheory`
  download+cache+verify-all benchmark script is not yet written.
