# covalence-opentheory — SKELETONS

Open work only. Severe first.

## Severe

- **Cross-package polymorphic assumption discharge.** Packages with
  `requires` whose theorems are used at a *different type instance* than
  assumed (e.g. `unit-def`: the `!` definition is `axiom`'d at `'A` but the
  proof needs it at `('A→bool)→bool`) leave a spurious hypothesis on the
  exported theorem, so the final `thm` (asserted hyp-free) is rejected. A
  `deductAntisym`/`proveHyp` that should cancel the two occurrences doesn't —
  they differ by type instance / `Def` representation. Suspect `inst_type_rule`
  (two-pass `inst_tfree`) or `deductAntisym`/`eq_mp` hyp matching not aligning
  instantiated terms. Blocks every std package past the pure-`defineConst`
  leaves (`unit-def`, `pair-def`, `function`, `list`, `natural`, `base`, …).
  Ignored test: `tests/articles.rs::pkg_unit_def`.

## Minor

- **Interpretation files (`.int`) parsed but not applied**
  (`resolve.rs::apply_interpretation`). Umbrella packages that rename
  types/constants across a dependency (e.g. `word`→`byte`) will report
  spurious assumptions until deep NameId renaming of theorem terms lands.

- **`defineTypeOp` version gating.** `new_basic_type_definition` returns the
  v5-shape theorems (`⊢ abs (rep a) = a` and `⊢ (P r) = (rep (abs r) = r)`).
  The interpreter does not yet wrap them into the v6 λ-abstracted forms for
  version-6 articles; verify against the OpenTheory article standard once the
  discharge blocker above is cleared and a typedef-using package can run
  end-to-end.

- **`cov hol check` / `cov hol pkg` CLI** not yet wired (still the exit-2
  stub in `crates/app/cov/src/cmd/hol.rs`), and the `bun run opentheory`
  download+cache+verify-all benchmark script is not yet written.
