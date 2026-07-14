# `covalence-k` — skeletons

## Severe

- **Lowering into `covalence-init` not started.** The crate stops at the
  S-expression IR + fragment classifier; the actual K-frontend payoff
  (rewrite rules → `Derivable_R` relations, SpecTec-style) is a later slice.
- **KORE-JSON + KAST-JSON ingestion missing.** Only textual `definition.kore`
  is parsed; kompile's JSON emissions (and KAST terms) are unconsumed.
- **Claims/reachability layer unconsumed.** `claim` sentences parse and
  render, but the classifier returns `Other` and nothing consumes them.
- **Alias expansion not implemented.** `alias … where lhs := rhs` is stored
  as data; no substitution of alias applications anywhere.

## Minor

- **`from_sexp` / round-trip missing.** `sexpr` is `to_sexp`-only; there is no
  reader back from the canonical IR (and hence no round-trip test).
- **Attribute semantics only partially interpreted.** The classifier reads
  `priority`/`owise`/`label`/`UNIQUE'Unds'ID` and uses `assoc`/`comm`/`idem`/
  `unit`/constructor-family attrs as class markers only — their semantics
  (AC matching, unit laws, …) are uninterpreted.
- **Legacy-K dialect untested.** Only hand-written kompiled-style examples;
  real dumps (c-semantics, x86-64 semantics, older grammar vintages) have not
  been run through the parser.
