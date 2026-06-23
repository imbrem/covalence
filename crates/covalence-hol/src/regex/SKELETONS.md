# Skeletons — `covalence-hol/src/regex`

Open placeholders in the regex → byte-predicate compiler + matching tactic (the
regular base case used by every grammar front end). See
[CLAUDE.md](../../../../CLAUDE.md) § Skeletons.

## Severe / blocking

- **`prove_member` one-time ~55s warm-up.** First call per process builds the
  impredicative-star `denote`/`lang` machinery (cached after; later calls ~260µs).
  Collapsing it needs sharing / hash-consing in the term builders (or a
  less-impredicative star encoding) — a kernel / `covalence-pure`-split item. The
  membership integration test stays `#[ignore]`d for this; `prove_matches` is fast.

## Polish / increments

- **Recognizer acceleration.** The pure-Rust `tactic::Recognizer` checks only simple
  properties (byte/prefix matches) — the part to push into a WASM/builtin
  accelerator once the WASM runtime lands. Not wired yet.
- **No subtree interner.** `Core` holds sub-regexes behind `Arc` for sharing, but
  `desugar` of a class or `r{m,n}` still allocates fresh nodes per member/copy
  rather than deduplicating structurally-equal subtrees.
- **`prove_word` variable matching is structural, not unifying.** A variable token is
  consumed only when the regex sub-goal is structurally equal (`Core: PartialEq`) to
  the variable's category; it does not unify against a regex that merely contains the
  category, nor split one variable across two goals. Full resolution belongs to the
  CFG stratum (see `../spectec/SKELETONS.md`).
- **Word normalisation deferred.** The word `w` in `Matches ⌜r⌝ w` is rule-shaped
  (`cat`/`cons`/`nil` tree), not flattened to a `cons`-list. Needs `list_cat`
  computation, which `init/list` does not yet provide (see that module's skeletons).
