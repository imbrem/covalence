# Skeletons — `covalence-hol/src/regex`

Intentional placeholders in the regex → byte-predicate compiler + matching
tactic (the regular base case used by every grammar front end). See
[CLAUDE.md](../../../../CLAUDE.md) § Skeletons.

## Partial subsystems

- **Recognizer acceleration is the open performance work.** Matching is split
  into a pure-Rust [`tactic::Recognizer`] (returns a [`tactic::Plan`]) and a
  kernel [`tactic::build`] pass, so the kernel only ever builds the winning
  derivation, and the recognizer memoises on `(node, span)` (polynomial, not
  exponential). What is *not* yet done:
  - the recognizer checks only **simple properties** (does a byte match a
    literal, does a prefix match) — exactly the part to push into a WASM/builtin
    accelerator once the WASM runtime lands. None of that is wired yet.
  - `Core` now holds sub-regexes behind `Arc` so subtrees can be **shared /
    hash-consed**, and `desugar` shares the `r+ = r r*` case, but there is no
    interner: `desugar` of a class or `r{m,n}` still allocates fresh nodes per
    member/copy rather than deduplicating structurally-equal subtrees.
  - [`tactic::prove_member`] additionally pays the slow `lang`-discharge
    soundness proof (`init/regex::soundness_at`) per call; matching itself
    (`prove_matches`) is the fast path.

- **`prove_word` variable matching is structural, not unifying.** A variable
  token is consumed only when the current regex sub-goal is *structurally equal*
  (`Core: PartialEq`) to the variable's category. The recognizer backtracks over
  `seq`/`star`/`alt` splits to align variable boundaries (covering the "header
  bytes then a `Var` payload" pattern), but it does **not** unify a variable
  against a regex that merely *contains* its category as a sublanguage, nor split
  one variable across two goals. Full grammar-reference resolution belongs to the
  CFG stratum (see `../spectec/SKELETONS.md`).

- **Word normalisation is deferred.** The word `w` in a proved `Matches ⌜r⌝ w`
  is rule-shaped (a `cat`/`cons`/`nil` tree), not flattened to a single
  `cons`-list. Rewriting it to a canonical form needs `list_cat` computation,
  which `init/list` does not yet provide (see that module's skeletons).
