# Skeletons — `covalence-hol/src/spectec`

Intentional placeholders in the grammar → byte-predicate compiler + matching
tactic. See [CLAUDE.md](../../../../CLAUDE.md) § Skeletons.

## Partial subsystems

The compiler + matcher for the **regular** base case live under `regex/`
(`regex/mod.rs` + `regex/tactic.rs`); the SpecTec-grammar entry is `grammar.rs`.

- **The CFG stratum (the headline next step).** This module covers only the
  **regular** base case: `regex::desugar`/`regex::compile` target the reified
  *regular* expression object logic (`crate::init::regex`), and `Var`
  (non-terminal reference) is rejected by the byte bridge in `grammar.rs`. We
  want our **own primitive notion of CFG**, one stratum up — exactly as
  `init/regex` is our own primitive notion of regular expression. That means:
  - a reified context-free grammar datatype (non-terminals + productions,
    impredicative-encoded like `init/regex`'s `regex` / `init/prop`'s `Prop`);
  - a `Derives` judgement closed under the productions, with rule induction
    over derivation trees;
  - a SpecTec `gram` definition lowering to those productions, with `Var`
    becoming a non-terminal symbol rather than a `BridgeError::GrammarRef`.

  `regex::tactic::prove_word`'s "variable parses as category" assumptions are the
  forward-compatible seed (a variable token = a non-terminal expansion), but
  the reified CFG datatype, the `Derives` judgement, and its soundness theorem
  are all unbuilt.

- **`prove_word` variable matching is structural, not unifying.** A variable
  token is consumed only when the current regex sub-goal is *structurally
  equal* (`Core: PartialEq`) to the variable's category. It backtracks over
  `seq`/`star`/`alt` splits to align variable boundaries, which covers the
  "header bytes then a `Var` payload" pattern, but it does **not** unify a
  variable against a regex that merely *contains* its category as a sublanguage,
  nor split one variable across two goals. Full grammar-reference resolution is
  the CFG-stratum work above.

- **Matcher is exponential backtracking.** `tactic::derive` tries every
  `seq`/`star` split with no memoisation, so it is worst-case exponential in
  the input length. Fine for the small tokens this bootstraps on; a
  derivative-based (Brzozowski) or memoised/DP matcher — ideally itself
  kernel-liftable — is the performance follow-on. `prove_member` additionally
  pays the slow `lang`-discharge soundness proof (`init/regex::soundness_at`)
  per call.

- **Word normalisation is deferred.** The word `w` in a proved
  `Matches ⌜r⌝ w` is rule-shaped (a `cat`/`cons`/`nil` tree), not flattened to
  a single `cons`-list. Rewriting it to a requested canonical form needs
  `list_cat` computation, which `init/list` does not yet provide (see that
  module's skeletons) — the same deferral `init/regex`'s `.cov` worked examples
  note.
