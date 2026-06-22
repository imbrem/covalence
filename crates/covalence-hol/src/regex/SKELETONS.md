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
  - [`tactic::prove_member`] used to take **~136s per call**. Three fixes
    (profiled with `COV_PROFILE`, see `crate::debug`) cut that to a one-time
    warm-up + ~4ms per call thereafter:
    1. it built `lang_ty` as `denote(rterm).type_of()` — constructing and
       re-type-traversing the whole impredicative-star denotation just to read
       the type `set (list u8)`; now built directly (`lang::lang(word_ty)`),
       removing ~135s/call;
    2. `soundness_at`'s `discharge_closed` (proving the rules for
       `D = λr w. mem w ⟦r⟧` over the impredicative Kleene star) was re-run at
       the *concrete* `u8` alphabet (~169s, dominated by structural `Type`
       comparisons over the `u8` subtype). It is alphabet-parametric, so it is
       now proved **once at a polymorphic type variable** (`closed_d_poly`,
       cached) and `inst_tfree`-instantiated to `u8`;
    3. it `beta_nf`-**normalised** `(λr w. mem w ⟦r⟧) rterm w`, which reduces
       the concrete regex's denotation and duplicates the lang-star handler at
       every fold node (exponential); replaced with **two head β-steps**
       (`beta_conv`) that leave the denotation un-reduced — the form the
       conclusion wants anyway.
    **Remaining:** the *first* `prove_member` in a process still pays a one-time
    **~55s warm-up** building the `denote`/`lang` machinery for the impredicative
    star (cached after — the second call's `denotation_pred` is ~260µs). This is
    the impredicative-term construction itself; collapsing it needs sharing /
    hash-consing in the term builders (or a less-impredicative star encoding) —
    a kernel / `covalence-pure`-split item. The membership integration test stays
    `#[ignore]`d for that warm-up; `prove_matches` is unaffected and fast.

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
