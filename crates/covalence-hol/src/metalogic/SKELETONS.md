# Skeletons — `covalence-hol/src/metalogic`

Intentional placeholders in the generic `Derivable_L` engine. See `CLAUDE.md`
§ Skeletons and the [crate index](../../SKELETONS.md). Design:
`docs/theories-models-and-logics.md` §5.5/§5.6.

## Status (what is done)

The generic impredicative rule-induction substrate is built and exercised:

- `mod.rs` — `RuleSet` (carrier `phi` + a clause builder), `Derivable_L A :=
  ∀d. Closed_L d ⟹ d A` (`derivable`/`closed_conj`), the conjunction helpers
  (`conj`/`conj_thms`), clause extraction (`nth_conjunct`), the shared
  derivation-constructor spine (`derive_via_closed`), the generic **rule
  induction** (`rule_induction` — the `inst d := pred` + `Closed_L pred`
  discharge, packaged once), and **one-step projection** (`project` /
  `project_normalized`). **Done, proven.**
- `toy.rs` — a from-scratch second instance (a base `tt` + a `box`
  necessitation rule), exercising every engine entry point end-to-end: derive
  `box (box tt)` *purely* (axiom + two rule applications), project in one step
  to `⊢ ⟦box (box tt)⟧ = T`; plus a `rule_induction`-driven soundness theorem.
  **Done, proven.**
- [`peano::pa`](../peano/pa.rs) is wired in as an instance (`pa_rule_set`):
  `Derivable_PA` / `derive_axiom` / `derive_mp` run through the engine, pinned
  byte-identical by `derivable_via_engine_matches`. **Done, proven.**
- [`init::prop`](../init/prop.rs) is **not** refactored onto the engine — left
  additive/alongside per the brief (it is foundational, 1344 lines). It remains
  the original hand-written template; the `toy` instance covers the
  "second genuine instance" requirement without touching it.

## Deferred

### The Metamath-`Database` → `Derivable_L` connection (the stretch)

Deriving a `Derivable_L` from a [`metamath::Database`](../metamath/)'s axioms
(`$a`, premise-free) + inference-rule schemas (`$a`/`$p` with mandatory
hypotheses), so "a logic = a Metamath database" yields "its HOL derivability
predicate" (the `#logic`-semantics seed, §5.6). Not built. The pieces it needs:

1. an **encoding** of Metamath `SExpr` expressions (faithful-flat sequences,
   typecode-headed) into a HOL carrier `Φ` the engine can range over — the
   metavariable layer's analogue of `peano/fol.rs`/`sem.rs`;
2. a **`RuleSet` builder** turning each database assertion into a `Closed_L`
   clause `∀(metavars). premises ⟹ d ⌜concl⌝`, with the metavariable
   substitution = the kernel's `inst` (the `$d` distinct-variable side
   conditions become freshness obligations);
3. a denotation/soundness instance per object logic (only needed to *project*,
   not to derive).

Demonstrate on the prop-calc example database in `src/metamath/` once built.

### North stars (SKELETON only — design, not build)

- **`S`-transport** `Derivable_L1(A) ⟹ Derivable_L2(S(A))` via a computable
  rewrite `S` on the carrier, proved by induction on the source derivation
  (`rule_induction` is the engine; `S` is the per-clause image map). §5.6 (2).
- **The `Metamath-L ≅ native-L` correspondence** (e.g. `Metamath-PA ≅
  our-PA`) — one theorem, two directions (validation + acceleration). §5.6 (3).
- **Full `#logic` directive wiring** into the `.cov`/surface compiler. §5.6 (4).
