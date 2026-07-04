# Skeletons — `covalence-init/src/metalogic`

Open work in the **metalogic** layer: the generic `Derivable_L` engine, databases
as HOL values, and Metamath import/replay. See `CLAUDE.md` § Skeletons, the
[crate index](../../SKELETONS.md), and the [root index](../../../../../../SKELETONS.md).
Design: `notes/vibes/theories-models-and-logics.md` §5.5/§5.6.

## Severe

- **Structural `σ` for transport.** `transport`/`transport_db` are proven only for
  `⟹`-homomorphic `σ`, demonstrated at `σ=id`. A genuinely structural `σ`
  (constant-symbol renaming, connective mapping; per-rule simulations honestly
  proved) is **not built**. *Blocker:* the `mm_database` carrier `Φ=nat` is a free
  algebra of uninterpreted free vars (`mm$concat`, `mm$c$<tok>`) with no
  recursor — a `σ` descending `concat`-trees needs the encoding reified as a
  genuine inductive datatype first.
- **HOL→ZFC-scale transport** (`Derivable_HOL ⟹ Derivable_ZFC ∘ σ`) — the
  north-star instance; needs structural-`σ` above + concrete HOL/ZFC rule sets.
  Not built.
- **`∃P. ValidProof(P,S,db) ⟺ Derivable_DB db S` grounding bridge.** `Derivable_DB`
  rests on the impredicative engine, not on a HOL reification of the
  [`metamath`](../../../../../proof/metamath/) verifier. Reifying that decidable checker as a HOL
  function and proving the equivalence is unbuilt. Upgrades the *grounding* only.

## Minor

- **`replay_prop` rejects compressed proofs.** The general `replay_db` path
  decompresses via `metamath::proof_steps`, but the Prop-specific
  `mm_replay::replay_prop` still accepts only `Proof::Normal`. Route it through
  `proof_steps` (or retire it in favour of `replay_db`).
- **Tie the Rust `RuleSet` to a first-class HOL `Database` value.** `mm_database`'s
  rule set is a Rust closure, not yet a HOL `db` value à la `database.rs`'s
  `Derivable_DB`.
- **Lift scoped `L' ⊆ L` to full `L`.** `derive_theorem` yields `Derivable_L'`;
  `transport_db` monotonicity can lift it to `Derivable_L` but is not auto-applied.
- **Typecodes & `$d` over-approximated** (sound for construct direction): clauses
  quantify each metavar over all of `Φ`, not the typecode sub-language; `$d`
  disjointness unenforced. Per-step replay re-checks each instance, so witnesses
  stay genuine.
- **Per-logic denotation** for `project`ing a finished `Derivable_L` to a concrete
  fact — not built.
- **Declarations-only load + prove-on-demand.** Parse keeping only declarations
  (`$a`/`$p`/frames/`$d`), skip proof bodies, decode one proof lazily on
  `derive_theorem`. Needs a proof-skipping parse mode in `covalence-metamath`.
- **Structured-former encoding** (shorter HOL repr): give each syntactic former a
  transparent `define`d HOL constant of its arity, so `⌜S⌝` is a tree of named
  constants (`wi(ph,ps)`) and the theorem's only free vars are real metavars.
  Replay keeps formers folded → still `all_elim`. Design: `metalogic` SKELETONS
  history / §5.6.
- **set.mm/ZFC stdlib program** (design): use set.mm as ZFC stdlib from the
  frontend (namespacing, tactics) with set.mm FFI kept as the mirror-principle
  check; two-phase definitions-first import; import instrumentation
  (inference/memory counters); definition/dependency-graph explorer.
- **`mm_import.rs` `temp_import_set_mm_broad` `#[ignore]`d "TEMP" sweep** — retire
  or keep as the standing COV_SET_MM broad-verify harness.
- **`mm_database.rs` `repro_bj1` `#[ignore]`d repro** — kept as a COV_SET_MM-gated
  regression for the bj-1 namespacing fix; fold into the gated sweep or delete.
  (The other `#[ignore]`s in `mm_import.rs`/`mm_database.rs` are intentional
  env-gated set.mm (~48 MB, not vendored) / benchmark harnesses, not deferred work.)

## North stars (design only — do NOT build)

- **`S`-transport** `Derivable_L1(A) ⟹ Derivable_L2(S(A))` (§5.6) — `⟹_σ`
  transport generalized across logics.
- **Conservative extension / equivalence `A ≅ B`** — mutual interpretation; the
  **category of databases** (objects = databases, morphisms = `⟹_σ`, `⊑` the
  sub-order; monotonicity/transport as functoriality) as a `crate::algebra::category`
  instance.
- **`Metamath-L ≅ native-L`** (§5.6) — lift a concrete `metamath::Database` into a
  HOL `Database` value; needs the `∃ValidProof ⟺ impredicative` bridge + a
  representation-equivalence metatheorem.
- **Full `#logic` directive wiring** into the `.cov`/surface compiler (§5.6).

## Notes

- No `unsafe` (project rule). Every relation theorem is kernel-proved and genuine;
  tests assert hypothesis- and oracle-freeness (`has_no_obs`). No postulates.
