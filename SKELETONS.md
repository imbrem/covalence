# Skeletons

Authoritative registry of intentional placeholders in the repo: empty/stub
modules, removed-pending-rewrite subsystems, `NotImplemented` / `todo!()` /
`unimplemented!()` stubs, and tests that are commented out, `#[ignore]`d, or
deleted "for later".

See `CLAUDE.md` § Skeletons for the rules: **add an entry whenever you leave a
skeleton; delete the entry when you fill one in.** Keep this list complete —
it is how unfinished work stays discoverable.

## Empty / stub modules

- **`crates/covalence-kernel/src/facts.rs`** — empty module. The *observer*
  layer that records and content-addresses proven `covalence-hol` theorems
  will land here as the HOL-on-store stack comes online. See the
  `covalence-kernel` crate-root docs and `docs/roadmap.md`.

## Partial subsystems

- **`covalence-alethe` rule coverage.** `HolAletheBridge` (in
  `crates/covalence-alethe/src/hol.rs`) checks the QF_UF fragment —
  `assume`, `resolution` / `th_resolution`, `refl`, `trans`, `symm`,
  `cong`, `equiv_pos2`, `false`. The following return
  `BridgeError::NotImplemented` (or `UnknownRule`) and still need wiring:
  - **`hole`** — cvc5's "untranslated rewrite" escape hatch. Cannot be
    checked without reconstructing the omitted rewrite; surfaced rather
    than trusted. Most cvc5 QF_UF proofs that reason about disequality
    (`¬(x = x)` → `false`) currently hit this.
  - **Subproofs** — `anchor` and any `step` carrying `:discharge`
    (`subproof`, `bind`, `let`, …). The bridge rejects `:discharge`.
  - **The rest of the propositional rule family** — `equiv_pos1`,
    `and_pos`/`and_neg`, `or_pos`/`or_neg`, `implies_pos`/`implies_neg`,
    `not_not`, `contraction`, `tautology`, `ite*`, plus the equality
    lemmas `eq_reflexive`/`eq_transitive`/`eq_symmetric`/`eq_congruent`.
    Each is either a `clause_intro` of an intuitionistic sequent or a
    direct equality derivation — the `init/logic.rs` machinery is in
    place; they just need cases in `hol.rs::step`.
  - **Theory arithmetic** (`la_*`, `lia_*`, …) — out of scope until the
    kernel's `int`/`real` arithmetic is wired through term translation.
  - **Parametric sorts** (`declare-sort` arity > 0) — rejected with
    `ParametricSort`.

## Registry maintenance

- **`SKELETONS.md` itself is incomplete.** This file was created to fix the
  missing `facts` module and currently records only the `covalence-kernel`
  skeletons surfaced there. It still needs a full repo audit — empty/stub
  modules, `todo!()` / `unimplemented!()` / `NotImplemented` stubs, and
  disabled / deleted tests across all crates — to become the authoritative
  registry `CLAUDE.md` describes.

## Removed-pending-rewrite subsystems

- **`covalence-kernel` legacy prover** — the arena + e-graph + union-find
  prover kernel that used to live in `covalence-kernel` was removed in the
  kernel rewrite. What remains is the content-addressed store wiring
  (`backend.rs`, `store.rs`) plus the empty `facts` module above. Recover the
  old prover from the `backup/pre-hol-cleanup` branch if needed.
