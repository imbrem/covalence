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

## Postulates pending proof

- **The four `add`/`mul` Peano axioms** in
  `crates/covalence-hol/src/init/nat.rs`
  (`Hol::{add_base, add_step, mul_base, mul_step}`) are **postulated** via
  `Thm::assume`, not proved. `nat_add`/`nat_mul` unfold to `natRec`, whose
  recursion equations are not yet available over variables. (Induction and
  the two freeness axioms `succ_inj` / `zero_ne_succ` are now genuine — backed
  by `Thm::nat_induct` and the `Thm::succ_inj` / `Thm::zero_ne_succ`
  freeness primitives.)

  Discharging them — the *soundness of PA in HOL* step — does **not** need a
  new computation primitive: `natRec` exists by `ε` (choice over its
  recursion-uniqueness predicate), so once `ε`/choice is exposed the recursion
  equations follow by induction, and these four with them. When that lands,
  replace the `Hol::axiom` calls with real derivations; the `Peano` trait/API
  does not change.

## Partial subsystems

- **`covalence-alethe` rule coverage.** `HolAletheBridge` (in
  `crates/covalence-alethe/src/hol.rs`) checks the QF_UF fragment —
  `assume`, `resolution` / `th_resolution`, `refl`, `trans`, `symm`,
  `cong`, `equiv_pos2`, `false` — plus the integer term layer (`Int`,
  literals, `+ - * < <= > >=`) and `hole` re-derivation by
  `reduce`+`simp`. The following return `BridgeError::NotImplemented` (or
  `UnknownRule`) and still need wiring:
  - **`hole` beyond closed arithmetic / propositional.** The recompute
    hook (`hol.rs::hole` → `normalize`) discharges a hole whose two sides
    share a `reduce`+`simp` normal form — closed `int` arithmetic
    (`1+2=3`), literal `=`, connective identities (`¬true=false`). A hole
    needing *variable-level ring normalisation* (`x+1 = 1+x`, distributes
    `*`) has no shared normal form yet → reported. Needs proved `int`
    ring identities (`add_comm`/`assoc`/`mul_distrib`) from the Peano/int
    theory + a linear normaliser. Likewise disequality-reflexivity holes
    over uninterpreted terms.
  - **Linear-arithmetic core** — `la_generic`, `la_mult_pos`/`la_mult_neg`,
    `la_rw_eq`, `la_disequality`, `la_tautology`, `la_totality`. The LIA
    proper: Farkas certificates over rational coefficients. Blocked on the
    **ordered-ring theory of `int`** (`le`/`lt` transitivity, add-
    monotonicity, sign rules) that the `high-hol` Peano build-up is
    producing. This is the major remaining undertaking.
  - **Subproofs** — `anchor` and any `step` carrying `:discharge`
    (`subproof`, `bind`, `let`, …). The bridge rejects `:discharge`.
  - **The rest of the propositional rule family** — `equiv_pos1`,
    `equiv_simplify`, `equiv1`/`equiv2`, `implies`, `and_intro`/`and_pos`/
    `and_neg`, `or_pos`/`or_neg`, `implies_pos`/`implies_neg`, `not_not`,
    `contraction`, `tautology`, `evaluate`, `ite*`, plus the equality
    lemmas `eq_reflexive`/`eq_transitive`/`eq_symmetric`/`eq_congruent`.
    Each is a `clause_intro` of an intuitionistic sequent, a `simp`/
    `tauto`, or a direct equality derivation — the `init/logic.rs`
    machinery is in place; they just need cases in `hol.rs::step`.
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
