# Handoff: the toHOL purge

**Goal:** `kernel/hol/core` → textbook HOL Light + a binary-data substrate; all
computation via admits-gated base rules; literals as lazy `toHOL` base
expressions (never materialized). Design: [`../tohol-denotation-design`] in
memory + [`../pure-hol-and-build-plan.md`](../pure-hol-and-build-plan.md).

## DONE + merged to main (through 4d3337a5)

- **Anti-sprawl rails:** `docs/deps/groups.json` (cross-group edge pin) +
  `BANNED_EDGES` in `scripts/dep-graph.mjs`; `scripts/purge-ratchet.mjs` +
  `docs/deps/purge-ratchet.json` (per-crate deprecated-pattern counts,
  decrease-only, CI + pre-commit wired, transitional-exception ledger).
- **S0–S8:** observers deleted (`obs_*`, `Object`, `Obs`/`TyConObs` leaves,
  `has_no_obs`); typedef freshness re-homed on opaque `FreshLeaf`/`FreshTyLeaf`
  (private fields, audited); `covalence-pure-eval` (`crates/kernel/base/eval`,
  the `Builtins` language, ~325 CanonRules, **fallible** — `eval → Option`, no
  `usize` clamp); the `toHOL` ops + `eq_mp` (the one new base-TCB method,
  audited sound) + the `CoreLang.extends(Builtins)` seam + `from_pure`
  (validates the sequent floor); 7 cert families in `thm/certs.rs`; the
  untrusted `covalence-hol-eval` driver; `TermExt`/script re-routed; **`reduce_prim`
  + `builtins.rs` DELETED** (−1,296 TCB lines).
- **Fallibility fix (audited):** total-where-representable Nat/Bytes; caught +
  fixed a wasm32-only `⊢False` (`nat.shr` keyed off `usize` not bit-length — see
  [`../../../.claude` memory `bytes-no-usize-clamp`]). Commit bf4c5664.
- **S9:** the Const-twin bridge (`crates/kernel/hol/init/src/init/twins.rs`) —
  each let-style `TermSpec` gains a `define`-produced twin + stored defining
  theorem; `delta`/`unfold_at_*`/script rules re-route onto it (fallback to the
  kernel unfold). `unit` `new_type_definition` prototype landed. Design writeup:
  [`../defs-rehome-design.md`](../defs-rehome-design.md). Bench baseline:
  `docs/deps/proving-baseline.json` (rat 229ms / int 111ms / regex / utf heavies).
  Audited sound (0 findings).

Ratchet now: obs 0, reduce_prim 0, tycon-obs 0, has_no_obs 0; remaining
unfold_term_spec ~36, termkind-literals 117, term-literal-ctors ~205,
cov-script-reduce 18.

## Remaining — reframed under the defs-out-of-core priority

S10 (literal deletion) and S11 (endgame: Nat/Succ/Bool, ε/rep/abs, HOL-Light
diff-check, renames) are **subsumed by** [`defs-out-of-core.md`](./defs-out-of-core.md):
literals become lazy `toHOL` base expressions (the laziness already exists — the
base `Expr`/`Op`/`Rule` algebra from S4/S5), and the object-term vocabulary moves
to predicate-parameterized `ε/rep/abs`. Prior mis-scopings (now corrected):
literals are NOT materialized into cons-towers; there is NO new `Term` leaf; and
S10 was NOT blocked on building lazy infra (it already exists).

## Process lessons banked

Run parallel agent work in **isolated worktrees** (a duplicate-agent race on the
shared tree bit us once). **Adversarial audit every TCB change** — it caught the
wasm32 `⊢False` that green tests could not (64-bit CI can't see 32-bit unsoundness;
consider a wasm32 test job). Robust wall-detection in workflow scripts ("no" ≠
"none").
