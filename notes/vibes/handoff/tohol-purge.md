# Handoff: the toHOL purge

**Goal:** `kernel/hol/core` → textbook HOL Light + a binary-data substrate; all
computation via admits-gated base rules; literals as lazy `toHOL` base
expressions (never materialized). Design: [`../tohol-denotation-design`] in
memory + [`../pure-hol-and-build-plan.md`](../plans/pure-hol-and-build-plan.md).

## Done + merged

- **Anti-sprawl rails:** `docs/deps/groups.json` cross-group edge pin +
  `BANNED_EDGES`; `scripts/purge-ratchet.mjs` + `docs/deps/purge-ratchet.json`
  (per-crate deprecated-pattern counts, decrease-only, CI + pre-commit).
- **S0–S8:** observers deleted; typedef freshness re-homed on opaque
  `FreshLeaf`/`FreshTyLeaf`; `covalence-pure-eval` (`crates/kernel/base/eval`,
  the `Builtins` language, fallible `eval → Option`, no `usize` clamp); the
  `toHOL` ops + `eq_mp` (the one new base-TCB method) + `CoreLang.extends(
  Builtins)` + `from_pure`; 7 cert families; the untrusted `covalence-hol-eval`
  driver. `reduce_prim` + `builtins.rs` deleted (−1,296 TCB lines).
- **Fallibility fix:** total-where-representable Nat/Bytes; caught + fixed a
  wasm32-only `⊢False` (`nat.shr` keyed off `usize` not bit-length).
- **S9:** the Const-twin bridge (`init/twins.rs`) — each let-style `TermSpec`
  gains a `define`-produced twin + stored defining theorem; `delta`/`unfold`/
  script rules re-route onto it. Design: [`../defs-rehome-design.md`].
- **defs-out tower (E1–E3):** see [`defs-out-of-core.md`](./defs-out-of-core.md).
- **Logic-out (L1+L2, audited 0 crit/high):** `nat_induct` reshaped to
  connective-free sequent form; the 13 connective/quantifier rules + `lem`
  deleted from the kernel (CoreLang manifest 39 → 26), moved to `hol-eval` defs
  + `derived.rs` derivations. **`lem` now DERIVED from `select_ax`** (HOL Light
  `class.ml` construction) — closes a former bare postulate, a net soundness
  improvement.

Ratchet: obs 0, reduce_prim 0, tycon-obs 0, has_no_obs 0; remaining
unfold_term_spec 38, termkind-literals 123, term-literal-ctors 201,
cov-script-reduce 18.

## Two architectural facts from the logic-out audit (don't lose)

1. **Connective derivations are `EvalThm` (CoreEval) tier, not pure CoreLang** —
   they bottom out in `truth()` (`⊢(T=T)=T`) which uses the eval-tier
   `LitEqCert`. Transitional: only because T/F are still kernel `Bool` literals;
   when T/F become definitions (EG5), `truth()` derives at pure `CoreLang` and
   connectives drop to the pure tier.
2. **Connective rules were hot-path, now multi-step derivations** — measured
   ~1.5–1.7× on the hot suites (conflated with S10 numeral reification + L1).
   Maintainer pre-authorized. Escape hatch: re-admit hot connective rules as
   `CoreEval`-tier accelerator rules with the derivation as the standing
   soundness witness (same pattern as the arithmetic certs).

## Open — EG5 (subsumed by defs-out priority)

S10 (literal deletion) and S11 (endgame: Nat/Succ/Bool as definitions, ε/rep/abs,
HOL-Light diff-check, renames) are subsumed by
[`defs-out-of-core.md`](./defs-out-of-core.md): literals become lazy `toHOL`
base expressions (the laziness already exists — the base `Expr`/`Op`/`Rule`
algebra from S4/S5), and the object-term vocabulary moves to
predicate-parameterized `ε/rep/abs`.

Corrected mis-scopings: literals are NOT materialized into cons-towers; there is
NO new `Term` leaf; S10 was NOT blocked on building lazy infra (it exists).
Current EG5 preflight state + the bytes/int toHOL-swap wall: `../eg5-preflight.md`
and `crates/kernel/hol/eval/SKELETONS.md`.

## Process lessons banked

- Run parallel agent work in isolated worktrees (a duplicate-agent race on the
  shared tree bit us once).
- Adversarially audit every TCB change — it caught the wasm32 `⊢False` green
  tests could not (64-bit CI can't see 32-bit unsoundness; consider a wasm32 job).
- Robust wall-detection in workflow scripts ("no" ≠ "none").
