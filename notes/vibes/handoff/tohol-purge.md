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
- **E1–E3 (defs-out, the tower):** `Thm<L: HolTier = CoreLang>`; `CoreEval` in
  `crates/kernel/hol/eval` owns the cert/toHOL rules (`docs/deps/eval-manifest.txt`,
  13 rules; core-manifest 52 → 39) + the moved `defs/` term catalogue next to
  them; `EvalThm = Thm<CoreEval>`; core keeps only the D3 residue
  (`core/SKELETONS.md`). Pure-HOL unit tests
  (`crates/kernel/hol/eval/tests/pure_hol_units.rs`) machine-check
  definition-vs-native per cert family; `scripts/tcb-audit.mjs` tracks the
  tiers (base+HOL 4,888 src-lines vs eval tier 11,012 — trust a
  `Thm<CoreLang>` consumer never depends on).

Ratchet now: obs 0, reduce_prim 0, tycon-obs 0, has_no_obs 0; remaining
unfold_term_spec 38, termkind-literals 123, term-literal-ctors 201,
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

## LOGIC-OUT DONE (L1+L2, audited 0 crit/high, on pure-impl-1)

- **L1** (514edc6f): `nat_induct` reshaped to connective-free **sequent form** —
  premises `Γ_b ⊢ p[0/x]`, `Γ_s ⊢ p[succ x/x]` with `p ∈ Γ_s` (IH), concl
  `(Γ_b ∪ (Γ_s\{p})) ⊢ p`, freshness `x ∉ FV(Γ_s\{p})` only (x free in `Γ_b`
  allowed — sound by the valuation argument in the docstring). Audit: **sound**.
- **L2** (1e88a443): the 13 connective/quantifier rules + `lem` DELETED from the
  kernel; **CoreLang manifest 39 → 26** (the auditable inventory: equality core
  + subtype/spec + `SuccInj ZeroNeSucc FalseElim NatInduct SelectAx` +
  `Define NewTypeDefRule`). Definitions moved to `hol-eval` defs; rules became
  derivations in `hol-eval/src/derived.rs`. **`lem` is now DERIVED from
  `select_ax`** (HOL Light `class.ml` construction) — closing a former bare
  postulate, a net soundness *improvement*.

### Two architectural facts the audit surfaced (record, don't lose)
1. **The connective derivations are `EvalThm` (CoreEval) tier, not pure
   `CoreLang`** — they bottom out in `truth()` (`⊢(T=T)=T`) which uses the
   eval-tier `LitEqCert`. This is **transitional**: it's only because T/F are
   still kernel `Bool` literals; when T/F become *definitions* in the
   literal-leaf endgame, `truth()` derives at pure `CoreLang` and connectives
   drop to the pure tier. Consequence for now: pure-`CoreLang`-tier proofs don't
   get ∧/∨/⟹ for free — they need the eval tier. (Net TCB still shrank: 13
   admitted rules → reuse of one existing eval axiom.)
2. **PERF: connective rules were hot-path, now multi-step derivations.** Audit
   measured real 1.67× / utf16 1.59× / int 1.54× / nat-div 1.50× vs the *stale
   pre-S10 baseline* (so the ratios conflate S10 numeral reification + L1 + L2 —
   cannot attribute to L2 alone). Maintainer pre-authorized this ("micro-
   optimization; acceptable"). **Escape hatch if it ever matters: re-admit hot
   connective rules as `CoreEval`-tier accelerator rules with the derivation as
   the standing soundness witness** — the same derived-in-pure/accelerated-by-
   axiom pattern the arithmetic certs use. Baseline refreshed to post-L2 so
   future perf gates are honest.
