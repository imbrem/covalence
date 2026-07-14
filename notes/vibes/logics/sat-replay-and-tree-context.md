# Fast SAT replay — the AND-tree context (handoff)

*Design handoff, 2026-07-14. The next speed step for `covalence-kernel-sat`'s
sequent-form replay: collapse the input-clause database into a single shared
`∧`-tree hypothesis, so hypothesis contexts stay small instead of accumulating
every used input clause.*

## The problem (measured)

The sequent backend (`crates/kernel/sat/src/sequent.rs`) carries a clause
`C = l₁∨…∨lₙ` as `{C, ~l₁,…,~lₙ} ⊢ F`. Resolution is a cut whose cost is the HOL
**hypothesis-set** operations (`or_elim` unions two hyp sets; `imp_intro` removes
one). The `~`-literals of any one clause are few, **but every input clause `Cᵢ`
ever used accumulates as its own hypothesis** — so the sets grow to O(#input
clauses) and each cut's union grows with them. Pigeonhole PHP(h+1,h): per-step
cost rises from ~1 ms (h=7, ~200 clauses) toward ~2.3 ms (h=8), i.e. ~O(#clauses)
per step. That accumulation is the bottleneck.

## Dead end: the persistent-set data-structure swap (don't re-try)

Swapping `TermSet`'s backing from `Arc<BTreeSet<Term>>` (copy-on-write, O(n)
spine deep-clone per op) to `imbl::OrdSet<Term>` (O(log n) path-copy) was
**benchmarked and is a ~1.3–1.5× REGRESSION** on the replay (same machine, PHP):

| h | BTreeSet | imbl::OrdSet |
|---|----------|--------------|
| 5 | 48 ms | 78 ms |
| 6 | 719 ms | 973 ms |
| 7 | 6.7 s | 8.7 s |

An isolated microbenchmark showed 20× on insert/remove at n=400, but it doesn't
translate: the replay's hot op is *union* on medium sets, where `OrdSet`'s
per-node `Arc` + poor cache locality outweigh the asymptotics; `BTreeSet` already
gets O(1) clone when the `Arc` is shared and O(1) element comparison
(`Term`'s `Arc::ptr_eq` + cached-fingerprint `Ord`). **The lever is set *size*,
not large-set op speed.**

## The fix: one shared `∧`-tree context `Γ_and`

Build `Γ_and` = a **balanced binary `∧`-tree of all input clause disjunctions**,
*once* (a single shared `Arc` `Term`). Carry a derived clause `C` as

```text
{Γ_and} ∪ {~l₁,…,~lₙ}  ⊢  F
```

— the input database is now **one** hypothesis `Γ_and`, not `m` of them, plus the
current clause's few `~`-literals. Then:

- **hyp-set size is bounded by clause width + 1**, never growing with proof
  length — union/`imp_intro` operate on small sets.
- unioning two clauses' sets, `Γ_and` is the *same* `Arc` in both →
  `Arc::ptr_eq` dedups it in O(1); only the small `~`-literal parts merge.

### Operations

- **`assume_clause(Cᵢ)`**: from the one assumed `{Γ_and} ⊢ Γ_and`, navigate the
  balanced tree by `and_elim_l`/`and_elim_r` to leaf `i` → `{Γ_and} ⊢ Cᵢ`
  (O(log m)); then eliminate the disjunction `Cᵢ` against the assumed `~lⱼ`
  (same `eliminate` as today) → `{Γ_and, ~lⱼ} ⊢ F`. Setup is O(m log m) total.
- **`resolve_on(a,b,p)`**: the *identical* cut (`imp_intro`×2 + `lem` + `or_elim`)
  — but now over small sets. `Γ_and` survives (it isn't the pivot).
- **empty clause / refutation**: `{Γ_and} ⊢ F`. Detect via `RupReplay`'s existing
  backend-agnostic `c_lits.is_empty()`.
- **final discharge**: `imp_intro(Γ_and)` → `⊢ Γ_and ⟹ F` = `⊢ ¬Γ_and`
  = `⊢ ¬(C₁∧…∧Cₘ)` — a **fully closed** kernel theorem: the CNF is unsatisfiable.

### Soundness contract (simpler + stronger)

The refutation's only hypothesis must be **exactly** `Γ_and` (the built tree of
the input clauses); the discharged `⊢ ¬Γ_and` is then hypothesis-free. Check
`thm.hyps() == {Γ_and}` (vs today's "hyps ⊆ input-clause disjunctions"). Every
step is still a real kernel rule → an unsound `⊢ F` is impossible; zero TCB.

## Implementation plan

- New backend `AndTreeClauseBackend` (a third `ClauseBackend`; or a mode of the
  sequent backend). Fields: `HolLightCtx`, the built `Γ_and` term, `{Γ_and} ⊢
  Γ_and`, and the leaf-index → and-elim-path map.
- **API wrinkle**: it needs the *whole* CNF up front to build `Γ_and`. Options:
  (a) a constructor `AndTreeClauseBackend::new(cnf)`; (b) a `ClauseBackend`
  `pre_seed(&mut self, cnf: &Cnf)` hook that `RupReplay` calls before per-clause
  `assume_clause` (it already holds the `Cnf`). Prefer (b) for API uniformity —
  it's a no-op default for the other backends. Then `assume_clause(Cᵢ)` extracts
  by matching `Cᵢ`'s term to its leaf (or by an assume-order counter).
- Reuse `sequent.rs`'s `eliminate`/`contradiction_branch`/`comp_literals` — only
  the input-clause hypothesis representation changes.
- Wire it as the demo/bench default; add a live pigeonhole test through it; run
  the `bench_pigeonhole_scaling` A/B (expect h=8's 60820 steps in seconds, not
  ~142 s).

## Expected win + open questions

- **Expected**: per-step cost O(clause width) not O(#clauses) → h=8 interactive.
  (Validate — the AND-tree is unmeasured; the OrdSet lesson says *measure*.)
- **Output shape**: the theorem is `⊢ ¬(big ∧-tree)` = "CNF unsat". Fine as a
  refutation certificate; a consumer wanting the un-collapsed `{clauses} ⊢ F`
  would keep the current sequent backend. Note this in the API docs.
- **`and_elim` cost**: balanced tree ⇒ O(log m) per clause; confirm
  `and_elim_l`/`and_elim_r` are the cheap derived rules (they are, in
  `DerivedRules`).

## Level 2 (further, optional): lower-level `Γ ⊢ b`

Beyond the AND-tree-as-one-HOL-hypothesis (level 1 above), a leaner path drops to
the `covalence-pure` base logic: carry `Γ` as an explicit AND-tree *term* and the
conclusion `b` flexibly (not necessarily `F`), skipping the HOL connective /
`or_elim` overhead entirely — "creative use of `Γ ⊢ b` via lower-level traits".
Bigger redesign; only if level 1's HOL-rule overhead is still the bottleneck
after measuring. Orthogonal to the reflective/WASM-oracle checker (the *native
speed* ceiling), which remains the separate long-term option.
