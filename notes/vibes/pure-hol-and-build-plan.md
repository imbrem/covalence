# From here to: a real build system + observer-free, literal-free HOL

**Status:** AI-drafted detailed plan (2026-07), written to be checked against the
maintainer's intent. Two tracks that share one goal — *everything trusted is an
enumerable axiom at the base layer; everything built is a declared artifact*.
Companion to [`../plans/next-stage.md`](../plans/next-stage.md),
[`closed-world-kernel.md`](./closed-world-kernel.md), and
[`substrate.md`](./substrate.md).

---

## Track 1 — the build system

### What we actually build (the artifact inventory)

1. Native binaries: `cov` (clap CLI, embeds the web bundle under `--features static`).
2. Rust libs: the workspace graph (docs/deps tracks it).
3. The Python module: `covalence` cdylib via maturin, into a venv.
4. WASM guests: `wasm-build-guest` fixture (copied into `packages/covalence-wasm-js/src/__fixtures__/`), `kernel/hol/test-guest` (test-only).
5. The web kernel: `kernel/web` → wasm-bindgen bundle → `apps/covalence-web/src/lib/kernel/`.
6. The SvelteKit app: `apps/covalence-web/build/` (embedded by `server/core` rust-embed).
7. JS bundles: esbuild outputs for the VSCode extension (desktop + web).
8. Generated docs: `docs/deps/*` (dep graph + TCB closure; CI-gated).

The recurring failure mode (seen twice this week: the rust-embed depth bug, the
venv move): **artifacts 3–6 are stitched together by paths hidden inside
scripts/attributes, with no declared dependencies**. The fix is not "buck2
someday"; it is making every artifact a *named node with declared inputs* now,
in whatever engine.

### The ladder (each rung ships alone)

**Rung 0 — single-checkout simplification (now).**
One repo checkout is what we care about: one root-adjacent venv
(`crates/ffi/python/.venv`), no worktree-hopping logic in `activate.sh` beyond
the plain fallback, no transitional paths. DONE in this pass.

**Rung 1 — artifact discipline in bun (this month).**
Keep bun as the task runner, but every `bun run X`:
- *declares* its inputs/outputs at the top of the script,
- checks inputs exist and fails with "run `bun run Y` first" (or auto-runs it),
- never silently reads a stale artifact.
Concretely: a tiny `scripts/tasks.mjs` registry (task → {inputs, outputs, cmd,
deps}) that the package.json scripts call through. This is 90% of buck2's
day-to-day value at 2% of the cost, and it *documents the artifact graph* we'd
feed to buck2/cog later. The rust-embed `static` feature gets a `build.rs`
existence check with a clear error (same pattern as the deps gate).

**Rung 2 — hermetic-ish python (this month).**
The venv is a build artifact like any other: `bun run python:setup` creates it
(pinned interpreter + `maturin`,`pytest` versions), `build:python` = maturin
develop, `test:python` depends on both. Consider `uv` for speed/lockfile
(maintainer call — new tool). No activation magic in docs; only the tasks.

**Rung 3 — buck2 spike (when C-splits start).**
Scope: `lib/` tier + the two wasm guests + fixture copying — the leaf artifacts
with the worst path-stitching. Success = `buck2 build //crates/lib/...` and the
fixture rule replacing the hand `cp` in package.json. Decision gate afterwards:
expand to the full graph or stay hybrid (buck for artifacts, cargo for dev
loop). **Non-goal**: forcing rustc through buck for the inner dev loop —
cargo's incrementality + rust-analyzer stay.

**Rung 4 — cog dogfood (vision).**
The tasks.mjs registry (rung 1) is deliberately shaped like a build *manifest*:
content-addressed inputs/outputs. When `cog`/store mature, the registry becomes
the thing cog certifies (build-as-theorem: `store ⊢ output = f(inputs)`), and
buck2 compatibility is an interchange, not a rewrite.

---

## Track 2 — observers out, literals out: HOL as *just* HOL Light

### End state (the invariant to hold in your head)

- **`kernel/hol` is textbook HOL Light.** Types = `TyVar | Bool | Ind | Fun`
  (+ conservative `new_type_definition`); terms = `Var | Const | App | Abs`
  with `=` and `ε` the only primitive constants; `Thm` minted by the 10 rules +
  `define`/`new_type_definition`. **No `TermKind::Int`, no `TermKind::Blob`, no
  `obs_*` rules, no `reduce_prim`, no defs/ acceleration in the kernel.** The
  HOL crate is small enough to audit against the HOL Light manual page-by-page.
- **All computational power lives at the base layer** (`kernel/base`, the
  closed-world `Thm<L,P>`/`Language` kernel): `Nat`/`Int`/`Bytes` are base
  *languages* whose `CanonRule`s evaluate native `covalence_types` values,
  admits-gated and MANIFEST-enumerated. What used to be an "observer" is now an
  ordinary **base axiom**: a `Rule<L>` that mints a base-level fact, in the
  TCB *by declaration*, enumerable, diffable.
- **The bridge is the existing core-on-pure seam**: `hol::Thm` is already a
  newtype over `pure::Thm<CoreLang, IsThm(Γ, p)>`. Acceleration = a base rule
  that mints `IsThm(Γ, p)` *directly*, where `p`'s literal leaves are `toHOL`
  denotations (below) — sound because the derivation exists in pure HOL; the
  rule is a certified shortcut, never new strength. Nat/int/bytes facts enter
  HOL as `IsThm` certificates minted by admitted base rules, not as kernel
  primitives.
- **Literals: denote, never construct (`toHOL`).** The maintainer's key move
  (2026-07): the canonical HOL term for a native value is **never materialized**.
  `toHOL` is an *uninterpreted base op* per carrier —
  `ToHOL: Op<In = Nat, Out = HolTm>` (likewise `Int`, `Bytes`) — so the base
  expression `toHOL 5` *denotes* `S(S(S(S(S(Z)))))` without building it, and
  `toHOL b` for a megabyte bytestring denotes the mega-`cons`-tower for free.
  The HOL term formers (`app`, `const`, …) are base ops on the `HolTm` sort too,
  so partially-symbolic terms like `S (toHOL 4)` are just base expressions.
  Admits-gated rules then derive facts about the denotations directly:
  - **structural/unfolding equations** (`Eqn` at sort `HolTm`):
    `toHOL (n+1) = S (toHOL n)`, `toHOL (byte:rest) = cons (toHOL byte) (toHOL rest)`
    — the defining properties of the denotation;
  - **computation-backed derivability certificates** (`IsThm` facts):
    from native `2 + 2 = 4` (the Nat `CanonRule`) derive
    `IsThm(⊢ toHOL 2 + toHOL 2 = toHOL 4)` — HOL-provable equations minted
    because the arithmetic computes, without ever unfolding either side.

  The **soundness contract** of every such rule (its docstring obligation): for
  every native value `b` there *exists* a HOL term `[b]` such that the defining
  properties are derivable in pure HOL — existence-without-construction, the
  same principle as "a standard theorem means a derivation exists". This
  dissolves the numeral-representation question entirely (no binary-numeral
  machinery needed for efficiency — the Peano/cons denotations are fine because
  they are never built), and it keeps the "kernel as binary-data substrate"
  efficiency with ZERO kernel support: big values live as native leaves under
  `toHOL`, and only the equations you actually use ever exist. (This is the
  `ToHOL(Nat, Tm)` idea from the covalence-fol sketch, now landing as base ops
  + admitted rules.)

Trust story after: **TCB = base kernel (~1k LoC) + the base MANIFEST (each
admitted rule auditable in isolation) + textbook HOL Light (~small)**. The
`docs/deps/tcb.json` closure plus the runtime MANIFEST *is* the audit surface.

### Why the crate environment comes first (the splits)

Today the observer/literal surface is smeared through `kernel/hol/core` (defs/,
reduce, obs rules, Int/Blob in TermKind) and consumed all over
`kernel/hol/init` (60k lines). Removing anything requires first making the
seams *visible as crate boundaries* — this is the "environment" to build:

```
kernel/
  base/            covalence-pure (closed-world; grows Stage-3/4 builtins)
    trusted/       the base TCB
    eval/          NEW: Nat/Int/Bytes base languages + CanonRules (Stage 3-4)
  hol/
    logic/         NEW HOME of the pure HOL Light kernel (target of the purge)
    obs/           NEW: quarantine crate — ALL observer rules + TermKind::Int/
                   Blob acceleration surface moves here behind traits; nothing
                   new may depend on it (CI-gated dep check); it shrinks to zero
    init/          the theory catalogue (shrinks as acceleration re-routes)
    eval/          NEW: HOL-side acceleration = admitted base-rule bridges
                   (replaces obs/ consumers one call site at a time)
    metamath/ spectec/ wasm/   the drivers, unchanged consumers of logic/+eval/
```

The quarantine move is the key trick: **step 1 makes the problem enumerable**
(everything deprecated is in one crate with a greppable consumer list), without
changing any semantics. Then removal is *gradual by construction* — each PR
re-routes one consumer from `obs/` to `eval/`, the dep edge count on `obs/`
is the progress meter, and CI forbids new edges.

### The migration ladder

1. **Freeze + inventory** — DONE, without the `obs/` quarantine crate
   (maintainer decision: the observer rules were externally dead, so the
   quarantine's enumerability job is done by `scripts/purge-ratchet.mjs` +
   `docs/deps/purge-ratchet.json` (per-crate counts, decrease-only) and
   `dep-graph.mjs` `BANNED_EDGES`; the rules `Thm::obs_eq/obs_true/obs_imp`
   + `ObsEq`/`ObsTrue`/`ObsImp`/`Hint` were then deleted directly from
   `covalence-core`). `Obs` LEAVES remain as `new_type_definition`
   freshness tokens pending the `FreshId` reclassification.
2. **Base builtins** (closed-world Stages 3–4, already planned): `base/eval`
   with `Nat`/`Int`/`Bytes` languages; each op an admits-gated `CanonRule`
   over `covalence_types`; MANIFEST pinned by a golden test.
3. **The `IsThm` accelerator rules** (the observer replacement): for each
   observer use-class, one base `Rule` that mints the same fact as an `IsThm`
   certificate (arithmetic equalities; bytes equality/concat/length; the
   metamath/wasm-spec drivers' fact injection). Soundness note per rule: "the
   definitional proof exists in HOL; this rule is a shortcut" — the same
   discipline as `reduce_prim`'s docstrings today, but *enumerable* in the
   manifest instead of latent in the kernel.
4. **Re-route + shrink** (many small PRs): consumer by consumer, init's
   accelerated paths call `hol/eval` instead of `obs/`; literal-carrying terms
   switch to `toHOL` denotations (never-constructed canonical terms) with the
   unfolding equations + computation-backed certificates replacing kernel
   literals.
5. **Delete**: `obs/` reaches zero consumers → delete crate; `TermKind::Int`/
   `Blob` reach zero constructors → remove variants (a *kernel-shrinking*
   change — celebrate it); `hol/logic` diff-checked against the HOL Light
   datatype. `covalence-hol`(traits) collapses into `logic/`'s public surface.
6. **Rename with the splits**: as each new crate stabilizes it takes its
   hierarchical name (`covalence-kernel-hol-logic`, …) — names move when
   content moves, never before.

### Anti-sprawl rails (make regression structurally hard)

- **Dep-direction lint in CI** (extend `scripts/dep-graph.mjs`, which already
  computes the graph): allowed edges only —
  `lib → lib`, `proof → lib`, `store → lib`, `kernel/base → lib(types)`,
  `kernel/hol → kernel/base + lib + proof(readers)`, `server → kernel + store`,
  `app → server + kernel`, `ffi → kernel`, plus the explicit obs/ freeze.
  Group-level cycles stay allowed; *crate*-level cycles and layer-violations
  fail CI like a stale dep-graph does today.
- **TCB budget**: `docs/deps/tcb.json` is already golden-checked; add the base
  MANIFEST goldens as they land. A PR that grows the TCB shows it in-diff.
- **One-way doors documented**: SKELETONS stays open-work-only (this pass);
  each quarantine/freeze gets its SKELETONS entry deleted on completion, so
  the registry monotonically shrinks toward the vision instead of recording it.

## Track 3 — the CoreLang three-tier tower (maintainer directive, 2026-07)

Split `CoreLang` into a **tower of three `Language` subsets**, lower casting
into higher via the existing `extends`/`lift` (never downward):

1. **`CoreHol`** — pure HOL Light: the 10 rules + `define`/`new_type_definition`
   + `FreshLeaf` typedef freshness. Nothing computational; auditable
   page-by-page against the HOL Light manual.
2. **`CoreEval`** — extends `CoreHol` + `Builtins` (the covalence-pure-eval
   CanonRules) + the toHOL/cert rules. (Today's post-purge `CoreLang` ≈ this.)
3. **`CoreWasm`** — extends `CoreEval` + the WASM-oracle/executor rules (the
   substrate vision's executor tier).

**Payoff = the test story.** An eval-tier definition's properties can be
*proved in `CoreHol`* — a `Thm<CoreHol, …>` about an op's defining equations is
machine-checked evidence its `CanonRule` semantics match the definitional
unfolding, upgrading the cert docstrings' existence-without-construction prose
(and the differential suites) into theorems. And a theorem's *language
parameter becomes its trust label*: `Thm<CoreHol, _>` carries no computation
TCB at all. Lands with S11 (when the pure set becomes exactly textbook HOL
Light) — mostly splitting the manifest downward, not new kernel surface.

## Track 4 — f32/f64 + ball arithmetic (parallel to the purge)

Floats unlock **ball arithmetic** → statistics. The design falls out of what
exists: `f32 := u32` / `f64 := u64` newtype specs already sit in
`defs/floats.rs`, and `base/trusted/float.rs` already solves the leaf problem
(bitwise `Eq` so `NaN ≠ NaN` never breaks reflexivity; one audited
NaN-canonicalization point implementing the WASM deterministic profile). A
float **is** its bit-pattern, so every op is definitional + computable and the
cert/toHOL machinery applies unchanged; the fallibility rule (Track just above)
is trivially met (ops are total on bit-patterns).

- **F0** finish the base op inventory in `float.rs` (has add/sub/mul/div; add
  sqrt, min/max, abs/neg/copysign, ceil/floor/trunc/nearest, comparisons,
  promote/demote, int↔float converts + `trunc_sat`, reinterprets).
- **F1** `covalence-pure-eval` `FloatOps` CanonRules + a **differential suite
  against real wasmtime execution** (`covalence-wasm` `runtime` feature) — the
  oracle is an actual engine, not self-comparison.
- **F2** HOL op definitions via the S9 Const-twin machinery (defining
  properties = the WASM spec equations on bits); script literal display/parse.
- **F3** `FloatCert` admitted family (FixedWidthCert pattern) + `covalence-hol-eval`
  wiring + `ToHolF32`/`ToHolF64`; route literals through the S7 `mk_u32` facade
  so S10's `SmallInt` deletion stays transparent (the parallelism enabler).
- **F4** ball arithmetic (init, untrusted): `ball := f64 × f64` (center,radius);
  ops **concrete** (`fl(a•b)` + outward ulp-bump) so statistics runs on
  certified computation immediately, with **enclosure theorems**
  (`x∈a, y∈b ⟹ x•y ∈ ball_add a b`) proved incrementally — pure-`CoreHol`-tier
  lemmas about eval-tier definitions, i.e. Track 3's test story with a real
  application.
- **F5** long-term: lower the WASM numerics via `covalence-spectec` to replace
  the hand-written defining properties; wasmtime differential becomes certified
  redundancy.

**Interlock:** F0/F1 are parallel-safe with S10/S11 (disjoint files/families,
run in a worktree); F2 needs S9 (landed); F4 enclosure lemmas exercise Track 3.
