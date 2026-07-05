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
  that mints `IsThm(Γ, ⌜2+3=5⌝)` *directly* (sound because the definitional
  unfolding exists in HOL — the rule is a certified shortcut, never new
  strength). Nat/int/bytes facts enter HOL as `IsThm` certificates minted by
  admitted base rules, not as kernel primitives.
- **Numerals/literals become definitional**: nat = HOL-Light-style binary
  numerals (`NUMERAL`/`BIT0`/`BIT1` over Peano zero/suc); int = the existing
  `(nat × nat)/~` quotient; bytes = `list u8` with u8 as a defined enumeration
  — and their *literal syntax* is sugar that elaborates to those terms, with
  equality/arithmetic on big literals discharged by base-rule certificates (so
  we keep the "kernel as binary-data substrate" efficiency WITHOUT the kernel
  primitives).

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

1. **Freeze + inventory** (1 sitting): CI check "no new deps on the observer
   surface"; a generated list of every `obs_eq/obs_true/obs_imp`,
   `hol_light_obs`, `TermKind::Int/Blob`, `reduce_prim` call site.
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
   accelerated paths call `hol/eval` instead of `obs/`; numerals switch to the
   definitional representation with certificate-backed literal equality.
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
