# Three-layer kernel refactor — plan

> **STATUS: PLAN (scoping, not yet executed).** Captures the refactor direction
> sketched after the first milestone — *importing `set.mm` into the internal
> logic*. This document is the shared map for a multi-branch effort: this branch
> only **scaffolds** (`covalence-pure` empty crate + this plan); later branches
> execute the moves. Companion to [`covalence-pure.md`](./covalence-pure.md)
> (the base-logic design) and [`roadmap.md`](./roadmap.md).

The repo has grown to many crates, and `covalence-hol` is by far the largest. The
problem is **legibility, not obsolescence**: most of `covalence-hol`'s *content*
is kept — the catalogue, the theories, the proof machinery, the Metamath bridge
are all live — but it has accreted into one megacrate that is hard to navigate.
The refactor *factors* it, it does not gut it. The goals, in order:

1. **Introduce `covalence-pure`** — a small, high-trust first-order base logic.
2. **Split `covalence-hol`** into a HOL-utilities crate (no `covalence-core`
   dependency, peer of `covalence-metamath`) and a `covalence-init` *family* of
   semi-trusted crates.
3. **Re-shape the crate stack** into legible layers (kernel / extensions /
   programmatic API / language / apps), grouped into subdirectories so the repo
   reads clearly to agents and people.
4. **Aggressively remove cruft** — git history is the backup.
5. **Bring the docs and skills back into sync** with the above.

---

## 1. Target architecture: three layers

```
  ┌─ covalence-lang ───────────── high-level surface language (future)
  │     depends on
  ├─ covalence-kernel ─────────── full user-facing PROGRAMMATIC API +
  │     TCB integration point: init + cons + eval, the standard TCB
  │     presets (base sets B), and PKI/federation trust options
  │
  │   ┌─ covalence-cons ──── content-addressing extension module
  │   ├─ covalence-eval ──── WASM-acceleration extension module
  │   │     depend on
  │   └─ covalence-init/* ── semi-trusted high-level covalence API:
  │           extension modules (nat/int/bytes/list/…), basic machinery,
  │           a very basic surface syntax — "a simple core for the language"
  │             built on
  ├─ covalence-core ──────────── the HOL TCB (pure HOL kernel)
  │     built on
  └─ covalence-pure ──────────── the base logic (TCB floor)
```

Three layers of trust, decreasing as you go up:

- **`covalence-pure`** — trusted *unconditionally*. A very small constructive
  first-order logic (§2). The user is hand-authoring this; maximize auditability.
- **`covalence-core`** — the HOL TCB, a pure-HOL kernel *built on* Pure. Trusted,
  but its trust reduces to Pure + the HOL object-logic encoding.
- **`covalence-init` + extensions** — *semi-trusted*. The catalogue
  (nat/int/bytes/list/prod/…), proof machinery, and a minimal surface syntax.
  Properties about e.g. `Nat`'s definition can be proved *without* trusting that
  definition, because the definition lives outside the meta-TCB (§2.3).

Above the kernel: `covalence-kernel` exposes the low-level **programmatic** API
(init + content-addressing + WASM), and `covalence-lang` will be the high-level
language. Everything else depends on one of those two.

**The name `covalence-hol` is repurposed.** Today's heavy `covalence-hol`
*content* moves wholesale into **`covalence-init` and its subcrates** (§3); the
freed name `covalence-hol` is then **re-introduced as a thin crate, exactly like
`covalence-metamath`** — HOL utilities / proof-format consumers, depending **not**
on `covalence-core` (§4). So after the move: `covalence-hol` = thin HOL substrate
(peer of `covalence-metamath`); `covalence-init` = the semi-trusted API family
that used to *be* `covalence-hol`.

---

## 2. `covalence-pure` — the base logic

> The detailed design lives in [`covalence-pure.md`](./covalence-pure.md). That
> document has two stratified presentations; the **current direction** is the
> Rust-trait encoding below, which refines the earlier "observer + two
> assumption-set" framing (still valid — observers become `Ker` entries).

### 2.1 A constructive first-order logic, encoded in Rust's trait system

The idea is to represent a **very basic constructive first-order logic** directly
with Rust's own types and traits — propositions-as-types, Curry–Howard at the
host level:

- `(P, Q)` (a Rust tuple) represents **`P ∧ Q`**.
- `Either<P, Q>` represents **`P ∨ Q`**.
- A trait `Prop` for **global predicates** (closed propositions).
- A trait `Local<T>` (name provisional) for **local, *inhabited* predicates on
  `T`** — predicates that come with a witness. `Local<T>` is what supports
  **sigma-types**.

With those, a sigma-type recovers the kernel's term representation. Schematically:

```rust
type Tm = Sigma<TmKind<Tm>, HasTy<Ty>, Ker>;
```

i.e. a term is "a `TmKind` together with the *local* fact `HasTy<Ty>` that it has
a type, validated against the meta-assumption context `Ker`." (Exact shape TBD —
this is the load-bearing sketch, not final API.)

### 2.2 `Ker` — the meta-assumption context (the dynamic TCB)

The third type parameter, **`Ker`**, is the set of **meta-assumptions**, and it
is the crux of the design:

- A meta-assumption can **promote computations to theorems** — e.g. a WASM
  computation, or a builtin operation on `u8`/`u16`/… literals.
- **The meta-assumption context *defines* the TCB.** Carrying data in `Ker` is
  *optional*, which yields a **dynamic TCB**: in general `Arc<dyn Ker>`, so the
  trust surface of a fact is a value you can inspect, grow, and discharge.
- This is the same two-set discipline as [`covalence-pure.md` §4]: the ordinary
  logical assumptions vs. the *meta*-assumptions (which executors / accelerators
  / observers a fact leans on). The earlier doc's `Observer` + `attest` mechanism
  becomes **entries in `Ker`**.

Why a relatively rich base system (sigma-types, `Local<T>`, `Ker`) rather than
the absolute minimum: it lets us **naturally represent things like WASM** and
builtin literal computation through `Ker`, so the same machinery handles the
object logic, executors, and accelerators uniformly.

### 2.3 Pure HOL as a `covalence-core` TCB on top

`covalence-pure` defines the abstract logic; `covalence-core` defines a **TCB for
pure HOL** on top of it. Then **extension modules** (`Nat`, `Bytes`, `Int`, …)
are added *above* — crucially **outside** the meta-TCB. This is the payoff:

> We can prove properties about the *definition* of `Nat` (etc.) **without
> relying on that definition being correct**, by leaving it out of the meta-TCB.

This is "nat the accelerator = nat the definition, made rigorous and
non-circular" from [`covalence-pure.md` §4.2] — develop the theory without the
accelerator's meta-tag, then discharge.

### 2.4 First step (deliberately incremental)

Factor the existing crate in two: stand up `covalence-pure` (abstract logic),
keep `covalence-core` as the HOL TCB on top. **Done in this branch only as far as
the empty scaffold + the `covalence-core → covalence-pure` edge.** The concrete
`Prop`/`Local`/`Sigma`/`Ker` API is authored next.

---

## 3. Module structure: `covalence-init` as a family

Break the bulk of today's `covalence-hol` into **`covalence-init`** — *a crate
containing a family of crates*, each describing one of:

- **basic extension modules** — the theory catalogue (`init/` today:
  nat/int/rat/real/bytes/list/prod/option/result, the algebra theories
  ring/semiring, prop, the inductive engine),
- **basic machinery** — proof tactics (`proofs/`), the AC tactic, rewriting,
  categorical/monoidal structure,
- **an extremely basic surface syntax** — the `.cov` proof-script layer
  (`script/`) and project compiler (`project.rs`), pared to a simple core.

Content-addressing and WASM acceleration are **special extension modules**:

- **`covalence-cons`** — content-addressing (today's `hash.rs`, BLAKE3-keyed
  hashing, canonical S-expression syntax), depending on `covalence-init`.
- **`covalence-eval`** — WASM acceleration, depending on `covalence-init`.

Then:

- **`covalence-kernel`** is the **TCB integration point** (not merely a
  re-export). It composes `covalence-init` + `covalence-cons` + `covalence-eval`
  into the full low-level **programmatic** API *and* packages the **standard TCB
  presets** — concrete base meta-assumption sets `B` (`covalence-pure.md` §4.1)
  the user can pick off the shelf:

  | Preset | Trusts (`B`) |
  |---|---|
  | `nothing` | bare Pure logic — every computation is an explicit assumption |
  | `cons` | + hash-consing / content-addressing |
  | `std` | + nat / int / bytes accelerators (+ cons) |
  | `std+wasm` | + the WASM executor |
  | (later) | + x86, other executors |

  Plus **PKI / federation options** — the *trust logic* for federating with
  other kernels: signed-theorem attestations (`covalence-sig`,
  `kernel-federation-pki`) enter as meta-assumptions ("admit if signed by a
  trusted key"), so a remote kernel's theorem rides as one more discharge-able
  tag in `M`. Choosing a preset = choosing which executor/accelerator/peer tags
  sit in your base `B`; everything outside it rides explicitly.

  (Replaces the legacy arena/egraph `covalence-kernel`, which is removed.)
- **`covalence-lang`** is a full language built on top of `covalence-kernel`.
- Everything else depends on `covalence-kernel` (programmatic) or
  `covalence-lang` (high-level).

### Today's `covalence-hol` modules → destinations (sketch)

| Module | Destination |
|---|---|
| `init/`, `ring/`, `semiring/`, `peano/`, `models/`, `category/`, `monoidal/` | `covalence-init` (extension modules) |
| `proofs/`, `ac.rs`, `debug.rs` | `covalence-init` (machinery) |
| `script/`, `project.rs`, `sexp.rs` | `covalence-init` (basic surface syntax) → later `covalence-lang` |
| `hash.rs` | `covalence-cons` |
| `regex/`, `spectec/` | `covalence-eval` / `covalence-init` (verified-WASM sketches, WASM semantics) |
| `traits.rs` (HolLightKernel/Terms/Types builder API) | **new `covalence-hol`** (general HOL API, §4) |
| `metalogic/` (Derivable, Metamath bridge) | split: HOL-side utilities → new `covalence-hol`; kernel-coupled metatheorems stay near `covalence-init` |
| `hol_light_obs.rs` | boundary glue — likely `covalence-core`/`covalence-init` |

(Exact partition decided when the split branch runs; this is the intended shape.
The **concrete, execution-ready** module assignment + cruft list is in
[`init-hol-split.md`](./init-hol-split.md).)

---

## 4. Re-introduce `covalence-hol` (thin HOL surface)

A **new, thin** `covalence-hol` — the HOL builder/trait surface proof *consumers*
need (`types`/`traits`/`HolLightCtx`, the surface the OpenTheory importer uses).
See [`init-hol-split.md`](./init-hol-split.md) for the exact contents. It folds
in, over time:

- **OpenTheory import** — merge today's `covalence-opentheory` in **behind an
  `opentheory` feature** (its `ureq` network dep gated too), then delete the
  standalone crate.
- later, HOL Light proof-trace consumption.

**Note on the no-core-dep goal:** the *initial* split's `covalence-hol` still
depends on `covalence-core` (the builder traits construct `covalence_core::Term`).
Becoming a genuinely core-free peer of `covalence-metamath` is a *later*
decoupling, not the first move.

The soundness story gets *simpler*: observers now have only **simple first-order
types**. The first pass needs **no metavariables / type variables** at the Pure
level — those all live in the *internal* HOL. (Whether Pure ever grows such
features is an explicit later decision.)

---

## 5. Crate organization: domain groups + layer groups + umbrellas

Flat `crates/covalence-*` no longer reads clearly. The reorg has two goals:
*conceptual clarity* (the tree should be a map of **what we reason about** and
**what the TCB is**) and *ergonomics* (depend on a domain in one line). The
machine-tracked graph + TCB closure live in [`deps/`](./deps/) (`bun run deps`).

### 5.1 The organizing axis: domain vs layer

Two kinds of top-level group:

- **Domain groups** — an external system or formalism we *interface with **and
  reason about*** (git, SQL, wasm, the logics, external provers). The decisive
  fact is that almost every such crate is **dual-role**: it has a *format/concept*
  aspect (git trees; SQL schema; DIMACS) *and* a *program* aspect (the git VCS; a
  DB engine; a solver). You can't split the directory by aspect — one crate is
  both — so group by **subject**: everything about git under `git/`, everything
  about SQL under `sql/`, regardless of which aspect a given crate covers.
- **Layer groups** — covalence's own generic vertical stack, plus primitives we
  *just call*: `util/`, `store/`, `kernel/`, `init/`, `lang/`, `app/`.

**The promotion rule:** a crate lives in `util/` while we merely *use* it
(hash, sig, parse); it graduates to its own domain group the moment we start
*reasoning about* it. So the tree literally tracks the reasoning frontier.

### 5.2 The TCB rule

Classify by **role in our system**, except: *reasoning about a system is itself
a primary role* (that's why `git`/`sqlite` are domains, not buried in `store/` —
`store/` keeps the *abstract* content-addressing core and depends on them as
backends). And: **the TCB stays out of the umbrella game** — `covalence-core` /
`covalence-pure` are plain standalone crates with an unconditional, minimal
dependency list, never "core with features that might pull X." The trusted base
must be auditable without reasoning about feature flags. `deps/tcb.json` tracks
its closure; CI flags any change.

### 5.3 The umbrella pattern (domain = facade crate + feature-gated subcrates)

A domain group is a **root umbrella crate** plus feature-gated subcrates:

```
crates/hol/
  Cargo.toml        covalence-hol  (umbrella; default-features minimal)
                      [features] interface (default), builder, opentheory
  interface/        covalence-hol-interface   types + traits — CORE-FREE
  builder/          covalence-hol-builder     HolLightCtx over covalence-core
  opentheory/       covalence-hol-opentheory  importer; gates `ureq`
```

The umbrella re-exports `#[cfg(feature = "builder")] pub use covalence_hol_builder as builder;`
etc., so a consumer writes `covalence-hol = { features = ["opentheory"] }`.

- **Group-level dependency cycles are fine** — Cargo only forbids *crate*-level
  cycles, and directories aren't a build concept. Wire domains and layers in both
  directions freely as long as the crate DAG stays acyclic.
- **Feature unification caveat:** in a `--workspace` build Cargo compiles the
  umbrella once with the *union* of requested features, so "minimal by default"
  benefits *external/sliced* builds (`-p covalence-hol --no-default-features
  --features interface`), not the monorepo build. The **auditable unit is the
  subcrate** (`hol/interface` is provably core-free on its own); the umbrella is
  convenience.
- Package names keep the `covalence-` prefix (`covalence-hol-interface`);
  **directories drop it** (`crates/hol/interface`). Never rename packages.

### 5.4 The layout

```
crates/
  util/     types parse sexp hash sig rand grammar json arrow parquet   (we just call these)
  store/    store object kv graph                                       (abstract content-addressing)
  git/      git                        ┐ domains: subject groups, dual-role crates
  sql/      sqlite                     │ together (format + engine + reasoning +
  wasm/     wasm spec spectec build-guest   kernel-bridge), umbrella where useful
  logic/    metamath sat smt           │ (cluster of small single-crate domains)
  provers/  lean egglog opentheory     ┘ (external provers we import from)
  kernel/   pure core hol kernel alethe   (TCB + builder + kernel-coupled bridges)
  init/     init (+ family)               (semi-trusted native-covalence-library layer)
  lang/     forsp (+ future surface/lang)
  app/      covalence repl serve client lsp proto python shell llm fuse web-kernel
theories/   (future: pure-`.cov` stdlib — no Rust; built on init's tactics)
```

- `logic/` = systems we **model natively** (metamath's full engine; SAT/SMT
  formula+proof models). `provers/` = systems we only **import from** (parsers
  for another tool's artifacts). Promote a clustered crate to its own domain
  group once it grows (e.g. metamath's kernel bridge in `init/metalogic` →
  `metamath/bridge`).
- `hol` is in `kernel/` while it still depends on `core`; its `interface`
  subcrate is core-free, so it can migrate to a `hol/` domain group once
  decoupled.
- arrow/parquet/json sit in `util/` until we reason about tabular data, then
  graduate to a `data/` domain (the promotion rule in action).

### 5.5 Sequencing & caveats

- **Do the move as one mechanical commit, when branch activity is low** — every
  `path = "../covalence-x"` changes and it conflicts with in-flight worktrees.
- **Resolve the layering inversion** the graph shows — `covalence-wasm →
  covalence-core` (a util-ish crate depending on the TCB) drags `core` into
  `sat`/`lsp`/`wasm-store`; cut or re-tier that edge before finalizing.
- **First domain to land: `hol/`** — carve `interface`/`builder`, stand up the
  umbrella, and fold OpenTheory in as the `opentheory` feature. It finishes the
  hol work, delivers the core-free `interface`, and establishes the template.
- `members = ["crates/*", "crates/*/*"]` to pick up nested subcrates.

---

## 6. Cruft to evaluate for removal

Aggressive removal is fine — git history restores anything. Candidates to review
on a cleanup branch (do **not** blanket-delete; confirm each is unreferenced):

- **`covalence-shell`** — thin re-export over kernel + hol; folds into the new
  `covalence-kernel` re-export façade.
- **Legacy `covalence-kernel`** internals (arena + egraph + UF) — superseded; the
  name is reused for the new re-export façade.
- **`covalence-forsp`**, **`covalence-fuse`**, **`covalence-grammar`** — assess
  whether still on the critical path or experiments to archive.
- **Keep — these are north-star seeds, not cruft:** `covalence-lean` (the
  type-theory / MLTT seed, §7), `covalence-egglog` / `covalence-alethe` / SMT
  (the sledgehammer), `covalence-opentheory` (folds into the new `covalence-hol`).
- Stale **docs sketches** (§8).

Each removal is its own small commit so it can be cherry-picked / reverted.

---

## 7. North stars (long-term, to align — not to build now)

These shape the design without being scheduled work. The unifying picture:
**many first-class proof systems, related through a universal substrate.** We
want, as first-class citizens — not afterthoughts —:

- **Generalized Haskell** — first-class (much of `covalence-hol` exists for this;
  it is *not* superseded).
- **ACL2 / full Lisp** — internalizing ACL2 proofs.
- **Type theories** — MLTT-style (Lean; `covalence-lean` is the seed),
  LF-style, and **HoTT** in the long run.
- **Metamath as the universal substrate** — the role of `covalence-metamath` is
  to be the common ground these systems **relate to each other** through: a place
  to *state the initial inter-system correctness theorems*. It is **not** a
  communication/interchange format used in practice — systems don't talk *in*
  Metamath; Metamath is where "system A's theorem corresponds to system B's" is
  *stated* and certified.

Plus the executor/tooling north stars:

- **WASM acceleration + content-addressing** — givens (`covalence-eval` /
  `covalence-cons`).
- **A "sketching" API for verified WASM programs** — e.g. parsing regexen
  (`regex/` is the seed), building up into an interesting macro language.
- **First-class SMT** — "we really need a sledgehammer."
- **A tiny subset of x86 as an alternative evaluator** (plus a WASM *emulator*
  for it) — the multi-executor end of the Pure design (`N` executors).
- **Near-term concrete north star: import a Git repo into the prover.** Move much
  of `covalence-git` into a subcrate of `covalence-init` depending on
  `covalence-cons`, formalizing Git's tree format — then importing a real Git
  repository *into* the theorem prover.

---

## 8. Docs & skills cleanup

Audit of `notes/` (reconcile against the layers above):

| Doc | Disposition |
|---|---|
| `VISION.md`, `kernel-design.md`, `type-hierarchy.md`, `roadmap.md` | **Keep**; the four canonical docs. Update `roadmap.md` to point at this plan. |
| `covalence-pure.md` | **Keep**; mark as the base-logic design, cross-link this plan. |
| `refactor-plan.md` (this) | New; the reorg map. |
| `frontend.md`, `surface-syntax.md`, `surface-compiler.md`, `theories-models-and-logics.md`, `metatheory.md`, `observers.md` | **Keep as design sketches**; verify cross-references after the split. |
| `soundness-audit.md` | Keep; re-anchor to the Pure/Core/init trust boundary. |
| `peano-arithmetic-plan.md` | **Likely retire** — superseded (recursion theorem done; PA postulate-free). Confirm then delete. |
| `cov-project.md`, `web-kernel.md`, `wasm3-rust.md` | Keep, but re-home once `script`/`project` move into `covalence-init`/`covalence-lang`. |
| `notes/sketches/*` (MAPS, OBSERVERS, SAMPLE, ml-naive-compiler, spectec-phase1-status, spectec-verification-plan, `spectec-tasks/*`) | **Mostly retire** — spectec task cards (23–37) are completed branch work; archive. Keep only what's still a live design input. |

Audit of `.claude/skills/` (all `disable-model-invocation: true`, i.e. reference
docs): `metamath-performance`, `performance`, `vscode-extension`, `wasm-guide`,
`web-server`. All still relevant; refresh crate names/paths after the split
(especially `metamath-performance`, which references `covalence-hol metalogic`).

The root `CLAUDE.md` "Core Crates" / "Wrapper Crates" lists must be rewritten to
the grouped layout once the moves land.

---

## 9. Sequencing (one branch per step, small commits)

1. **This branch** — `covalence-pure` empty scaffold + `core → pure` edge + this
   plan + low-risk docs touch-ups.
2. **`covalence-pure` design** — author the `Prop`/`Local`/`Sigma`/`Ker` API
   (the user leads; high TCB scrutiny).
3. **Split `covalence-hol`** — carve out new `covalence-hol` (utilities, no-core)
   + `covalence-init` family; fold in `covalence-opentheory`.
4. **Extensions** — `covalence-cons` (from `hash.rs`) + `covalence-eval`.
5. **Re-export façade** — rebuild `covalence-kernel`; remove legacy internals +
   `covalence-shell`.
6. **Subgroup move** — relocate crates into `crates/<group>/`; update globs +
   `CLAUDE.md`.
7. **Cruft sweep** — per §6, each removal its own commit.
8. **`covalence-git` → `covalence-init` subcrate** — the Git-import north star.

Steps 3–8 each verify with `bun test` (Rust + Python) before merge.
