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

Separately, **`covalence-hol` is re-introduced** as a HOL-flavored analogue of
`covalence-metamath`: a crate of HOL utilities / proof-format consumers that does
**not** depend on `covalence-core` (§4).

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

(Exact partition decided when the split branch runs; this is the intended shape.)

---

## 4. Re-introduce `covalence-hol` (HOL utilities, no core dependency)

A **new** `covalence-hol`, peer of `covalence-metamath`: defines traits and APIs
for **consuming HOL proofs** and **does not depend on `covalence-core`**. It folds
in:

- the abstract HOL term/type/sequent representation and builder traits,
- **OpenTheory import** (merge in today's `covalence-opentheory`),
- later, HOL Light proof-trace consumption.

The soundness story gets *simpler*: observers now have only **simple first-order
types**. The first pass needs **no metavariables / type variables** at the Pure
level — those all live in the *internal* HOL. (Whether Pure ever grows such
features is an explicit later decision.)

---

## 5. Crate subgroups (legibility)

There are many `covalence-*` crates; flat `crates/*` no longer reads clearly.
The actual internal dependency graph is rendered in
[`crate-graph.md`](./crate-graph.md) (regenerate with the script below).

**Recommendation: do the grouping, but *last*** — after the `hol` split (§3–4)
and the cruft sweep (§6). Reasons:

- Directory nesting is **cosmetic to Cargo** (path deps don't care) yet churns
  every `path = "../x"` → `path = "../../wrap/x"` and conflicts with every
  in-flight branch/worktree (there are many). So it must be one mechanical commit
  landed when branch activity is low — *not* interleaved with the real work.
- Grouping **does not reduce "too much"** by itself; it relocates it. The real
  cognitive load is the `hol` megacrate, dead experiments, and a sprawling
  SKELETONS registry. Fix those first, *then* the surviving crates group cleanly.
- It helps **people more than agents** (agents navigate by grep/path already);
  the human win is a clear "where does this live" map and a visually obvious TCB
  boundary (`kernel/`).

The graph also surfaced a **layering inversion to resolve first**:
`covalence-wasm → covalence-core` (a wrapper depending on the TCB), which drags
`core` into `sat`/`lsp`/`wasm-store` transitively. Decide its tier (or cut the
edge) before drawing group boundaries.

Proposed grouping (Cargo supports `members = ["crates/*/*"]` globs), for the
dedicated move-branch:

| Group | Crates (illustrative) |
|---|---|
| `crates/wrap/` — external-dep wrappers | types, parse, sexp, rand, sig, hash, sqlite, json, wasm, arrow, parquet, smt, sat, grammar, spectec |
| `crates/store/` — content-addressing & storage | store, object, git, kv, graph, wasm-store |
| `crates/kernel/` — the three-layer kernel | pure, core, init/*, cons, eval, kernel |
| `crates/hol/` & frontends — proof-format importers | hol, metamath, opentheory, lean, alethe, egglog |
| `crates/lang/` — the surface language (future) | lang |
| `crates/app/` — user-facing | covalence (cli), repl, serve, client, lsp, proto, python, shell, llm, web-kernel |

Naming/exact membership to be settled on the move-branch. The point is **layered
directories that mirror the dependency stack**.

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

Audit of `docs/` (reconcile against the layers above):

| Doc | Disposition |
|---|---|
| `VISION.md`, `kernel-design.md`, `type-hierarchy.md`, `roadmap.md` | **Keep**; the four canonical docs. Update `roadmap.md` to point at this plan. |
| `covalence-pure.md` | **Keep**; mark as the base-logic design, cross-link this plan. |
| `refactor-plan.md` (this) | New; the reorg map. |
| `frontend.md`, `surface-syntax.md`, `surface-compiler.md`, `theories-models-and-logics.md`, `metatheory.md`, `observers.md` | **Keep as design sketches**; verify cross-references after the split. |
| `soundness-audit.md` | Keep; re-anchor to the Pure/Core/init trust boundary. |
| `peano-arithmetic-plan.md` | **Likely retire** — superseded (recursion theorem done; PA postulate-free). Confirm then delete. |
| `cov-project.md`, `web-kernel.md`, `wasm3-rust.md` | Keep, but re-home once `script`/`project` move into `covalence-init`/`covalence-lang`. |
| `docs/sketches/*` (MAPS, OBSERVERS, SAMPLE, ml-naive-compiler, spectec-phase1-status, spectec-verification-plan, `spectec-tasks/*`) | **Mostly retire** — spectec task cards (23–37) are completed branch work; archive. Keep only what's still a live design input. |

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
