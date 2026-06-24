# Compiling a multi-file `.cov` project

> **DIRECTION + working prototype.** The dependency-resolving `.cov`→`.cov`
> loader (§3) is **implemented** (`covalence-hol/src/project.rs`). The
> bidirectional Rust↔`.cov` resolution (§4), the mutual-recursion fixpoint
> (§5), and the WASM-component / Cargo-features distribution story (§7) are
> **design only** (tracked in `crates/covalence-hol/src/SKELETONS.md`).

## 1. The problem

A Covalence "standard library" is today a pile of `.cov` theory files
(`init/logic.cov`, `init/nat.cov`, `init/rat.cov`, `init/set.cov`, …) **plus**
the Rust code that surrounds them. Each `.cov` file declares its dependencies
with `(#import NAME)` directives; `NAME` is resolved to a pre-built [`Env`] by a
**resolver closure** the host supplies to `script::run`.

The wiring is entirely manual:

- Each `.cov` theory gets a hand-written `cov_theory!` block
  (`init/logic.rs`, …) that lists its `import "name" = expr;` dependencies and
  force-evaluates them eagerly (so the nested `block_on` never re-enters).
- `init::library_env(name)` is a `match` arm per theory mapping a string to
  its `Env`, and `prime_library_imports` scans a script's top-level
  `(#import …)` forms to warm those statics before the proof runtime starts.
- The compile **order** is implicit — it falls out of the Rust call graph and
  `LazyLock` forcing order. There is no project-level dependency graph, no
  topological build, and no single entry point that takes "these `.cov` files +
  these Rust pieces" and produces "the checked theory".

Two further pains, both about the **Rust↔`.cov` boundary**:

- A `.cov` file frequently imports a **Rust-supplied "seam" env**: `nat.cov`
  imports `natrec` (the recursion-equation givens proved in `init/nat.rs`),
  `rat.cov` imports `ratprim`, `set.cov` imports `setprim`. These are
  `.cov`→Rust *constant/lemma* edges, wired by hand.
- The reverse edge — Rust code that needs a constant/theorem a `.cov` file
  proved — exists only through the `cov_theory!` accessor `fn`s, and there is
  no way to express genuine **mutual** reference (a Rust module and a `.cov`
  file each needing the other).

The vision is **one function in `init/mod.rs`** that compiles a project of
mutually-referencing `.cov` files *together with* Rust code, handling
dependencies **both ways**, replacing the per-theory `cov_theory!` + `match`-arm
wiring with an automatic dependency graph and topological build.

## 2. The project model

A **project** is:

- a set of **`.cov` source units** — each a `(name, source)` pair. The name is
  the `(#import …)` target other units use and the key the compiled environment
  is looked up under;
- a set of **Rust-supplied seam environments** — pre-built [`Env`]s a `.cov`
  unit may `(#import …)` (the `natrec` / `ratprim` / `setprim` givens; `core`
  is always provided). These are project **leaves**: no `.cov` body, always
  available;
- a set of **Rust-supplied FFI tactics** — resolved by
  `(#register-ffi-tactic NAME)` inside a unit (e.g. `tauto`).

Compiling the project yields, per unit, its **exported [`Env`]** (what
downstream units — and downstream Rust — pull lemmas/constants out of) plus the
**list of checked theorems**. Every theorem is re-derived by the real kernel:
**the sources are untrusted**; the prototype runs each one through
`script::run` → `Theory::resolve_blocking`, exactly the path
`check_script`/`cov_theory!` use.

## 3. Dependency graph + topological compile order (implemented)

The loader's core is mechanical and is the **most concrete win** — it replaces
the hand-ordered `library_env` wiring with an automatic build:

1. **Discover edges.** For each unit, parse its source and collect the names in
   its top-level `(#import NAME)` directives (the same scan
   `prime_library_imports` already does, generalised). This reads the
   dependency edges **out of the sources themselves** — no separate manifest.
2. **Classify each import.**
   - `NAME` is another **source unit** → a `.cov`→`.cov` **graph edge**.
   - `NAME` is `core` or a **registered Rust seam env** → a **leaf** (always
     available, *not* a graph edge), validated so a typo fails fast.
   - otherwise → `UnknownImport { unit, missing }`, reported before any kernel
     work.
3. **Topologically sort** the unit graph (Kahn's algorithm over in-degree, with
   a name-sorted ready set for **deterministic** order). A cycle leaves units
   with non-zero in-degree → `Cycle(units)`.
4. **Compile in order.** Walk the units dependency-first. Maintain a map of
   already-compiled units' exported envs. Each unit's resolver closure resolves
   `core` → the prelude, a sibling unit name → its compiled exported env, a
   seam name → the registered Rust env; the tactic closure resolves FFI
   tactics. Run the unit through the kernel; store its exported env for the
   units that import it.

### The entry point

```rust
// covalence-hol/src/project.rs
pub fn compile_project(
    sources:   impl IntoIterator<Item = CovSource>,
    rust_envs: impl IntoIterator<Item = (String, Env)>,      // seam givens, `core` implicit
    tactics:   impl IntoIterator<Item = (String, Arc<dyn Tactic>)>,
) -> Result<CompiledProject, ProjectError>;

// builder form
Project::new()
    .source("base", base_src)
    .source("mid",  mid_src)            // mid: (#import base)
    .rust_env("natrec", init::nat::natrec_env())
    .tactic("tauto", Arc::new(init::logic::Tauto))
    .compile()?;                        // → CompiledProject { envs, thms, order }
```

`CompiledProject` exposes `env(name) -> Option<&Env>`, the per-unit `thms`, and
the `order` the units compiled in. The shape mirrors `init::library_env` but is
*computed*, not hand-written: ultimately `library_env`/`library_tactic` become
a single `Project` definition whose `.compile()` result is cached, and the
per-theory `cov_theory!` blocks collapse into entries in that one project.

### How it builds on the existing `Env`/resolver mechanics

The prototype changes nothing in the kernel or `script` layer; it composes what
is already there:

- **`script::run(src, resolver, tactics)`** is called once per unit. The
  `resolver: Fn(&str) -> Option<Env>` and `tactics: Fn(&str) -> Option<Arc<dyn
  Tactic>>` are exactly today's signatures — the loader just *constructs* the
  resolver from the accumulated compiled envs instead of a fixed `match`.
- **`Theory::env()`** gives a unit's exported [`Env`] (driven by its
  `(#export …)` / `(#provide …)` directives). That env, cloned, is what the
  resolver hands to a downstream unit's `(#import NAME)` — the same mechanism
  `cov_theory!`'s `ENV` static exposes, but threaded automatically.
- **Eager forcing.** Each unit is `resolve_blocking`-forced before the next
  compiles, so a downstream unit's resolver only ever **clones an
  already-built env** — never nests one `block_on` inside another. This is the
  same invariant `cov_theory!` maintains by forcing its `import` exprs eagerly,
  and the same reason `check_script` calls `prime_library_imports`. (When
  `script::block_on` becomes a nestable synchronous executor — see the script
  SKELETONS — this ordering constraint relaxes and the loader could compile
  units concurrently.)

### Error propagation

`ProjectError` separates **graph errors** (`UnknownImport`, `Cycle`,
`DuplicateUnit`) — surfaced before any kernel work — from a **per-unit compile
error** (`Unit { unit, source: ScriptError }`) that carries the failing unit's
name alongside the underlying script/kernel error. So a wrong proof in
`nat.cov` reports as `unit 'nat': conclusion mismatch …`, not an anonymous
failure.

## 4. The Rust↔`.cov` boundary (the bidirectional vision)

The prototype handles two of the three edge directions:

- **`.cov` → `.cov`** — automatic graph edge (§3). ✅
- **`.cov` → Rust const/tactic** — a `.cov` imports a registered seam [`Env`]
  or FFI [`Tactic`]; these are project inputs, resolved like any leaf. ✅
- **Rust → `.cov` const/theorem** — Rust code consuming a `.cov`-proved
  lemma. Today this is *post-hoc*: after `compile()`, Rust reads it out of
  `CompiledProject::env(name)` (the same data `cov_theory!`'s accessor `fn`s
  expose). What is **not** yet handled is when that Rust code is itself a
  *project input feeding a later `.cov` unit* — i.e. a genuine cycle through
  the Rust↔`.cov` boundary. ⚠️ deferred (§5).

The longer-term framing: **a Rust crate is a first-class but basic way to build
a Covalence project.** The crate is compiled to **WASM against an abstract
Covalence API** (the `cov:*` WIT surface — kernel rules, the store, the
observer substrate), so "Rust seam env" and "`.cov` unit" become two
producers of the *same* artifact kind: a node in the project graph that, given
its imports' exported environments, emits an exported environment. A `.cov`
unit emits one by replaying a proof script; a Rust unit emits one by running
compiled WASM that calls the abstract kernel API. The loader is identical
either way — it only sees "node with imports → node with exports". This is the
narrow-waist picture of `notes/kernel-design.md` §11: the Rust "zoo" of
efficient constructions and the `.cov` proof units both present the **same HOL
waist API**, so the project graph does not care which produced a given env.

## 5. Mutual reference (deferred design)

Real mutual reference — two units (or a Rust unit and a `.cov` unit) that each
need a name the other defines — breaks the strict topological order. Two
standard resolutions, to choose between when this is built:

1. **Two-phase (declare-then-check).** Phase A: every unit declares its
   *signature* — the names and statements (types of constants, conclusions of
   theorems) it exports — without proving anything. All signatures are merged
   into a shared environment. Phase B: every unit checks its *bodies* against
   that environment, so each may reference any other unit's declared names. The
   discipline that keeps this sound: a theorem may be *referenced* by signature
   in phase A but is only *trusted* once its body is checked in phase B, and a
   body may only depend on signatures, never on unchecked bodies — so the
   checked artifacts form a well-founded order even though the *source*
   references are cyclic. This matches the kernel's conservative-extension
   discipline (a `define` introduces a name; its defining theorem is separate).
2. **SCC + fixpoint.** Condense the graph into strongly-connected components
   (Tarjan); compile across components in topological order (as §3 already
   does), and *within* a non-trivial SCC run a fixpoint — re-checking the
   cluster until the set of available names stabilises. Heavier, only needed
   for genuinely circular *value* dependencies (rare in proof code, where the
   two-phase signature split usually suffices).

The prototype detects cycles and **errors** (`ProjectError::Cycle`) rather than
silently mis-ordering, so the deferral is explicit and safe — turning the error
into a two-phase compile is a localized change to `compile()`.

## 6. The single `init/mod.rs` entry point

The end state folds today's `library_env` + `library_tactic` +
`prime_library_imports` + the per-theory `cov_theory!` blocks into **one
`Project` definition** in `init/mod.rs`:

```rust
fn stdlib_project() -> Project {
    Project::new()
        .source("logic", include_str!("logic.cov"))
        .source("nat",   include_str!("nat.cov"))
        .source("rat",   include_str!("rat.cov"))
        .source("set",   include_str!("set.cov"))
        // … every init/*.cov …
        .rust_env("tauto",   tauto::cov::env())     // foundational seam
        .rust_env("natrec",  nat::natrec_env())     // Rust-proved givens
        .rust_env("ratprim", rat::rat_env())
        .rust_env("setprim", set::setprim_env())
        .tactic("tauto", Arc::new(logic::Tauto))
}
// `library_env(name)` becomes `STDLIB.env(name).cloned()` over a cached compile.
```

`check_script` then runs a user proof against the *compiled* project's envs —
no per-import priming pass, because the project is already topologically built
and cached.

## 7. Longer-term: WASM-against-abstract-API + Cargo features for distribution

Tie-in to the system vision (`notes/VISION.md`, `notes/kernel-design.md` §11):

- **A crate compiled to WASM against an abstract Covalence API.** A Covalence
  project unit is, at bottom, "given my imports' exported environments, produce
  my exported environment." A `.cov` unit does this by proof replay; a Rust
  unit does it by running compiled WASM that calls the abstract kernel/store
  API (`cov:kernel`, `cov:store`, the observer substrate). Compiling Rust
  against the *abstract* API (not the in-process kernel) is what makes a Rust
  unit a portable, content-addressed project node — runnable on any backend,
  the same on every host (the store-is-a-container picture).
- **Cargo features as content-addressing-friendly distribution.** A Covalence
  project's optional pieces map naturally onto **Cargo features**: a feature
  flag selects which units/seam-envs are included, and because each unit's
  output is a content-addressed environment, a feature set names a *specific
  content hash* of the resulting library. Distributing a Covalence project is
  then distributing a crate + a feature selection, with the store providing the
  content-addressed backing — features are a familiar, tooling-supported way to
  express "this build of the library" that the content-addressing layer can
  pin and verify.

These are **design only**; the WIT-abstract-API compile and the
feature→content-hash mapping are recorded as skeletons.

## 8. What exists today

`covalence-hol/src/project.rs`:

- `CovSource`, `Project` (builder), `CompiledProject`, `ProjectError`;
- `compile_project(...)` free function + `Project::compile()`;
- `.cov`→`.cov` import-edge discovery, validation, deterministic topological
  sort, cycle/duplicate/unknown-import detection;
- `.cov`→Rust seam-env and FFI-tactic inputs as project leaves;
- per-unit compile through the **real kernel** (no trust), threading each
  unit's exported env to its importers;
- tests: a chained two-unit project (compiled out of input order), a diamond
  (deterministic order), a Rust-seam-env import, unknown-import / cycle /
  duplicate / bad-proof errors, and the free-function entry point.

Deferred (see `crates/covalence-hol/src/SKELETONS.md`): the Rust→`.cov`
*feeding* edge and full mutual-recursion resolution (§4–§5), the single
`init/mod.rs` `Project` replacing `library_env` (§6), and the WASM-against-
abstract-API + Cargo-features distribution framing (§7).

[`Env`]: ../crates/covalence-hol/src/script/env.rs
[`Tactic`]: ../crates/covalence-hol/src/script/tactic.rs
