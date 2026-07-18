+++
id = "N000E"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:claude"
at = "2026-07-03T21:05:38+01:00"
source = "legacy"
agent = "claude"
harness = "claude"
+++

There's a few refactors I want to do, with the primary goals of:

- Making the codebase more approachable and auditable for agents and humans
- Getting started on WASM acceleration
- Building demos you can actually play with
- Scaffolding the long-term vision more effectively

One of the major issues we deal with in particular is there's a *lot* of crates,
so the direct cognitive load when first approaching the codebase is high.

We want to experiment with a more hierarchical structure.

Likewise -- our notes/vibes/ and documentation are not particularly good.

# Notes, Documentation, and Skills

First -- right now the notes/vibes/ folder is mainly AI generated notes with some cross referencing, with the primary purpose being

- Capturing the "vibes" of our long-term plans -- it's not particularly consistent!
- Documenting a few of our basic design decisions, but not in a very structured way

I propose breaking this up into:

- "vibes" -- basically everything we have right now; either vibes/ or notes/vibes/vibes -- probably the latter

- notes/vibes/ -- a more structured tree, with different subdirectories for different topics, e.g. notes/vibes/ideas, notes/vibes/experiments, etc. -- this is "aspirational" in that things here are what we _want_ rather than necessarily what we currently have -- and may be out of sync or contain historical information

- docs/ -- more formal documentation, with the constraint that this should be _true_ -- i.e. what we actually have, and should be kept aggressively in sync with the codebase

We also want to refactor our SKILLS.md, CLAUDE.md, README.md, and the SKELETONS.md system 
-- especially the latter needs to be both simplified and made more structured,
since we waste a lot of tokens going through SKELETONS files --
one idea I had was a *database* of skeletons parsed automatically from comments?
Future work -- just organize for now, but think about it!

# Tooling

We need to clean up our build and test system.

I'm thinking we should move to using a proper build system -- maybe something like `buck2` (eventually we want to dogfood and use `cog` as our build system -- but building in-project experience is a _good_ thing for this, plus we can then think about e.g. cog and buck compatibility) -- which `bun run build:(thing)` delegates to -- bun still being the central tool used for "tasks", and for now for testing (though discuss).

Especially useful would be sharing artifacts/build cache across worktrees -- something we suffer a bit with now even though we've got a lot of crates.

This will be more important as we compile WASM artifacts -- eventually we want a "covalence library" to export to a .wasm file which imports the covalence WIT and constructs itself, potentially exporting helpers -- written in covalence + Rust -- and in particular we want to compile the covalence surface language to WASM. We'll want to import lots of artifacts from lots of different tools for lots of different things (e.g. now we had issues with the Web build failing) and we should have a standard way of doing this and sharing -- also, all bun run commands should first ensure all dependencies are built, or fail with a clearly understandable error.

Next up -- we want to get back into the VSCode plugin game, and part of that means setting up a proper LSP, especially as we develop the covalence language, but also as a full-featured .wasm/.wat/.watsup LSP.

Our LSP should probably talk to the covalence server but itself be a separate process (potentially running a covalence server in-process, like the client/REPL) -- right now it doesn't do much.

We also need to make sure CI actually works reliably. 
I also think dev-containers are a good idea -- 
especially with agents (discuss how this works) --
I'm not sure if we can make our CI use the dev-container too, cross-testing these?
How does this interact with our flake?
dev-containers may be particularly useful for installing covalence and playing around with e.g. global caches -- 
especially in the future when we might have a system covalence installed and don't want to interfere with that.

# Organization

## Rust

We want to make our crates more hierarchical. I propose breaking down the current smorgasbord into the following recursive groups. In general, we want the pattern `covalence-group-subgroup-subsubgroup-etc-thing` -- but we probably want to establish the convention of leaving out the "catchall" groups `lib` and `lib/core`.

We probably want each layer to be a crate (though lib would just be a simple "re-export everything" crate -- maybe with some basic indexing/documentation/segmentation by feature -- people shouldn't import it directly!) -- discuss the idiomatic Rust pattern for nested crates that's also easy for an agent to navigate.

- lib/ -- libraries, wrappers, etc. -- _most_ external dependencies should be via a `lib/` crate
  - core/ -- core abstractions: `covalence-hash` fits here as core/hash, `covalence-rand`, etc. -- note I don't always give all the leaf-level crates, e.g. for wasm/, proto/...
  - proto/ -- protocols
  - data/ -- data formats, codecs, datasets, etc. -- separate out an fmt/?
    - Do we put sexp/ here or make itit's own thing?
    - Where do we put parse/ here?
  - wasm/ -- low-level WASM utilities, the WASM spec itself
  - sat/ -- low-level SAT utilities -- LRAT, DRAT, etc. go here
  - smt/ -- low-level SMT utilities
  - crypto/ -- cryptography (hashes go in `covalence-hash`) -- just `covalence-sig` for now (becoming `covalence-crypto-sig`)
  - db/ -- database utilities -- fuse into data/?
    - sqlite/
  - git/ -- low-level git utilities
  - fuse/ -- FUSE utilities
- proof/ -- interfaces with other provers + proof formats; bikeshed name. Part of `lib/`?
  - hol/ -- today's `covalence-hol`
  - metamath/ -- today's `covalence-metamath`
  - lean/ -- today's `covalence-lean`
  - alethe/ -- today's `covalence-alethe`
  - future: rocq/
- store/ -- the storage layer 
- kernel/ -- the covalence kernel
  - base/ -- the base, first-order logic layer -- what's `covalence-pure` today
    - trusted/ -- the _base_ TCB crate
    - derive/ -- derive macros for the base layer
    - eval/ -- basic expression evaluation (e.g. `Nat`, `Vec<T>`, `Map<K,V>`, etc.)
      implemented as a base layer logic -- may fold into `trusted/`, but it's a good
      dogfooding exercise to make this a separate crate
    - wasm/ -- WASM evaluation implemented as a base layer logic -- 
      so facts about what WASM modules evaluate to
    - cap/ -- basic capability logic
    - db/ -- SQLite database support for the base layer, as an interchange format (discuss?)
    - fed/ -- federation implemented over capability logic: generating a keypair, trusting someone else's keypairs, signing a theorem database, etc.
  - hol/ -- higher-order logic -- what's `covalence-core` today
    - logic/ -- the basic HOL constructs over the base logic
    - script/ -- a maximally simple, S-expression based scripting language for covalence
      -- a _subset_ of the eventual full covalence-language
      -- along with basic APIs/traits for tactics/goals/etc.
    - init/ -- basic definitions, proofs, and algorithms using only `logic/` -- e.g. basic properties of nats/ints/rationals/reals, functions to define simple inductive datatypes, tactics to discharge simple tautologies, etc. The high-level API the rest of the crates are built over -- smaller than today's `covalence-init`, much of which goes into other crates.
    - eval/ -- basic expression evaluation to accelerate HOL -- so `Nat`/`Int`/etc. support -- this is a larger TCB, we should prove basic theorems about the definitions used here (e.g. the definition of addition) using only `logic/`
    - metamath/ -- metamath support over HOL
    - spectec/ -- spectec support over HOL
    - wasm/ -- WASM acceleration -- we should build up this theory using only `eval/` (probably possible with only `logic/`, even)
- lang/ -- the actual covalence language
- server/ -- the covalence server and implementation
- vcs/ -- version-control + filesystem code -- put trees, commits, etc, in here
- app/ -- apps built over the covalence server; note the single-binary + subcommands architecture though, hence the cyclic dep
  - repl/ -- the REPL
  - cog/ -- cogit (depends on lib/git/ + vcs/)
  - fuse/ -- FUSE implementation (depends on lib/fuse/ + lib/git/ + vs/)
- ffi/ -- runtime interfaces for covalence (WIT is fundamental so goes in `kernel/...`)
  - python/ -- the Python API
  - LATER: js/ -- a JS API, could be useful for the web build/`category.wiki`

Cyclic dependencies are allowed between the groups, e.g. lib/ depending on store/ depending on lib/ -- as a form of "strange loop" -- but the crates themselves should form a DAG.

## Everything Else

`scripts/` is good 
-- I guess `apps/` and `extensions/` is a decent start, 
but we only want one extension here at least for now (unless we go multiple-extensions with dependencies), and `extensions/` doesn't communicate VSCode, so think about it.
Eventually we want to start developing `category.wiki` here!

We want a subdirectory for a proper JS + Svelte library 
-- with Svelte being the default way to integrate `covalence`
-- I suppose that's `packages/`?

The vision here is making it easy to integrate `covalence`-readable data into your site
without dragging along the entire `covalence`-binary, in particular! 

`category.wiki` is a good place to dogfood this
-- everything should use standard `covalence` components but only the editor (and perhaps a "local check" button) should need to download the actual binary (which should ofc be cached!)

So yeah we need to think about how to lay all this out on-disk!

We should probably break up `assets/` into

- `assets/` -- actual images, etc; useful for `category.wiki`

- `data/` -- data

We also need a name for the subdirectory containing we have in `assets/` now: opentheory, spectec, tests.

Eventually, we want to dogfood using `cog` for large files we use in e.g. tests 
-- e.g. `set.mm`.

# WASM roadmap

Our most important milestone to aim for is proper WASM support. In particular, we need:

- WASM acceleration

- Running WASM in the browser/natively/in VSCode effectively with a shared high-level API

- Letting us async-wait on completion of WASM tasks -- eventually full WASM3.0 async support; but start with (and keep, for older WASM binaries/general use, `spawn_blocking`-based implementation)
