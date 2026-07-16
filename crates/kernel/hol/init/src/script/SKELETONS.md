# Skeletons — `covalence-init::script` (proof-script authoring + replay layer)

Open placeholders for the S-expression proof authoring + replay layer. See
`CLAUDE.md` § Skeletons for the rules, the [crate index](../../SKELETONS.md), and
the [root index](../../../../../../SKELETONS.md).

## Severe

- **Async holes/channels removed, pending channel-based rebuild.** The
  `#hole`/`#fill`/`splice_holes`/`collect_holes`/`obligations`/`is_resolved`
  machinery was deleted (wrong shape). Today every `#thm` checks inline, so the
  in-progress/resolved `TheoryHandle` split is only nominal. Target rebuild
  (`script/mod.rs`):
  - **Env channels + holes-as-yields** — `(#channel NAME)` adds a channel,
    `(#fill NAME DRV)` pushes, `(#hole NAME)` in a proof receives; an unfilled hole
    awaits the channel → genuinely yields.
  - **`ThmHandle` + manual poll** — `prove()` returns a future; `poll_once` (noop
    waker, single-threaded); complete → store `Thm`, yield → stash `ThmHandle =
    Ready | Pending` and drive later. Parallelism stays explicit opt-in.
  - **`EnvHandle` (in-progress env)** — an in-progress env's imported lemmas/consts
    are futures; `EnvHandle::resolve().await`, `#import` returns `EnvHandle`s, `#dep`
    becomes a real `await`. A failed import yields a partial-but-importable theory.
- **`(#dep NAME)` is a sync availability guard, not an await.** Errors if `NAME`
  isn't already known; its real semantics (block the task until `NAME` completes,
  forward refs included) depend on the cooperative scheduler above.
- **`ScriptError` is flat strings — no source spans or traces.** Should carry source
  extents (byte/line spans threaded from parsing) and traces (the rule/tactic/obligation
  chain to a failure). **Very important for LLM-assisted proofs** (precise localized
  feedback). Pairs with the typed-pipeline note below.
- **Typed pipeline + extents missing.** `run_async` parses directives into a typed
  `Stmt`, but `#thm` bodies stay raw `SExpr` and no extents are carried. The full
  pipeline — parse → untyped elaboration → typechecking → typed elaboration → execution,
  with a typed term/proof IR and spans threaded through every stage — is TODO. Spans are
  the prerequisite for the rich errors above and editor/LSP feedback.
- **`Term` futures (term-level holes) not represented.** Terms are built eagerly.
  Target: a **unification hole** as a term future (optionally asserting a fixed type),
  letting the elaborator explore unification variants and resolve lazily — and, with
  content-addressing, fetch a term's contents on demand. Needs a future-carrying
  `Term`/elaborator value in `script/infer.rs`.
- **`lookup_const`/`lookup_tactic`/`lookup_rule` still sync** (`get_ready` peeks).
  Making `lookup_const` async makes the elaborator (`infer.rs`) async (recursive
  `BoxFuture` + const-lookup await) → `parse_term`/`CheckCtx::term`/`elaborate_concl`
  async — the unbuilt step for *one async task per definition* (a `const` loaded from
  the network, like `#spawn` for a theorem). Lemma lookup is already async.

## Perf

- **Slow `.cov` files.** `cov_theory!` is timed by `COV_PROFILE=1`. Pathologically slow:
  **`list.cov` ~99s**, **`utf8.cov` ~60s**, **`rat.cov` ~24s**, `int.cov` ~5s,
  `prop.cov` ~2s (vs `nat.cov` 240ms, rest <85ms). Real proof-replay cost, likely the
  same impredicative-term / structural-equality blow-ups as `init/regex` soundness (large
  terms re-traversed without sharing). Repro:
  `COV_PROFILE=1 cargo test -p covalence-init --lib init -- --nocapture` then grep
  `cov-profile`. Candidate fix: term hash-consing / the `covalence-pure` split.

## Minor / deferred features

- **Inference is best-effort (untrusted).** `infer.rs` HM unification is incomplete and
  need not be sound (`check` re-validates). Known partials: the `ε`/`select` result type
  is approximated; leftover-metavar generalisation names tvars positionally, so a conclusion
  and proof that independently generalise must coincide in order. `all-intro`/`abs-rule`
  take an explicit binder type (var not usage-constrained across sub-proofs); inferring it
  needs a threaded metavar arena or a check-time `find_free_type` pass.
- **Pluggable unifier not built.** `apply`/`rw` do first-order matching via
  `Env::apply_unify`/`rw_unify`. TODO: (a) a **registerable custom handler** (the reason
  the ops route through `Env`); (b) a third facet **`rewrite(a) -> ⊢ a = b`** (a rewriter,
  what `rw` consumes) as a first-class kind; (c) higher-order patterns (matcher is
  first-order); (d) "rewrite at occurrence-N" control (`rw` matches the leftmost-outermost
  subterm only).
- **No proof/`Term` pretty-printer (serialization-out).** `script` only parses + replays;
  no printer from a proof/`Term` back to the surface S-expression. Blocks content-addressing
  (hashing a proof) and lemma-by-hash references (`notes/vibes/surface-syntax.md` §7). When added,
  reuse/extend the printers in `src/sexp.rs` and the hasher in `hash.rs` (which cover
  terms/types but not proofs).
- **`rw` does not descend under binders.** `rewrite_conv` (`script/drv.rs`) rewrites
  through `App` and at leaves but returns `refl` for `Abs`, so it cannot rewrite inside
  `λ`/`∀`/`∃` bodies. Going under binders needs de-Bruijn-aware shifting of the equation.
- **Prelude `Env::core()` covers only logic + nat.** int/rat/real/list/option/prod/coprod/set
  catalogue names aren't bound yet; add entries to `script/env.rs::Env::core` as those
  theories are ported.
- **No wasm path for opt-in parallelism.** `block_on` is cfg-split (native tokio
  current-thread, wasm `futures::executor::block_on`). The deferred "explicit parallelism
  via `tokio::spawn` / multi-thread runtime" has no wasm path — a browser build would need
  a `wasm-bindgen-futures`-style spawner.
- **No WASM/WIT kernel API.** Authoring proofs in WASM guests and importing them through a
  WIT kernel interface (driving proof replay across the component boundary) is not started.
  `check` is the intended single kernel-coupled entry point behind such an interface.
- **`#comp` calc handles only `=`.** The heterogeneous form (`a = b ≤ c < d ⊢ a < d`,
  per-relation transitivity lookup, à la Lean `calc`) is deferred until a
  relation/transitivity registry exists (`notes/vibes/surface-syntax.md` §5.1).
- **Equational seams not yet registerable per-logic.** `Env::beta`/`congr`/`funext`/
  `comp_default` are methods (the `apply_unify`/`rw_unify` seam pattern) but still hold the
  single built-in HOL default. Swapping in a logic's own `HandlerSet`
  (`notes/vibes/surface/surface-compiler.md` §9) needs scoped `Context`/`HandlerSet` plumbing. Same gap as
  the `rw_unify` registerable-handler TODO; wire together.
- **`#inductive` realises only the `nat` shape.** `script/inductive.rs` dispatches through
  `LogicInductive` (PA/SOA/MLTT impls planned) but for fresh user types it can only consume
  the engine's public API, which needs (a) an `Inductive` adapter with derived
  `induct`/`injective`/`distinct` over a `new_type_definition` carrier, and (b) a recursor
  selector predicate (`nat` reads `nat_rec_spec` from `defs`; a fresh type has none). Missing
  capability: a **carrier-construction + freeness-derivation + recursor-spec synthesis** seam
  (partly the engine's multi-rec-arg work, partly a new `defs`/elaborator path to mint a
  fresh subtype + recursor spec from a signature). The directive reports the gap rather than
  fabricating; `nat` is the worked end-to-end case.
- **`#def` catalogue-resolution path not audited.** A `#def NAME` whose body references
  catalogue constants should reuse the cached `defs::*` accessors (as core's `cov.rs`
  `canonical_by_label` does) for a byte-identical result; today it mints a *fresh*
  opaque-`SmolStr` spec, semantically equal but not pointer-equal to the `Canonical::*` entry.
- **`#sig`/`#thy`/`#model`/`#models` scope** (`script/theory.rs`): single-sorted/first-order
  signatures only; `(from WITNESS)` is a transitional host-axiom path; no typed `.sig`/`.thy`
  imports; no reified `M ⊨ T` certificate object; no model synthesis. Full list in
  `models/SKELETONS.md`.
