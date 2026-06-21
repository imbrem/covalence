# Skeletons — `covalence-hol::script` (proof-script authoring + replay layer)

Intentional placeholders for the S-expression proof authoring + replay layer.
See `CLAUDE.md` § Skeletons for the rules, the [crate index](../../SKELETONS.md),
and the [root index](../../../../SKELETONS.md).

## Proof-script layer (`covalence-hol/src/script`)

The S-expression authoring + replay layer (`Env`/prelude, the `infer`
type-inference elaborator, the `check` replayer + derivation registry, the
`rw`/`tauto` rules, and the `cov_theory!` loader macro). The
**parse → replay** direction is built and tested; `init::logic`'s `truth`/`and_comm`/`or_comm` (and the reified
`exists.intro`, with the Rust `exists_intro` rule rewired onto it) are now
**loaded from `init/logic.cov`** via `cov_theory!` (replacing the hand-written Rust proofs — the whole crate's
~225 tests still pass, since everything downstream of `truth()` re-checks).
`run(src, resolver)` resolves `(open NAME)` against caller-supplied envs and
returns a `Theory` whose **export** env — built explicitly by `(export NAME …)`
directives — is `open`-able by other scripts; the macro binds it as a
`static ENV: LazyLock<Env>`.

**Inline definitions are built** (`script/mod.rs`): the four directives
`(#def NAME TERM)` / `(#newtype NAME TY)` / `(#subtype NAME TY PRED)` /
`(#quot NAME TY REL)` — the script-layer counterpart of
`covalence_core::defs::cov`'s sync parser — elaborate their body through the
`syntax`/`infer` elaborator and bind the result into the running env (`#def`
mints a genuine `defs/` `TermSpec`, so the constant carries a δ-unfolding
equation; the type directives register a user `TypeSpec` resolved by
`Env::lookup_type_spec` from an env-aware `parse_type`). This **replaces the
`*_env()`/`*prim` givens pattern** (a constant built in Rust only to be named
from `.cov`) — `init/cond.rs`'s `cond_env`/`condprim` is gone, `cond` is now
`#def`'d inline in `cond.cov` (the proof-of-concept; other `*_env`s remain to
migrate as needed). Not yet done: an audited *catalogue-resolution* path (a
`#def NAME` whose body references catalogue constants reuses the cached
`defs::*` accessors, as core's `cov.rs` `canonical_by_label` does, so the
result is byte-identical to the hand-written one — the script `#def` mints a
*fresh* opaque-`SmolStr` spec instead, semantically equal but not pointer-equal
to the `Canonical::*` catalogue entry).

These are deliberately deferred:

- **Inference is best-effort (untrusted).** `infer.rs` does Hindley–Milner
  unification for free-variable and binder-domain types; it is not complete
  and need not be sound — `check` re-validates every elaborated term against
  the kernel. Known partials: the `ε`/`select` result type is approximated;
  generalisation of leftover metavariables names type vars positionally
  (`'a`, `'b`, …), so a conclusion and proof that independently generalise
  must coincide in order (fine for the single-tvar cases today). `all-intro` /
  `abs-rule` still take an **explicit** binder type — their var isn't
  usage-constrained across the independently-elaborated sub-proof terms;
  inferring it would need either threading one metavar arena through the whole
  derivation or a check-time `find_free_type` pass.
- **Lemma application + `rw` unify (first-order); the pluggable unifier is not
  built.** `apply` (a dual-mode inference) instantiates a lemma by first-order
  matching its conclusion against the goal/target (`Env::apply_unify`), and `rw`
  instantiates a quantified `∀x⃗. L = R` by matching `L` against a subterm of the
  target (`Env::rw_unify` → `script/unify.rs::find_match`), so neither needs a
  hand-written `all-elim` prefix; bare lemma names (`(N w…)`) replaced the old
  `lemma` keyword. `rw` takes several equations
  (`(rw E1 E2 …)` / `(rw E… TARGET)`), applied in sequence; bare atom names work
  (`(rw sub_zero)`). Still TODO: (a) the unifier is hard-coded — a **registerable
  custom handler** (the stated motivation for routing through `Env` methods) is
  not wired; (b) a third inference facet **`rewrite(a) -> ⊢ a = b`** (a
  *rewriter*, what `rw` consumes — a lemma casts to one via `rw_unify`) is not a
  first-class kind yet; (c) the matcher is purely first-order (no higher-order
  patterns); (d) `rw` matches the FIRST (leftmost-outermost) subterm — no
  "rewrite at occurrence-N" control yet.

- **No proof/`Term` pretty-printer (serialization-out).** `script` only
  *parses* the named syntax and *replays* it; there is no printer from a
  proof / `Term` back to the surface S-expression. This blocks content-addressing
  (hashing a proof term) and lemma-by-hash references — both noted as
  future in `docs/surface-syntax.md` §7. Authoring (the immediate goal —
  porting the Rust `init/` theorems) needs only the parse direction. When
  added, reuse/extend the low-level printers in `crates/covalence-hol/src/sexp.rs`
  and the hasher in `hash.rs` (which today cover terms/types but **not** proofs).
- **`rw` does not descend under binders.** `rewrite_conv` in `script/drv.rs`
  rewrites through `App` and at leaves but returns `refl` for `Abs`, so it
  cannot rewrite inside `λ`/`∀`/`∃` bodies. Adequate for the quantifier-free
  goals it targets now; going under binders needs de-Bruijn-aware shifting of
  the equation.
- **Prelude `Env::core()` covers only logic + nat.** The name→catalogue
  resolvers are a starting set (the connectives, `=`, `nat.add/mul/sub/le/lt`,
  `succ`). int/rat/real/list/option/prod/coprod/set catalogue names are not yet
  bound; add entries to `script/env.rs::Env::core` (the `defs/` churn
  boundary) as those theories are ported.
- **Async core: types + tokio in place; the open-obligation (hole) feature was
  removed, pending a channel-based rebuild.** `script/mod.rs::run_async` is
  `async`; `run`/`resolve_blocking` block via a tokio **current-thread** runtime
  (`block_on`). On `wasm32-unknown-unknown` (the browser build) tokio does not
  compile, so `block_on` is **cfg-split**: native keeps the tokio current-thread
  runtime byte-for-byte, wasm falls back to `futures::executor::block_on`. The
  wasm fallback drives the same cooperative core fine, but the deferred
  "explicit opt-in parallelism via `tokio::spawn` / multi-thread runtime"
  (below) has **no wasm path** yet — a browser build would need a
  `wasm-bindgen-futures`-style spawner when that lands. `run` returns a
  `TheoryHandle` (in-progress) and
  `TheoryHandle::resolve` (async) forces it to a `Theory` (resolved) — but with
  no obligations, every `#thm` is checked inline (eagerly) and `resolve` is
  trivial, so the in-progress/resolved split is currently only nominal. The
  earlier `#hole`/`#fill` machinery (pending theorems, `splice_holes`,
  `collect_holes`, the manual `prove`/`poll_once` drive, `obligations`/
  `is_resolved`, `UnresolvedObligation`) was **deleted** — it was the wrong
  shape and is to be rebuilt cleanly. Target rebuild:
  - **Env channels + holes-as-yields.** A top-level `(#channel NAME)`
    declaration adds a **channel** to the environment; `(#fill NAME DRV)`
    **pushes** to it; `(#hole NAME)` in a proof **receives** from it. Because a
    future cannot mutate the env, the channel is the async-safe bridge: when
    `prove()` hits an unfilled hole it awaits the channel → genuinely **yields**.
  - **`ThmHandle` + manual poll.** `prove()` returns a future; `poll_once` it
    (one poll, noop waker — single-threaded, no spawn); if it **completes**
    store the `Thm`, if it **yields** stash a `ThmHandle = Ready(Thm) |
    Pending(future)` and move on, driving it later at force. Parallelism stays
    an explicit opt-in (`tokio::spawn` / multi-thread runtime), not the default.
    (`covalence_core::Error` + `ScriptError` are now `Clone`, so a `Pending`
    handle can be a multi-consumer `Shared` future.)
  - **`EnvHandle` (in-progress env).** Mirror of `TheoryHandle`: a fully-resolved
    `Env` holds no futures, but an in-progress one's **imported** lemmas/consts
    ARE futures (an import need not be fully proved to start proving importers);
    `EnvHandle::resolve().await -> Env`, `#import` resolver returns `EnvHandle`s,
    `#dep` becomes a real `await`. A failed import yields a *partial* theory
    that is still importable (wanted for BLAKE3-range partial verification).
- **`(#dep NAME)` is a synchronous availability guard, not an await.**
  `script/mod.rs` accepts `(#dep NAME)` and errors if `NAME` is not already a
  known lemma/const/tactic/import. Its real semantics — *force the enclosing
  task to block until `NAME` completes* (forward references included) — depend
  on the cooperative scheduler above.
- **`ScriptError` is flat strings — no source spans or traces.** Errors carry
  only a message (e.g. the cycle error stringifies theorem names; kernel errors
  wrap `covalence_core::Error`). Eventually the error type should carry **source
  extents** (byte/line spans, threaded from parsing) and **traces** — the chain
  of rules/tactics/obligations that led to a failure. **Very important for
  LLM-assisted proofs**, where the model needs precise, localized, structured
  feedback to repair a proof. Pairs with the typed-pipeline note below (extents
  come from preserving spans through every stage).
- **Typed `Stmt` exists for directives, but the pipeline + extents don't.**
  `run_async` now parses every directive into a typed `Stmt` enum (`parse_stmt`)
  in a first pass, then executes — but `#thm` bodies are still raw `SExpr`
  (typed elaboration of the proof is deferred), and **no source extents** are
  carried. The full pipeline — **parse → untyped elaboration → typechecking →
  typed elaboration → execution**, with a typed term/proof IR and spans threaded
  through every stage — is still TODO. The spans are the prerequisite for the
  rich, well-located errors above and good editor/LSP feedback.
- **Async tactics + async `check` + a uniform derivation registry all exist.**
  `Tactic` is an `#[async_trait]` trait (`apply` async; `Interp::run`/`prove`/
  `run_thm` async; recursing tactics are structs, goal-closers stay sync `fn`s
  via the blanket). `drv.rs::check` is **async** (returns `BoxFuture`); both
  tactic-mode and tree-mode (`#proof`) can **await mid-proof** (tests
  `async_tactic_can_yield_mid_proof`, `registry_rule_in_tree_mode_can_await`).
  There is no separate `Rule` trait: `Tactic` has **two** async methods —
  `apply` (tactic mode) and `rule` (tree mode), each defaulting to a "wrong
  mode" error — so ONE registered object serves either/both. `check` dispatches
  **every** `#proof` head through `Env::lookup_rule` (alias of `lookup_tactic`)
  and calls `.rule()`; `drv.rs::core_rules()` installs the ~30 forward rules
  into `Env::core` (override only `rule`), and dual-mode `refl`/`sym`/`not-intro`/
  `rw` (+ `tauto` in logic) are single structs overriding both. The old
  hardcoded `Drv` AST + `parse_drv` pass are gone — `Tactic::rule(&[SExpr], &mut
  CheckCtx)` **self-parses** its term/type/name/sub-derivation args (a
  `CheckCtx` gives `term`/`ty`/`name`/`push_var`/`check`), so a custom rule has
  the same power as a built-in. No remaining TODO for this item.
- **Lemma lookup is async; const lookup is sync (the data model is ready, the
  accessor + elaborator aren't).** `Env` is now ONE unified `entries:
  LazyMap<Entry>` (`Entry` = `Const|Lemma|Tactic`), so EVERY kind is already
  future-capable — a const *can* pend, no new machinery needed.
  **`Env::lookup_lemma` is `async`** (awaits a still-`#spawn`-ing
  `Entry::Lemma`); the old boundary-await `lemma_refs`/`await_computed_deps` was
  deleted. `#spawn` binds NAME via `define_spawned` → `insert_pending`; a later
  reference (or the force) just awaits it. The remaining half of **"all env
  accesses async"** (user) is now just the *accessor*: `lookup_const`/
  `lookup_tactic`/`lookup_rule` are still SYNC `get_ready` peeks. Making
  `lookup_const` async makes the **elaborator (`infer.rs`) async** (recursive
  `BoxFuture` + const-lookup await) → `parse_term`/`CheckCtx::term`/
  `elaborate_concl` async — that's the unbuilt step for *one async task per
  definition* (a `const` loaded from the network, like `#spawn` for a theorem).
  The non-async `lemma_ready(name)` peek stays for the sync `Theory::lemma` macro
  accessor (a forced theory's lemmas are all Ready).
  - **`#spawn` replaced `#compute`.** A `#spawn`ed proof is a *deferred
    cooperative async task* (a pending `BoxFuture` stored via `insert_pending`,
    polled when first awaited) — **no `spawn_blocking`, no nested `block_on`**.
    Because it shares the cooperative runtime, a `#spawn` CAN `await` a *prior*
    sibling lemma (the env clone structurally shares its pending `Shared`
    futures). Still snapshot-scoped, so it cannot see siblings declared *after*
    it. **Genuinely blocking work is deferred to the FFI tactic's own
    responsibility** (an FFI call that must block should manage that itself) —
    the script layer no longer owns a blocking-thread pool.
- **`Term` futures (term-level holes) not represented.** Terms are eagerly
  built — there is no `Term` future (and proof holes were removed, see above).
  A key target use case: represent a **unification hole** as a term future
  (optionally asserting a fixed type up front), letting the elaborator explore
  unification variants and resolve holes lazily — and, with content-addressing,
  fetch a term's contents on demand. Needs a future-carrying `Term`/elaborator
  value wired into `script/infer.rs`.
- **No WASM/WIT kernel API.** The longer-term goal of authoring proofs in WASM
  guests and importing them through a WIT kernel interface (driving the proof
  replay path across the component boundary) is not started. `check` is
  intentionally the single kernel-coupled entry point such an interface would
  sit behind.

- **`#comp` calc handles only `=` (no heterogeneous relations).** The
  `#comp` rule (`script/tactic.rs`) folds `trans` over `(= RHS [BY])` steps,
  per `docs/surface-syntax.md` §5.1; the heterogeneous form (`a = b ≤ c < d ⊢
  a < d`, looking up a transitivity rule per adjacent relation pair, à la Lean
  `calc` / Isabelle `also`) is deferred until a relation/transitivity registry
  exists. Each step head must be `=` for now.
- **Equational seams not yet registerable per-logic.** `Env::beta` /
  `Env::congr` / `Env::funext` / `Env::comp_default` (`script/env.rs`) are
  *methods* — the seam pattern of `apply_unify`/`rw_unify` — so the rules
  (`beta`/`congr`/`funext`/`#comp`) *request* these operations rather than
  hard-wiring them, but the methods still hold the single built-in HOL default.
  Swapping in a logic's own `HandlerSet` (`ctx.active.rewrite`/`.reduce` of
  `docs/surface-compiler.md` §9 — a monoid normalizer, a reified-logic decider)
  needs the scoped `Context`/`HandlerSet` plumbing, not yet built. Same gap as
  the `rw_unify` "registerable custom handler" TODO above; they should be wired
  together.

- **`#inductive` directive realises only the `nat` shape (metalogic).**
  `script/inductive.rs` parses `(#inductive NAME (ctor ARGTY…) …)`, dispatches
  through the per-internal-logic `LogicInductive` trait (the metalogic =
  `HolMetalogic`; PA/SOA/MLTT realisations are the planned extra impls), and —
  for the `nat` constructor shape `(zero)` + `(succ nat)` — binds the
  constructors and emits the genuine recursion theorem `⊢ ∃rec. P_rec rec`
  (the engine's `recursion_theorem`) plus a worked induction instance
  `⊢ ∀n. n = n`. **What's missing for fresh user types** (a binary tree, a
  custom enum): the directive can only consume the inductive engine's public
  API, which needs (a) an `Inductive` adapter supplying genuine
  `induct`/`injective`/`distinct` — for a non-kernel-primitive type these are
  *derived* theorems over a carrier carved out by `new_type_definition`, plus
  (b) a recursor **selector predicate** that `nat` reads from the `defs`
  catalogue (`nat_rec_spec`) but a fresh type has no entry for. So the missing
  capability is a **carrier-construction + freeness-derivation + recursor-spec
  synthesis** seam — partly the engine's multi-recursive-argument work (see the
  inductive-engine entry above), partly a new `defs`/elaborator path to mint a
  fresh subtype and its recursor spec from a signature. The directive reports
  the gap (`ScriptError::Syntax`) rather than fabricating anything; `nat` is the
  prototype's worked end-to-end case.
