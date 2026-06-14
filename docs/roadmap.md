# Covalence — Roadmap

This is the "what's next" doc. For the vision see
[`VISION.md`](./VISION.md); for the kernel TCB see
[`kernel-design.md`](./kernel-design.md); for the type catalogue and
equality hierarchy see [`type-hierarchy.md`](./type-hierarchy.md).

## Backup branch

The `kernel-design` branch was aggressively pared down to the *current
design only*. Everything removed lives on the **`backup/pre-hol-cleanup`**
branch (created at commit `6ba9a7d`). What you can recover there:

- **`covalence-hol` postulate catalogues** — `nat_axioms.rs`,
  `int_axioms.rs`, and the `init/` (formerly `stdlib/`) modules
  (`nat`, `int`, `rat`, `real`, `bytes`, `byte`, `list`, `option`,
  `either`, `fun`, `bool`). Half-implemented, postulate-filled stubs.
- **Gated Pure-era modules** — `bridge.rs`, `peano.rs`, `pure_hol.rs`
  (the old `Trueprop`/`eq_reflection` HOL-on-Pure design).
- **The HOL Python bindings** — `covalence-python/src/pure.rs`
  (`Type`/`Term`/`Thm`) and `tests/test_pure.py`. (Only the HOL
  bindings were removed; the store/WASM/SAT/graph Python API stays.)
- **Retired docs** — `ARCHITECTURE.md`, `AGENTS.md`, `DESIGN.md`,
  `MVP_DESIGN.md`, `plan.md`, the whole `docs/design/proposals/*` set,
  the arena/egraph prover docs (`prover-*.md`, `prop-egraph-design.md`,
  `c4.md`, `institution-map.md`, `refactor-plan.md`, `where-we-are.md`),
  and the `architecture` skill.

Restore any of it with `git checkout backup/pre-hol-cleanup -- <path>`.

## Learnings from the deleted stubs

Brief, so we can refill correctly:

- **Propositional logic derives cleanly.** Every connective is a
  let-style definition in `defs/logic.rs`; `unfold_term_spec` hands
  back its defining equation, and a β-normalizer (`beta_nf`, in
  `covalence-hol::proofs::rewrite`) + congruence reconstruct all
  intro/elim rules (the HOL Light `bool.ml` bootstrap). These are now
  fast kernel methods with executable soundness witnesses in
  `covalence-hol::proofs::bool`. No postulates needed.
- **Arithmetic is gated on the recursion theorem.** The `nat`/`int`
  laws all bottom out in proving that `natRec` *exists* (from its
  ε-uniqueness predicate in `defs/nat.rs`), which needs the **Hilbert
  choice axiom** over `TermKind::Select`. That is the single gate for
  the entire arithmetic tier; the deleted `nat_axioms`/`int_axioms`
  were postulating around it.
- **The `defs/` bodies are the source of truth.** The real
  definitions are let-style (`natAdd ≡ λn m. iter n succ m`, etc.) and
  `unfold_term_spec` gives their equations for free. The deleted
  `nat_axioms.rs` had drifted — it referenced a fictional
  `Term::const_("natrec")` disconnected from `defs::nat_rec`. Refill
  from the `defs/` bodies, not from re-postulating.

## Plan

### Phase 1 — finalize `covalence-core` `defs/` (pure definitions + ops)

Expose complete, tested pure definitions for
`defs/{nat, int, rat, real, bytes, list, stream, option, result}` with
all basic operations. Longer-term: `f32`/`f64` re-axiomatized through
`real`.

- Add **definition macros** to `covalence-core` so defining an op (its
  body, type, `Canonical` label, and `reduce_spec` literal-dispatch
  arm) is a few lines instead of boilerplate.
- **Test `covalence-core` extensively.** For every macro-defined op,
  add a test that the macro definition is *equal to a naive/reference
  definition* (and that closed-form `reduce_prim` agrees with the
  host-language computation on sampled literals). The kernel is the
  TCB — it should be the most-tested crate in the repo.

### Phase 2 — choice + the recursion theorem (refill the arithmetic tier)

- Add `Thm::select_ax` — the Hilbert choice axiom over `Select`
  (`⊢ ∀P x. P x ⟹ P (ε P)`), the third (and final intended)
  non-computational primitive.
- Prove the `natRec` recursion theorem from the ε-uniqueness predicate
  + `nat_induct`; then derive the Peano facts (`zero_ne_succ`,
  `succ_inj`) and the nat/int algebraic laws by induction — all
  postulate-free. This refills what the deleted catalogues stubbed.

### Phase 3 — `covalence-kernel` becomes a re-export façade

`covalence-hol` *is* the kernel rewrite. Replace the legacy
`covalence-kernel` (arena + egraph + UF) contents with a thin crate
that re-exports `covalence-hol` + `covalence-store` (+ the WASM
evaluator + tree-store) — i.e. the whole TCB + content-addressing
foundation — with `covalence-shell` sitting on top. Migrate the app
stack (`shell`, `repl`, `serve`, `client`, `alethe`, `egglog`, the
`cov` CLI) onto it.

### Phase 4 — wire end-to-end, then ship

Reconnect the shell / REPL / server so we can run **`covalence-core`
proofs from the shell again**; reinstate the HOL Python bindings on
`covalence-hol`; wire in the stores, WASM oracles (via the observer
rules), and tree-store. Then ship.
