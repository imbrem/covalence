+++
id = "N0019"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:claude"
at = "2026-07-13T20:42:09+01:00"
source = "legacy"
agent = "claude"
harness = "claude"
+++

# Kernel soundness audit + assumption-tracking design

Audit report + forward-looking design. §1–§3 inventory/critique the trusted base
and propose non-blocking confidence steps; §4 designs **assumption tracking** (the
key ask). No kernel code is changed by this doc; §4's API is a proposal.

Original audit was against the old `crates/covalence-core/src/` layout (branch
`proof-thoughts`, 2026-06); the crate has since moved to
`crates/kernel/hol/core` and some specifics (e.g. `FalseElim` now derived, T/F now
defined constants) have shifted — treat file/rule names as indicative, the
*structure* of the risk as current. Grounds in
[`../kernel-design.md`](../kernel-design.md), [`../../observers/observers.md`](../../observers/observers.md)
§7, [`../../vision/VISION.md`](../../vision/VISION.md) §4.

## Where the trust actually concentrates

The logical core (HOL Light's primitive rules + standard derived rules) is on
solid ground: textbook rules, tight single-shot term builds, module-private
`Thm::build` as the sole minting surface. The risk lives in the **non-logical
extensions** the kernel adds for efficiency and its binary-data mission:

- **Accelerated reduction** (`reduce_prim` / `unfold_term_spec`) — sound "by
  literal denotation," but the claim rests on Rust arithmetic agreeing with the
  catalogue bodies it is coupled to. Guarded by *example-based* tests, not
  exhaustive proof. One real hole (`nat.mod n 0` reducing to `0` while the body
  gave `n`, yielding `⊢ 0 = 5`) was found and fixed here historically.
- **The `defs/` catalogue** — "semi-trusted," but several rules
  (`unfold_term_spec`, `spec_ax`, the `spec_*` subtype laws) commit the kernel to
  facts about catalogue *bodies*. Internal consistency (that `int.add`'s body
  really is Grothendieck addition, that `unit`'s predicate carves a singleton) is
  asserted by construction, never machine-checked. The catalogue is semi-trusted
  for *user-constructed* specs but **fully trusted for the kernel-shipped coupled
  subset** (only that subset can be enlarged only through `PRIM_TABLE`, i.e.
  kernel code).
- **The non-computational axioms** — `nat_induct`, `false_elim`, `unit_eq`, `lem`,
  plus `select_ax`/`spec_ax`/`succ_inj`/`zero_ne_succ`. That is **eight**
  axiom-shaped rules, not the four sometimes quoted. Standard and sound, but
  `lem`, `succ_inj`, `zero_ne_succ` are *postulated* where they are *derivable* —
  each is a place a coding bug could not be caught by "it's the standard
  derivation," because no derivation is in the loop.
- **No provenance for any of it.** `has_no_obs` tracks only `Obs` leaves. A `Thm`
  via `reduce_prim`, `lem`, or `nat_induct` carries **zero trace**. So the kernel
  cannot answer "does this proof use nat acceleration?" — the question §4 makes
  answerable. `has_no_obs == true` does **not** mean constructive or
  acceleration-free.

## Gaps worth naming

- **Provenance is syntactic-only** — the headline gap; acceleration/axiom use
  leaves no trace.
- **The acceleration coupling guards are example-based** (`audit_reduce_matches_body`,
  `audit_reduced_def_specs_satisfy_their_predicate` probe finite tuple lists).
  Adding a coupled spec without extending the probe list silently leaves it
  unguarded.
- **The `spec_ax` × `reduce_prim` coupling** rests on a uniqueness-by-construction
  claim that is not machine-checked (only "reduce satisfies the equations" is).
- **Catalogue content is asserted, never checked.**
- **`subst.rs`** — the largest fiddly-index surface (open/close/shift/subst,
  simultaneous tvar subst, capture avoidance) — has no property tests; only
  end-to-end rule tests. A capture/off-by-one here is a silent soundness bug.
- **No independent re-check path** (kernel-design's "paranoid mode" is design, not
  code).

## Confidence-improvement roadmap (non-blocking)

1. **Make acceleration guards exhaustive-ish + self-extending** — property-based
   over ranges incl. zero/sign/overflow edges; a table-completeness test iterating
   `PRIM_TABLE` so a new coupled spec without a guard fails; a uniqueness check for
   the `spec_ax` coupling.
2. **Discharge the postulated-but-derivable axioms** — restore the connective
   witness cross-check (the `covalence-hol::proofs::bool` witnesses were deleted; a
   test that would catch an implementation divergence is gone), then extend the
   pattern to `lem` (HOL Light's `EXCLUDED_MIDDLE` from ε + extensionality +
   `deduct_antisym`) and `succ_inj`/`zero_ne_succ` (from the nat recursion
   theorem). Shrinks the *effective* axiom surface from eight to ~three
   (`nat_induct`, `false_elim`, `unit_eq`) while keeping the fast constructors.
3. **Property tests for `subst.rs`** — subst/shift commutativity, `open ∘ close =
   id` on closed terms, α-equivalence under renaming, simultaneous-vs-sequential
   subst divergence.
4. **Make the catalogue *checkable* via the `core.cov` data migration** — when the
   catalogue becomes data, the body-vs-reduce coupling, the spec-predicate
   obligations, and "`unit` carves a singleton" become *checks over the data* run
   at load time (a new small trusted parser, but the arithmetic moves from "trusted
   by inspection" to "data + checked reduction").
5. **A minimal "paranoid mode" prototype** re-checking `reduce_prim` outputs.
6. **Cross-validation / external model** (HOL Light, a Lean/Coq model) — big,
   blocks nothing.

## Assumption tracking — the design

Forward-looking; not to implement now. The concrete `Thm`-assumption-set mechanism
for the two-assumption-set idea of [`../pure-design.md`](../pure-design.md)
§4; realizes [`../../observers/observers.md`](../../observers/observers.md) §7.2 ("this proof doesn't use
`Nat`"). §4.4 code is illustrative.

### Principle: a trusted observer = a sound assumption + an efficient representation

`Int`/`Bytes`/`Nat` are *trusted observers*: the only thing separating a trusted
observer from an untrusted one is that "this observer is sound" is an assumption
with a compiled-in representation rather than a hypothesis threaded through
`Thm::assume`. Same logical content; only the carrying cost differs. Assumption
tracking makes that content **visible without making it expensive**.

### The base assumption set + lattice

A small extensible set of named base-assumption tags:

```
Accel(NatAccel) Accel(IntAccel) Accel(BytesAccel) Accel(FixedWidthAccel)
Axiom(Lem)      Axiom(Choice)   Axiom(Peano)      Axiom(UnitSingleton)
Obs(TypeId)     -- one per Rust observer type (WasmSpec, Store, Blake3, …)
Postulate(Hash) -- one per content-addressed assumed body (Thm::assume)
```

An **assumption set** = a set of these (bitset for fixed tags + a set for
open-ended `Obs`/`Postulate`), a join-semilattice under union with bottom `∅`
("bare logic only"). Each rule's result set = union of premises' sets + any tag the
rule introduces:

- `reduce_prim` adds the `Accel(_)` tags for the literal kinds it touched.
- `unfold_term_spec` adds nothing for a *user* spec (definitional let-binding,
  sound for any body) but adds the `Accel` tag when unfolding a *coupled*
  kernel-shipped spec.
- `lem`→`Axiom(Lem)`; `select_ax`/`spec_ax`→`Axiom(Choice)`;
  `nat_induct`/`succ_inj`/`zero_ne_succ`→`Axiom(Peano)`; `unit_eq`→
  `Axiom(UnitSingleton)`.
- `obs_*` add `Obs(TypeId::of::<O>())`; `Thm::assume(body)` also records
  `Postulate(hash(body))`.
- The pure logical rules add **nothing** — identical to how `hyps` already
  propagate (union on multi-premise, identity on single), so it slots into the
  existing `Ctx::union` plumbing.

### Null-base default — everyday proving is unburdened

The set is an **additional, ignored-by-default field** on `Thm`. Existing code,
`Display`, equality, hashing, `has_no_obs` are unaffected. It never blocks a rule
or changes a conclusion — pure additive audit annotation. Cost model matches
`observers.md` §7: standard assumptions are "on" by default (null base = "I accept
all standard base assumptions"); tracking only *surfaces* what was used when asked.

### Query + discharge (illustrative — PROPOSAL)

```rust
pub enum Assumption {
    NatAccel, IntAccel, BytesAccel, FixedWidthAccel,
    Lem, Choice, Peano, UnitSingleton,
    Obs(std::any::TypeId),
    Postulate(O256),
}
pub struct Assumptions { /* bitset + small set */ }

impl Thm {
    pub fn assumptions(&self) -> &Assumptions;
    pub fn uses(&self, a: Assumption) -> bool;
    /// Discharge `a` with a Thm proving it in the bare logic (or under a
    /// strictly smaller set). Removes the tag. Fails if `proof` is invalid or
    /// itself depends on `a` (no circularity).
    pub fn discharge(self, a: Assumption, proof: &Thm) -> Result<Thm>;
}
```

`has_no_obs` becomes `!assumptions().has_any_obs()`; a stronger new query "is this
in the bare logic?" is `assumptions().is_empty()`.

### Discharging by proving — `Nat` without `NatAccel`

The payoff `observers.md` §7.2 names:

1. Develop Peano arithmetic over the *defined* naturals (`defs/nat.rs` bodies via
   `nat_rec`) using only `nat_induct` + bare rules + `define`, *never*
   `reduce_prim`. Every such theorem's set **excludes `NatAccel`**.
2. Prove the development **categorical** (naturals unique up to iso) — so the
   accelerated `Nat` literals and defined naturals are provably the same structure.
3. With that isomorphism *as a `NatAccel`-free theorem*, `discharge(NatAccel,
   iso_proof)` strips the tag from any `reduce_prim`-derived numeric equation,
   which is now backed by a bare-logic proof.

No-circularity is structural: `discharge` rejects a `proof` whose own set contains
the tag. `NatAccel` moves from *assumed* to *proved* — the observer becomes
known-sound by a proof. Generalizes: a `WasmSpec` `Obs(TypeId)` is discharged once
someone proves `WASM(P,D,A) ⟹ ∃D'. ZFC(D',A)`; a `Postulate(hash)` by a bare-logic
proof of that body. One uniform ledger across all three.

### Relationship to existing substrate + migrations

- `has_no_obs` is the seed (the syntactic half). The set generalizes it to a
  semantic ledger. Works today (literals still `TermKind` variants) by having
  `reduce_prim` tag `NatAccel` directly; composes cleanly with the "literal as
  observer" move (tag via `Obs(TypeId)` instead).
- **`core.cov`:** coupled-spec tags become readable off the data; the frozen
  catalogue's content hash can itself be a `Postulate`-style provenance root ("this
  proof trusts catalogue blob `O256(…)`").
- The `observers.md` §3 validator state `(M,P,mFrozen,pFrozen)` and this set are
  the same ledger from two ends: the validator's `P` = upstream aggregation of an
  observer's assumptions; the `Thm` set = downstream record of what a proof
  inherited. Discharge connects them.

## Bottom line

The logical core is solid and the minting boundary genuinely small. Trust
concentrates, correctly, in the non-logical extensions — acceleration, the coupled
catalogue subset, the postulated-but-derivable axioms — verified by example-based
tests plus docstrings (which found a real hole once and could miss another). The
single most valuable structural improvement is **assumption tracking**: it turns
"what does this proof trust?" into a cheap query, makes `has_no_obs` a special
case, and gives a principled, no-circularity path to *retire* the most-used trusted
assumptions (`NatAccel` first) by proving them.
