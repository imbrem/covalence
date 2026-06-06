# MVP specs

> **STATUS: PRELIMINARY — first-pass execution plan, not yet
> committed-to.** Execution-side companion to
> [`00-overview.md`](./00-overview.md). Breaks down the path into
> minimal, measurable MVPs. Each MVP is one PR-sized step with a
> concrete acceptance test. Read sequentially; the dependency graph
> in §10 says which can run in parallel.
>
> **Expect revision.** Scopes, acceptance tests, file lists, and
> effort estimates here will tighten or shift as we start
> implementing. Treat this as the first scaffold of an execution
> plan, not a contract. Each MVP's spec should be re-read and
> refined when its turn arrives.

The design has converged across the session's notes. This doc
translates it into **specific commits a human or agent can actually
ship**, in order, with the smallest scope per step that still
delivers something demonstrable.

---

## Contents

1. [MVP discipline](#1-mvp-discipline)
2. [Template](#2-template)
3. [MVP-0: Kernel grows three tables](#3-mvp-0-kernel-grows-three-tables)
4. [MVP-1: `Prover::observe` API](#4-mvp-1-proverobserve-api)
5. [MVP-2: Alethe TRUST_THEORY_REWRITE migrates to `observe`](#5-mvp-2-alethe-trust_theory_rewrite-migrates-to-observe)
6. [MVP-3: `Prover::union` → `NotImplemented`](#6-mvp-3-proverunion--notimplemented)
7. [MVP-4: Corelib v0 (one theorem end-to-end)](#7-mvp-4-corelib-v0-one-theorem-end-to-end)
8. [MVP-5: VCS commit + mount + FUSE round-trip](#8-mvp-5-vcs-commit--mount--fuse-round-trip)
9. [MVP-6: Joint demo — prover reasons about a VCS-stored value](#9-mvp-6-joint-demo--prover-reasons-about-a-vcs-stored-value)
10. [Dependency graph and ordering](#10-dependency-graph-and-ordering)
11. [What's deliberately *not* an MVP yet](#11-whats-deliberately-not-an-mvp-yet)
12. [Cross-references](#12-cross-references)

---

## 1. MVP discipline

Each MVP must:

- **Be smaller than 500 LoC** of net diff (including tests). If
  bigger, split.
- **Have a single, concrete acceptance test** that demonstrates the
  capability. Either an automated test or a documented manual
  procedure.
- **Touch a bounded set of files.** Listed explicitly per MVP.
- **Be reversible.** Either by direct revert, or by a follow-up that
  removes the new code without breaking dependents.
- **Land green.** All existing tests pass after the MVP merges.
- **Be standalone for review.** A reviewer should be able to
  understand the MVP's purpose and acceptance test by reading the
  PR description and 1–2 of the architecture notes.

What an MVP **is not**:

- A complete feature. MVPs are atomic steps; features arrive after
  several MVPs.
- A refactor for its own sake. Each MVP advances toward
  [`VISION.md`](../../../VISION.md).
- A doc-only change. Doc-only work happens in this directory; MVPs
  ship code.

---

## 2. Template

```
## MVP-N: <Name>

**Goal.** <One sentence: what becomes possible after this MVP that
wasn't possible before.>

**Scope.** <What's in. ~3–5 bullets.>

**Out of scope.** <What's deliberately left for later. ~2–4 bullets.>

**Acceptance test.** <The smallest empirical check that the MVP
works. Code-level: a `cargo test` invocation. Human-level: a
manual REPL/CLI procedure.>

**Files touched.** <List + estimated diff size per file.>

**Dependencies.** <Which MVPs must land first. None for the first.>

**Risks.** <What could go wrong + mitigation.>
```

---

## 3. MVP-0: Kernel grows three tables

**Goal.** `covalence-shell::Kernel` becomes the operational
foundation for authorities, facts, and content-addressed values
([per `kernel-as-os.md`](./notes/kernel-as-os.md)), without changing
any trait surfaces. Sets up everything downstream.

**Scope.**

- **Authority registry**: a `HashMap<AuthorityId, AuthorityRecord>`
  on `Kernel`. `AuthorityRecord` carries the kind (`Local | Keyed`)
  and the set of owned relation names. Methods:
  `register_authority(name, relations) -> AuthorityId`,
  `lookup_authority(id) -> Option<&AuthorityRecord>`.
- **Fact table**: a `BTreeMap<(AuthorityId, RelationName), Vec<Fact>>`
  on `Kernel`. `Fact` carries `args: Vec<FactArg>` and an opaque
  `FactId`. Methods:
  `record_fact(authority, relation, args) -> FactId`,
  `query_facts(authority, relation) -> impl Iterator<Item = &Fact>`.
- **Typed CA accessors**: thin wrappers over the existing
  `BlobStore<O256>` for typed retrieval —
  `get_thm_bytes(hash)`, `get_library_bytes(hash)`,
  `get_tree_bytes(hash)`. Each is `Option<Vec<u8>>`-returning.
- **Starter authorities** registered at `Kernel::new()`: `user`,
  `release`, `blake3`, `ed25519`. Each owns a minimal set of
  relations (e.g., `release.signed`, `blake3.hashed`).
- **Fold `tree_hashes` into the fact table** as
  `tree_store.is_tree(hash)`. The existing `is_tree(hash)` /
  `store_tree(data)` methods keep their signatures; their
  implementations now route through the fact table.

**Out of scope.**

- Any change to `Prover`, `HolLightKernel`, or other public traits.
- Any new authorities beyond the four starters.
- Persistence — the fact table is in-memory only.
- Path-based access (`/auth/...`, `/lib/...`). That's MVP-5 territory.
- Tree mount-as-overlay; that's a follow-up.

**Acceptance test.**

```rust
// crates/covalence-shell/src/kernel.rs (tests module)

#[test]
fn round_trip_a_fact() {
    let mut k = Kernel::new();
    let release = k.lookup_authority_by_name("release").unwrap();
    let fact_id = k.record_fact(
        release,
        "signed",
        vec![FactArg::Hash(O256::zero()), FactArg::Bytes(b"sig".to_vec())],
    ).unwrap();
    let facts: Vec<_> = k.query_facts(release, "signed").collect();
    assert_eq!(facts.len(), 1);
    assert_eq!(facts[0].id, fact_id);
}

#[test]
fn existing_tree_hashes_keep_working() {
    let mut k = Kernel::new();
    let data = sample_tree_bytes();
    let hash = k.store_tree(&data).unwrap();
    assert!(k.is_tree(&hash).unwrap());
    // And: the fact is observable via the new API too.
    let tree_auth = k.lookup_authority_by_name("tree_store").unwrap();
    let facts: Vec<_> = k.query_facts(tree_auth, "is_tree").collect();
    assert_eq!(facts.len(), 1);
}
```

**Files touched.**

- `crates/covalence-shell/src/kernel.rs` (+~200 lines).
- `crates/covalence-shell/src/lib.rs` (re-export, ~5 lines).
- New file: `crates/covalence-shell/src/facts.rs` (~100 lines) for
  the `Fact`, `FactArg`, `AuthorityId`, `RelationName` types.
- Tests inline.

**Dependencies.** None.

**Risks.**

- Renaming `Kernel` is *not* part of this MVP (we decided against
  it; the rename was wrong). But the existing `Kernel` may need
  doc-comment updates so it's clear it's growing into a system
  kernel role rather than staying a blob backend.
- `FactArg` type design: `enum { Hash(O256), Handle(u32), Bytes(Vec<u8>), Str(String) }`
  is the strawman. Lock before this MVP starts to avoid churn.

---

## 4. MVP-1: `Prover::observe` API

**Goal.** The `Prover` trait gains a kernel-agnostic
`observe(authority, relation, args) -> Thm` method, with the
`covalence-kernel` impl routing it through the
[MVP-0](#3-mvp-0-kernel-grows-three-tables) fact table. Downstream
shells can start writing call sites that compile.

**Scope.**

- New method on `Prover`:
  ```rust
  fn observe(
      &mut self,
      authority: &str,
      relation: &str,
      args: &[Self::Term],
  ) -> Result<Self::Thm, ProverError>;
  ```
- Impl in `prover_kernel.rs`: record the fact in `Kernel`; allocate
  the term `authority.relation(args...)` in the HOL kernel as a
  conclusion; produce a `Thm` whose conclusion is that term and
  whose hypothesis set is empty (matching the framework's
  `(observe)` rule shape — atomic observations land in the empty
  context).
- Stub trait methods: `Prover::stdlib_thm` and `Prover::corelib_thm`
  remain `NotImplemented` for now; they'll get real impls in MVP-4.

**Out of scope.**

- Killing `Prover::union`. That's MVP-3.
- Wiring Alethe through `observe`. That's MVP-2.
- Soundness proof — `observe` is currently the trust escape hatch
  in *named* form; the user manually discharges via meaning-axioms.
  The framework redesign (per
  [`modified-hol.md`](../layered-framework/notes/modified-hol.md))
  later replaces the impl with a proper soundness story.

**Acceptance test.**

```rust
#[test]
fn observe_produces_a_thm() {
    let mut k = Kernel::new();
    let x = k.free_var("x", k.bool_ty()?)?;
    let thm = k.observe("user", "asserts", &[x])?;
    assert_eq!(k.hyps(&thm).count(), 0);
    let concl = k.conclusion(&thm)?;
    // concl is now the term "user.asserts(x)" — we just check the head.
    // Exact term shape is impl detail.
    assert!(format!("{concl:?}").contains("user"));
    assert!(format!("{concl:?}").contains("asserts"));
}
```

**Files touched.**

- `crates/covalence-shell/src/prover.rs` (+~30 lines).
- `crates/covalence-shell/src/prover_kernel.rs` (+~50 lines).
- `crates/covalence-shell/src/kernel.rs` (helper for forming
  `authority.relation(args)` terms, +~30 lines).

**Dependencies.** MVP-0.

**Risks.**

- How is `authority.relation(args)` represented in the kernel? As a
  named constant + applications? As a fresh `TermKind` variant? V1
  recommendation: just a `Const("authority.relation", τ)` applied
  to args; the framework refines later.

---

## 5. MVP-2: Alethe TRUST_THEORY_REWRITE migrates to `observe`

**Goal.** The Alethe bridge's `cong`-based trust escape hatch is
expressed as an `observe` under an `alethe` authority's
`trust_rewrite` relation. End-to-end Alethe proofs still close.

**Scope.**

- Register an `alethe` authority in `covalence-alethe`'s bridge,
  owning `trust_rewrite`.
- Replace every `prover.union(lhs, rhs)` in `covalence-alethe`'s
  TRUST_THEORY_REWRITE path with
  `prover.observe("alethe", "trust_rewrite", &[lhs, rhs])`, then
  use the resulting Thm to feed downstream `eq_mp` / `cong` calls.
- Existing Alethe tests continue to pass.

**Out of scope.**

- Killing `Prover::union` — that's MVP-3.
- Other `union` call sites — they migrate in MVP-3.
- Discharging the `trust_rewrite` observation via a meaning-axiom
  in the test suite. The observation remains a hypothesis on the
  resulting Thm; that's the LCF-correct outcome.

**Acceptance test.**

```sh
cargo test -p covalence-alethe
```

Plus: visual inspection of one resulting Thm shows the
`trust_rewrite` observation in its hypothesis set.

**Files touched.**

- `crates/covalence-alethe/src/*.rs` — wherever `Prover::union` is
  called; replace + restructure (~100 lines).

**Dependencies.** MVP-1.

**Risks.**

- The Alethe rules feeding off the union (`cong`, `eq_mp`,
  `tautology_intro`) may need adjustment: they currently expect
  unioned equalities to be observable via `egraph.find()`; under
  observation they instead see a Thm with the equality as a
  hypothesis. Routing depends on whether subsequent rules consume
  the hypothesis or the union state.

---

## 6. MVP-3: `Prover::union` → `NotImplemented`

**Goal.** The trust escape hatch is gone. Any call site that hasn't
migrated to `observe` crashes loudly. The kernel's "named-source
discipline" is enforced.

**Scope.**

- Change `Prover::union`'s body to:
  ```rust
  fn union(&mut self, _a: Self::Term, _b: Self::Term)
      -> Result<(), ProverError>
  {
      Err(ProverError::NotImplemented(
          "union is gone; route through observe under a named authority"
              .to_string()))
  }
  ```
- All `Prover::union` call sites in the workspace are either
  (a) migrated to `observe` (the natural ones) or (b) marked
  `#[ignore]` in test modules with a TODO referencing this MVP.
- The trait's docstring is updated to explain the deprecation
  pattern: `observe` for named sources, framework primitives for
  the proper soundness story.

**Out of scope.**

- Adding a "proper soundness" path beyond `observe`. That's
  framework-redesign territory.

**Acceptance test.**

```sh
cargo test --workspace
```

All tests pass. Specifically: no test was disabled to make this
pass; any disable-with-TODO is documented in the PR description.

**Files touched.**

- `crates/covalence-shell/src/prover.rs` and `prover_kernel.rs`
  (impl change, ~20 lines).
- Any remaining `union` call sites in `covalence-alethe`,
  `covalence-hol`, etc. (typically ~10–30 lines each).

**Dependencies.** MVP-2 (to make sure Alethe doesn't break here).

**Risks.**

- Alethe rules that consume unioned equalities (`cong` with depth >
  0) may stop firing because the equality is now only in a Thm
  hypothesis, not in the UF. May need follow-up to re-introduce
  equalities into the UF *as derivations* (via `eq_mp` chains from
  the observation Thm).

---

## 7. MVP-4: Corelib v0 (one theorem end-to-end)

**Goal.** Prove the corelib loading pipeline by shipping *one*
theorem (`nat_add_comm`) end-to-end. Default mode only (no paranoid
yet; that's a stretch goal).

**Scope.**

- New crate `covalence-corelib`.
- Internal: derive `nat_add_comm` (`∀a b. a + b = b + a`) against
  `covalence-kernel`'s primitive rules + `Prover` API. Serialize
  the resulting `(Arena, UF, name-table)` into a blob.
- Sign the blob with a hardcoded dev Ed25519 key (the future
  `release` authority's key).
- A `OnceCell<CoreLib>` exposed via `pub fn corelib(kernel: &mut
  Kernel) -> &'static CoreLib`. On init: load the embedded sigblob,
  verify signature, import into the kernel.
- `Prover::corelib_thm("nat::add_comm")` returns the imported Thm.

**Out of scope.**

- Paranoid mode (`corelib-verify` feature). Stretch goal; can land
  in a follow-up.
- Any theorem besides `nat_add_comm`. The whole list in
  [`core-lib.md` §3](./notes/core-lib.md#3-what-corelib-contains)
  is V0+1 work.
- Stdlib libraries.
- Optional tree mount overlay.

**Acceptance test.**

```rust
#[test]
fn corelib_nat_add_comm() {
    let mut k = Kernel::new();
    let thm = k.corelib_thm("nat::add_comm").unwrap();
    // Check the conclusion has the expected shape: ∀a b. a + b = b + a.
    let concl = k.conclusion(&thm).unwrap();
    let s = format!("{concl:?}");
    assert!(s.contains("forall"));
    assert!(s.contains("add"));
}
```

**Files touched.**

- New crate `crates/covalence-corelib/` (~300 lines including the
  derivation, serialization, signature, loader).
- `crates/covalence-shell/src/prover.rs` — `corelib_thm` becomes
  non-stub (~20 lines).
- `crates/covalence-shell/src/prover_kernel.rs` — loader plumbing
  (~30 lines).

**Dependencies.** MVP-1 (the observe API; corelib loading uses it
internally). Optionally MVP-0 alone if loading doesn't need
observation primitives.

**Risks.**

- Serialization format: arena + UF + name-table is non-trivial to
  serialize. Use `covalence-object`'s `Table` machinery. Lock the
  format before starting; document in `core-lib.md` §11 (Open
  questions: signed-blob format).
- The derivation of `nat_add_comm` itself may surface kernel API
  gaps. Plan to either fill them in as part of this MVP or stub
  with `NotImplemented` (documenting which gap).

---

## 8. MVP-5: VCS commit + mount + FUSE round-trip

**Goal.** Existing FUSE scaffold (`covalence-fuse`) graduates to
"commits a tree, mounts it, reads files through the mount." The
VCS stream has an end-to-end demo.

**Scope.**

- `cog cog commit <working-tree-dir>` — produces a tree hash and
  records it via the `tree_store` authority's `is_tree` relation.
- `cog cog mount <tree-hash> <mountpoint>` — mounts the tree via
  FUSE.
- `cog cog ls <mountpoint>/...` reads back the original files.
- A smoke test that does all three in sequence.

**Out of scope.**

- Authorship metadata (who committed, when). Future MVP.
- Branching, history. Future.
- Cross-store federation. Future.

**Acceptance test.**

```sh
# Manual or scripted:
mkdir /tmp/wt && echo hello > /tmp/wt/file.txt
H=$(cov cog commit /tmp/wt)
mkdir /tmp/mnt
cov cog mount $H /tmp/mnt
test "$(cat /tmp/mnt/file.txt)" = "hello"
fusermount -u /tmp/mnt
```

**Files touched.**

- `crates/covalence-fuse/src/*.rs` — wherever the mount logic lives
  (~100–200 lines).
- `crates/covalence/src/cog.rs` or similar — CLI integration
  (~50 lines).
- Smoke test script in `tests/` or as a `bun test` integration.

**Dependencies.** MVP-0 (the new `tree_store` authority lookup).
Otherwise independent of the prover stream.

**Risks.**

- FUSE on Linux only initially. macOS/Windows are follow-ups.
- The mount's lifecycle interacts with the Kernel's `Arc<Mutex<>>`
  story (per [`kernel-as-os.md` §9](./notes/kernel-as-os.md#9-open-questions));
  V1 may need to serialize all FUSE requests.

---

## 9. MVP-6: Joint demo — prover reasons about a VCS-stored value

**Goal.** First end-to-end exercise of the substrate fusion: VCS
commits a value; the prover proves a fact about its hash.

**Scope.**

- `cov demo joint` — a CLI subcommand that:
  1. Commits a small file into the VCS (`covalence-fuse` /
     `cov cog commit`).
  2. Constructs a Prover term referencing the committed file's
     hash (the user-friendly form: `commit_hash`).
  3. Derives a Thm like `tree_store.is_tree(commit_hash)` via
     `observe` (the fact is in the kernel from the VCS step).
  4. Prints the Thm.
- The same workflow is also runnable from the REPL.

**Out of scope.**

- The Thm being non-trivial. The goal is mechanics, not depth.
- Cross-instance federation. Future.

**Acceptance test.**

```sh
cov demo joint
# Output includes the committed tree hash and a printed Thm
# whose conclusion mentions `tree_store.is_tree(<hash>)`.
```

**Files touched.**

- `crates/covalence/src/demo.rs` (new, ~80 lines).
- Plumbing changes in `covalence-shell` (~30 lines).

**Dependencies.** MVP-0, MVP-1, MVP-5.

**Risks.** Low — the building blocks land in earlier MVPs.

---

## 10. Dependency graph and ordering

```
              MVP-0  (Kernel tables)
                │
        ┌───────┼───────┐
        │       │       │
      MVP-1   MVP-5   MVP-4
        │     (VCS)   (corelib)
        │       │       │
      MVP-2     │       │
        │       │       │
      MVP-3     │       │
        │       │       │
        └───────┼───────┘
                │
              MVP-6  (joint demo)
```

**Parallelizable tracks** after MVP-0 lands:

- **Prover track**: MVP-1 → MVP-2 → MVP-3 → MVP-4.
- **VCS track**: MVP-5.

Both feed MVP-6.

**Estimated effort** (rough; one human-day each unless noted):

- MVP-0: 1 day.
- MVP-1: 1 day.
- MVP-2: 1–2 days (Alethe restructure).
- MVP-3: 1 day.
- MVP-4: 2–3 days (serialization + derivation).
- MVP-5: 2 days (FUSE polish + CLI).
- MVP-6: 1 day.

Total: ~10–12 days end-to-end. With parallelism: ~6–8 calendar
days.

---

## 11. What's deliberately *not* an MVP yet

Listed by name with one line. Each gets its own MVP later.

- **Paranoid corelib mode.** Stretch within MVP-4 or a follow-up.
- **Stdlib libraries (regex, parsers, inductive datatypes).** Each
  is a future MVP modeled after MVP-4.
- **`Prover::observe` proper soundness story.** Currently named
  trust; framework redesign replaces.
- **Framework crate** (`covalence-framework`) as a separate
  artifact. The Phase-2 layered-framework split happens later;
  for now the framework concerns live in `covalence-shell`.
- **HOL Light shell migration off direct kernel access.** Future
  MVP per [`HolPrim`'s docstring].
- **OpenTheory full standard prelude.** Future MVP.
- **Cross-instance federation.** Distant future.
- **Format plane** (keyed-BLAKE3 identities, etc.). Distant future.
- **Base-shift functor.** Distant future.
- **Probability internal logic (`L_prob`).** Distant future.

---

## 12. Cross-references

- [`./00-overview.md`](./00-overview.md) — the path doc. MVPs above
  realize Phase 2 (parallel prover + VCS) and Phase 3 (the seam).
- [`./notes/kernel-as-os.md`](./notes/kernel-as-os.md) — the
  Kernel-as-OS framing. MVP-0 implements it.
- [`./notes/core-lib.md`](./notes/core-lib.md) — corelib design.
  MVP-4 is V0 of it.
- [`../layered-framework/notes/modified-hol.md`](../layered-framework/notes/modified-hol.md)
  — the kernel logic. MVPs above expose its surface; the kernel
  rewrite itself is post-MVP.
- [`../layered-framework/notes/arena-and-uf.md`](../layered-framework/notes/arena-and-uf.md)
  — substrate/framework split. MVPs above work *above* the
  substrate; the substrate refactor is post-MVP.
- [`../../../VISION.md`](../../../VISION.md) — the vision the MVPs
  collectively realize the first slice of.
