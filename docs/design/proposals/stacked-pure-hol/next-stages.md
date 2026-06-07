# Pure: Optional Next Stages

> **STATUS: OPTIONAL PROPOSALS, NOT COMMITTED.**
>
> Companion to [`README.md`](./README.md). Records design ideas for
> follow-up work after the current `covalence-pure` / `covalence-pure-shell`
> merge. Every entry below is marked **OPTIONAL** — none of these
> block any pending work, and any of them can be pursued, deferred,
> reordered, or rejected independently.

This document captures the design conversations from the
`covalence-pure` MVP work that we deliberately *did not* land in the
initial merge candidate, so they're available to refer back to without
cluttering the kernel.

---

## Status of the merge candidate

`covalence-pure` after this round includes:

- Locally-nameless terms (`Term`) and types (`Type`) with α-transparent
  `Hint` for binder labels.
- Tuple-variant `TermKind` / `TypeKind` (cleaned up from earlier
  struct-like variants).
- All Pure LF rules + the six equality rules + `inst_tfree`.
- `Thm::define(name, body)` — fresh `Arc`-identity-based definitions
  with no kernel-side signature (each call allocates a unique pointer;
  freshness comes from the allocator).
- `Thm::obs_eq<O: ObsEq>` — observation equality. Per-`O` policy via
  the user-implemented `ObsEq` trait; soundness is *unconditional*
  under the parametric ε-model regardless of impl. `ObsEq` impls are
  **not** in the TCB.
- `DynObs` — `Arc<dyn Any + Send + Sync>` with pointer-identity
  `Eq`/`Hash`/`Ord` (kernel safety doesn't depend on user trait impls).
- Lazy-static canonical instances of `Type::prop()`, `Type::bytes()`,
  `Type::bool()` — O(1) `Arc::clone` on the hot path.
- `Term::cast` (universal — Term has no observer parameter now, this
  is just discharge predicates: `has_no_obs`, `all_obs_match::<O>`,
  `for_each_obs::<O>`).

`covalence-pure-shell` includes:

- Handler-driven `term_to_sexp` / `term_from_sexp` (caller supplies
  `ObsSerializer` / `ObsParser` trait impls).
- Handler-driven content hashing (`hash_term` with `ObsHasher`).
- `UnitObs` / `UnitObsHasher` defaults for the trivial `()` observer.

`covalence-python`: pyo3 wrappers for `Type`, `Term`, `Thm` with the
full rule API.

`covalence-wasm/wit/pure.wit`: `cov:pure@0.1.0` WIT package defining
the guest-facing kernel API, with `term-set` as an *opaque* resource
so the host's hyp-set representation can change without breaking
guests.

**Tests:** ~118 across `observer`, `soundness`, `rules`, `hash`,
`sexp_roundtrip`, `define`, and `test_pure` (Python).

---

## Optional next stages

### A. **OPTIONAL** — `Thm::new_type_definition` (HOL Light parity)

Mirror HOL Light's `new_basic_type_definition`. Given a witness
theorem `⊢ P x : bool`, introduce a fresh type constant `τ` and two
fresh constants `abs : α → τ`, `rep : τ → α`, returning the two
bijection theorems:

```
⊢ ∀a:τ. abs (rep a) = a
⊢ ∀r:α. P r ↔ rep (abs r) = r
```

**Implementation approach:** use the same Arc-identity trick as `Def`.
Each call allocates a fresh `Arc` for the new type constant; the
allocator gives us freshness. No stateful signature needed.

**TCB cost:** ~80–100 LoC.

**Unblocks:** HOL Light's standard library (`num`, `list`, `prod`,
real numbers, …) without resorting to user-asserted bijection axioms.

**Variant — the disjunct trick:** instead of requiring a witness
theorem, define `τ = {x | P x ∨ x = some_canonical_witness}`. Always
inhabited. Lives at the HOL layer, not the kernel — but the kernel
rule should still take a witness, and HOL builds on top.

---

### B. **OPTIONAL** — TyCon-as-observation (radical TyCon redesign)

The user pointed out that `TypeKind::Tycon(SmolStr, Vec<Type>)` could
be replaced — or *extended* — with something resembling the
observation system. The natural shape:

```rust
/// A type constructor carrying type-erased Rust data, compared by
/// `Arc` pointer identity. Mirrors `DynObs`.
pub struct DynTyCon {
    name: Hint,
    inner: Arc<dyn Any + Send + Sync>,
    debug_fn: fn(&dyn Any, &mut fmt::Formatter<'_>) -> fmt::Result,
}

pub enum TypeKind {
    TFree(SmolStr),
    Prop,
    Bytes,
    Fun(Type, Type),
    /// Structural type constructor — compared by name + args.
    Tycon(SmolStr, Vec<Type>),
    /// Identity-based type constructor — compared by Arc pointer.
    DynTycon(DynTyCon, Vec<Type>),
}
```

**Pros of this hybrid:**
- Same `Arc`-identity freshness property as `Def`. Distinct `DynTyCon::new`
  calls produce distinct type constructors even with identical names
  — exactly the property `new_type_definition` (option A) needs for
  freshness, without an explicit signature.
- Per-Rust-type extensions: a `BoolTyCon` struct can carry
  kernel-managed metadata; a `ListTyCon` can expose variance
  information through its own Rust type. The trait-based policy lever
  we get from `ObsEq` could have an analogue here for
  `TyConEq` — letting each type constructor declare when two
  applications should be equated.
- Structural `Tycon(SmolStr, Vec<Type>)` is preserved for the simple
  cases (display strings, cross-process stable names, the common
  HOL type constants).
- `new_type_definition` from option A could produce a `DynTycon` —
  the two proposals compose.

**Cons:**
- Loses the structural simplicity of "all type constants are names."
  Cross-process serialization of `DynTycon` becomes a process-local
  concern (just like serializing a `DynObs`).
- Users defining their own type families have to write a Rust type
  per family.
- Two type constructors with the same display name and the same
  args — one structural, one identity-based — compare *unequal*. A
  potential source of confusion.

**Recommendation:** keep both. `Tycon` for "named uninterpreted" cases
(matches current behaviour, good for cross-process). `DynTycon` for
kernel-introduced subtype declarations (`new_type_definition` plus
type-class-style extensions). Best of both worlds: same architectural
pattern Pure already uses for `Def` (term constants) and `DynObs`
(observations) is reused for type constants — three places in the
kernel where Arc identity gives us freshness for free.

---

### C. **OPTIONAL** — Lightweight TyCon signature tracking

Conservative alternative to B. Keep `Tycon(SmolStr, Vec<Type>)` exactly
as it is. Add a `Signature` struct (separate from `Thm`/`Term`/`Type`)
that tracks declared type-constant arities and constant principal
types:

```rust
pub struct Signature {
    type_consts: HashMap<SmolStr, u32>,         // name -> arity
    consts: HashMap<SmolStr, Type>,             // name -> principal type
}
```

Pure stays stateless; the `Signature` is threaded through `Kernel`
operations in a separate `covalence-kernel` crate (option F below).

**Pros:** small, conservative, easy to retrofit.
**Cons:** introduces a stateful object the user must thread through
operations. Signature management becomes a UX concern. Doesn't solve
the "fresh tycon identity" problem `new_type_definition` needs.

---

### D. **OPTIONAL** — Drop `Hint` from the kernel

Discussed in this session but punted. Options:

- **Drop `Hint` from `Def` only.** `Def` names are kernel-allocated
  tags, not user-written source-level information. The shell can
  print them as `Def#<ptr-hex>` or maintain a side table. Smaller
  scope than dropping hints from `Abs`/`All`.
- **Drop `Hint` from `Abs`/`All`/`Def` entirely.** Pretty-printing
  synthesizes fresh names from de Bruijn depth (e.g. `_0`, `_1`).
  Most theoretically pure; loses user-friendly display of binders
  the user *did* name.

Recommendation noted but not implemented: drop `Hint` from `Def`
only; keep it on `Abs`/`All` because user-written binder names are
real source-level UX information.

---

### E. **DONE** — WASM theorem-proving tests

Two complementary test layers landed:

**Host-side direct tests** — `crates/covalence-wasm/tests/pure_integration.rs`.
Sixteen tests calling the bindgen-generated `Host*` trait methods
directly on `PureHost`. Exercises every rule (`refl`, `trans`, `sym`,
`cong_app`, `beta_conv`, `assume`/`imp_intro`, `all_intro`/`all_elim`,
`inst_tfree`) plus error-path mapping. Fast, no guest compilation.

**Real guest .wasm tests** — `crates/covalence-pure-test-guest/`
(wasm32 cdylib using `wit_bindgen::generate!`) + the host test
`crates/covalence-wasm/tests/pure_guest_integration.rs`. The guest
imports `cov:pure/api` and exposes one name-dispatched export
`run-prover(name) -> result<string, string>`. The host test:

1. Invokes `cargo build --target wasm32-unknown-unknown` for the
   guest (cached in a `OnceLock` for the test process).
2. Wraps the core module via `wit_component::ComponentEncoder`.
3. Wires a `wasmtime::component::Linker` over a `PureHost` store
   using `cov::pure::api::add_to_linker::<_, HasSelf<PureHost>>(...)`.
4. Instantiates via `PureGuest::instantiate(...)`.
5. Calls `bindings.call_run_prover(&mut store, name)` and verifies
   the returned rendered theorem.

Seven guest provers tested: `refl-blob`, `trans-refl-refl`,
`imp-intro-p-implies-p`, `beta-identity`, `all-intro-elim`,
`inst-tfree`, plus an error-path case for an unknown prover name.

The scaffold is **fully reusable** for `cov:kernel/api`,
`cov:hol-light/api`, etc.: clone the guest crate, change the WIT
world the `generate!` macro points at, write new prover bodies, point
the host test at the matching bindings. The `cargo build` +
`wit_component::ComponentEncoder` + `add_to_linker` + `Guest::instantiate`
pattern carries over unchanged.

---

### F. **OPTIONAL** — `covalence-kernel` crate

Sits between `covalence-pure` and any HOL-style layer. Per the
stacked-pure-hol-mvp plan, this is where signature management and
local-authority observations would live:

- `Signature` (from option C above, if we go that way)
- `Authority` + `observe` (local-only trust hook, planned in
  `02-framework.md`)
- `new_type_definition` (option A) — could live here or in Pure
  itself; this crate is where the signature interactions land

Optional dependency on `covalence-pure-shell` for sexp/hash.

---

### G. **OPTIONAL** — `covalence-hol` crate

Classical HOL Light on top of `covalence-kernel`. From the stacked
plan:

- Define `bool` properly (currently a convenience `Type::bool()` in
  Pure with no kernel-enforced arity).
- Define HOL connectives (`∧`, `∨`, `¬`, `⟹`, `↔`, `∀`, `∃`, `ε`) via
  `Thm::define`.
- Derive the 10 HOL Light rules (`REFL`, `TRANS`, `MK_COMB`, `ABS`,
  `BETA`, `ASSUME`, `EQ_MP`, `DEDUCT_ANTISYM_RULE`, `INST`, `INST_TYPE`)
  from Pure's existing rule set.
- Add the three HOL axioms (`ETA_AX`, `SELECT_AX`, `INFINITY_AX`) via
  `Thm::assume` at the HOL crate's boundary — they appear in the hyps
  of any HOL theorem that depends on them.
- Subset types via the disjunct trick (lives here, not in the kernel).
- Bootstrap from a content-addressed standard library blob set, per
  the original `stacked-pure-hol-mvp` plan.

---

### H. **REJECTED** — Observation primitives beyond `obs_eq`

This entry previously proposed `Thm::obs_compute<O>(expr) -> Thm<⊢ expr ≡ rhs>`
and `Thm::obs_assert<O>(args) -> Thm<⊢ (Obs O) args>` as possible
extensions. **Both are rejected.** The pattern in section **I** below
subsumes everything they would have done, using only the existing
`obs_eq` rule plus careful grouping of related observations under one
Rust type.

Keep the kernel observation surface minimal: `Term::obs` for leaf
construction, `Thm::obs_eq<O: ObsEq>` for the only computational rule.
Anything fancier is policy and lives in user crates.

---

### I. **RECOMMENDED — IMMEDIATE NEXT WORK** — Store observations via "System-with-modes"

This is the design that replaces `covalence-kernel`'s old HOL with
`covalence-pure` + `covalence-hol` + a content-addressing observation
layer. Confirmed approach as of this round:

#### The pattern

Group conceptually-related observations into **ONE Rust observer
type** (a "system"). All instances of that type share one ε-family,
so `obs_eq` between any two of them is sound by the existing
parametric-ε argument. Each named observation is a value-level
*instance*, distinguished by internal data:

```rust
pub struct Blake3System { mode: Blake3Mode }
pub enum Blake3Mode { Direct, Keyed, Context, UntrustedIdentity }

// blake3                 := Term::obs(Blake3System { mode: Direct }, blob→blob)
// keyedBlake3            := Term::obs(Blake3System { mode: Keyed },  blob→blob→blob)
// contextBlake3          := Term::obs(Blake3System { mode: Context},blob→blob→blob)
// untrustedBlakeIdentity := Term::obs(Blake3System { mode: UntrustedIdentity },
//                                     blob→blob)
```

The `impl ObsEq for Blake3System` is where computational policy
lives. Given `obs_eq(Direct LIT, UntrustedIdentity (blob H))`, the
impl computes BLAKE3(LIT), checks equal to H, returns true. The
kernel produces `⊢ blake3 LIT ≡ untrustedBlakeIdentity (blob H)` —
structurally an equation between two observer applications, no
materialised hash content yet.

#### Computational extraction is opt-in

To extract the literal hash bytes into a proof, user asserts ONE
axiom per family:

```
⋀a:blob. untrustedBlakeIdentity a ≡ a
```

This axiom comes from `Thm::assume`, so it threads through
hypotheses on any theorem that uses it. Combined with the obs_eq
output via `trans`: `⊢ blake3 LIT ≡ blob H` with the
`untrustedBlakeIdentity` axiom as a hypothesis. The audit story is
"grep for `untrusted_identity_axiom` to find every place a proof
depends on materialised hashes."

#### The opaque-hash mode is a feature

If `untrustedBlakeIdentity` is not in scope, hashes stay *opaque*.
You can still:

- Prove `blake3 b₁ = blake3 b₂ → b₁ = b₂` (under the `inStore` premise
  pair).
- Substitute, chain equalities, do all the structural reasoning about
  hash identities.
- ...without ever exposing the 32 concrete bytes anywhere in the
  proof artifact.

Useful for proofs about secrets you don't want leaking into the
conclusion, smaller proof terms, and cleaner abstraction barriers
when you don't care what the hash *is*, only that two computations
agree on it. Package the `Untrusted*` mode + axiom factory in a
separate submodule so opting in is explicit.

#### `inStore` follows the same pattern

```rust
pub struct StoreSystem { mode: StoreMode }
pub enum StoreMode { InStore, UntrustedTruth }

// inStore         := Term::obs(StoreSystem { mode: InStore },        blob→bool)
// untrustedTruth  := Term::obs(StoreSystem { mode: UntrustedTruth }, bool)
```

The store mints `obs_eq(inStore <lit>, untrustedTruth)` only when it
has actually indexed the blob. User axiom `untrustedTruth ≡ T` (HOL
true) chains to give `⊢ inStore <lit> ≡ T`; standard HOL bool
reasoning lifts that to `⊢ inStore <lit>` wherever needed.

#### Meaning axioms (all user-asserted via `Thm::assume`)

```
blake3-inj-on-store:
  ⋀ b₁ b₂ : blob.
    inStore b₁ ⟹ inStore b₂ ⟹ blake3 b₁ = blake3 b₂ ⟹ b₁ = b₂

keyed-inj-on-store:
  ⋀ k₁ k₂ b₁ b₂ : blob.
    inStore b₁ ⟹ inStore b₂ ⟹ length k₁ = 32 ⟹ length k₂ = 32 ⟹
    keyedBlake3 k₁ b₁ = keyedBlake3 k₂ b₂ ⟹ k₁ = k₂ ∧ b₁ = b₂

mode-disjoint-blake3-keyed:
  ⋀ b₁ k₂ b₂.
    inStore b₁ ⟹ inStore b₂ ⟹ length k₂ = 32 ⟹
    blake3 b₁ ≠ keyedBlake3 k₂ b₂
```

(Analogous keyed-context, blake3-context disjointness. Six axioms
total for the three modes.)

Restricted to `inStore` blobs because cryptographic collision-freedom
is a model-level assumption we can't prove; we trust the store
because it's actually checked. Restricted by length on key/context
because BLAKE3's mode separation only holds when those constraints
are met.

#### Suggested crate layout

- **`covalence-store-obs`** (new) — `Blake3System` and `StoreSystem`
  Rust types, the meaning-axiom factories, the `BlobStore` integration
  that mints `obs_eq` results when it has the blob indexed. Imports
  `covalence-pure` and `covalence-store`. Does NOT import
  `covalence-hol` — pure abstract-hash reasoning works without HOL.
- **Untrusted-axiom factories** live in a separate submodule
  (`covalence-store-obs::untrusted::*`) so opting in is explicit.

#### Implications for `covalence-kernel`

The existing `crates/covalence-kernel/` (with its arena/egraph/uf HOL
implementation) is the displaced thing. Migration:

1. Build `covalence-hol` (option G), `covalence-store-obs` (this
   section), plus the orchestration crate alongside — call the
   orchestration thing `covalence-kernel` from the start; it just
   has no HOL in it yet.
2. Move the orchestration responsibilities into `covalence-kernel`:
   wires Pure + HOL + Store + WASM evaluator + tree-store (the FUSE
   layer). Re-exports the user-facing types.
3. Delete the old HOL kernel files (`arena.rs`, `egraph.rs`, `eprop.rs`,
   `kernel.rs`, `prop.rs`, `reduce.rs`, `term.rs`, `ty.rs`, `uf.rs`)
   from `covalence-kernel`. Keep only the orchestration shell.

The HOL Light "frontend" the user mentioned isn't a separate crate
— it's the naming/structure of `covalence-hol`'s public surface. The
10 derived HOL Light rules (`REFL`, `TRANS`, `MK_COMB`, …) are
`covalence-hol`'s primary API. The standard library
(num/list/real/etc.) and tactics can live in a `covalence-hol-stdlib`
or similar later crate — not on the critical path.

---

## How to pick up any of these

Each item above is self-contained. The current recommended path:

- **PHASE 1 (immediate):** G (`covalence-hol` with HOL Light's 10
  derived rules + 3 axioms). Self-contained; doesn't need any kernel
  changes.
- **PHASE 2 (immediate after G):** I (`covalence-store-obs` —
  `Blake3System`, `StoreSystem`, meaning axioms, store integration).
- **PHASE 3:** F as orchestration only — make the existing
  `covalence-kernel` re-export Pure + HOL + Store + WASM-eval +
  tree-store. Delete the old HOL kernel files.
- **PARALLEL/LATER:** A (`new_type_definition`) when HOL stdlib needs
  it. B (`DynTyCon`) only if subtype identity becomes a problem in
  practice. D (drop `Hint` from `Def`) as a cleanup whenever.

None of these are blocking. **Option H is no longer on the menu** —
the system-with-modes pattern in section I gets everything we wanted
from a computational rule without changing the TCB.
