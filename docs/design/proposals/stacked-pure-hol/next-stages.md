# Core: Optional Next Stages

> **STATUS: HISTORICAL.** Canonical reference is
> [`docs/kernel-design.md`](../../../kernel-design.md).
>
> Companion to [`README.md`](./README.md). Records design ideas
> deferred from the initial `covalence-pure` / `covalence-pure-shell`
> merge. As of the `kernel-design` branch, most have landed:
> Option A (`new_type_definition`), Option B (`TyConObs` + unified
> `Observer`), Option G (HOL collapsed into the kernel; Pure meta-
> layer subsequently deleted entirely), single-axiom kernel reduction
> (only `nat_induction` remains), `int := signed2 nat` and
> `bytes := list u8` as derived TypeSpecs.

This document captures the design conversations from the
core MVP work that we deliberately *did not* land in the
initial merge candidate, so they're available to refer back to without
cluttering the kernel.

---

## Status of the merge candidate

`covalence-core` (formerly `covalence-pure`) after this round includes:

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

`covalence-hol` (absorbed `covalence-pure-shell`) includes:

- Handler-driven `term_to_sexp` / `term_from_sexp` (caller supplies
  `ObsSerializer` / `ObsParser` trait impls).
- Handler-driven content hashing (`hash_term` with `ObsHasher`).
- `UnitObs` / `UnitObsHasher` defaults for the trivial `()` observer.
- `HolLightCtx` / `PureHol` / the 10 derived HOL Light rules over
  the core's bona-fide reflection axioms.
- `nat_axioms` / `int_axioms` — postulated stdlib axioms via
  `Thm::assume` (kept with self-hyp audit trail; bona-fide kernel
  axioms only for the four reflection / induction primitives).

`covalence-python`: pyo3 wrappers for `Type`, `Term`, `Thm` with the
full rule API.

`covalence-wasm/wit/pure.wit`: `cov:pure@0.1.0` WIT package defining
the guest-facing kernel API, with `ctx` as an *opaque* resource
so the host's hyp-set representation can change without breaking
guests. (Name may rename to `cov:core` in a future round.)

**Tests:** ~118 across `observer`, `soundness`, `rules`, `hash`,
`sexp_roundtrip`, `define`, and `test_pure` (Python).

---

## Optional next stages

### A. **DONE** — `Thm::new_type_definition` (HOL Light parity)

Landed in `covalence-core::thm`. Given a witness theorem
`Γ ⊢ P x`, introduces a fresh type constant `τ` and two fresh
constants `abs : α → τ`, `rep : τ → α`, returning a `TypeDef`
bundle with three theorems (split Pure-style rather than HOL Light's
two, because Pure has no `↔`):

```
⊢ ⋀a:τ. abs (rep a) ≡ a
⊢ ⋀r:α. P r ⟹ rep (abs r) ≡ r
⊢ ⋀r:α. rep (abs r) ≡ r ⟹ P r
```

All three carry the witness's hyps. Identity via the `TyConObs`
Arc-pointer mechanism (kernel-private `TypeDefMarker` ZSTs). The
rule handles polymorphic carriers — `tvars` are extracted from α's
free TFrees and stored in `TypeDef.tvars` for downstream
`inst_tfree` use.

**Note:** the disjunct-trick wrapper (avoiding the inhabitedness
obligation entirely) is still pending in `covalence-hol`; the kernel
rule is ready for it.

**Variant — the disjunct trick using ε (canonical formulation).** The
kernel rule above still requires a witness theorem `⊢ ∃x. P x`. To
avoid that obligation, the `covalence-hol` layer wraps it with the
**disjunct trick** keyed on HOL's `ε`:

> Instead of forming the subset type from `P` directly, form it from
> the *modified predicate*
>
> `Q := λx. P x ∨ x = ε P`
>
> and apply `new_type_definition` to `Q`. The witness is `ε P`
> itself: `Q (ε P)` reduces to `P (ε P) ∨ ε P = ε P`, and the right
> disjunct holds by reflexivity, so `∃x. Q x` is unconditionally
> provable.

What the disjunct tells you is *exactly* what would be obstructed in
classical HOL: either `P x` holds, or P is uninhabited and you can
only land on the canonical witness `ε P`:

- **If `∃y. P y`** (P inhabited): then `ε P` satisfies `P` (by ε's
  defining property), so `x = ε P → P x`. Therefore `Q x ↔ P x`, and
  τ is exactly the classical `P`-subtype.
- **If `¬∃y. P y`** (P uninhabited): then `Q x ↔ x = ε P`, so τ is a
  singleton containing only the canonical ε-witness. The type is
  well-formed but only useful as a degenerate carrier — anything you
  prove about τ either tells you `x = ε P` or implicitly requires
  `∃y. P y` to instantiate quantifiers, which contradicts the empty
  branch.

This formulation is preferred over the older `P x ∨ ¬∃y. P y` (used
in the sibling [modified-hol notes](../layered-framework/notes/modified-hol.md))
because:

- The canonical witness is tied to `P` rather than a global default,
  so the type is more localised.
- When P is uninhabited, τ is a singleton `{ε P}` rather than the
  entire carrier α — a much better-behaved degenerate case.
- The proof obligation `∃x. Q x` is discharged by reflexivity, no
  case-split required.

**Where it lives.** The disjunct-trick wrapper is a
`covalence-hol`-layer construct, not a kernel one. The kernel rule
`Thm::new_type_definition` still consumes a witness theorem; HOL's
wrapper synthesizes the witness from `ε P` via reflexivity, applies
the kernel rule to `Q`, and exposes the resulting `abs`/`rep` to
users. The kernel doesn't need to know about `ε`.

---

### B. **DONE** — Unified `Observation` trait, `TyConObs` variant

Landed. `TypeKind::TyConObs(Object, BinderHint, Vec<Type>)` lives
alongside the structural `Tycon(SmolStr, Vec<Type>)`; both forms
coexist, picked by use-case. The `Observer` trait is auto-impl'd
for any `Any + Send + Sync + Debug`, so the same Rust type can
appear both as a term-level `Obs` head and a type-level `TyConObs`
head when the surrounding theory wants that. The historical context
below describes the design rationale.

#### `TypeKind` extension

Add a single new variant; keep everything else:

```rust
pub enum TypeKind {
    TFree(SmolStr),
    Prop,
    Bytes,
    Fun(Type, Type),
    /// Structural type constructor — compared by name + args.
    /// Cross-process stable. Best for "named uninterpreted" cases
    /// (HOL `bool`, `num`, `list`, …).
    Tycon(SmolStr, Vec<Type>),
    /// Identity-based type constructor — compared by Arc pointer.
    /// Process-local. Best for fresh kernel-introduced subtypes
    /// (`new_type_definition`, theory-local opaque types).
    TyConObs(DynObs, Vec<Type>),
}
```

`DynObs` is **the same wrapper already used by `TermKind::Obs`** —
identical Arc-identity discipline, identical downcast story, identical
ε-family. A single `impl Observer for HOLTheory` value can appear
both as a term head (`Term::obs(theory, ty)` → HOL constants) and as
a type head (`Type::tycon_obs(theory, args)` → HOL type constants).
The Rust type is the unifying identity.

This is symmetric to the term side, not redundant with it:

| role               | named uninterpreted          | fresh identity-based             |
|--------------------|-------------------------------|----------------------------------|
| term constant      | `Const(SmolStr, Type)`        | `Obs(DynObs, Type)`              |
| type constructor   | `Tycon(SmolStr, Vec<Type>)`   | `TyConObs(DynObs, Vec<Type>)`    |

Each form is best at different things. Don't drop `Tycon` — it's
cross-process-stable and what most code wants. Don't drop `Const` for
the same reason.

#### Default display: opt-in `ObsDisplay`

The base `Observer` trait stays auto-impl'd (`Any + Send + Sync +
Debug`). For pretty-printing in both term and type positions, opt in:

```rust
pub trait ObsDisplay: Observer {
    fn display_term(
        &self, args: &[Term], f: &mut fmt::Formatter<'_>
    ) -> fmt::Result;
    fn display_tycon(
        &self, args: &[Type], f: &mut fmt::Formatter<'_>
    ) -> fmt::Result;
    // Default impl falls back to Debug formatting.
}
```

A single trait covers both roles. The kernel-level renderer always
produces *something* via the Debug fallback, even for observers that
don't bother. `NamedFamily(SmolStr)` (see below) overrides to render
the name.

#### `Hint` rides along

`TyConObs(DynObs, Hint, Vec<Type>)` — `Hint` is α-transparent (same
trick as on `Def`/`Abs`/`All`), so it doesn't affect equality but
gives the pretty-printer something to render before falling back to
`ObsDisplay::display_tycon` or to Debug. Cheap convenience.

#### Recovering the old SmolStr-keyed story

If you want a TyCon family where multiple instances with the same
name compare *equal* (rather than each call producing a fresh Arc),
write a thin user-level registry that canonicalises a `NamedFamily`
observer by name:

```rust
pub struct NamedFamily(SmolStr);
// Registry hands out a single Arc<NamedFamily> per unique name.
```

But this is opt-in policy, not a kernel concern. Most code should use
structural `Tycon(SmolStr, …)` for cross-process-stable named tycons
and `TyConObs` for theory-introduced fresh tycons.

#### Type-level equality: start with **none**

Resist the temptation to add `Thm::tycon_eq<O>` analogous to
`Thm::obs_eq<O>`. Types are compared structurally (`Tycon`) or by Arc
identity (`TyConObs`) and that's it. Reasons:

- Soundness story stays trivial — no per-theory ε-model to extend to
  types.
- The Isabelle/HOL precedent (no type-equality assertions; internal
  equality is the term-level `=` constant) is well-tested.
- Things that look like type equality (record extensibility,
  type-class instances, refinement subtyping) are better modelled as
  definitional unfolding + term-level lemmas.

**If a real use case appears later**, add the kernel rule with the
weak guarantee: "a theory can assert equalities (not disequalities)
about its own types." Sound by the "interpret all types in family
`O` as Unit" model — any equality of types is consistent with that
collapse. Disequalities would require a richer model and are deferred
indefinitely; the user explicitly flagged that disequalities feel
like an inner-theory rather than outer-theory problem.

#### Pros (now)

- Same Arc-identity discipline as `Def` and `DynObs` — three places
  in the kernel where Arc identity gives us freshness for free.
- `new_type_definition` (option A) becomes mechanical: allocate a
  fresh `Arc<dyn Observer>` for the new type constant, wrap in
  `TyConObs`, return.
- Per-Rust-type theory extensions (a `HOLTheory` struct can carry
  its own metadata, debug info, etc.).
- ε-family per Rust type covers both terms *and* types from the same
  theory uniformly.

#### Cons

- `TyConObs` serialization is process-local (same as `Obs`). Cross-
  process workflows lean on the structural `Tycon` form. The duality
  makes this explicit and choosable.
- Users defining their own type families need to write a Rust type
  per family. This is fine — it's the same discipline as observers.
- Two type constructors with the same display name and same args —
  one structural, one identity-based — compare *unequal*. Matches
  the term-side `Const`/`Obs` situation; same audit guidance applies.

#### TCB cost

~30 LoC: one variant on `TypeKind`, the corresponding cases in
`type_of_in` (just propagate arity-check), the `Display`/`Hash`/`Eq`
plumbing. The `ObsDisplay` trait lives in `covalence-hol` (non-TCB).

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

**Real guest .wasm tests** — `crates/covalence-core-test-guest/`
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

### F. **DEFERRED** — `covalence-kernel` orchestration crate

The existing `crates/covalence-kernel/` (arena + egraph + UF HOL)
is still in the workspace as the legacy implementation. The plan
remains to delete its old HOL implementation and reshape it as
a thin orchestration crate wiring `covalence-core` + `covalence-hol`
+ `covalence-store` + WASM evaluator + tree-store. No active work
yet; tracked here so it doesn't get lost.

---

### G. **PARTIALLY DONE** — `covalence-hol` crate

Classical HOL Light builder. Status:

- **DONE.** `Type::bool()` and the HOL connectives (`=`, `==>`, `~`,
  `/\`, `\/`, `<=>`, `!`, `?`, `@`, `Trueprop`) are kernel-native via
  `TermKind::Bool` and `TermKind::HolOp` — *not* `Thm::define`'d.
- **DONE.** The 10 HOL Light rules derived in `pure_hol.rs` from the
  core's bona-fide reflection axioms (`eq_reflection`,
  `forall_reflection`, `imp_reflection`) plus the regular LF rules.
- **PENDING.** The three HOL axioms (`ETA_AX`, `SELECT_AX`,
  `INFINITY_AX`) via `Thm::assume` at the HOL crate's boundary — most
  HOL Light proofs need these.
- **PENDING.** Subset types via the disjunct trick (kernel rule
  `new_type_definition` is ready; the disjunct-trick wrapper isn't).
- **PENDING.** `define_type` derived rule — the construction that
  takes a recursive type spec like `nat = Zero | Suc nat` and
  returns the type + constructors + injectivity + induction +
  recursor. **This is the gate to the internal-logic ladder
  (PA, commutative semiring, HS, internal HOL).**
- **PENDING.** Stdlib bootstrap from a content-addressed blob set
  per the original plan.

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
`covalence-core` + `covalence-hol` + a content-addressing observation
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
  `covalence-core` and `covalence-store`. May import `covalence-hol`
  for the canonical hashing / sexp helpers (now consolidated there).
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

Each item above is self-contained. Current state (as of the
`kernel-design` branch):

- **DONE:** A (`new_type_definition`), B (`TyConObs` + unified
  `Observer`), E (WASM theorem-proving tests). The kernel-fold of
  HOL went farther than original Option G envisioned — HOL primitives
  are kernel-native via `TermKind::Bool`/`HolOp` and the four bona-fide
  axioms now live in `Thm::*`.

- **PARTIALLY DONE:** G — the 10 HOL Light rules + builder API are in
  `covalence-hol`; the three HOL axioms (`ETA_AX`, `SELECT_AX`,
  `INFINITY_AX`), the disjunct-trick wrapper, and the stdlib bootstrap
  are still pending.

- **HIGHEST-VALUE PENDING:** `define_type` derived rule in
  `covalence-hol` (the inductive-type construction). Gates the
  internal-logic ladder (PA → commutative semiring → HS → internal
  HOL). Polymorphic typedef plumbing in `pure_hol.rs` is the
  prerequisite.

- **PENDING but not blocking:** I (`covalence-store-obs`), F
  (orchestration), the HOL axiom postulates, stdlib loader.

- **PARALLEL/LATER:** D (drop `Hint` from `Def`) — cleanup whenever.

**Option H stays off the menu** — the system-with-modes pattern in
section I gets everything we wanted from a computational rule
without changing the TCB. **The next concrete move** is the
`define_type` work in `covalence-hol`, plus the small wrapper-level
fixes (polymorphic-typedef rejection, disjunct trick) that unblock it.
