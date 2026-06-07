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

### E. **OPTIONAL** — WASM theorem-proving tests (task 17 from this round)

Implement the host-side `cov:pure` traits in `covalence-wasm` (or a
new `covalence-pure-wasm` crate). Write a guest module — possibly
authored via `covalence-wasm-build-guest` — that uses the WIT to prove
simple theorems and exposes the result via an exported function. Drive
end-to-end from a Rust integration test.

**Scope options:**

1. **Minimal:** guest proves `⊢ x ≡ x` (single `Thm.refl`); test
   verifies the returned theorem.
2. **Useful:** guest proves a short equational chain via
   `trans`/`sym`/`cong-app`; test verifies the conclusion.
3. **Ambitious:** if option A (`new_type_definition`) lands and we
   write a `covalence-hol` bootstrap, guest proves a real HOL
   theorem (e.g. `⊢ ∀p. p ⟹ p`).

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

### H. **OPTIONAL** — Observation primitives beyond `obs_eq`

The current observation surface is **just** `Term::obs` (leaf
construction) and `Thm::obs_eq` (equate two same-Rust-type
applications). Other patterns could be added if needed:

- `Thm::obs_assert<O>(expr)` for bool-returning observations that
  always emit `⊢ expr ≡ true`. Sound under the same parametric ε
  model with `ε(bool) = ⊤`. Probably unnecessary — `Thm::assume` on
  a user-written meaning axiom achieves the same effect with
  explicit hypothesis tracking.
- `Thm::obs_make<O: ObsMake>(expr)` for observers that produce a
  user-chosen RHS. Discussed in this session; concluded to be
  semantically equivalent to `Thm::assume(specific_fact)` while
  pushing the soundness obligation into observer impls. Not
  recommended; keep observations to `obs_eq` + user-assumed meaning
  axioms.

---

## How to pick up any of these

Each item above is self-contained. A reasonable next-merge pick is:

- **For HOL bootstrap progress:** A (`new_type_definition`) + F
  (`covalence-kernel`) + G (`covalence-hol`).
- **For demo / integration:** E (WASM tests) using just what's already
  in `covalence-pure`.
- **For TyCon-as-observation experimentation:** B as a separate PR
  that adds the `DynTycon` variant alongside `Tycon`. Doesn't disturb
  existing code.
- **For cleanups:** D (drop `Hint` from `Def`) as a small,
  self-contained PR.

None of these are blocking. Order them however makes sense.
