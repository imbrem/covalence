# Refactor plan — toward the ARCHITECTURE.md vision

Working list of commits to move from the current kernel toward the
design described in [`ARCHITECTURE.md`](../ARCHITECTURE.md) and codified
in [`AGENTS.md`](../AGENTS.md). Ordered for **smallest possible audit
surface at each step**: every commit either *removes* something from
the trusted core, *simplifies* something that's already trusted, or
adds one well-scoped capability with tests.

Conventions:

- Each commit lands self-contained — the kernel and all crates build,
  all tests pass.
- Where a commit can be either pure-subtraction or "add-deprecate-
  switch-remove", we prefer the latter so the working tree stays green
  the whole way.
- TCB grows only when the goal *requires* it; usually it shrinks.

---

## Phase A — shrink `TermDef` to its essentials

The vision keeps just the structural HOL shapes plus the existentials
and primops. Today's `TermDef` has several convenience variants that
can be expressed as ordinary constants + axioms.

- **A1.** Drop `Iter`, `Comp`, `Id`, `Ite`, `LiftOp1`, `LiftOp2`. Move
  them to a user-space prelude as `Const`s with axioms. Update
  type-inference, the `deps()` / `with_zeroed_deps()` tables, and any
  stale tests. Net: ~250 lines deleted from arena/term/inference.
- **A2.** Drop `Ne`. `Ne(a, b)` ≡ `Op1(LogicalNot, Eq(a, b))`. Pure
  derivation; trivial rewrite at call sites.

After A: `TermDef` carries Bound, Free, Const, Comb, Abs, Eq, Bool,
the three existentials (`Forall`, `Exists`, `Eps`), `Op1` / `Op2`,
and the literal flavours. Vanilla HOL plus our primops.

## Phase B — foreign references as `TermDef` / `TypeDef` variants

Collapses two distinct mechanisms ("local TermRef" vs "foreign side
table") into one: every reference is a `TermId` into the current
arena, and "foreign" is a structural variant just like `Comb` is.

- **B1.** Add `TermDef::Foreign(ImportId, TermId)` and
  `TypeDef::Foreign(ImportId, TypeId)` variants. Side tables still
  coexist; nothing routes through the variants yet.
- **B2.** Update `Arena::foreign_term_ref` / `foreign_type_ref` to
  allocate the variant instead of the side-table entry. Tests cover
  the new shape.
- **B3.** Update `deref_term` and all consumers to recognise the new
  variants. Drop the old foreign-flag bit on `TermRef` / `TypeRef`.
- **B4.** Remove `foreign_terms` / `foreign_types` side tables,
  `ForeignTermId` / `ForeignTypeId`, and the packed-flag plumbing.
  `TermRef` collapses to `TermId`; same for types. Probably ~400 lines
  of plumbing removed.

After B: `TermRef`/`TypeRef` are essentially aliases for the raw IDs;
the kernel speaks one language of references.

## Phase C — pull term union-find out of `Arena`

UF state is *equality state*, not arena structure. Today it's
embedded; the vision keeps it external so the arena itself stays
hash-stable.

- **C1.** Introduce a `TermUf` struct in `crates/covalence-kernel/src/uf.rs`
  holding canonical pointers. Construction: `TermUf::new(arena: Arc<Arena>)`.
  All arena fields read; only UF state writes.
- **C2.** Move `union` / `canonical_local` / `eq_at_level_0` /
  `union_if_congruent` from `Arena` onto `TermUf`. Arena keeps only
  structural traversal.
- **C3.** Update `Thm` to thread `TermUf` alongside `Arena` where
  needed. `Kernel` facade holds both.
- **C4.** Drop `uf_terms: Vec<TermUfEntry>` from Arena. Arena is now
  pure structural data + interning tables + imports.

After C: Arenas can freeze and be content-addressed without dragging
mutable equality state. Diamond imports still work — the UF keeps
its canonical-as-tuple invariant.

## Phase D — make `TypeDef` private

Same treatment as `TermDef`: stable public surface via opaque
`TypeRef` accessors; internal layout free to change.

- **D1.** Mark `TypeDef` `pub(crate)`. Add a `TypeKind` public view
  paralleling `TermKind`.
- **D2.** Move the `Bool` / `Bytes` / `Int` / `Nat` variants of
  `TypeDef` behind the `BuiltinTy` accessor surface. External code
  goes through `arena.bool_ty()` / etc.

After D: kernel can rework type representation (kinds, HOL-Omega, ...)
without changing the public surface.

## Phase E — imports carry substitutions

Today's imports are bare `Arc<Arena>` pointers. The vision attaches
a term-substitution and type-substitution to each import, with
unmapped names defaulting to `epsilon(λ_. true) : α`.

- **E1.** Add `TermSubst` and `TypeSubst` types stored in interning
  tables; allocate via `Arena::intern_term_subst` /
  `intern_type_subst`. Sealed `TermSubstId` / `TypeSubstId`.
- **E2.** Replace `Arena::add_import(source: Arc<Arena>)` with
  `add_import(source, term_subst: TermSubstId, type_subst: TypeSubstId)`.
  Empty-substitution paths keep existing tests green.
- **E3.** Apply the substitution inside `deref_term`. Foreign `Free`
  / `TVar` names mapped by the subst → their image; unmapped → the
  epsilon-of-true default of the appropriate type.
- **E4.** Require imported terms to be **locally closed** pre-
  substitution. De-Bruijn indices that survive (currently
  forbidden) default to epsilon-of-true (forward-compat hook for a
  future de-Bruijn-aware substitution).

After E: the import edge *is* the theory translation — re-exporting
a theorem from `A` through `B` to `C` is just composing substitutions.

## Phase F — variable IDs (deferred / forward-compat)

Today free / type-variable names are `StrId`s. The vision targets
small-integer `VarId` / `TyVarId` for cheaper substitutions and
"variable range" imports. Forward-compatible with E's substitution
shape — only the ID type changes.

- **F1.** Introduce `VarId` and `TyVarId` newtypes; allocator is
  per-arena monotonic.
- **F2.** Migrate `Free` and `TVar` to carry the new IDs. Keep the
  printer-facing `StrId` as a separate "display name" side table
  (not part of identity).

Deferred until after the other phases land; nothing else depends on
it.

## Phase G — subset typedef with the disjunct trick

The kernel's **only** new way to introduce a type. Replaces HOL
Light's `new_type_definition` with the unconditional version
(§3.6 of the canonical doc).

- **G1.** Add `TypeDef::Subset(TypeRef /*α*/, TermId /*P*/)` (or
  equivalent). Side conditions enforced at allocation: `P` locally
  closed, `fv(P) = ∅`, `P : α → bool`.
- **G2.** `Thm::subset_axioms(arena, subset_ty) -> (Thm, Thm)`
  produces the two axioms:
  - `abs(rep a) = a`
  - `rep(abs x) = x ⇔ P x ∨ ¬∃y. P y`
- **G3.** Tyvar-ordering: `Arena::declare_type_operator(P,
  declared_order) -> TypeRef` for polymorphic subset types. Check the
  declared list permutes `tyvars(P)`.

After G: every well-formed type is decidably well-formed without
touching the proof engine.

## Phase P — Prop-as-E-graph redesign

Reframe the kernel's core data model so a `Prop` is a self-contained
E-graph + designated conclusion + optional precondition chain, and
inference rules become mutating methods on `Thm` that pattern-match
and union. Scope and migration roadmap in
[`prop-egraph-design.md`](./prop-egraph-design.md).

Phase P is no longer a migration — `EProp` / `EThm` live alongside the
legacy `Prop` / `Thm` indefinitely. The plan committed P1 (Egraph
wrapper), P2 (precondition chain on legacy Prop), and a `refl` rule
in the new shape (`EThm::refl`) as a prototype. Further rule
conversion happens at the user's request only.

## Phase H — content-addressed type identity (done)

Implemented as a single hash over linear arena buffers — **no
canonicalisation**. The invariant is `hash → bytes` injective; the
reverse is **not** required (two arenas built with different
allocation orders that express the same logical content hash
differently). The kernel doesn't compute semantic equivalence.

- **H1.** `Arena::hash() -> O256` streams every table (`types`,
  `terms`, `term_props`, `imports` recursively, interned
  strings/bytes/ints/nats, tyargs, substitutions) through
  BLAKE3 with per-section domain-separation tags.
- **H2.** `Prop::hash(&Arena) -> O256` combines the arena hash with
  the concl TermId and the context / precondition-chain entries.
  `EProp::hash() / EThm::hash()` operate on the embedded egraph.

---

## Out of scope for kernel-1 (above-kernel work)

These follow the same pattern (simple trusted check + clever
untrusted layer), but they're not changes to the LCF core:

- Decision procedures wired up via `covalence-sat` / `covalence-smt`
  as oracle implementations.
- WASM executor wrapping `covalence-wasm` as the canonical oracle.
- Theory-DAG content store: arenas referenced by hash, hash-only
  imports surfacing `None` from `deref_term`.
- Format plane: `valid(format, data)` opaque relation, keyed-BLAKE3
  typed identity.
- Storage / VCS / prolly-tree tables.
- Filesystem mount layer (FUSE).
- Internal logics (`L_prob`, embedded intuitionistic logic, …).
- Functor base-shift.

These all sit *outside* the kernel and gain soundness by re-checkability.

---

## Audit-surface ratchet

After each commit, the entry in [`AGENTS.md`](../AGENTS.md)'s "INSIDE
the TCB" list either shrinks or stays the same. Anything that would
*grow* it is flagged in the commit message and proposed instead as a
certificate-checked OUTSIDE design (per AGENTS.md's directive).
