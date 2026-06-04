# Prop-as-E-graph redesign — scope

**Status:** in progress. `EProp` / `EThm` live alongside the legacy
`Prop` / `Thm` indefinitely — both APIs coexist; this is *not* a
migration. The Phase P direction will be revisited in a future
rewrite, so don't plan a tear-down of the legacy types.

## Motivating sentence

> *A `Prop` is an E-graph on an `Arena`, with an optional precondition
> (another `Prop`). A `Thm` is a `Prop` known to be `true`. Inference
> rules are mutating methods on `Thm` that pattern-match in the E-graph
> and union the matched shape with `Bool(true)` (or with some other
> term).*

The current design has the same conceptual content scattered across:

- `Arena` — term/type allocator + properties.
- `TermUf` — separate union-find on the arena.
- `Context` — a chain of `Arc<Prop>` assumptions, dangling outside the
  arena.
- `Prop { context, concl }` — a triple of (Arc-shared chain, arena
  term id).
- `Thm { prop }` — opaque wrapper.

Inference rules take `(&mut Arena, &TermUf, ...)` and return new
`Thm`s built against the same arena. The arena, the UF, and the
context all carry independent lifetimes; the kernel facade
(`Kernel { arena, uf, ctx }`) bundles them by convention, not by type.

The redesign collapses these four concerns into one self-contained
object so that "a proof" is a value, not a tuple of references.

## Target shape

```rust
/// A proof environment: an E-graph plus an optional precondition.
/// Anyone can construct a Prop; the kernel makes no claim about truth.
pub struct Prop {
    /// E-graph: term/type allocator + union-find state.
    pub egraph: Egraph,
    /// Single chained precondition, or None for unconditional Props.
    /// A chain of preconditions encodes "assumption set".
    pub precondition: Option<Arc<Prop>>,
}

/// E-graph: arena + UF, unified.
pub struct Egraph {
    pub arena: Arena,
    pub uf: TermUf,
}

/// A Prop where the kernel has performed at least one UF-union
/// justified by an inference rule. Constructible only via those rule
/// methods.
pub struct Thm(Prop);
```

**The E-graph is the conclusion.** There is no separate `concl` field.
"What this Thm proves" = any pair of terms `a`, `b` in `prop.egraph`
for which `uf.canonical_local(a) == uf.canonical_local(b)`. The
user-facing query is `thm.eq(a, b)` — "given these two `TermRef`s,
does this Thm prove they're equal?"

**No canonical truth in the kernel.** Userspace allocates whatever
`Bool(true)` (or other sentinel) it wants to use as a "known true"
target and threads that `TermRef` through every rule that should
mark something as true. The kernel does not pick a canonical
`Bool(true)`; the trusted core just unions whatever the user
designates.

**One big Thm.** The idiomatic flow is to seed one `EThm` at proof
start, accumulate facts via rule calls, and query equality at the
end. Not "produce a new Thm per rule and stitch them together".

A chain of preconditions `P_n ← P_{n-1} ← ... ← P_1 ← None` encodes
the assumption set: `P_n` claims its egraph-truths hold *given* every
predecessor's egraph-truths. Each link is `Arc<Prop>`, so weakening
and re-export share structure.

Inference rules mutate the egraph in place: they pattern-match for a
shape (e.g. `Eq(t, t)` for `refl`), build any missing terms, and
`uf.union(matched, Bool(true))` — or, for purely equational rules,
`uf.union(lhs, rhs)`. A `Thm(Prop)` is the witness that the kernel
performed those unions. Untrusted code can build arbitrary Props and
mash arbitrary unions into their UFs; the trust boundary is the `Thm`
constructor.

## Mapping current concepts

| Today | After |
| --- | --- |
| `Arena` | `Egraph::arena` |
| `TermUf` | `Egraph::uf` |
| `Context` (chain of `Arc<Prop>`) | `Prop::precondition` (chained `Arc<Prop>`) |
| `Prop { context, concl }` | `Prop { egraph, precondition }` — no concl field |
| `Thm { prop }` | `Thm(Prop)` — same wrapper, no concl |
| Rule: `Thm::refl(arena, ctx, t)` | Method: `Thm::refl(&mut self, t)` — pattern-match `Eq(t, t)` in the egraph and union it with `Bool(true)` |
| Rule: `Thm::trans(arena, uf, ab, bc)` | Method that combines two parent Thms — see "cross-Prop composition" below |
| `Kernel { arena, uf, ctx }` | Goes away; or shrinks to a thin scratchpad |
| `thm.concl()` | Gone. Callers track the `TermId` they expected externally and check `uf.canonical_local(t) == uf.canonical_local(Bool(true))` themselves. |

## Inference rules as mutating methods

A rule's body now does three things:

1. **Look up / build pattern.** Walk `self.egraph.arena` for the
   shape the rule recognises; allocate any helper terms if needed.
2. **Discharge side-conditions.** Type checks, context checks,
   variable-capture checks etc. — the existing logic, just relocated.
3. **Union.** `self.egraph.uf.union(pattern_term, target_term)`. For
   most rules the target is `Bool(true)`; for purely equational rules
   the target may be another term (e.g., `trans` unions `concl` with
   the new `Eq(a, c)` term and leaves the truth-marking implicit).

Example: reflexivity becomes

```rust
impl EThm {
    /// Build `Eq(t, t)` in self.egraph and union it with the
    /// user-supplied `truth` ref. Returns the freshly-built Eq
    /// TermRef so the caller can query later.
    pub fn refl(&mut self, t: TermId, truth: TermRef)
        -> Result<TermRef, ProofError>
    {
        let egraph = &mut self.0.egraph;
        if !egraph.arena.is_well_typed(t) {
            return Err(ProofError::IllTypedInput);
        }
        let eq = egraph.arena.alloc_term(TermDef::Eq(
            TermRef::local(t), TermRef::local(t)));
        let eq_ref = TermRef::local(eq);
        egraph.uf.union(eq_ref, truth)
            .expect("user truth ref is local");
        Ok(eq_ref)
    }
}
```

The pattern is identical for every rule: build / recognise a shape,
discharge side-conditions, union (against `truth` or against another
term). The caller passes `truth` through every rule and queries the
result with `thm.eq(eq_ref, truth)`.

## Cross-Prop composition

`trans`, `eq_mp`, `mp`, `deduct_antisym_rule` combine two source Thms.
Today both source Thms must share the same `Arc<Context>` and live in
the same arena (the caller's). After the redesign, the two source
Thms each own their own `Egraph`.

**Approach.** Use Phase E's `add_import` machinery: pick one Thm as
host, import the other's frozen Egraph into the host's arena, and
materialise the foreign concl as a local term in the host. Then apply
the rule normally: union the matched shape, build the new concl, wrap
in `Thm`.

UF state from the imported Prop is *not* automatically replayed. If
the imported Prop's UF held a non-trivial equivalence we want to
preserve, the import edge's substitution machinery already handles
this — the imported terms are materialised in their post-substitution
form. Equalities established in the foreign UF carry over only if
the host re-derives them via its own rules.

For now treat UF state as proof-local. A future "UF lift" operation
can copy equalities across the import edge if it becomes a bottleneck.

## Lifecycle and sharing

- `Prop` is owned (not `Arc`).
- Its **precondition** chain uses `Arc<Prop>` so siblings share an
  upstream Prop without cloning the whole proof.
- Mutating a rule produces a new `Prop` (and new `Thm(Prop)`) —
  inputs are consumed. This keeps the equality state safely
  monotonic.
- Cloning a Thm clones the whole Prop (Arena + UF + precondition Arc).
  Tests will exercise that the precondition Arc-shares.

## Migration roadmap

The new shape lives alongside the legacy `Prop` / `Thm` indefinitely.
There is no plan to remove the legacy types in Phase P — both APIs
coexist; cleanup happens in a future rewrite.

**P1 (done).** Introduce `Egraph { arena, uf }` as a thin wrapper.
The `Kernel` facade holds one Egraph; rule signatures unchanged.

**P2 (done).** Add `precondition: Option<Arc<Prop>>` to legacy Prop
so the chain shape is in place. Constructors default it to `None`.

**P3 (in progress).** Introduce `EProp` / `EThm` as new types
(`crates/covalence-kernel/src/eprop.rs`). Implement each inference
rule as a method on `EThm` that takes a `truth: TermRef` and
performs a UF-union. Legacy `Thm` rules stay; the new ones are
additive. Rules to port in this style: `refl` (done), `assume`,
`add_assumption`, `not_from_false`, `sym`, `trans`, `eq_mp`, `mp`,
`cong`, `beta`, `abs` (lambda binder), `inst`, `deduct_antisym_rule`,
`reduce`, `subset_axioms`.

**P4 (later).** Cross-Prop composition: when a rule combines two
EThms (e.g., trans), reuse Phase E's import substitution to bring
the second Thm's egraph into the first one as a foreign sub-arena.
Likely surfaces gaps in the substitution path (e.g., UF lift across
imports).

Older drafts of this doc included a "P5 cleanup" phase that would
have renamed `EProp` → `Prop`. That is **not** the current plan; the
two type families coexist.

## Open design questions

1. **Should `Egraph::uf` be an `RwLock<TermUf>` for parallel reads?**
   The current design is single-threaded. For Phase H (content
   addressing), we'll want canonical hash computations that don't
   mutate — but those want `&Arena`, not `&Egraph`. Defer.

2. **Hashing.**
   Phase H wants per-arena content hashes. The egraph's UF state is
   derivation-order-sensitive, so hashing must cover only the
   structural arena. Treat this as a Phase H constraint, not Phase P.

3. **How are preconditions deduplicated?**
   Today `deduct_antisym_rule` deduplicates assumptions by canonical
   equality at UF level 0. In the new model, the precondition chain
   does **not** auto-dedupe — Arc-sharing handles object identity, but
   two semantically-equal Props built independently are distinct
   chain entries. Either:
   - Push dedup to rule level (current behaviour), or
   - Surface a `Prop::canonicalise(&Egraph) -> Prop` that rewrites the
     chain in some host Egraph. Defer until a rule needs it.

4. **Does the precondition itself carry an E-graph?** A precondition
   is a `Prop`, which carries its own Egraph. That's redundant if the
   chain lives entirely inside one host arena. Two options:
   - **Self-contained chain:** each Prop owns its arena. Cross-arena
     reasoning goes through imports.
   - **Host-bound chain:** each Prop's `precondition` is a `TermId`
     in the same arena, not an `Arc<Prop>`. The chain is a linked list
     of terms in one host arena.
   The self-contained variant matches the user's wording most
   literally. The host-bound variant is cheaper and aligns with how
   `Context` works today. **Recommend self-contained** so a Prop is
   genuinely a value; revisit if memory pressure shows up.

5. **How does the caller know "what they proved"?**
   With no `concl` field, the Thm just carries the egraph. A caller
   that wanted to prove `P` builds `P` in the egraph, runs rules
   threading their chosen `truth: TermRef` through, and afterwards
   queries `thm.eq(p_ref, truth)`. The `TermRef`s are the caller's
   responsibility to remember; the Thm doesn't track them. This is
   the egraph idiom — the proof state is what's in the UF, not a
   named target.

## Audit-surface impact

After this redesign:

- **IN the TCB** stays roughly the same — the Thm constructors are the
  trusted units, and their bodies do exactly what the current rules do
  (allocate, check, union).
- **NEW IN the TCB:** the `Egraph` type and the Prop / Thm wrappers,
  but their visible surface is smaller than today's
  Arena+TermUf+Context bundle.
- **OUT of the TCB:** the kernel facade (`Kernel`) shrinks or
  disappears — bundling is implicit in `Prop`.

## Not in scope for this redesign

- Per-arena content hashing (Phase H).
- Polymorphic subset types' tyvar ordering (Phase G3).
- Small-integer `VarId`/`TyVarId` (Phase F).
- Hash-only / lazy imports surfacing `None` from `deref_term`.
- Any change to the term / type language itself.

Once this redesign lands, those subsequent phases can be built on the
new `Prop`/`Egraph` shape without further structural churn.
