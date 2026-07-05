# `defs/` re-home: the dual-representation bridge (toHOL purge S9/S10/S11)

**Status:** AI design doc (2026-07). Companion to
[`pure-hol-and-build-plan.md`](./pure-hol-and-build-plan.md) (Track 2) and
[`closed-world-kernel.md`](./closed-world-kernel.md). Records the decisions made
building **S9a — the reversible dual-representation bridge** — and the plan for
the maintainer-gated flip (S10/S11).

## The problem

The `defs/` catalogue (nat/int/logic/list/set/… constants) is encoded as
`TermKind::Spec(TermSpec, args)` leaves that δ-unfold via the kernel rule
`Thm::unfold_term_spec`, and `TypeKind::Spec(TypeSpec, args)` derived types with
their own abs/rep coercion laws. The toHOL-purge endgame is *textbook HOL Light*:
no `TermKind::Spec`, no `unfold_term_spec` — every catalogue constant an ordinary
`define`-produced defined constant, every derived type a `new_type_definition`
subtype. The 267 `defs::` call sites and the whole `init/` proof corpus must
survive that swap with **zero churn**.

## The bridge (S9a, built)

For each **monomorphic let-style** `TermSpec`, `crate::init::twins` lazily builds
a `Twin` (keyed by the spec's `Arc` pointer identity, cached process-globally):

- `const_tm` — a fresh `Def` twin, `Thm::define(dotted_name, body)`.
- `def_thm` — the stored `⊢ const = body` (the **permanent** artifact).
- `spec_eq` — `⊢ Spec(spec, []) = body`, minted once via `unfold_term_spec`
  (the **transitional** artifact `delta` uses today; dies at the flip).

Reversibility is asserted at build time: `⊢ spec = const` is derivable
(`spec_eq.trans(def_thm.sym())`), so the two representations are definitionally
interchangeable. Every δ-unfold consumer (`TermExt::delta`, `delta_all`,
`proofs::rewrite::unfold_at_1`, the `rel` head-unfold, the `delta` /
`unfold-term-spec` script rules) now calls `twins::unfold_spec(t)`, which returns
the cached `spec_eq` for a twinned spec and **falls back** to `unfold_term_spec`
for anything not yet covered — so nothing breaks. The single kernel-rule call
site is consolidated inside `twins` (build + fallback).

## Decisions

### (a) The twin keeps the *same* dotted name — no collision

`Thm::define`'s `name` is **display-only**; identity is a fresh `Def` token, not
the name. So the twin `const_tm` carries the spec's dotted name (`nat.add`, `∧`)
for readable printing while being a distinct kernel symbol from the `Spec` leaf.
At the flip, the accessor `defs::nat_add()` returns the twin `const_tm` *instead
of* the `Spec` leaf; the 267 `defs::` call sites resolve through the accessor
and never mention the representation, so they are unaffected. Two named constants
sharing a body are independent (no `⊢ body₁ = body₂` leak) — exactly the
conservative-extension guarantee `define` already documents.

### (b) Only let-style specs get body-theorems; the def-style plan

`define` needs a *body* (the denotation). Let-style specs (`let_term!` /
`poly_let_term!`, `tm` = the body, `type_of(tm) == declared_ty`) have one.
**Def-style** specs (`spec_term!` / `poly_spec_term!`, `tm` = a `carrier → bool`
ε-selector predicate) do not — they are named Hilbert choices. Their re-home
route (deferred, S10-family) is the `new_specification` shape: define the twin as
`const := ε pred` (`Thm::define(name, Term::select(pred))` gives `⊢ const = ε
pred`) and recover the characterizing property from `Thm::spec_ax`/`select_ax` —
the same `(p w) ⟹ p(const)` fact the def-spec commits to today. Declaration-only
specs (`term_decl!`, opaque atoms) become plain `new_constant`-style opaque
`Def`s with no equation.

### (c) The stored theorem is sound by construction

`Thm::define(name, body)` mints `⊢ const = body` for a **fresh** `Def` — a
conservative extension, no trust in the catalogue. `unfold_term_spec` gives
`⊢ spec = body` by the let-style denotation the spec commits to. The bridge
`⊢ spec = const` is then pure `trans`/`sym`. Nothing here widens the TCB.

### (d) Polymorphic specs: deferred

A poly spec (`forall`, `exists`, `list.map`, …) unfolds *at type arguments*; its
`spec_eq` would need instantiating the cached base equation via `inst_tfree` in
the tvar order. S9a twins only the monomorphic (empty-args) case and falls back
for the rest. Instantiating the cached equation for the poly case is the next
increment (recorded in `init/SKELETONS.md`); it is a pure-derivation change, no
new kernel surface.

### (e) `TypeSpec` re-home: `new_type_definition` (prototyped: `unit`)

Derived types re-home through the conservative-extension rule
`Thm::new_type_definition(hint, abs_hint, rep_hint, witness)`, which mints a fresh
τ with `abs`/`rep` and the three bijection theorems (all freshness allocated
inside the rule). `twins::unit_typedef()` prototypes this for
`unit = { b : bool | b = T }`, witnessed by `⊢ (λb. b = T) T`. This replaces the
witness-free `TypeSpec` abs/rep laws (which are weaker on the "back" direction
because they take no non-emptiness witness) with the full bijection. Quotient
types (`int := (nat × nat)/~`) re-home the same way once a quotient-typedef
helper lands; that decision is deferred to the quotient re-home increment.

## The flip (S10/S11, maintainer-gated)

1. Point each `defs/` accessor at its twin `const_tm` (twin registry becomes the
   catalogue's backing store).
2. `twins::unfold_spec` returns `def_thm` (now that the op *is* the const);
   `spec_eq` and its `unfold_term_spec` call are deleted. Consumers unchanged.
3. Delete `TermKind::Spec` / `TypeKind::Spec` / `unfold_term_spec` /
   `Term::spec_abs` / `spec_rep` and the TypeSpec abs/rep laws.

Consumers move **once** (onto `twins::unfold_spec`, done in S9a) and never again.
