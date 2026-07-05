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

### (e) `TypeSpec` re-home: `new_type_definition` (prototyped end-to-end: `unit`)

Derived types re-home through the conservative-extension rule
`Thm::new_type_definition(hint, abs_hint, rep_hint, witness)`, which mints a fresh
τ with `abs`/`rep` and the three bijection theorems (all freshness allocated
inside the rule). `twins::unit_typedef()` prototypes this for
`unit = { b : bool | b = T }`, witnessed by `⊢ (λb. b = T) T`. This replaces the
witness-free `TypeSpec` abs/rep laws (which are weaker on the "back" direction
because they take no non-emptiness witness) with the *full* bijection — the
witnessed back direction is the clean `rep (abs r) = r ⟹ P r`, not the
disjunctive escape-hatch form `P r ∨ ¬∃x. P x` the `TypeSpec` laws must use.

**S9b validated the coercion story end-to-end** by re-proving, *through the
`new_type_definition` representation*, every fact the `TypeSpec`-unit ships:

- **wrapper round trip** `⊢ abs (rep a) = a` — `TypeDef::abs_rep` directly (the
  analogue of `Thm::spec_abs_rep`);
- **carrier round trip** `⊢ rep (abs T) = T` (`twins::unit_rep_abs_t`) —
  `rep_abs_fwd` at `T` with the premise `P T` discharged by the witness (the
  analogue of `Thm::spec_rep_abs_fwd` β-discharged);
- **`rep`'s image is `{T}`** `⊢ rep a = T` for free `a : τ`
  (`twins::unit_rep_is_t`) — apply `rep` to `abs (rep a) = a`, feed the result
  into the *witnessed* back direction `rep_abs_back` to get `P (rep a)`, β-reduce;
- **singleton law** `⊢ ∀x:τ. ∀y:τ. x = y` (`twins::unit_singleton`) — the fact
  the `TypeSpec`-unit gets as the *kernel rule* `Thm::unit_eq`, here **derived**:
  `x = abs (rep x) = abs (rep y) = y` since `rep x = T = rep y`. The
  non-emptiness witness is load-bearing — without it the empty-predicate escape
  in the `TypeSpec` back law blocks `P (rep a)`, so the singleton would not
  close. This is the concrete payoff of moving from witness-free `TypeSpec` laws
  to `new_type_definition`.

**Generalizing to the rest of the `defs/` `TypeSpec`s:**

- **Subtype specs** (`unit`, `char`, the `uN`/`sN` bit-width carves, `int.pos`):
  same shape as `unit` — a `carrier → bool` selector `P` plus a **non-emptiness
  witness** `⊢ P w`. The re-home is `new_type_definition(name, abs, rep, ⊢ P w)`;
  the catalogue accessor returns the fresh τ, and `Term::spec_abs`/`spec_rep`
  call sites return the fresh `abs`/`rep` constants. The one new obligation the
  `TypeSpec` form didn't carry is *producing the witness* (a canonical inhabitant
  proof) — cheap for the numeric carves (`bits.len v = N` on a concrete N-bit
  literal), and exactly the fact `unit_witness` builds for `unit`.
- **Newtype specs** (`set`, `rel`, `stream`, `bytes = list u8`, `bits`, the
  container wrappers): `P = λ_. T`, so the witness is trivial (`⊢ (λ_. T) w` for
  any carrier witness `w`) and `rep_abs_fwd` discharges unconditionally — the
  `spec_abs_rep`/`spec_rep_abs_fwd` newtype tests already exercise this shape.
- **Quotient specs** (`int := (nat × nat)/~`, `rat`): **not** a subtype — the
  `tm` is an *equivalence relation* `R`, not a `carrier → bool` predicate, and
  `new_type_definition` (a subtype rule) does not apply directly. The re-home
  needs a **quotient-typedef helper** that, from `⊢ equivalence R`, mints τ with
  `abs : carrier → τ` / `rep : τ → carrier` and the quotient laws
  `abs x = abs y ⟺ R x y` and `R (rep a) (rep a)` (the standard HOL Light
  `define_quotient_type` shape). The kernel already carries the witness-free
  quotient coercions (`spec_abs_rep` holds for quotient specs per its soundness
  note); the helper packages them behind an `equivalence`-witnessed front the
  same way `new_type_definition` packages the subtype ones. Prototyping this on
  `int` is the next `TypeSpec` increment (tracked in `init/SKELETONS.md`).

**Do the `Spec` type leaves become `Tycon`s in place?** No — like the term
twins (decision (a)), the τ from `new_type_definition` is a *distinct fresh*
`FreshTyCon`, allocated alongside the `TypeKind::Spec` leaf, not a mutation of
it. At the flip the catalogue accessor (`Type::unit()`, `defs::int()`) is
re-pointed from the `Spec` leaf to the fresh τ; the ~267 call sites resolve
through the accessor and never name the representation, so they are unaffected.
The `abs`/`rep` coercions likewise flip from `Term::spec_abs`/`spec_rep` (which
build `Spec`-keyed leaves) to the fresh `abs`/`rep` constants the typedef
returned. The bijection *laws* move from the four `spec_*` kernel rules to the
three stored `TypeDef` theorems; consumers that today call
`Thm::spec_abs_rep(...)` re-route to `TypeDef::abs_rep.all_elim(...)` — a
mechanical swap prototyped by the S9b derivations above.

## The flip (S10/S11, maintainer-gated)

1. Point each `defs/` accessor at its twin `const_tm` (twin registry becomes the
   catalogue's backing store).
2. `twins::unfold_spec` returns `def_thm` (now that the op *is* the const);
   `spec_eq` and its `unfold_term_spec` call are deleted. Consumers unchanged.
3. Delete `TermKind::Spec` / `TypeKind::Spec` / `unfold_term_spec` /
   `Term::spec_abs` / `spec_rep` and the TypeSpec abs/rep laws.

Consumers move **once** (onto `twins::unfold_spec`, done in S9a) and never again.
