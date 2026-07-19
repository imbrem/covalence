+++
id = "N0012"
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

# Inductive-types support — how it works now

Walk-through of the current inductive-type machinery, with citations, plus a
skeletons/improvements list. Answers "why *carved*? / why that domain?" (§0–§1).
Companion to [`inductive-api-design.md`](./inductive-api-design.md) (the
`covalence-inductive` API this feeds).

## 0. "carved" — where the name comes from

Not a standard type-theory term — a deliberate project coinage contrasting the two
strategies for realizing an inductive spec as a HOL object:

- **Church / impredicative** (`init/inductive/church.rs`, embedded in
  `init/sexpr.rs`): the type is a rank-1 fold `T⟨r⟩ := H₁→…→Hₙ→r`. Generic over any
  spec, cheap — but hits a *wall* (§6): you cannot recover a recursive subtree from a
  fold at rank 1, so **no injectivity at recursive positions and no primitive
  recursion**.
- **Carved / exact-type** (`init/inductive/carved.rs`): the type is literally *carved
  out* of a universal domain by a well-formedness predicate + `new_type_definition`
  (a genuine HOL subtype). This closes the gaps Church can't — `car`/`cdr` are
  definable projections, so injectivity-at-recursive-positions and primitive recursion
  are real.

So "carved" ≈ "subtype-of-a-universal-domain." Alternatives: *exact-type*,
*subset/subtype construction*, *tree-as-labeled-paths*. The name is everywhere because
`sexpr` is the linchpin datatype (the Lisp/ACL2 layer + the parsers sit on it).

## 1. The S-expression construction (`init/inductive/carved.rs`)

### 1a. The universal domain — a tree as its path→label table

```
U   := list bool → LB           -- paths → node labels
LB  := bytes  +  unit  +  unit   -- coprod bytes (coprod unit unit)
```

A binary tree is presented as **the table mapping each path to the label at that
node**. A path is a `list bool` (`false` = head/left, `true` = tail/right); the label
says which node lives there: `inl b` (a `bytes`) → `atom b` leaf; `inr (inl ())` →
`snil`; `inr (inr ())` → `scons`. Constructors put their label at the *empty* path and
route non-empty paths into children:

```
atomU b    := λp. cond (p = nil) (inl b) snilLab
snilU      := λp. snilLab
sconsU x y := λp. cond (p = nil) sconsLab
                    (cond (head p = some true) (y (tail p)) (x (tail p)))
```

(Leaves answer the `snil` label off their root; below `Wf` that's harmless junk.)

### 1b. Why `bytes + unit + unit`, not `bytes + bool`

A label does exactly two jobs: **(a) say which constructor** produced the node, and
**(b) carry that constructor's *non-recursive* arguments**. Recursive arguments are
**not** in the label — they live in the path table (the children). Per constructor:
`atom` has one non-recursive `bytes` arg → summand `bytes`; `snil` has none → `unit`;
`scons`'s two args are both *recursive* → no non-recursive payload → `unit`. Hence `LB
= bytes + unit + unit`. General recipe: **one summand per constructor, each = the
product of that constructor's non-recursive argument types** (a polynomial-functor /
container label; recursive positions become path children).

`bytes + bool` would *work for this specific type* (`bool ≅ unit + unit`) but is an
ad-hoc collapse that merges the snil/scons tags into a `bool` and **doesn't
generalize** — a generic carver for an N-constructor spec must build `Σᵢ (Πⱼ
nonrec_argⱼ)`. (Caveat: the current code is **hand-built for `sexpr`** — §6 — so this
is the intended shape a generic carver would follow, not yet a generic builder.)

### 1c. Freeness via *definable projections*

Because `scons` routes head/tail into disjoint path-prefixes, the projections are
plain functions on `U`:

```
carU u := λq. u (cons false q)      cdrU u := λq. u (cons true q)
```

so `cdrU (sconsU x y) = y` is a **pointwise computation + function extensionality**,
and `scons` injectivity *at recursive positions* follows by congruence. Constructor
distinctness is `inl ≠ inr` on the empty-path label. Exactly the capability the Church
encoding can't reach.

### 1d. Carving the exact type

`Wf : U → bool` is the impredicative least predicate closed under the three
`U`-constructors; then `sexpr := { u : U | Wf u }` via `Thm::new_type_definition`.
Induction transports through `abs`/`rep`, so membership is trivial (`mem = λt. ⊤`) and
every membership guard in the generic bundle discharges for free. Introduced constants
are fresh `Thm::define` `Def`s (small, β-inert), built once in a process-global
`LazyLock`.

## 2. The generic recursion engine (`init/inductive/{graph,existence,uniqueness,determinacy,recursor}.rs`)

Everything recursion-shaped is produced by a **generic pipeline** parameterized over
the abstract `Hol` surface and an `Inductive` feeder (§3). It builds a recursor and
proves its defining equations from *only* induction + freeness:

1. **`graph.rs` — the recursion relation.** The impredicative *paramorphic* graph
   `Graph t a := ∀G. Closed(fs, G) ⟹ G t a`, one clause per constructor: `∀x⃗ b⃗. (⋀ⱼ G
   rⱼ bⱼ) ⟹ G (Cᵢ x⃗) (fᵢ x⃗ b⃗)` — the step `fᵢ` sees the **raw** recursive args `x⃗`
   *and* their images `b⃗` (paramorphism).
2. **`existence.rs` — totality `∀t. ∃a. Graph t a`.** `graph_intro` proves each
   constructor's intro rule without freeness; `graph_total` closes totality by the
   supplied structural induction, peeling each recursive `∃` via `exists_elim` so the
   conclusion stays witness-free.
3. **`uniqueness.rs` — inversion.** `graph_inv`: `Graph (Cᵢ x⃗) a ⟹ ∃b⃗. (⋀ Graph rⱼ
   bⱼ) ∧ a = fᵢ x⃗ b⃗`, via a determinizing relation `Good k c := Graph k c ∧ wit k c`;
   off-diagonal clauses discharge by **distinctness**, the diagonal by **injectivity**.
4. **`determinacy.rs` — uniqueness `Graph t a ⟹ Graph t b ⟹ a = b`.** Structural
   induction; each case inverts both graphs and equates witnesses by the IH, bridging
   inner ε-terms to applied form by β-normalization.
5. **`recursor.rs` — assembly.** `rec := λsteps. λt. ε a. Graph steps t a`;
   `graph_at_rec` gives `⊢ Graph __t (ε a. Graph __t a)` from totality + Hilbert
   choice; `rec_equation` proves each computation law `⊢ ∀x⃗. rec steps (Cᵢ x⃗) = fᵢ x⃗
   (rec r⃗)` from graph-intro + determinacy. `recursion_equations(...)` is the raw
   output the carved backend consumes; `recursion_theorem(...)` wraps it in `∃rec. P
   rec`.

**The role of ε (Hilbert choice):** the recursor is *defined* as `ε a. Graph t a` —
choice picks the unique image totality/determinacy prove exists and is unique. The
"recursion via ε" pattern (recursive spec as an ε-term; the defining equations are then
theorems, not axioms) — the same mechanism the base `holomega_proto`/`ty_inst` and the
"general recursion via ε" vision use.

## 3. What a type must supply — the `Inductive` trait + engine spec

The engine is generic over `Inductive<H: Hol>` (`init/inductive/data.rs`):

```rust
trait Inductive<H: Hol = NativeHol> {
    fn sig(&self) -> &GenSig<H::Term, H::Type>;
    fn induct(&self, motive, cases) -> Result<H::Thm>;                 // ⊢ ∀t. P t
    fn injective(&self, i, xs, ys) -> Result<H::Thm>;                  // Cᵢ x⃗=Cᵢ y⃗ ⟹ ⋀ xₖ=yₖ
    fn distinct(&self, i, j, xs, ys) -> Result<H::Thm>;                // Cᵢ x⃗=Cⱼ y⃗ ⟹ F
}
```

`SExprInductive` (carved.rs) implements it for `sexpr` (all four proved there).

The **engine-internal spec** (`sig.rs`) is `GenSig`/`GenConstructor`/`GenArg`
(`Param{ty,name} | Rec{name,image}`). Distinct from the **logic-neutral public spec**
in `covalence-inductive` (`InductiveSpec<X>`/`CtorSpec<X>`/`ArgSort<X>`, `Rec |
Ext(X)`), which omits the constructor *term* and relation binder — backends
materialize those. Two spec models (engine-internal HOL-typed, serializable
logic-neutral); a backend converts the latter into the former.

## 4. The abstract HOL surface

The engine runs on the `Hol` trait (`init/inductive/hol.rs`, re-exported as
`covalence-hol-api`): value-typed term builders (`var/app/lam/eq/imp/and/forall/exists`
+ `bool_ty/fun_ty/tvar`), queries (`type_of/dest_*`), and the derived rule set
(`assume/refl/sym/trans/eq_mp/beta_conv/cong_app/inst/all_*/imp_*/and_*/select_ax/
beta_nf/exists_*/rw_all`). `NativeHol` implements it over the kernel. Intent: "same
engine, any HOL backend" (native today; an object-level HOL tomorrow).

## 5. The logic-neutral API (`crates/lang/inductive/`)

A logic-agnostic wrapper so consumers name one crate and swap representations:

- **`Logic`** (carriers `Type/Term/Thm/Error`) + **`LogicOps`** (term builders +
  minimal rule surface). `NativeHol` gets `impl LogicOps` in `init/inductive/api.rs`
  (method-by-method forwarding).
- **`InductiveBackend<L>`**: `realize(logic, spec) → InductiveTheory<L>`, refusing
  dishonestly (`SpecMismatch`/`Unsupported`) rather than degrading silently.
- **`InductiveTheory<L>`**: the bundle `{ spec, ty, mem, ctors, facts }`.
- **`InductiveFacts<L>`**: theorem accessors — `rec_app`/`comp`, `injective`/`distinct`,
  `induct`, `cases`, optional `prec_app`/`pcomp` (paramorphism), `mem_ctor`/
  `mem_trivial`, `caps()`.
- **`BackendCaps`**: `mem_trivial`, `rec_injective`, `prim_rec` — honesty flags a
  consumer checks before relying on a capability.

**The membership-relativized contract**: every theorem is guarded by `mem t ⟹ …`. For
**exact-type** backends `mem = λt.⊤` and `mem_trivial = Some(⊢∀t. mem t)`, so the guard
vanishes. For **Church** backends `mem` is the real junk-excluding `Wf`, so freeness
statements are relative to well-formed elements and take their antecedent at a
backend-chosen *observation instance* (e.g. `r := bool` for tag-distinctness). One
contract lets a single consumer work over either representation.

## 6. The three backends today

| Backend | File | Type | `mem_trivial` | `rec_injective` | `prim_rec` | Generic? |
|---|---|---|---|---|---|---|
| **Carved sexpr** | `carved.rs` | `atom bytes \| snil \| scons rec rec` | ✓ | ✓ | ✓ | **No — sexpr-specific** |
| **Nat engine** | `engine.rs` | `zero \| succ nat` | ✓ | ✓ (`succ_inj`) | ✓ (`natRec`) | **No — nat-specific** |
| **Church** | `church.rs` | **any** v1 spec | ✗ (`Wf` guard) | **✗ (rank-1 wall)** | **✗** | **Yes** |

The **Church rank-1 wall**: recovering a recursive subtree from a fold needs a
reconstruction fold whose result type is the carrier itself, unquantifiable at rank 1;
at a collapsing instance of `r` the injectivity statement is false, so no polymorphic
proof exists — the backend honestly reports `rec_injective = false` and `Unsupported`
for `prim_rec`. So: **one generic-but-capability-limited backend (Church) + two
full-capability but type-specific backends (kernel S-expression, nat).**

## 7. Skeletons + improvements

Sourced from `init/src/init/SKELETONS.md`, `crates/lang/inductive/SKELETONS.md`, and
the code above.

### Representation / backend gaps

1. **No generic exact-type carver.** `carved.rs` hand-builds the `sexpr` domain; a
   generic "carve any `InductiveSpec` into a subtype" builder (label = `Σᵢ Πⱼ
   nonrec_argⱼ`, children via paths, `Wf` closed under the constructors) is future
   work. *Highest-leverage* — turns the carved strategy from one type into a functor
   over specs.
2. **Engine adapters are type-specific.** Only `nat`/`sexpr` have `Inductive`/
   `InductiveBackend` adapters; a generic adapter (+ a `list` instance) is deferred
   until a second consumer exists.
3. **Full ≥2-recursive-arg end-to-end run unproven.** The pipeline is written general
   for `k ≥ 1` (a binary-tree test in `existence.rs`), but no fresh ≥2-rec-arg type
   has been driven through the *whole* `recursion_theorem`.

### Genericity / layering

4. **Proof modules still concrete over `NativeHol`.** The trait/data model/graph
   builders/`Inductive<H>` are generic, but `existence`/`uniqueness`/`determinacy`/
   `recursor` are still written against `NativeHol` (a `<H: Hol, I: Inductive<H>>` port
   + shim is planned). Blocks "same engine on an object-level HOL."
5. **`Hol` vs `LogicOps` duplication.** `init/inductive/hol.rs`'s `Hol` should *extend*
   `covalence_inductive::LogicOps` instead of duplicating its surface.

### Expressiveness (v1 exclusions — all deferred by design)

6. No mutual recursion. 7. No nested recursion. 8. No indexed families. 9. No
parameterized types as a first-class notion (instances monomorphic today).
10. **General/well-founded recursion beyond structural** — the engine covers total
structural recursion; ACL2-style measure/ordinal termination is not here. The bridge
needed for a real ACL2 `eval` (connects to "general recursion via ε": an ε-defined
fixpoint valid-but-undefined off its termination domain).

### Ergonomics / cross-cutting

11. **No deparse / observation for the carved type**: a `sexpr → bytes` deparse +
    round-trip theorem, a certified `Term → RustSExpr` observation. Belongs with the
    `SExprRep` trait proposal.
12. **`Def` proliferation / perf** not currently a problem (constants `LazyLock`-built
    once, equations proved polymorphic + instantiated), but a generic carver minting
    many `Def`s per spec should watch it.

**Suggested order:** 1. `list` exact-type instance (validates the engine on a second
real type + a 2-rec-arg-adjacent shape) → 2. generic exact-type carver (the big one) →
3. deparse/observe + `SExprRep` → 4. finish the generic-`Hol` port → 5. measure/ordinal
recursion (the ACL2 `eval` on-ramp). Mutual/nested/indexed come after a generic carver
exists to extend.
