+++
id = "N0011"
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

# The inductive-types API — design (`covalence-inductive`)

**Design locked** for the `inductive-api` track (2026-07). Backends built (§9/§10).
Companion: [`inductive-support.md`](./inductive-support.md) (the HOL engine this API
sits over).

**Goal:** an API for *simple* inductive types that (a) abstracts over their
**representation**, (b) other crates **consume**, (c) is generic enough to **swap the
backend within a logic** — inside HOL: impredicative ∀-least-fixpoint encodings vs
typedef + recursion-theorem constructions; inside set.mm: different ZFC constructions.
One pole to move toward: a solid API for a basic Lisp (S-expressions as inductive
data) and **ACL2** within that (total recursive functions over sexprs, ACL2-style
induction).

## 0. Placement + crate identity

**Package `covalence-inductive`, at `crates/kernel/data/inductive`** (not
`crates/kernel/hol/inductive`):

- Logic-agnostic **by constraint**: no `covalence-init`/`covalence-core` dependency.
  Placing it under `kernel/hol/` would brand a logic-neutral vocabulary as
  HOL-specific and force the future set.mm backend to reach sideways into the HOL
  subtree.
- `crates/lang/` is already home to kernel-independent language-level vocabulary
  (`covalence-grammar`, `covalence-forsp`). An `InductiveSpec` is a *language of
  datatype declarations* — a `lang/` concern.
- **Backends live with their logics:** `covalence-init` implements the HOL backends;
  the set.mm backend later slots in beside `crates/proof/metamath`. The dependency
  arrow always points *from the logic's crate to `covalence-inductive`*.

Deps of the core crate: `thiserror`, `smol_str` — nothing else. **No `unsafe`**
(kernel-liftable surface-language crate).

## 1. The `InductiveSpec` data model

### 1.1 "Simple" scope (v1)

A **single, non-indexed, strictly-positive, first-order** datatype: one type per spec
(no mutual blocks); no type indices/dependent families; every recursive argument is
`T` *itself* (no nesting, no infinitary branching); constructors are finite arg lists,
each arg either a **recursive occurrence** of `T` or an **external type** of the
ambient logic. Covers `nat`, `bool`-as-enum, `list`-at-fixed-element, binary trees,
and the flagship `sexpr := atom(bytes) | snil | scons(sexpr, sexpr)` — exactly the
scope the existing `init/inductive` engine handles, so the HOL backends need no new
mathematics.

### 1.2 The data (logic-agnostic via one type parameter)

The spec must not embed a logic's `Type`/`Term` (that is what makes `init`'s `GenSig`
engine vocabulary rather than an API). Instead it's plain data, generic over an
**external-sort token** `X`:

```rust
pub enum ArgSort<X> { Rec, Ext(X) }        // recursive occurrence | external sort
pub struct CtorSpec<X> { pub name: SmolStr, pub args: Vec<(SmolStr, ArgSort<X>)> }
pub struct InductiveSpec<X> { pub name: SmolStr, pub ctors: Vec<CtorSpec<X>> }
```

- A consumer picks `X = L::Type` (external sorts are the logic's types — `bytes` for
  `atom`) or a symbolic sort name resolved by the backend. Same struct.
- Binder names are hints (legibility), owned `SmolStr` (not `&'static str`) so specs
  can be parsed/loaded.
- **Plain serializable data** (`Clone + Eq + Hash` when `X` is; no trait objects, no
  closures) — deliberate (§6: a spec should be able to live as a content-addressed
  value / base-language `Tree`).

Convenience constructors (`CtorSpec::nullary`, `InductiveSpec::enum_of`, a
`sexpr_spec()` sample) ride along.

### 1.3 Explicit LATER scope (none in v1)

- **parameterized** datatypes (`list α` with `α` a spec-level parameter + functorial
  action). v1 workaround: instantiate at `X = L::Type` containing the logic's type
  variable (`Ext(tfree "a")`) — how `init/list_recursion.rs` handles `list α`. Genuine
  spec-level params (`params: Vec<SmolStr>` + `ArgSort::Param(usize)`) are a later
  additive extension.
- **mutual** blocks; **nested** recursion (`F⟨T⟩`); **indexed** families / inductive
  *predicates* (the `metalogic` `RuleSet`/`Derivable_L` engine is today's answer for
  rule inductions; folding it here is a later unification, §5); **higher-order** args
  (`nat → T`).

Each lands as a new `ArgSort`/spec variant + a backend capability flag — the bundle
(§2) is shaped so this is additive.

## 2. The backend trait + `InductiveTheory` bundle

### 2.1 The key decision: membership-relativized types

The two HOL backends cannot present identical raw theorems: the **typedef** backend
carves an exact type (every inhabitant reachable, induction on the bare type); the
**impredicative** backend's carrier `Φ⟨'r⟩` has **junk** inhabitants (genuine
induction/exhaustiveness need a well-formedness predicate). And the future **set.mm**
backend has no types — a "type" is a class, every fact membership-relativized natively.

So the API's inductive type is a **(carrier, membership) pair** and every theorem is
stated **relative to membership**:

```
ty        : the carrier type (opaque to consumers)
mem       : Term — the membership predicate `T? : ty → bool`
induction :  (⋀ᵢ closure-of-mem cases)  ⟹  ∀t. T? t ⟹ P t
cases     :  ∀t. T? t ⟹ (∃x⃗. t = C₀ x⃗ ∨ …)
freeness  :  Cᵢ x⃗ = Cᵢ y⃗ ⟹ x⃗ = y⃗ ;  Cᵢ x⃗ ≠ Cⱼ y⃗   (i ≠ j)
comp      :  rec steps (Cᵢ x⃗) = stepᵢ x⃗ (rec-images)
mem_ctor  :  T? (Cᵢ x⃗)  given T? on the recursive args
```

For an exact-type backend, `mem = λt. T` + `mem_trivial : ⊢ ∀t. T? t` so consumers
discharge relativization for free. This is the honest common denominator: stable
*statements* across backends within a logic, deliverable by the impredicative encoding,
*native* for set.mm. Consumers that only use the recursor + comp laws never touch `mem`.

### 2.2 The bundle

```rust
pub struct InductiveTheory<L: Logic> {
    pub spec: InductiveSpec<L::Type>,
    pub ty: L::Type,               // the carrier (opaque!)
    pub mem: L::Term,              // membership predicate `ty → bool`
    pub ctors: Vec<L::Term>,       // constructor terms, spec order
    pub facts: Box<dyn InductiveFacts<L>>,
}
```

**Theorems are behind a trait, not eager fields**, because: several are *schematic*
(induction takes a motive; injectivity wanted at specific tuples; a Metamath scheme is
applied by substitution) — a method is the portable carrier of a scheme; backends
differ in cost (the typedef backend's `graph_det` is expensive, built on demand);
it lets a backend serve extra derived facts later without churn.

```rust
pub trait InductiveFacts<L: Logic> {
    // recursion
    fn rec_app(&self, steps: &[L::Term], t: &L::Term) -> Result<L::Term, L::Error>;
    fn comp(&self, steps: &[L::Term], i: usize) -> Result<L::Thm, L::Error>;
    // freeness
    fn injective(&self, i: usize, xs: &[L::Term], ys: &[L::Term]) -> Result<L::Thm, L::Error>;
    fn distinct(&self, i: usize, j: usize, xs: &[L::Term], ys: &[L::Term]) -> Result<L::Thm, L::Error>;
    // induction / cases (membership-relativized)
    fn induct(&self, motive: &L::Term, cases: Vec<L::Thm>) -> Result<L::Thm, L::Error>;
    fn cases(&self) -> Result<L::Thm, L::Error>;
    // membership plumbing
    fn mem_ctor(&self, i: usize, args: &[L::Term], rec_mems: Vec<L::Thm>) -> Result<L::Thm, L::Error>;
    fn mem_trivial(&self) -> Option<L::Thm>;   // Some for exact-type, None for junk-y carriers
}
```

(Exact signatures shook out slightly in I2 — see §9; the *shape* is the locked part.)

### 2.3 The backend trait + "swap within a logic"

```rust
pub trait InductiveBackend<L: Logic> {
    fn realize(&self, logic: &L, spec: &InductiveSpec<L::Type>)
        -> Result<InductiveTheory<L>, L::Error>;
}
```

Two values implementing `InductiveBackend<HolLogic>`:

1. **`ImpredicativeBackend`** — generalizes what `init/sexpr.rs`+`init/prop.rs`
   hand-roll: carrier `Φ⟨'r⟩` with recursive slots at `'r`; constructors = handler
   folds; recursor = application (comp laws are pure β, one `beta_nf` each); `mem` =
   `Wf t := ∀d. Closed(d) ⟹ d t` (impredicative least fixpoint); induction = one `inst`
   of `d := motive`; freeness from distinguishing folds. Cheap, rank-1, TCB-free,
   available for *every* v1 spec on day one.
2. **`TypedefBackend`** — adapts the existing engine: build the graph, run
   `graph`/`existence`/`uniqueness`/`determinacy`/`recursor`, carve the type (or reuse
   a carved carrier as `nat`/`list` do), `mem = λt. T` + `mem_trivial`. Heavyweight,
   exact.

A consumer holds a `&dyn InductiveBackend<HolLogic>` (or is generic over `B`), calls
`realize`, works purely through the bundle — nothing mentions `Φ⟨'r⟩` vs a carved
subtype. Swapping = passing the other backend value. The repo precedent is
`variant.rs`'s `VariantBackend` ("pluggable realization, callers stable"), which this
supersedes for the recursive case.

## 3. The logic-abstraction trait

Informed by `init/inductive/hol.rs`'s value-typed `Hol`. Two tiers, so *stating* a
bundle needs almost nothing while *generic derivations* get what they need:

```rust
pub trait Logic {                        // Tier 1 — the carrier
    type Type: Clone + PartialEq + fmt::Debug;
    type Term: Clone + PartialEq + fmt::Debug;
    type Thm:  Clone + fmt::Debug;
    type Error: std::error::Error;
}
pub trait LogicOps: Logic {              // Tier 2 — construction + minimal rules
    // types: bool_ty, fun_ty | terms: var, app, lam, eq, imp, and, forall, exists
    // queries: type_of, concl, hyps, dest_app/dest_eq/dest_var, subst_free
    // rules: assume, refl, sym, trans, eq_mp, beta_conv, cong_app, inst,
    //        all_intro/all_elim, imp_intro/imp_elim, and_intro/and_elim_l/r
}
```

- **`Logic` is deliberately tiny** — a backend needs only tier 1 to *deliver* a bundle
  (it builds proofs with native machinery). Tier 2 is for code that must be generic:
  `cases()`-from-`induct()` defaults, discharge plumbing, the ACL2 layer.
- **`init`'s `Hol` extends `LogicOps`** rather than duplicating it. The `Hol` trait's
  "hard derived rules" (β-nf, ∃-intro/elim, rewriting) stay in `init`.
- **No `define` in the trait** — introducing named constants is backend-internal
  (typedef uses `covalence-core`'s `define`/`new_type_definition`; impredicative
  defines nothing). The bundle hands back *terms*; whether named or big λ-terms is
  representation.
- **Value-typed, `&self`, immutable** — the `hol.rs` lesson (arena-style `&mut self` +
  `NameId` handles was the wrong shape). An arena-backed logic still implements `Logic`
  with cheap-clone id-typed `Term`s.

## 4. The Lisp pole and the ACL2 pole

### 4.1 SExpr — the flagship datatype

```rust
InductiveSpec { name: "sexpr", ctors: [
    CtorSpec { name: "atom",  args: [("b", Ext(bytes))] },
    CtorSpec { name: "snil",  args: [] },
    CtorSpec { name: "scons", args: [("h", Rec), ("t", Rec)] },
]}
```

`init/sexpr.rs` *is* this spec hand-realized through the impredicative encoding.
`ImpredicativeBackend::realize` on `sexpr_spec()` reproduces it **plus** the `mem = Wf`
predicate and genuine relativized induction/cases/freeness; then `init/sexpr.rs` is a
thin wrapper over the bundle. A `covalence-sexp SExp → constructor-terms` quotation
helper lands next to the HOL backend in `init` (not the core crate — it needs the
logic). This makes "a basic Lisp" concrete: quoted S-expr data + a recursor =
`car`/`cdr`/`cons`/`atom?` as bundle-level operations with proved equations, uniformly
over any backend.

### 4.2 ACL2 — a THEORY over SExpr (design only, no v1 code)

ACL2 = the logic of **total recursive functions over sexprs** with **measure-based
admission** and **induction schemes read off admitted definitions**. As a layer over
this API (generic over `LogicOps` + the SExpr `InductiveTheory`):

- **Definitional admission (`defun`).** A candidate `f(x⃗) = body` (body from bundle
  constructors/destructors, prior functions, `if`/`atom?` tests, recursive calls).
  Obligations: (1) a **measure** `m : sexpr → nat` (default: sexpr size = a recursor
  fold, `acl2-count`); (2) **termination** — for each recursive call under governing
  tests `g⃗`, `⊢ mem x ⟹ g⃗ ⟹ m(args-of-call) < m(x)`. Then the definitional equation
  `⊢ ∀x. mem x ⟹ f x = body` becomes a theorem via well-founded recursion on the
  measure — strong (course-of-values) `nat` induction (`lambda_iter.cov`'s
  `strong_induct`), with the graph existence/uniqueness argument the engine already
  implements at the `nat` measure. No new logic — a *derived* construction over the
  bundle + `nat`'s bundle.
- **ACL2 induction schemes.** Every admitted `f` induces the scheme mirroring its case
  analysis, justified by the same measure (strong `nat` induction transported along
  `m`) — a *theorem generated per definition*, packaged like `induct`. The ACL2
  `:induction` machinery as ordinary derived theorems.
- **Totality is structural to the layer** (only measure-certified functions exist).
  Partial/reflexive functions, `mbe`, guards: out of scope.

Home when built: a module/crate above `covalence-inductive` (e.g. `covalence-acl2`) —
NOT the core trait crate (it needs `LogicOps` but stays logic-generic).

### 4.3 What a `proof/acl2` frontend consumes

A future ACL2 frontend (the `.lisp`/`defun`/`defthm` reader, peer of the
`proof/metamath` and `proof/alethe` replayers) never touches the kernel; it compiles
each top-level form onto the bundle + derived-theorem API, as the built `init/lisp.rs`
slice already does by hand:

| ACL2 surface | Lowers to |
|---|---|
| `(defun f (x⃗) body)` with measure `m` | pick recursor step terms; `Thm::define` `f := prec[steps]`; discharge termination → **the definitional equation** as a theorem (via `nat` strong induction along `m`). `init/lisp.rs` builds this for structural recursion — `len`/`append` *are* two hand-lowered `defun`s. |
| a `defun`'s per-constructor computation | `prec_eq(steps, i, β)` + `apply_def` unfolding (`len_scons`, `append_scons`, …). |
| `car`/`cdr`/`consp`/`atom`/`cons`/`eq` | carved recursion-position extractors + `bool` catamorphisms (`Lisp::{car,cdr,cons,consp,atom_p}`) — `car`/`cdr` are *why* the carved backend is required (§4.4). |
| `(defthm name claim :hints ((:induct (f x))))` | `CarvedSExpr::induct(motive, [cases…])`. `Lisp::{append_assoc,len_append}` are two hand-lowered `defthm`s. |
| the ground-term evaluator (`(len '(a b))` ⇒ `2`) | the eval tier (`Thm<CoreEval>`) accelerating the same comp laws on quoted data (§6.3). |

The frontend adds **zero** trusted surface — parse → choose measure/scheme → emit these
calls, all ordinary derived theorems.

### 4.4 The universal-vs-exact split (permanent capability story)

The two HOL backends are two permanent points on a genuine expressiveness tradeoff; a
datatype's *Lisp-completeness* is what distinguishes them:

- **Church / `ImpredicativeBackend` — universal, no `cdr`.** Realizes *any* v1 spec in
  a single rank-1 impredicative encoding (needs only ∀/λ, transports to any
  `LogicOps`). Its recursor is an **iteration** (catamorphism): a step sees the *fold
  images* of recursive subterms, never the subterms. So the recursion-position
  destructor `cdr : sexpr → sexpr` (and rec-position injectivity) is **provably
  unstatable** — at a collapsing instance of the result tyvar the claim is false, so no
  rank-1 polymorphic proof exists. `rec_injective = false` reports this honestly. You
  get `atom?`, `consp`, `len` (a cata) — but not a real `cdr`, hence not Lisp.
- **Carved / typedef `CarvedSExpr` — exact, full Lisp.** Realizes the specific shape as
  a `new_type_definition` subtype of a well-founded tree pre-carrier. Terms are the
  honest carrier type, so full caps: **`prim_rec`** (paramorphic recursor, step sees
  raw subterms), **`car`/`cdr` as rec-position extractors**, **rec-position
  injectivity**, `mem = ⊤`. What `init/lisp.rs` builds on.

The dividing line: **anything Lisp needs `cdr`, and `cdr` is a rec-position extractor,
which only the exact backend can state.** Church is right for datatypes consumed purely
by folds (`bool`-tests, size measures, evaluators); carved whenever you take a datatype
apart structurally. Same `InductiveFacts` surface, `BackendCaps` names the difference,
consumers dispatch on the caps they need. Future exact backends (a generic carver; the
set.mm ordered-pair construction) inhabit the same "exact, full-caps" pole.

## 5. The set.mm backend sketch (design only — NOT implemented)

`L = SetMmLogic`: `Type` = degenerate marker (set.mm is untyped; "carrier type" is
carried by `mem`), `Term` = class expressions (Metamath `SExpr` via
`crates/proof/metamath`), `Thm` = a certificate that the statement is
`Derivable_DB`-provable (replayed Metamath derivation via `metalogic/mm_replay`, or a
constructed `⊢ Derivable_ZF ⌜S⌝` — the CONSTRUCT-don't-trust rule).

- **Carrier:** the standard ZFC construction — tag-and-tuple encode constructors
  (`Cᵢ x⃗ ↦ ⟨i, ⟨x₁, …⟩⟩` with ordered pairs), then the carrier = the **least class
  closed under the constructor operations** (intersection of closed classes), or built
  in ω stages via `rdg` (finite rank suffices for v1). Two constructions = two set.mm
  backends behind the same trait.
- **`mem`** is class membership `x ∈ T` — the membership-relativized contract is
  *native* here, precisely why it was chosen.
- **Freeness** from ordered-pair injectivity + tag distinctness (`opth`); **induction**
  from leastness of the closure; **recursor + comp laws** from set.mm's
  well-founded/finite recursion (`wfr*`, `rdg`).
- Facts surface as the same `InductiveFacts` methods (each mints/replays a Derivable
  certificate). Consumers written against the bundle transport **without changes** —
  requirement (b)+(c) across logics.

Open item for that stage: how `LogicOps` maps onto a schematic FOL substrate (Metamath
substitution vs HOL λ) — likely via the mm_subst ≅ locally-nameless bridge.

## 6. Compatibility with the Tree-reflection / carrier direction

The current architecture: three-tier tower `CoreLang ⊂ CoreEval` via `Thm<L>`;
literals **denote, never construct** — per-carrier uninterpreted `toHOL` base ops
(`ToHOL : Op<In = Nat, Out = HolTm>`). Keeping this API compatible:

1. **Specs are plain data** — an `InductiveSpec` can itself become a base-language
   value / content-addressed blob (a `Tree`), so "the datatype `sexpr`" can be named,
   hashed, shipped.
2. **`Logic::Term` is opaque**, so a backend whose terms are *symbolic base
   expressions* (leaves like `App<ToHolNat, Val(n)>`) implements `Logic` unchanged.
3. **The comp laws are the cert shape.** `⊢ rec steps (Cᵢ x⃗) = …` is exactly what the
   eval tier accelerates: a per-spec `toHOL_T : NativeT → HolTm` base op + admitted
   unfolding rules mint bundle facts at native speed under the standard soundness
   contract (∃ a HOL derivation — here provided by the pure backend). I.e. **a third
   HOL backend slot: the eval-tier-accelerated one**, minting `Thm<CoreEval>` facts
   whose pure witnesses are the `ImpredicativeBackend`'s output. The trait needs nothing
   extra — the tier lives inside `L::Thm`.
4. **Constructors are index-addressable** (spec order everywhere), so cert tables can
   key on `(spec-hash, ctor-index)` without name plumbing.
5. The quotation seam (surface `SExp` → constructor terms) is where a "denote don't
   construct" swap would happen — a *helper beside the backend*, not part of the trait.

## 7. Migration map

| Existing | Fate |
|---|---|
| `init/inductive/sig.rs` (`GenSig`/`GenArg`) | stays — the *engine's* internal vocabulary; the `TypedefBackend` adapter converts `InductiveSpec` → `GenSig` |
| `init/inductive/data.rs` (`Inductive`) | stays engine-internal; the adapter implements it |
| `init/inductive/hol.rs` (`Hol`) | becomes/extends `LogicOps`; generic free functions migrate to the core crate |
| `init/inductive/variant.rs` (`VariantBackend`) | superseded eventually (a `Variant` is a `Rec`-free spec); kept until callers migrate |
| `init/sexpr.rs` | reimplemented as a thin wrapper over `ImpredicativeBackend`; gains `Wf`-relativized induction |
| `init/prop.rs`, `metalogic` `RuleSet` | untouched — inductive *predicates* / rule induction are LATER scope |
| `crates/lib/sexp` | the surface-parsing source for quotation |

## 8. Staging

- **I1:** worktree + this design doc.
- **I2:** `crates/kernel/data/inductive` skeleton — spec, `Logic`/`LogicOps`, bundle, backend,
  errors, unit tests; SKELETONS for unbuilt backends.
- **I3:** the HOL `ImpredicativeBackend` in `covalence-init`; SExpr flagship end-to-end;
  `Hol`→`LogicOps` glue.
- **I4:** the HOL `TypedefBackend` adapter (`nat`, `list` consumers); backend-swap test.
- **I5+** (design-gated): ACL2 layer; set.mm backend; parameterized specs.

## 9. I2 outcome (built; contract deltas from §2)

Landed `crates/kernel/data/inductive` (spec model, `Logic`/`LogicOps`, bundle, error, a
generic `conformance` suite = the backend-swap test) + both HOL backends in
`covalence-init::init::inductive`:

- **`church::ImpredicativeBackend`** — realizes any v1 spec; delivered the `sexpr`
  flagship (handler names pinned to `fa`/`fn_`/`fc` so bundle ctors β-agree with the
  hand-rolled encoding), a `btree` second datatype, Church `nat`. `mem = Wf`, genuine
  relativized induction/cases/mem_ctor, distinctness via bool tag folds, Ext-position
  injectivity via projection folds.
- **`engine::NatEngineBackend`** — the adapter over the typedef+recursion engine
  (`rec_holds_proof_at` = the full graph/uniqueness/ε run), `mem = λt.⊤` +
  `mem_trivial`; kernel `succ_inj`/`zero_ne_succ` surfaced. Generic `Inductive`→bundle
  adapter deferred.

Contract deltas vs §2 (recorded in `theory.rs` docs):

1. **Recursion is iteration (catamorphism), not primitive recursion** — steps receive
   fold images only. A rank-1 Church encoding cannot pass raw recursive args; `natRec`
   is wrapped and β-bridged. Primitive recursion is a later additive capability.
2. **`injective` is per-position** (`injective(i, k, xs, ys)`), not a conjunction.
3. **Rec-position injectivity is a hard wall for Church** (at a collapsing instance of
   `'r` the statement is *false*). Surfaced as `rec_injective = false` + `Unsupported`;
   the exact backend supplies it.
4. **Freeness antecedents sit at a backend-chosen observation instance** (`'r := bool`
   for tags, `'r := payload` for projections; the carrier itself for exact backends).
5. **Applied-form convention** — every `P x`/`mem x` is the unreduced application;
   binder hints are reserved names (hygiene validated up front; violations are rule
   errors, never unsoundness).
6. `cases()` is **derived generically from `induct`** (refl + ∃-intro + ∨-intro per
   constructor).

The `sexpr` induction skeleton is **closed** (the `Wf`-relativized form ships).

## 10. I3/J outcome (the carved carrier + the Lisp theory)

The exact-type pole and first consumer theory landed:

- **The carved SExpr carrier** (`init/inductive/carved.rs`, `CarvedSExpr`) — the
  `atom bytes | snil | scons rec rec` shape via `new_type_definition` over a
  well-founded tree pre-carrier, delivering the full-caps set: a **paramorphic**
  recursor (`prec`/`prec_eq`, steps see raw subterms), the extractors `car`/`cdr`,
  **rec-position injectivity** (`scons` injective in both fields — the `prod.rs`
  pair-injectivity route), constructor distinctness across all three pairs, `mem = ⊤`.
  Machinery cribbed from `recursion.rs`/`list_recursion.rs` (recursor), `prod.rs`
  (injectivity), `tree.rs` (`leaf_inj`), `cond`/`coprod` (distinctness). Everything
  flows through existing kernel rules — a failed derivation is an error, never
  unsoundness; base/trusted + core were untouched.
- **The Lisp theory** (`init/lisp.rs`, `Lisp`) — the ACL2 groundwork, a *consumer* of
  the carved carrier: `car`/`cdr`/`cons`, the `bool` catamorphisms `consp`/`atom?`, the
  `nat` catamorphism `len`, and the **paramorphism** `append` (its `scons` step reuses
  the raw head), each a `Thm::define`d constant with per-constructor comp laws off
  `prec_eq`. Two genuine **structural-induction** theorems ship as ordinary derived
  theorems via `CarvedSExpr::induct`: `append_assoc` and `len_append` (tying
  catamorphism, paramorphism, and `nat`'s `add` recursion together) — the two archetypal
  ACL2 `defun` + `:induct` pairs.

Proof lesson (recorded in `lisp.rs`): a paramorphic comp law's RHS holds the *recursor
images*; fold them back to the function applications via the definitional equation
**before** `reduce_rhs`, so β-reduction cannot unfold the recursor's ε-term.

Still open (Lisp/ACL2, tracked in `init/SKELETONS.md`): `eq` (sexpr equality) and
`assoc` (association-list lookup) are the obvious next functions; the full ACL2 `defun`
measure-based admission + per-definition induction-scheme generation (§4.2) is the
frontend's job, not yet built (current theorems hand-pick structural measures).
