# The inductive-types API — design (`covalence-inductive`)

**Status:** design locked for the parallel `inductive-api` track (2026-07).
**Goal (maintainer):** a proper API for *simple* inductive types that
(a) abstracts over their **representation**, (b) other crates **consume**, and
(c) is generic enough to **swap the backend within a logic** — e.g. inside HOL:
the impredicative ∀-least-fixpoint encodings (`init/prop.rs`, `init/sexpr.rs`,
`init/lambda_iter.rs` style) vs the typedef + recursion-theorem constructions
(`init/recursion.rs`, `init/list_recursion.rs`); inside set.mm: different ZFC
constructions. One pole to move toward: a solid API for a **basic Lisp**
(S-expressions as inductive data), and **ACL2** within that (the logic of total
recursive functions over sexprs, ACL2-style induction).

Authorship: AI-generated design note (vibes tier).

---

## 0. Placement + crate identity (decision)

**Package `covalence-inductive`, at `crates/lang/inductive`** (not
`crates/kernel/hol/inductive`). Reasoning:

- The core trait crate is **logic-agnostic by constraint**: no
  `covalence-init` dependency, no `covalence-core` dependency. Placing it under
  `kernel/hol/` would brand a logic-neutral vocabulary as HOL-specific, and
  would force the future set.mm backend (which lives with the Metamath/metalogic
  machinery) to reach *sideways into the HOL subtree* for a vocabulary that has
  nothing HOL about it.
- `crates/lang/` is already the home of kernel-independent language-level
  vocabulary (`covalence-grammar`, `covalence-forsp`). An `InductiveSpec` is a
  *language of datatype declarations* — exactly a `lang/` concern. The
  workspace member glob `crates/lang/*` picks it up with no `Cargo.toml` churn.
- **Backends live with their logics** (the mission's constraint): `covalence-init`
  implements the HOL backends over its existing engine; the set.mm backend later
  slots in beside `init/metalogic` / `crates/proof/metamath` — in both cases the
  dependency arrow points *from the logic's crate to `covalence-inductive`*,
  never the reverse.

Dependencies of the core crate: `thiserror` (error enum), `smol_str` — nothing
else (wrapper discipline is trivially satisfied; both are already
workspace-standard). **No `unsafe`** (this is a kernel-liftable surface-language
crate in the sense of the standing feedback rule).

---

## 1. The `InductiveSpec` data model

### 1.1 "Simple" scope (v1)

A **single, non-indexed, strictly-positive, first-order** datatype:

- **single**: one type per spec (no mutual blocks);
- **non-indexed**: no type indices / dependent families;
- **strictly positive + first-order + direct**: every recursive argument is the
  inductive type `T` *itself* — never `T → …`, never `F⟨T⟩` under another
  functor (so no nesting, no infinitary branching);
- constructors are finite lists of arguments, each argument either a
  **recursive occurrence** of `T` or an **external type** of the ambient logic.

This covers `nat`, `bool`-as-enum, `list`-at-a-fixed-element-type, binary
trees, and — the flagship — `sexpr := atom(bytes) | snil | scons(sexpr, sexpr)`.
It is exactly the scope the existing `init/inductive` engine handles
("basic" in `sig.rs`'s sense), so the HOL backends need no new mathematics.

### 1.2 The data (logic-agnostic via one type parameter)

The spec must not embed a logic's `Type`/`Term` values (that is what makes
`init`'s `GenSig` *engine vocabulary* rather than an API: `GenSig` carries the
constructor **terms** and argument **types** of a specific representation).
Instead the spec is plain data, generic over an **external-sort token** `X`:

```rust
/// One argument position of a constructor.
pub enum ArgSort<X> {
    /// A direct recursive occurrence of the type being defined.
    Rec,
    /// A non-recursive argument of external sort `X`
    /// (the backend maps `X` to its logic's type).
    Ext(X),
}

pub struct CtorSpec<X> {
    pub name: SmolStr,               // "atom", "scons", …
    pub args: Vec<(SmolStr, ArgSort<X>)>, // binder-name hints + sorts
}

pub struct InductiveSpec<X> {
    pub name: SmolStr,               // "sexpr", "nat", …
    pub ctors: Vec<CtorSpec<X>>,     // non-empty, declaration order
}
```

- At instantiation time a consumer picks `X = L::Type` (the common case: the
  external sorts are just the logic's types — `bytes` for `atom`), or `X = `
  some symbolic sort name resolved by the backend. Both are the *same* struct.
- Binder names are hints (legibility of generated terms), as in `GenArg` today
  — but owned `SmolStr`, not `&'static str`, so specs can be parsed/loaded.
- The spec is **plain serializable data** (`Clone + Eq + Hash` when `X` is;
  no trait objects, no closures). This is deliberate — see §6: a spec should be
  able to live as a content-addressed value / base-language `Tree`.

Convenience constructors (`CtorSpec::nullary`, `InductiveSpec::enum_of`, a
`sexpr_spec()` sample in tests) ride along.

### 1.3 Explicit LATER scope

Recorded here so v1 doesn't accidentally paint them out; **none are in v1**:

- **parameterized** datatypes (`list α` with `α` a *spec-level* parameter and a
  functorial action). v1 workaround: instantiate the spec at `X = L::Type`
  containing the logic's type variable (`Ext(tfree "a")`) — exactly how
  `init/list_recursion.rs` handles `list α` today. Genuine spec-level
  parameters (with map/functor laws in the bundle) are a later, additive
  extension (`InductiveSpec` gains a `params: Vec<SmolStr>` and `ArgSort::Param(usize)`).
- **mutual** blocks (`Vec<InductiveSpec>` realized together);
- **nested** recursion (`F⟨T⟩` — e.g. `tree := node(list tree)`);
- **indexed** families / inductive *predicates* with non-trivial indices (the
  `metalogic` `RuleSet`/`Derivable_L` engine is today's answer for rule
  inductions; folding it under this API is a later unification, see §5);
- **higher-order/infinitary** arguments (`nat → T`).

Each lands as a new `ArgSort`/spec variant + a backend capability flag — the
consumer-facing bundle (§2) is shaped so this is additive.

---

## 2. The backend trait + the `InductiveTheory` bundle

### 2.1 The key representational decision: membership-relativized types

The two HOL backends *cannot* present literally identical raw theorems:

- the **typedef** backend carves an exact type — every inhabitant is reachable,
  induction holds for the bare type;
- the **impredicative** backend's carrier `Φ⟨'r⟩` has **junk** inhabitants —
  genuine induction/exhaustiveness need a well-formedness predicate
  (`init/sexpr.rs`'s `induct_note` documents exactly this wall).

And the future **set.mm** backend has no types at all — a "type" is a class,
and every fact is membership-relativized natively.

So the API's notion of an inductive type is a **(carrier, membership) pair**,
and every theorem in the bundle is stated **relative to membership**:

```text
  ty        : the carrier type (opaque to consumers)
  mem       : Term — the membership predicate `T? : ty → bool`
  induction :  (⋀ᵢ closure-of-mem cases)  ⟹  ∀t. T? t ⟹ P t
  cases     :  ∀t. T? t ⟹ (∃x⃗. t = C₀ x⃗ ∨ …)
  freeness  :  Cᵢ x⃗ = Cᵢ y⃗ ⟹ x⃗ = y⃗ ;  Cᵢ x⃗ ≠ Cⱼ y⃗   (i ≠ j)
  comp      :  rec steps (Cᵢ x⃗) = stepᵢ x⃗ (rec-images)
  mem_ctor  :  T? (Cᵢ x⃗)  given T? on the recursive args
```

For an exact-type backend, `mem = λt. T` and the backend also provides
`mem_trivial : ⊢ ∀t. T? t` so consumers can discharge relativization for free.
This is the honest common denominator: it makes the *statements* stable across
backends within a logic (the mission's requirement (c)), it is what the
impredicative encoding can genuinely deliver, and it is *native* for set.mm.
Consumers that only ever use the recursor + computation laws (the
`init/prop.rs` soundness pattern) never touch `mem` at all.

### 2.2 The `Logic` carrier trait (what the bundle is stated over)

See §3 — the bundle only needs the associated types.

### 2.3 The bundle

```rust
/// What a backend realizes from a spec: the type, the constructors, the
/// recursion machinery, and the characteristic theorems.
pub struct InductiveTheory<L: Logic> {
    pub spec: InductiveSpec<L::Type>,
    pub ty: L::Type,               // the carrier (opaque!)
    pub mem: L::Term,              // membership predicate `ty → bool`
    pub ctors: Vec<L::Term>,       // constructor terms, spec order
    pub facts: Box<dyn InductiveFacts<L>>, // the theorem surface (below)
}
```

The **theorems are behind a trait, not eager fields**, for three reasons:
(1) several are *schematic* (induction takes a motive; injectivity is wanted at
specific argument tuples; in Metamath a scheme is applied by substitution, not
∀-instantiated) — a method is the portable carrier of a scheme;
(2) backends differ in cost — the typedef backend's `graph_det` is expensive
and should be built on demand / memoized behind the impl;
(3) it lets a backend serve extra derived facts later without churn.

```rust
pub trait InductiveFacts<L: Logic> {
    // -- recursion --
    /// The recursor applied: `rec(steps)(t)` as a term. `steps` in ctor order.
    fn rec_app(&self, steps: &[L::Term], t: &L::Term) -> Result<L::Term, L::Error>;
    /// Computation law for ctor `i`: ⊢ rec steps (Cᵢ x⃗) = stepᵢ x⃗ (images),
    /// ∀-closed over the constructor arguments.
    fn comp(&self, steps: &[L::Term], i: usize) -> Result<L::Thm, L::Error>;

    // -- freeness --
    /// ⊢ Cᵢ x⃗ = Cᵢ y⃗ ⟹ ⋀ₖ xₖ = yₖ, at the given argument tuples.
    fn injective(&self, i: usize, xs: &[L::Term], ys: &[L::Term]) -> Result<L::Thm, L::Error>;
    /// ⊢ (Cᵢ x⃗ = Cⱼ y⃗) ⟹ F, for i ≠ j, at the given argument tuples.
    fn distinct(&self, i: usize, j: usize, xs: &[L::Term], ys: &[L::Term]) -> Result<L::Thm, L::Error>;

    // -- induction / cases (membership-relativized, §2.1) --
    /// Rule-form structural induction: given the motive and one case proof
    /// per ctor (⊢ hyps-on-recursive-args ⟹ motive (Cᵢ x⃗), membership of
    /// external/recursive args available as hypotheses), conclude
    /// ⊢ ∀t. mem t ⟹ motive t.
    fn induct(&self, motive: &L::Term, cases: Vec<L::Thm>) -> Result<L::Thm, L::Error>;
    /// ⊢ ∀t. mem t ⟹ ⋁ᵢ ∃x⃗. t = Cᵢ x⃗ (derivable from induct generically;
    /// backends may override with a native proof).
    fn cases(&self) -> Result<L::Thm, L::Error>;

    // -- membership plumbing --
    /// ⊢ mem (Cᵢ x⃗), given membership proofs for the recursive arguments.
    fn mem_ctor(&self, i: usize, args: &[L::Term], rec_mems: Vec<L::Thm>) -> Result<L::Thm, L::Error>;
    /// ⊢ ∀t. mem t — Some for exact-type backends, None for junk-y carriers.
    fn mem_trivial(&self) -> Option<L::Thm>;
}
```

(Exact signatures may shake out slightly in I2; the *shape* — rule-form
schematic methods, membership-relativized, recursor + comp laws first-class —
is the locked part.)

### 2.4 The backend trait

```rust
pub trait InductiveBackend<L: Logic> {
    /// Realize a spec as a theory bundle in logic `L`.
    fn realize(&self, logic: &L, spec: &InductiveSpec<L::Type>)
        -> Result<InductiveTheory<L>, L::Error>;
}
```

**How "swap backend within a logic" works.** Two values implementing
`InductiveBackend<HolLogic>`:

1. **`ImpredicativeBackend`** — generalizes what `init/sexpr.rs` +
   `init/prop.rs` hand-roll today (and what `variant.rs::ChurchBackend`
   gestures at): carrier `Φ⟨'r⟩ = (A₀→'r) → … → 'r` with recursive slots at
   `'r`; constructors = handler folds; recursor = application (comp laws are
   **pure β**, one `beta_nf` each); `mem` = the wellformedness predicate
   `Wf t := ∀d. Closed(d) ⟹ d t` (impredicative least fixpoint, the
   `metalogic::derivable` shape); induction = one `inst` of `d := motive`
   against `Wf`; freeness from computing distinguishing folds. Cheap, rank-1,
   TCB-free, available for *every* v1 spec on day one.
2. **`TypedefBackend`** — adapts the existing engine: build the impredicative
   *graph*, run `graph`/`existence`/`uniqueness`/`determinacy`/`recursor`
   (`init/inductive/*`), carve the type (or reuse a carved carrier as
   `nat`/`list` do), `mem = λt. T`, `mem_trivial = Some(⊢ ∀t. T? t)`.
   Heavyweight, but exact.

A consumer holds a `&dyn InductiveBackend<HolLogic>` (or is generic over `B`),
calls `realize`, and works purely through the bundle. Nothing in the consumer
mentions `Φ⟨'r⟩` vs a carved subtype — `ty` is opaque, `mem` uniformly guards,
and the relativized statements are verbatim identical. Swapping = passing the
other backend value. (Within set.mm, the same trait at `L = SetMmLogic` hosts
e.g. an ω/`rdg`-recursion backend vs a pure least-fixpoint-class backend.)

The precedent inside the repo is `variant.rs`'s `VariantBackend` —
"pluggable realization, callers stable" — which this API supersedes for the
recursive case (and can absorb: a `Variant` is an `InductiveSpec` with no
`Rec` args).

---

## 3. The logic-abstraction trait

Informed directly by `init/inductive/hol.rs`'s value-typed `Hol` trait (the
port that already made the engine backend-generic *within* HOL). Two tiers, so
that *stating* a bundle needs almost nothing while *generic derivations* get
what they need:

```rust
/// Tier 1 — the carrier: what an InductiveTheory is stated over.
pub trait Logic {
    type Type: Clone + PartialEq + fmt::Debug;
    type Term: Clone + PartialEq + fmt::Debug;
    type Thm:  Clone + fmt::Debug;
    type Error: std::error::Error;
}

/// Tier 2 — construction + the minimal rule surface, for generic machinery
/// built ON TOP of the bundle (default-method derivations in the core crate,
/// the ACL2 layer, generic consumers). A strict subset of init's `Hol` trait.
pub trait LogicOps: Logic {
    // types:  bool_ty, fun_ty
    // terms:  var, app, lam, eq, imp, and, forall, exists
    // queries: type_of, concl, hyps, dest_app/dest_eq/dest_var, subst_free
    // rules:  assume, refl, sym, trans, eq_mp, beta_conv, cong_app, inst,
    //         all_intro/all_elim, imp_intro/imp_elim, and_intro/and_elim_l/r
    // (signatures as in init/inductive/hol.rs, verbatim shapes)
}
```

Decisions:

- **`Logic` is deliberately tiny** — a backend needs only tier 1 to *deliver*
  a bundle (it builds its proofs with its own native machinery; the HOL
  backends keep using `covalence-core`/`init` directly). Tier 2 exists for the
  code that must be generic: `cases()`-from-`induct()` default derivations,
  `discharge_conj`-style plumbing (today's generic free functions in
  `hol.rs`), and the ACL2 layer (§4).
- **`init`'s `Hol` trait implements/extends `LogicOps`** rather than being
  duplicated: in I3, `init` gets `impl Logic for NativeHol`-shaped glue (or
  `Hol: LogicOps` supertrait) so the existing engine and the new API share one
  vocabulary. The `Hol` trait's "hard derived rules" (β-nf, ∃-intro/elim,
  rewriting) stay in `init` — the core crate's generic code must make do with
  the primitive set or take those as backend-supplied capabilities.
- **No `define` in the trait.** Introducing named constants is
  backend-internal (the typedef backend uses `covalence-core`'s
  `define`/`new_type_definition`; the impredicative backend defines nothing).
  The bundle hands back *terms*; whether they are named constants or big
  λ-terms is representation, which the API abstracts.
- **Value-typed, `&self`, immutable** — the `hol.rs` lesson (the arena-style
  `HolLightKernel` with `&mut self` + `NameId` handles was the wrong shape for
  this machinery). An arena-backed logic can still implement `Logic` with
  cheap-clone id-typed `Term`s.

---

## 4. The Lisp pole and the ACL2 pole

### 4.1 SExpr — the flagship datatype

```rust
// X = HolLogic::Type
InductiveSpec {
    name: "sexpr",
    ctors: [
        CtorSpec { name: "atom",  args: [("b", Ext(bytes))] },
        CtorSpec { name: "snil",  args: [] },
        CtorSpec { name: "scons", args: [("h", Rec), ("t", Rec)] },
    ],
}
```

`init/sexpr.rs` *is* this spec hand-realized through the impredicative
encoding — constructors, recursor, β-comp laws, and the documented missing
`Wf`/induction. The flagship milestone (I3): `ImpredicativeBackend::realize`
on `sexpr_spec()` reproduces everything `init/sexpr.rs` provides **plus** the
`mem = Wf` predicate and genuine relativized induction/cases/freeness — then
`init/sexpr.rs` is reimplemented as a thin wrapper over the bundle (its public
functions preserved; skeleton entry for the `Wf` gap deleted). Surface parsing
(`crates/lib/sexp`) already produces the tree shape; a `covalence-sexp
SExp → bundle-constructor-terms` quotation helper lands next to the HOL
backend in `init` (NOT in the core crate — it needs the logic).

This makes "a basic Lisp" concrete: quoted S-expression data + a recursor =
`car`/`cdr`/`cons`/`atom?` defined as bundle-level operations with proved
equations, uniformly over any backend.

### 4.2 ACL2 — a THEORY over SExpr (design only, no v1 code)

ACL2 = the logic of **total recursive functions over sexprs** with
**measure-based admission** and **induction schemes read off admitted
definitions**. As a layer over this API (generic over `LogicOps` + the SExpr
`InductiveTheory`):

- **Definitional admission (`defun`).** A candidate `f(x⃗) = body` where `body`
  is built from bundle constructors/destructors (`car`/`cdr` = recursor
  projections), previously admitted functions, `if`/`atom?` tests, and
  recursive calls. Admission obligations, ACL2-style:
  1. a **measure** `m : sexpr → nat` (default: sexpr size, itself a recursor
     fold — `acl2-count`);
  2. **termination**: for each recursive call under governing tests `g⃗`,
     `⊢ mem x ⟹ g⃗ ⟹ m(args-of-call) < m(x)`.
  Given these, the **definitional equation** `⊢ ∀x. mem x ⟹ f x = body`
  becomes a theorem via well-founded recursion on the measure — concretely:
  strong (course-of-values) induction on `nat` (`lambda_iter.cov`'s
  `strong_induct` is the exact pattern), with the graph-style
  existence/uniqueness argument the `init` engine already implements at the
  `nat` measure. No new logic — this is a *derived* construction over the
  bundle + `nat`'s bundle.
- **ACL2 induction schemes.** Every admitted `f` induces the induction scheme
  that mirrors its case analysis: to prove `∀x. mem x ⟹ P x`, prove `P` for
  each non-recursive branch and each recursive branch assuming `P` at the
  recursive-call arguments. Justified by the same measure (strong `nat`
  induction transported along `m`) — i.e. the scheme is a *theorem generated
  per definition*, packaged as a rule-form method like `induct`. This is the
  ACL2 `:induction` machinery, landed as ordinary derived theorems.
- **Totality is structural to the layer**: only admitted (measure-certified)
  functions exist, so the theory is exactly "total recursive functions over
  sexprs". Partial/reflexive functions, `mbe`, guards: out of scope.

The layer's home when built: a new module/crate above `covalence-inductive`
(e.g. `covalence-acl2` or an `acl2` module in the consumer tier — decided when
implemented; it must NOT live in the core trait crate, since it needs
`LogicOps` machinery but stays logic-generic).

---

## 5. The set.mm backend sketch (design only — NOT implemented now)

`L = SetMmLogic`: `Type` = degenerate (a marker — set.mm is untyped; "the
carrier type" is carried by `mem`), `Term` = class expressions (Metamath
`SExpr` terms via `crates/proof/metamath`), `Thm` = a certificate that the
statement is **`Derivable_DB`-provable** — either a replayed Metamath
derivation (the `metalogic/mm_replay` path) or a constructed
`⊢ Derivable_ZF ⌜S⌝` fact (the CONSTRUCT-don't-trust rule from the Metamath
thin-waist architecture).

Realizing a spec:

- **Carrier**: the standard ZFC construction — tag-and-tuple encode
  constructors (`Cᵢ x⃗ ↦ ⟨i, ⟨x₁, …⟩⟩` with ordered pairs), then take the
  carrier as the **least class closed under the constructor operations**
  (intersection of all closed classes — set.mm's usual inductive-definition
  idiom), or equivalently build it in ω stages via `rdg` (finite rank
  suffices for v1's first-order specs). Two different constructions = two
  set.mm backends behind the same trait — the within-logic swap again.
- **`mem`** is class membership `x ∈ T` — the membership-relativized bundle
  contract (§2.1) is *native* here, which is precisely why the contract was
  chosen.
- **Freeness** from ordered-pair injectivity + tag distinctness (`opth` etc.);
  **induction** from leastness of the closure; **recursor + comp laws** from
  set.mm's well-founded/finite recursion theorems (`wfr*`, `rdg`, or
  structural recursion along the ω-stage rank).
- Facts surface as the same `InductiveFacts` methods; each method mints /
  replays the corresponding Derivable certificate. Consumers written against
  the bundle (including the ACL2 layer, modulo its `LogicOps` needs) transport
  **without changes** — requirement (b)+(c) across logics, not just within HOL.

Open design item recorded for that future stage: how `LogicOps` (tier 2) maps
onto a schematic FOL substrate (Metamath substitution vs HOL λ) — likely the
ACL2 layer runs there via the mm_subst ≅ locally-nameless bridge, or tier-2
consumers stay HOL-only at first.

---

## 6. Compatibility with the Tree-reflection / carrier direction

The current architecture (handoff docs): three-tier tower `CoreLang ⊂ CoreEval`
via `Thm<L>`; literals **denote, never construct** — per-carrier uninterpreted
`toHOL` base ops (`ToHOL : Op<In = Nat, Out = HolTm>`), with HOL terms as *one
carrier among many* in the closed-world base language. Design points keeping
this API compatible:

1. **Specs are plain data** (§1.2) — `Clone/Eq/Hash`-able, closure-free,
   serializable. An `InductiveSpec` can itself become a base-language value /
   content-addressed blob (a `Tree`), so "the datatype `sexpr`" can be named,
   hashed, and shipped — a prerequisite for spec-indexed base-op families.
2. **`Logic::Term` is opaque**, so a backend whose terms are *symbolic base
   expressions* (leaves like `App<ToHolNat, Val(n)>` instead of materialized
   literals) implements `Logic` unchanged. Nothing in the API assumes terms
   are concrete `covalence-core` `Term` trees.
3. **The comp laws are the cert shape.** `⊢ rec steps (Cᵢ x⃗) = …` is exactly
   the kind of equation the eval tier accelerates: for a generated inductive
   type with a *native carrier* (e.g. sexprs represented as `covalence-sexp`
   values on the Rust side), a per-spec `toHOL_T : NativeT → HolTm` base op +
   admitted unfolding rules (`toHOL_T (scons h t) = scons (toHOL_T h)
   (toHOL_T t)`) mint bundle facts at native speed under the standard
   soundness contract (∃ a HOL derivation — here literally provided by the
   pure backend). I.e. **a third HOL backend slot: the eval-tier-accelerated
   one**, minting `Thm<CoreEval>` facts whose pure witnesses are the
   `ImpredicativeBackend`'s output. The trait needs nothing extra — the tier
   lives inside `L::Thm` (`Thm<CoreLang>` vs `EvalThm`), which is precisely
   how the tower already parameterizes trust.
4. **Constructors are index-addressable** (spec order everywhere), so base-op
   families / cert tables can key on `(spec-hash, ctor-index)` without name
   plumbing.
5. The quotation seam (surface `covalence-sexp` `SExp` → constructor terms,
   §4.1) is where a `toHOL`-style "denote don't construct" swap would happen —
   it is deliberately a *helper beside the backend*, not part of the trait, so
   replacing eager construction with symbolic denotation is a local change.

---

## 7. Relationship to existing code (migration map)

| Existing | Fate |
|---|---|
| `init/inductive/sig.rs` (`GenSig`/`GenArg`) | stays — the *engine's* internal vocabulary; the `TypedefBackend` adapter converts `InductiveSpec` → `GenSig` (minting ctor terms) |
| `init/inductive/data.rs` (`Inductive` trait) | stays engine-internal; the adapter implements it from the spec + carved carrier |
| `init/inductive/hol.rs` (`Hol` trait) | becomes/extends `LogicOps` (I3 glue); generic free functions migrate to the core crate where they only need tier 2 |
| `init/inductive/variant.rs` (`VariantBackend`) | superseded eventually — a `Variant` is a `Rec`-free spec; kept until callers (wasm syntax) migrate |
| `init/sexpr.rs` | reimplemented as a thin wrapper over `ImpredicativeBackend` (I3); gains genuine `Wf`-relativized induction |
| `init/prop.rs`, `metalogic` `RuleSet` | untouched — inductive *predicates* / rule induction are LATER scope (§1.3); the shared impredicative machinery may be factored under the hood later |
| `crates/lib/sexp` | the surface-parsing source for quotation (helper in `init`, not core) |

## 8. Staging (this track)

- **I1** (this commit): worktree + this design doc.
- **I2**: `crates/lang/inductive` skeleton — `InductiveSpec`, `Logic`/`LogicOps`,
  `InductiveTheory`/`InductiveFacts`, `InductiveBackend`, errors, unit tests on
  the data model; SKELETONS entries for the unbuilt backends.
- **I3**: the HOL `ImpredicativeBackend` in `covalence-init` (generalizing
  `sexpr.rs`/`prop.rs` machinery), SExpr flagship end-to-end through the API;
  `Hol`→`LogicOps` glue.
- **I4**: the HOL `TypedefBackend` adapter over the existing engine (`nat`,
  `list` as consumers); backend-swap test: one consumer proof script run
  against both backends verbatim.
- **I5+** (design-gated): ACL2 layer; set.mm backend; parameterized specs.
