+++
id = "N000X"
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

# The relation-calculus base — authoritative redesign

**Status:** authoritative plan for the **base redesign** (2026-07). The base
becomes a *calculus of relations-as-untrusted-functions* with a reflected
type-representation sort `TyRep` as a first-class base sort. Committed scope is
binding: **base relation-calculus (`Rel`/`execute` + the positive calculus) +
`TyRep`-in-base**. A HOL-ω middle is a *future direction only* (Appendix A).

**This wave is design + sketches only — no change to `base/trusted` or `core` TCB
behavior.** Phase 0 (§6) is specified as a small, additive, reversible slice for
the orchestrator to build; it is not built here.

Companions: [`closed-world-kernel.md`](./closed-world-kernel.md) (the realized
base), [`literals/literal-endgame-design.md`](./literals/literal-endgame-design.md)
(EG1–EG5, the symbolic-operand mechanism this subsumes),
[`../logics/wasm-spec.md`](../logics/wasm-spec.md) / [`../web/wasm3-rust.md`](../web/wasm3-rust.md)
(WASM prior art), and the built code in `crates/kernel/base/trusted/src/`.

---

## 0. The two north stars (the judging axis)

Every base choice is judged, above soundness alone, on making these two
**first-class AND efficient**:

1. **Content-addressing = hash-consing (interning) — the aspirational
   representation, not merely a hash op.** The intended native representation
   addresses every term by its O256 content hash: structurally-identical terms are
   deduplicated and shared (one canonical `Arc` per content hash) — an
   interning/hash-consing decision, not an operation. **NOT YET BUILT (MF3):**
   today `Dyn::new` does `Dyn(Arc::new(e))` (a fresh `Arc` per call), so
   structurally-identical terms are *not* shared and `Dyn`'s `Arc::ptr_eq` does
   *not* yet coincide with content equality. The claim "`Dyn` ptr_eq = content
   equality" holds only once a content-hash-keyed interning layer is added; it is
   **future work, NOT relied upon by Phase 0 or Phase 1**. `Hash: Op<Bytes, O256>`
   (serialize-then-hash) is available today as the *computational witness*
   `⊢ hash(blob) = h` via `canon`.
2. **WASM** — a WASM module run is a *subset of untrusted relations*: executing it
   witnesses `input → output`, i.e. `a R b = true`.

The load-bearing observation tying execution together: **both a store lookup and a
WASM run are untrusted functions whose *execution* supplies positive facts and
never negative ones.** A store miss on one backing says nothing (the blob may be
elsewhere); a non-halting module proves nothing (halting problem). The base is
built around exactly this asymmetry. (The pure `Hash` op is the deterministic-total
corner: its `canon` equation is a genuine functional identity, unlike
store/WASM relations.)

---

## 1. The crux against the real types

The base today (`crates/kernel/base/trusted/src/`) is a closed-world **equality**
kernel:

- `op.rs` — `trait Op: Any { type In; type Out; }`. Already the **function sort**;
  relations are ops with `Out = bool`. Open vocabulary; uninterpreted ⇒ inert.
- `expr.rs` — sealed `trait Expr { type Ty; }`; `Val<C>`, `App<F,A>`, `Dyn<T>`
  (Arc, pointer-eq), `True`/`False`, tuples, faithful-pointer `Ref<P>`.
- `eqn.rs` — `Thm<L,P>` (`P: Expr<Ty=bool>`), **private fields, sole mint
  `pub(crate) Thm::new`**; the equality calculus (`refl`/`sym`/`trans`/`cong_app`/
  `cong_pair`/`eq_mp`); gated injectors `apply`/`canon`; `lift`.
- `lang.rs` — `Language` (`admits`/`extends`/`const MANIFEST`), `Rule<L>`
  (own-`TypeId` gate), `CanonRule: Op` (mints the *functional* equation
  `App<F,Val(v)> = Val(eval(v))`).
- `prop.rs` — the ungated bool theory, sound in every `L`.

Three facts decide the redesign:

- **Fact 1** — `Op<In,Out>` is already the function sort; `CanonRule` already
  executes ops (mints a functional equation). What is *missing* is **relational**
  (partial / effectful / nondeterministic) execution and a calculus over relations.
- **Fact 2** — `CanonRule` mints only a *functional* identity. It cannot serve
  WASM or a federated store (not functions). The relational reading `a R b` is
  sound where the functional reading `f(a)=b` is not.
- **Fact 3** — the base already proves **no disequalities** (the deferred
  `Evaluate` seam). The relational base **turns this into the load-bearing
  feature**: positive membership is native; negative membership (`¬(a R b)`) is
  axiom-only.

So the redesign completes the base's own `Op`/`CanonRule`/no-disequality trio into
a relation calculus, plus `Ty` promoted to a base sort.

---

## 2. The design (Architect B — additive relational layer, the winner)

Three architect proposals were weighed. **A** ("full allegory collapse": delete
`Val`/`App`/`Eqn`, everything is an `Op`, equality = the diagonal relation) is the
correct *limit* but a flag-day rewrite with no honest Phase 0 — graft its
vocabulary, defer the collapse to Phase 5. **C** ("relations in the middle, base
stays a pure equality kernel") fails both north stars' "first-class in the *base*"
requirement — graft its base-TCB minimalism, reject the placement. **B** wins:
`Op<In,Out>` is *already* the function sort and `Val<C>` *already* the primitive
point, so realize the Op/Val unification as a **stated identity + thin bridge**,
and add relational execution + the relation calculus as an *additive layer* that
touches zero existing behavior and keeps `Thm::new` the sole gate.

### 2A. Relation calculus base

**Membership needs no new grammar.** For a relation op `R : Op<(In,Out), bool>`,
the proposition `a R b` is just `App<R, (leaf<In>, leaf<Out>)>`, an `Expr<Ty=bool>`;
a proven membership is a `Thm<L, App<R, (leaf,leaf)>>`. The existing
`prop.rs`/`eqn.rs` calculus transports it for free.

**Leaves are ZERO-COPY (`Ref<Arc<_>>`), not owned `Val` (F1).** Operand leaves
must be the Arc-shared `Ref<P: TrustedDeref>` (`Arc: TrustedDeref`), **never** owned
`Val<C>` (holds `C` by value). Load-bearing on the WASM/store hot path: a megabyte
input buffer or store blob is seated as `Ref(Arc::new(buf))`, so the buffer lives
behind one `Arc`. Every calculus step that duplicates a leaf clones an **Arc
handle, not the payload** (`refl` clones its leaf, `cong_app` its op) — a refcount
bump (O(1)) vs a `Val<Buf>` deep copy. The `execute` bound is therefore
`F::In: 'static` / `F::Out: 'static`, **not** `F::In: Clone` over the payload.

**`Rel(F)` — the untrusted-function constructor:**

```rust
/// An untrusted, possibly effectful / partial / nondeterministic function.
/// `run` returning `Ok(b)` witnesses ONE pair `(a,b)` of the graph. Failure or a
/// different `b` on a re-run prove NOTHING.
pub trait UntrustedFn: Any { type In; type Out;
    fn run(&self, a: &Self::In) -> Result<Self::Out, RelErr>;
}
/// The GRAPH of `f`, as a relation-op. Writing `Rel(f)` is inert; only `execute`
/// mints, and only the true/returned direction.
pub struct Rel<F: UntrustedFn>(pub F);
impl<F: UntrustedFn> Op for Rel<F> { type In = (F::In, F::Out); type Out = bool; }
```

`Rel(f)` *is* `Lift(f)` — the graph of `f`. A pure total `F: CanonRule` also lifts
to `Rel`, its membership derivable from its functional `canon` equation; an impure
`F` is *only* a `Rel`.

**The execution rule — the one new trusted primitive (gated):**

```rust
/// Run untrusted `f` on ground input `a`. On `Ok(b)`, mint `⊢ a Rel(f) b` over
/// ZERO-COPY Arc-shared leaves. Gated on `Rel<F>`'s TypeId. NEVER mints falsity —
/// `Err`, or a different `b` next time, is simply unprovable.
pub fn execute<L: Language, F: UntrustedFn>(f: Rel<F>, a: F::In, lang: L)
    -> Result<Thm<L, App<Rel<F>, (Ref<Arc<F::In>>, Ref<Arc<F::Out>>)>>, Error>
where F::In: 'static, F::Out: 'static {
    let id = TypeId::of::<Rel<F>>();
    if !lang.admits(id) { return Err(Error::NotAdmitted(id)); }
    let b = f.0.run(&a).map_err(|e| Error::RuleFailed(format!("{e:?}")))?;
    Ok(Thm::new(lang, App(f, (Ref(Arc::new(a)), Ref(Arc::new(b))))))  // sole gate
}
```

`canon`'s sibling: same shape, same choke point, same `admits` gate — but mints
**graph membership** (`a R b`) over Arc-shared leaves, sound for *any* `f` (the
pair was observed), where `canon`'s functional equation is sound only for
deterministic total `f`. Each executable relation is a `Rel<F>` manifest entry.

**The soundness asymmetry:**

| direction | rule | soundness |
|---|---|---|
| `a R b` **true** from execution | `execute` (f returned b) | ✓ observed pair ∈ graph |
| `a R b` **true** from calculus | positive intro rules | ✓ monotone, true-from-true |
| `¬(a R b)` **false** | **none** | ✗ requires an **axiom** |

**The positive calculus** (monotone; each mints `true` from `true`):

```
transpose:  ⊢ a R b           ⟹ ⊢ b R° a          (iff — both directions sound)
join-L/R:   ⊢ a R b           ⟹ ⊢ a (R∪S) b
meet:       ⊢ a R b ∧ a S b   ⟹ ⊢ a (R∩S) b
compose:    ⊢ a R b ∧ b S c   ⟹ ⊢ a (R;S) c        (∃ witness b — still monotone)
```

These are the intro half of the allegory, realized as ordinary rules. They are
**ungated framework methods** on `Thm` (like `and_intro`) — sound in every `L`,
injecting no external trust (they only recombine proven positive facts).
**Complement `¬R`** and any *elimination* need a *negative* premise, so they are
**axiom-gated** and live outside the base TCB. The base's relation calculus is the
monotone Horn/allegory-intro fragment; falsity is entirely axiom-territory.
(Datalog/Datafun/allegory connection — `sketches/acset-datalog-datafun.md`.)

**North star #2 — WASM.** A WASM module is `Rel(WasmRun { module })`; `execute`
mints `⊢ input Rel(module) output` — trace certification, sound under
nondeterminism/traps by construction (a trap is `Err` ⇒ proves nothing).
Composition `;` chains module runs; correctness-of-compilation is a relational
inclusion (§4). Operands ride in zero-copy `Ref<Arc<_>>` leaves — no term
materialization, no buffer copy.

**North star #1 — content-addressing.** Three mechanisms, different copy
characteristics:

- **Interning (aspirational, MF3, NOT built).** One canonical `Arc` per O256 hash
  would make `Dyn`'s `Arc::ptr_eq` a sound *and complete* structural-equality
  decision. Today `Dyn::new` allocates fresh, so ptr_eq does *not* coincide with
  content equality; Phase 0/1 do not rely on it.
- **`Store : Rel<O256, Bytes>` (effectful) → `execute` mints the ZERO-COPY
  membership `⊢ addr Store blob`.** The only zero-copy form (MF2): the returned
  blob is seated behind one `Arc`. A store is *not* a function (a miss ≠ "absent";
  federated backings), so the relational reading is correct and a miss soundly
  proves nothing (needs a "this store is closed" axiom to conclude absence).
- **`Hash : Op<Bytes, O256>` (pure `CanonRule`) → `canon` mints the functional,
  rewritable `⊢ hash(blob) = h` — but NOT zero-copy (MF2).** `canon` owns a
  `Val<Bytes>` and deep-copies the blob (no "`canon` over `Ref<Arc>`" rule today),
  so the equation form costs an O(n) copy. A `canon`-over-`Ref<Arc>` variant is
  possible future work if a rewritable zero-copy hash equation is needed.

Content-addressing a *term* via the membership path (`execute` over a
`Rel<Serialize>`/`Rel<Blake3>`) runs over zero-copy `Ref<Arc<Term>>`/`Ref<Arc<Bytes>>`
leaves — addressed without walking a materialized tree *and* without copying the
blob (same "never materialize" laziness as EG2).

**What happens to Val / App / Dyn / CanonRule:**

- **`Val<C>` — retained as the primitive point**, *stated* to be the nullary op
  `Op<In=(), Out=C>` via a one-line bridge `Point<C> = dyn Op<In=(),Out=C>`. Not
  deleted (deletion is A's flag-day). Values and functions are uniformly `Op`,
  with `Val` the canonical nullary witness.
- **`App` — unchanged** (composition specialized to a point argument; general
  composition arrives with the calculus's `;`).
- **`Dyn<T>` — becomes the erased relation/point carrier**, the homogeneous type
  for heterogeneous collections (EG's deferred B2, now the home for a `Vec` of
  executed witnesses).
- **`CanonRule` — retained as the *functional* (deterministic-total) special
  case**; `Rel`/`execute` is the *relational* (general) case. `CanonRule ⟹ Rel`;
  the converse fails. Both stay; each serves a north star (canon → canonical hash;
  execute → effectful store / WASM).

### 2A-negation. The admitted-axiom discipline (F3) — a USER obligation

`execute` and any functionality/totality/closure axiom are **not "complementary by
construction"**; keeping them consistent is an explicit soundness obligation the
user discharges, and the framework does **not** enforce it:

- **`execute` grants ONLY positive facts, and is sound for ANY `f`** — including
  nondeterministic (`b` varies across calls) or partial (`Err`) `f`. Every minted
  `⊢ a Rel(f) b` records a pair that *was actually observed*; that pair is
  genuinely in the graph. The base can never mint falsity from `execute`.
- **Any NEGATIVE or UNIQUENESS conclusion requires an explicitly-admitted axiom** —
  `¬(a R b)`, functionality ("`b` is *the* output"), totality/closure ("`a` is out
  of domain") — a per-relation nullary `Rule` whose soundness is the user's burden.
- **They must be kept consistent BY THE USER.** If you `execute` a nondeterministic
  `f` into `R` *and* admit a functionality axiom for `R`, that axiom is simply
  **false** — admitting a false axiom is unsound (the user's error, like admitting
  `⊢ False`). The base cannot detect that your `f` is nondeterministic.

This is the sound reading of the deferred `Evaluate` seam: a disequality/decision
is an admitted axiom that a relation is functional/total/closed — never
auto-granted.

### 2B. `Ty` in the base — the **generic** reflected `TyRep` sort (F7, MF1)

Add a **generic reflected type-representation**. `Val<C>` is already generic, so
the base carries reflected type reps as `Val<C>` leaves **without ever naming a
concrete type** — the concrete `C` is chosen by the *consumer*. **The base CANNOT
name `core::Type`** (the hierarchy is base → core, so `type TyRep = core::Type` in
the base would be a circular dependency, MF1). `core` supplies `C = core::Type`;
the base stays generic. Type constructors are generic ops building `App` spines:

```rust
// GENERIC in the base — polymorphic in the reflected sort `T`. The base names NO
// concrete type. (`core` later fixes `type TyRep = core::Type`; Phase 0 uses an
// in-base demo stand-in `struct TyRepDemo(u32);` for `C`.)
pub struct TyFn<T>(PhantomData<T>);  impl<T: 'static> Op for TyFn<T>  { type In = (T, T); type Out = T; }  // →
pub struct TyApp<T>(PhantomData<T>); impl<T: 'static> Op for TyApp<T> { type In = (T, T); type Out = T; }  // type-op application
```

Distinct type reps are distinct `Val<C>` leaves, so `⊢ a = a'` between them is
meaningful: it holds via `of_eq` exactly when the two `C` values are `Eq`-equal,
and two *different* reps are not provably equal. Two payoffs:

- **Type equality/congruence come free from the existing calculus.**
  `⊢ TyFn(a,b) = TyFn(a',b')` from `⊢ a=a'`, `⊢ b=b'` by combining into a pair
  equation via `cong_pair`, then `cong_app` under `TyFn<C>` — no separate
  type-equality machinery (today `core` re-implements `Type`/`TypeKind` equality).
- **Leaf-elimination reuses the same symbolic mechanism** at the reflected sort:
  a rep enters as `Val<C>` or symbolically as a `TyFn`/`TyApp` spine; `eq_mp`/`trans`
  transport it without materializing the tree (B1 applied at the reflected sort).

**Scope note (F5).** `TyRep`/`TyFn`/`TyApp` are *ground first-order type TERMS*
(`App` spines over leaves) — the whole of `Ty`-in-base committed here. Type
*variables*, `TyAbs` binding, capture-avoiding `TyInst`, kind-checking are a binder
layer the base does NOT provide, deferred to Appendix A.

### 2C. HOL-ω middle — DEFERRED (F4/F5, Appendix A)

Everything about the HOL-ω *middle* — kinds, type-operator variables, rank-N type
quantification, `TyBeta`/`TyAbs`/`TyInst`/`TyAll`, the micro-Haskell front end — is
**out of committed scope** and moved to Appendix A, with its two hard prerequisites
(a required rank stratification for consistency; a real binder/kind middle layer
the ground base does not provide) stated plainly.

---

## 3. Honest TCB-delta accounting (F8) — gating ⊥ trust

**Manifest-gating is ORTHOGONAL to trust.** Every function calling `pub(crate)
Thm::new` is IN THE TCB and must be audited, *whether or not it is
manifest-gated* — exactly as `prop`'s `and_intro`/`or_inl`/`mp` are ungated yet
trusted mint sites. It is **wrong** to call the positive relation calculus "zero
trust / free". The honest delta:

| new mint site | gated? | trust character |
|---|---|---|
| `execute` (§2A) | **yes** — `admits(TypeId::of::<Rel<F>>())` | new *external-trust* rule; per-`Rel<F>` enumerated; audit that it mints only the observed pair |
| `transpose`/`compose`/`join`/`meet` (§2A) | **no** (ungated methods) | **TRUSTED-BUT-UNGATED** mint sites — in the TCB, audited like `and_intro`; each must be sound-in-every-`L` |
| per-relation functionality/totality/closure **axioms** (§2A-negation, §5.8) | **yes** — admitted `Rule` | user-admitted; soundness is the **user's** burden (F3) |

Base-TCB minimality is real but must be stated precisely: the positive calculus
adds *no manifest entries* and injects *no external trust*, but it *does* add
*audited-but-ungated `Thm::new` call sites*. Only `execute` and negation axioms are
*gated*; the positive operators are *ungated-yet-trusted*.

**EG5 subsumption.** The literal endgame's per-family symbolic landers
(`ToHolNat`/`Int`/`Bytes`/… each needing its own reify rule — the *float wall*)
dissolve: in B, every native value is `Val<C>` (a nullary op), symbolic-by-default;
`TyRep`-in-base extends it to type trees; `Dyn` (erased point/relation) is EG's
deferred B2 heterogeneous carrier. EG3–EG5 become *instances* of "Op/Val
unification + `TyRep`-in-base" — one mechanism, no per-family rules, no float wall.

**Coherence with the binding decisions:** base stays closed-world/enumerable
(`execute` manifest-listed per-`Rel<F>`, positive calculus ungated-auditable, no
opacity, `Thm::new` sole mint); "no disequalities" promoted to design invariant
(negative membership axiom-only, the `Evaluate` seam *defined* as an admitted
functional/total/closed axiom — a user obligation); `TyRep`-in-base is generic
(base never names `core::Type`; any "replace core's equality" step happens in
`core`, later).

---

## 4. Phase 0 — the concrete, additive, reversible slice

**Goal.** Prove end-to-end, with **zero change to existing base/core behavior**,
that: (i) an untrusted function's execution mints a positive membership witness and
*cannot* mint falsity — **including for a NONDETERMINISTIC or PARTIAL `f`** (F6);
(ii) both north stars are served (WASM-shaped + content-addressing runs) with
**O(1) materialized nodes AND O(1) copies** over large I/O (zero-copy
`Ref<Arc<_>>`, F1); (iii) the canon/execute duality holds; (iv) the positive
calculus (transpose) works as an ungated-but-trusted method; (v) `TyRep`-in-base
transports a type equation through the existing calculus. All through `Thm::new`;
delete nothing.

**New code (all additive):**

1. **`base/trusted/src/rel.rs`** (`lib.rs` gains `mod rel; pub use rel::*;`):
   `UntrustedFn`/`Rel`/`RelErr`; `execute<L,F>` (zero-copy `Ref<Arc<_>>` leaves,
   `F::In/Out: 'static`, gated on `TypeId::of::<Rel<F>>()`, mints via `Thm::new` —
   add one *gated* audited call-site line to `lib.rs`'s mint-site list **and extend
   the closed mint-site enumeration in the `eqn.rs` docstring**). **Transpose** as
   an ungated-but-trusted method (`struct Transpose<R>(R)` + `Thm::transpose`) —
   sound in every `L`, no manifest entry, **but still a `Thm::new` site ⇒ a TCB
   addition** (audit like `and_intro`; add one *ungated-trusted* line). Compose/
   join/meet are the same pattern; Phase 0 ships only `transpose`.
2. **`base/trusted/src/tyrep.rs`**: generic `TyFn<T>`/`TyApp<T> : Op<(T,T),T>`
   (F7, MF1). No rules — reps transport through the existing
   `refl`/`cong_pair`/`cong_app`; reps enter as `Val<C>` leaves. Commits to an
   **in-base demo stand-in `struct TyRepDemo(u32);`** as `C` (the base **CANNOT**
   name `core::Type`, MF1), so the module + tests build with no `core` dependency.
   Full `core::Type` integration lands later, in `core`.
3. **Tests** (`base/trusted/src/tests.rs`, or a `rel_tests` module). A demo
   `struct RelCalc;` whose manifest admits exactly `Rel<Blake3Fn>`, `Rel<AddModFn>`,
   `Rel<CoinFn>`, `Rel<PartialFn>`. Prove:
   - **`execute_nondeterministic_or_partial`** (MANDATORY, the test that
     *justifies* `execute`, F6) — a `CoinFn` returning different values across calls
     + a `PartialFn` returning `Err` on some inputs. Show: (a) both observed pairs
     mint true memberships (both in the graph), neither a functional equation;
     (b) functionality (`b₀ = b₁`) and negation are **not derivable**; (c) on a
     `PartialFn` `Err` input, `execute` mints **nothing**.
   - **`execute_witnesses_wasm_shaped`** — `AddModFn` (deterministic-total WASM
     stand-in); `execute` mints `⊢ (a,b) Rel(AddMod) c`; the *wrong* `c'` is not
     obtainable (the never-false asymmetry).
   - **`execute_content_address_O1_copies`** — `Blake3Fn: Bytes->O256` over
     `crates/lib/hash::Blake3`; a ≥1 MB blob; assert node count O(1), `Arc` strong
     count increments on transport, payload pointer unchanged (EG2 laziness).
   - **`canon_vs_execute_duality`** — the same Blake3 as a `CanonRule` mints the
     functional `⊢ hash(blob) = h` via `canon` (owning `Val<Bytes>`, *copies* the
     blob, MF2), contrasted with the effectful-store membership shape via `execute`.
   - **`transpose_positive`** — from `⊢ a R b` derive `⊢ b R° a`.
   - **`tyrep_in_base_transports`** — distinct reps `a ≠ a'` as `Val<TyRepDemo>`;
     `⊢ a = a'` ⟹ `⊢ TyFn(a,b) = TyFn(a',b)` by `cong_pair` then `cong_app`, no new
     rule; also assert `⊢ a = a'` between *distinct* reps is **not** derivable.

**Why reversible.** Two new files + a `mod`/`pub use` + audited mint-site lines
(one gated for `execute`, one ungated-trusted for `transpose` — both real TCB
additions per F8) + tests. No edit to the *behavior* of
`expr.rs`/`op.rs`/`eqn.rs`/`lang.rs`/`prop.rs`/`matching.rs`. The demo `RelCalc`
lives in tests (no production manifest change). Deleting the two files + `pub use`
+ tests returns the tree byte-identical.

---

## 5. Staged plan (additive first, collapse last)

- **Phase 0** (§4): `rel.rs` + `tyrep.rs` + the six tests (incl. the mandatory
  nondeterministic/partial test, F6). *The slice the orchestrator builds next.*
- **Phase 1** — the rest of the positive calculus (`compose`/`join`/`meet`) + a
  real `WasmRun` `UntrustedFn` over `crates/lib/wasm` and a `Store` `Rel` over
  `crates/store` (the two north stars, real backings). Each new operator is another
  audited `Thm::new` site.
- **Phase 2 (DEFERRED — Appendix A)** — the HOL-ω middle. Needs real binder/kind
  machinery (F5) and a consistency-critical rank discipline (F4); out of committed
  scope. Migrating `core` type-equality onto the base `TyRep` calculus (a ground
  first-order step) *is* in scope and independent of the HOL-ω binder layer.
- **Phase 3** — EG5 subsumption: drop `TermKind::{Nat,Int,SmallInt,Blob,Bool}`
  (values are `Val` nullary ops via one polymorphic embed; per-family reify rules +
  float wall dissolve). Maintainer-gated (irreversible).
- **Phase 4** — verified Haskell→WASM: compilation as a `Rel`, correctness as the
  relational inclusion `graph(compile ; wasm_eval) ⊆ graph(hol_eval)`, proved with
  `execute` witnesses.
- **Phase 5** (maintainer-gated, one-way door) — the full Op/Val **collapse**
  (Architect A): `Val` retired to the nullary-op `Point`, `Expr := Op<In=()>`,
  equality re-based on the diagonal relation. Only once Phases 0–4 prove the
  vocabulary; never forced.

Phases 0–2 are additive/reversible. Phase 3 (literal deletion) and Phase 5 (the
collapse) touch the innermost TCB irreversibly — both explicitly maintainer-gated.

---

## 5b. Open maintainer decisions

1. **Depth of Op/Val unification.** Keep `Val` as the primitive nullary point,
   state the `Op<(),C>` identity, bridge thinly; defer the full collapse to Phase 5.
2. **Positive calculus: ungated methods vs admitted rules.** Ungated framework
   methods (transpose/join/meet/compose are monotone, sound in every `L`); only
   `execute` and negation are gated. **But ungated ≠ untrusted** (F8) — each is a
   `Thm::new` site in the TCB, audited like `and_intro`.
3. **`execute` stays gated** (per-`Rel<F>` `admits`) — the WASM/store TCB stays
   enumerated.
4. **Nondeterminism semantics of `Rel(F)`** — the graph/membership reading; the
   functional equation is reserved for deterministic `CanonRule` ops. Consistency
   is a **user obligation** (F3).
5. **`TyRep` representation** — a generic reflected type-representation (`Val<C>`
   leaves + `TyFn<T>`/`TyApp<T> : Op<(T,T),T>`); the base names no concrete type
   (rejecting both a marker `Ty` with one inhabitant and a circular
   `type TyRep = core::Type`). Phase 0 uses `TyRepDemo(u32)`; `core::Type`
   integration lands later, in `core`.
6. **HOL-ω kind placement — DEFERRED** (F4/F5, Appendix A). The prior "kinds = base
   sorts, simpler than plain HOL" recommendation is **retracted**: the ground base
   has no binders, and HOL-ω needs a rank stratification for consistency.
7. **`execute` bounds** — `F::In/Out: 'static` (Arc-seated zero-copy leaf, not
   `Val`, not `Clone` over the payload); `Eq` only where used as a `trans`/`eq_mp`
   middle (`Ref<Arc<C>>` uses the `Arc`'s pointee `Eq`, or `ptr_eq` on a future
   interned store).
8. **Negation/`Evaluate` seam** — an admitted **axiom** that a relation is
   functional/total/closed, a per-relation `Rule` the **user** admits, never
   auto-granted. Where `¬(a R b)` and op-decision live (out of base TCB).

---

## Appendix A — HOL-ω middle (FUTURE / ASPIRATIONAL — NOT THIS PASS)

Out of committed scope (F4/F5). Recorded as a *direction*; two prerequisites gate
any future attempt.

**A.1 — Required soundness constraint: rank stratification (F4).** HOL-ω (Homeier's
HOL-Omega) adds a kind system, type-operator variables, and **type quantification**
(`TyAll`, `TyInst`). **Unrestricted impredicative type quantification is
INCONSISTENT over a HOL universe** (a type-in-type / Girard paradox). A future
HOL-ω design **MUST** impose a **rank stratification** on `TyAll`/`TyInst`, fully
specified and discharged, not waved through. Until then HOL-ω is not a sound middle.

**A.2 — Required machinery: a real binder/kind middle layer (F5).** The base
grammar is **ground, first-order, binder-free** — no variables, no binders, no
substitution. HOL-ω needs type variables, `TyAbs` binding, capture-avoiding
`TyInst` (substitution under binders), and kind-checking. **None comes "for free"
from the base** — it is genuine middle-layer machinery a future HOL-ω crate must
build. The earlier "kinds ARE base sorts / simpler than plain HOL" claims are
retracted (they conflated ground type *terms* with the binder/kind layer). The base
**DOES** give ground first-order type *terms* (`TyFn`/`TyApp` spines over `Val<C>`
leaves, equality/congruence free); it **DOES NOT** give any binder, type variable,
substitution, or kind judgement.

**A.3 — The direction.** Retarget the middle from plain HOL to HOL-ω, using the
base `TyRep` calculus for the ground type-term layer and building the binder/kind
layer (A.2) with the rank discipline (A.1) on top. Add `TyBeta`, `TyAbs`/`TyInst`
(kind-correct, capture-avoiding), rank-N `TyAll` intro/elim. A micro-Haskell
dialect maps ~directly, a typeclass becoming a rank-n dictionary over a type-operator
variable:

| micro-Haskell | HOL-ω (future) |
|---|---|
| type `T` | ground type term of sort `TyRep` |
| `Maybe :: * -> *` | type operator: a `ty⇒ty` constant — needs the kind layer (A.2) |
| `class Monad m` | dictionary type operator `Monad : (ty⇒ty)⇒ty` + `LawfulMonad` predicate |
| `instance Monad Maybe` | term `dict : Monad Maybe` + proof `⊢ LawfulMonad Maybe dict` |
| `f :: Monad m => a -> m a` | rank-N `f : ∀(m:ty⇒ty). Monad m → …` (a `TyAll` — needs A.1's ranks) |
| `do { x <- p; k x }` | `bind d p (λx. k x)` |

The big-vision endpoint — compile that Haskell to WASM, verified by the kernel — is
stated in the base relation calculus (§2A, Phase 4) and does not itself require
HOL-ω; the HOL-ω middle is the *typing* front end, deferred here.

---

*Audit provenance: this design closed an 8-finding HIGH adversarial audit (F1–F8:
zero-copy `Ref<Arc>` leaves; content-addressing = hash-consing not a hash op;
nondeterministic-execute admitted-axiom discipline; HOL-ω rank stratification as a
required constraint; HOL-ω binder/kind layer not "free"; mandatory
nondeterministic/partial Phase-0 test; coherent single `TyRep` representation; TCB
accounting ungated ≠ untrusted) plus a second pass (MF1: `type TyRep = core::Type`
was a circular base→core dep, now generic; MF2: zero-copy is `execute`-membership
only, `canon` copies; MF3: the interner is future work, not relied upon by
Phase 0/1). Git history on `relcalc-design` is the full record.*
