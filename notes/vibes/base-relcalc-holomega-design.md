# The relation-calculus base + HOL-ω middle — authoritative design

**Status:** AI-authored design panel (2026-07, branch `relcalc-design`, revised
to close an 8-finding HIGH audit, then a **second light pass** for three
precision/scoping findings (MF1–MF3) — see the revision log at the end). The
authoritative plan for the **base redesign**: a base that is a *calculus of
relations-as-untrusted-functions* with a reflected type-representation sort
`TyRep` as a first-class base sort. A HOL-ω middle is sketched as a **future
direction only** (deferred to Appendix A — *not this pass*). Records three
architect proposals, a judge scoring, the synthesized winner, and a **concrete,
additive Phase-0 spec** the orchestrator will build next.

**Committed scope of this design (binding):** base relation-calculus (`Rel`/
`execute` + the positive calculus) + `TyRep`-in-base. HOL-ω is explicitly
*out of committed scope* and lives only in Appendix A.

Companions it must stay coherent with: [`closed-world-kernel.md`](./closed-world-kernel.md)
(the realized base), [`literal-endgame-design.md`](./literal-endgame-design.md)
(EG1–EG5, the symbolic-operand mechanism this subsumes),
[`wasm-spec.md`](./wasm-spec.md) / [`wasm3-rust.md`](./wasm3-rust.md) (WASM prior
art), and the built code in `crates/kernel/base/trusted/src/`.

**Scope of this wave (binding):** design + illustrative sketches ONLY. **No
change to `base/trusted` or `core` TCB behavior.** Phase 0 (§6) is specified for
the orchestrator to implement as a *small, additive, reversible* slice; it is not
built here.

---

## 0. The two north stars (the judging axis)

Every base choice below is judged, above soundness alone, on whether it makes
these two **first-class AND efficient**:

1. **Content-addressing = hash-consing (interning) — the aspirational
   representation (MF3), not merely a hash op.** The *intended* native
   representation addresses every term by its O256 content hash:
   structurally-identical terms built separately are *deduplicated* and *shared* —
   one canonical `Arc` per content hash — an *interning/hash-consing
   representation* decision, not an operation you invoke. **This interning layer is
   NOT YET BUILT (MF3):** today `Dyn::new` does `Dyn(Arc::new(e))`
   (`expr.rs:160`) — a **fresh `Arc` per call** — so structurally-identical terms
   are *not* shared, and `Dyn`'s `Arc::ptr_eq` (`expr.rs:164-170`) does **not** yet
   coincide with content equality. The claim "`Dyn` ptr_eq = content equality"
   holds *only once* a content-hash-keyed interning layer is added; it is **future
   work and is NOT relied upon by Phase 0 or Phase 1** (see §3A). `Hash: Op<Bytes,
   O256>` (serialize-then-hash) is available today as the *computational witness*
   `⊢ hash(blob) = h` via `canon`. Data & terms are addressed by content hash
   without materializing a term tree.
2. **WASM** — a WASM module run is a *subset of untrusted relations*: executing
   it witnesses `input → output`, i.e. `a R b = true`.

The load-bearing observation that ties the *execution* half together: **both a
store lookup and a WASM run are untrusted functions whose *execution* supplies
positive facts and never negative ones.** Running a store lookup gives you
`addr ↦ blob` *if present*; running a WASM module gives you `a ↦ b` *if it
halts with `b`*. Neither can ever prove a *negative* — a store miss on one
backing says nothing (the blob may be on another), a non-halting module proves
nothing (halting problem). **The base is built around exactly this asymmetry.**
(The pure `Hash` op is the deterministic-total corner: its `canon` equation is a
genuine functional identity, unlike the store/WASM relations.)

---

## 1. The crux, stated against the real types

The base today (`crates/kernel/base/trusted/src/`) is a closed-world **equality**
kernel:

- `op.rs` — `trait Op: Any { type In; type Out; }`. Already the **function
  sort** the vision asks to "introduce": `Op<In,Out>`. Relations are "ops with
  `Out = bool`" (its own docstring says so). Open vocabulary; uninterpreted ⇒
  inert.
- `expr.rs` — sealed `trait Expr { type Ty; }`; leaf `Val<C>(C): Expr<Ty=C>`;
  `App<F:Op, A:Expr<Ty=F::In>>: Expr<Ty=F::Out>`; `Dyn<T>` (`Arc<dyn Expr>`,
  pointer-eq); `True`/`False`; tuples; faithful-pointer `Ref<P>`.
- `eqn.rs` — `Thm<L,P>` (`P: Expr<Ty=bool>`), **private fields, sole mint
  `pub(crate) Thm::new`**; the equality calculus (`refl`/`sym`/`trans`/
  `cong_app`/`cong_pair`/`eq_mp`); gated injectors `apply`/`canon`; `lift`.
- `lang.rs` — `trait Language` (`admits`/`extends`/`const MANIFEST`), `Rule<L>`
  (own-`TypeId` gate), `CanonRule: Op` (`eval -> Option<Out>`, mints the
  *functional* equation `App<F,Val(v)> = Val(eval(v))`).
- `prop.rs` — the ungated bool theory (`and_intro`/`mp`/…), sound in every `L`.

Three facts about this base decide the whole redesign (numbered *Fact 1–3* to
avoid collision with the audit findings F1–F8 used elsewhere in this doc):

- **Fact 1 — `Op<In,Out>` is already the function sort; `CanonRule` already
  executes ops.** `canon` runs `f.eval(v)` and mints a **functional** equation.
  What is *missing* is the **relational** (partial / effectful / nondeterministic)
  execution rule and the calculus over relations.
- **Fact 2 — `CanonRule` mints only a *functional* identity.** It cannot serve
  WASM or a federated store, which are *not* functions (nondeterministic / partial
  / present-on-some-backing). The relational reading `a R b` (b *is one* output of
  f on a) is sound where the functional reading `f(a)=b` is not.
- **Fact 3 — the base already proves *no disequalities*** (`closed-world-kernel.md`
  §"Leaf equality", the deferred `Evaluate` seam). The relational base **turns
  this bug into the load-bearing feature**: positive membership is native;
  negative membership (`¬(a R b)`) is axiom-only. The "no falsity" wall the old
  design apologized for is exactly the computability asymmetry WASM forces.

So the redesign is **not a rewrite of a mismatched base** — it is the base's own
`Op`/`CanonRule`/no-disequality trio *completed into a relation calculus*, plus
`Ty` promoted to a base sort, plus the middle retargeted to HOL-ω.

---

## 2. Architect A — full allegory collapse (aggressive)

**Thesis.** Take "unify Op/Val" literally: **delete `Val`, `App`, the sealed
`Expr` grammar; everything is an `Op`.** Define points as nullary ops
(`Point<C> := Op<In=(), Out=C>`), application as composition, and make the base a
genuine **allegory** (Freyd–Scedrov) / calculus of relations (Tarski):

- Objects = sorts (incl. base `Ty` terms). Morphisms = `Op<In,Out>`.
- A value of sort `C` is a point `() → C` (what `Val<C>` becomes).
- `Rel<In,Out> := Op<(In,Out), bool>`; `Lift : Op<In,Out> → Rel<In,Out>` is the
  graph functor.
- The **primitive** judgement is relational membership `a R b`, minted by:
  - **execution** (`f(a)=Ok(b) ⟹ ⊢ a Lift(f) b`), the only external-trust rule;
  - the **allegory operations** `;` (compose), `°` (transpose), `∩` (meet),
    `∪` (join), `¬` (complement) as intro rules.
- **Equality is recovered, not primitive**: `a = b` is `a Δ b` where `Δ` is the
  diagonal (coreflexive) relation; `refl`/`sym`/`trans`/`cong` are the
  *coreflexive sub-allegory* laws. So the current equality calculus becomes a
  *derived* corner of the relation calculus — maximal elegance and unification.

**North stars.** Served natively: hash/store/WASM are `Lift(f)` with the
execution rule; composition `Hash ; Store°`, transpose, etc. are base
vocabulary. Content-addressing = `Lift(hash)`; a store is a genuine (partial)
relation, not forced into a function.

**Ty-in-base.** Falls out: `Ty` is an object, type constructors are ops
`TyFn : Op<(Ty,Ty),Ty>`; kinds are objects, type operators are morphisms
`Op<Ty,Ty>`.

**Why it loses.** (1) **Not additive** — deleting `Val`/`App`/`Eqn` rebuilds the
entire minted calculus and every downstream crate (core, eval, init) in one
irreversible cut; there is *no* honest Phase-0. (2) **Re-derives equality as a
sub-allegory** — a large, subtle re-proof of the very calculus that already
works, for aesthetic gain. (3) **Thm::new audit churn** — every mint site moves.
The insight (equality = diagonal relation; the allegory is the true shape) is
**correct and worth recording as the limit**, but the vehicle is a
flag-day rewrite. **Graft the vocabulary, defer the collapse.**

---

## 3. Architect B — additive relational layer over the existing `Op` grammar (the winner)

**Thesis.** `Op<In,Out>` is *already* the function sort and `Val<C>` is *already*
the primitive point (`Op<(),C>` in spirit — a nullary op). So realize the Op/Val
"unification" as a **stated identity + a thin bridge**, and add the genuinely new
things — **relational execution** and the **relation calculus** — as an
*additive layer* that touches **zero existing behavior** and keeps `Thm::new` the
sole gate.

### 3A. Relation calculus base

**Membership needs no new grammar.** For a relation op `R : Op<(In,Out), bool>`,
the proposition `a R b` is just the existing `App<R, (leaf<In>, leaf<Out>)>`, an
`Expr<Ty=bool>`. A *proven* membership is a `Thm<L, App<R, (leaf,leaf)>>`. The
existing `prop.rs`/`eqn.rs` calculus transports it for free.

**Leaves are ZERO-COPY (`Ref<Arc<_>>`), not owned `Val` (F1).** The operand
leaves must be the Arc-shared `Ref<P: TrustedDeref>` (`expr.rs:55-64`; `Arc:
TrustedDeref` at `expr.rs:32`) — **never** owned `Val<C>` (`expr.rs:44`, which
holds `C` *by value*). This is load-bearing on the WASM/store hot path: a
megabyte input buffer or a store blob is seated as `Ref(Arc::new(buf))`, so the
buffer lives behind one `Arc`. Every calculus step that duplicates a leaf then
clones an **Arc handle, not the payload**: `refl` clones its leaf (`eqn.rs:116`)
and `cong_app` clones its op (`eqn.rs:192`) — for a `Ref<Arc<_>>` leaf that is a
refcount bump (O(1)), whereas for `Val<Buf>` it would deep-copy the whole buffer.
The relevant `execute` bound is therefore `F::In: 'static` / `F::Out: 'static`
(to seat behind `Arc` and satisfy `TrustedDeref`), **not** `F::In: Clone` over
the payload — nothing ever clones the payload. (`Ref<Arc<C>>` compares by the
`Arc`'s `Eq`, which compares pointees; on a *future* interned store — MF3, not
built yet — that pointee compare would degenerate to `Arc::ptr_eq`, see §0
hash-consing.)

**`Rel(F)` — the untrusted-function constructor** (analogue of `Val`, for
functions):

```rust
/// An untrusted, possibly effectful / partial / nondeterministic function.
/// `run` returning `Ok(b)` witnesses ONE pair `(a,b)` of the graph. Failure or a
/// different `b` on a re-run prove NOTHING.
pub trait UntrustedFn: Any { type In; type Out;
    fn run(&self, a: &Self::In) -> Result<Self::Out, RelErr>;
}

/// The GRAPH of `f`, as a relation-op. Writing `Rel(f)` is inert (uninterpreted);
/// only `execute` mints, and only the `true`/returned direction.
pub struct Rel<F: UntrustedFn>(pub F);
impl<F: UntrustedFn> Op for Rel<F> { type In = (F::In, F::Out); type Out = bool; }
```

**`Lift`** is definitional: `Rel(f)` *is* `Lift(f)` — the graph of the function
`f`. A pure total op `F: CanonRule` also lifts to `Rel`, and its membership is
*derivable* from its functional `canon` equation (see §3A-duality); an impure `F`
is *only* a `Rel`.

**The execution rule — the one new trusted primitive (gated):**

```rust
/// Run untrusted `f` on ground input `a`. On `Ok(b)`, mint `⊢ a Rel(f) b` over
/// ZERO-COPY Arc-shared leaves (= `App<Rel(f), (Ref(Arc(a)),Ref(Arc(b)))>`, a
/// bool prop). Gated on `Rel<F>`'s TypeId. NEVER mints falsity — `Err`, or a
/// different `b` next time, is simply unprovable.
pub fn execute<L: Language, F: UntrustedFn>(
    f: Rel<F>, a: F::In, lang: L,
) -> Result<Thm<L, App<Rel<F>, (Ref<Arc<F::In>>, Ref<Arc<F::Out>>)>>, Error>
where F::In: 'static, F::Out: 'static {
    let id = TypeId::of::<Rel<F>>();
    if !lang.admits(id) { return Err(Error::NotAdmitted(id)); }
    let b = f.0.run(&a).map_err(|e| Error::RuleFailed(format!("{e:?}")))?;
    // Seat both operands behind ONE Arc each — the buffer is never copied; every
    // downstream refl/cong clones only the Arc handle (a refcount bump).
    Ok(Thm::new(lang, App(f, (Ref(Arc::new(a)), Ref(Arc::new(b))))))  // sole gate: Thm::new
}
```

This is `canon`'s sibling: same shape, same single choke point, same `admits`
gate — but it mints **graph membership** (`a R b`) over Arc-shared leaves, which
is sound for *any* `f` (the pair was observed), where `canon`'s **functional
equation** (`f(a)=b`) is sound only for deterministic total `f`. Per-function TCB
stays enumerated: each executable relation is a `Rel<F>` entry in the language's
manifest. Note the operand-owning `Rel(f)` wraps `f` by value, but the *I/O
payloads* — the only large data — ride in `Ref<Arc<_>>`, so a megabyte-I/O run
still yields an O(1)-copy theorem whose every calculus transport bumps refcounts.

**The soundness asymmetry, made precise.**

| direction | rule | soundness |
|---|---|---|
| `a R b` **true** from execution | `execute` (f returned b) | ✓ observed pair ∈ graph |
| `a R b` **true** from calculus | positive intro rules below | ✓ monotone, true-from-true |
| `¬(a R b)` **false** | **none** | ✗ requires an **axiom** |

**The positive calculus** (monotone; each mints `true` from `true`; *no rule
mints falsity*):

```
transpose:  ⊢ a R b           ⟹ ⊢ b R° a          (iff — both directions sound)
join-L/R:   ⊢ a R b           ⟹ ⊢ a (R∪S) b
meet:       ⊢ a R b ∧ a S b   ⟹ ⊢ a (R∩S) b
compose:    ⊢ a R b ∧ b S c   ⟹ ⊢ a (R;S) c        (∃ witness b — still monotone)
```

These are the intro half of the allegory (§2), realized as ordinary rules. They
are **ungated framework methods** on `Thm` (like `and_intro`), because — exactly
like propositional logic — they are sound in *every* `L` and inject no external
trust (they only recombine already-proven positive facts). **Complement `¬R`**
and any *elimination* (from `a R b` conclude something false of another pair)
need a *negative* premise, so they are **axiom-gated** and live outside the base
TCB. This is the crisp statement of the north-star asymmetry: **the base's
relation calculus is the monotone Horn/allegory-intro fragment; falsity is
entirely axiom-territory.** (Datalog/Datafun/allegory connection —
`sketches/acset-datalog-datafun.md`: execution supplies the EDB, the positive
calculus is the IDB, negation/aggregation are the stratified/axiom layer.)

**North star #2 — WASM, made efficient & first-class.** A WASM module is
`Rel(WasmRun { module })` with `run(input) = execute the module`; `execute` mints
`⊢ input Rel(module) output` — trace certification, *sound under
nondeterminism/traps by construction* (a trap is `Err` ⇒ proves nothing; a
nondeterministic result is still a true graph member). Composition `;` chains
module runs; correctness-of-compilation is a relational inclusion (§5). The
operands ride in **zero-copy `Ref<Arc<_>>` leaves** (the input/output buffers) —
**no term materialization and no buffer copy** (F1), so a megabyte-I/O run mints
an O(1)-node theorem *and* every subsequent calculus step over it bumps an Arc
refcount rather than deep-copying the buffer.

**North star #1 — content-addressing, made efficient & first-class, and the
canon/execute duality (F2, MF2, MF3).** Content-addressing is served by three
mechanisms with **different copy characteristics** — stated honestly:

- **The interning representation (aspirational — the substance of "hashing =
  addressing", NOT yet built, MF3).** The *intended* term store keeps one
  canonical `Arc` per O256 content hash; building a structurally-identical term
  twice would return the *same* `Arc`, making `Dyn`'s `Arc::ptr_eq`
  (`expr.rs:164-170`) a sound *and complete* decision for structural equality.
  **This is future work:** `Dyn::new` currently allocates a fresh `Arc` per call
  (`expr.rs:160`), so ptr_eq does *not* yet coincide with content equality, and
  **Phase 0/1 do not rely on it.** Once built, this is where "hashing = addressing
  = hash-consing" lives — a representation decision, not a proof rule.
- **`Store : Rel<O256, Bytes>` (effectful `Rel`) → `execute` mints the
  ZERO-COPY membership `⊢ addr Store blob`.** This is the **only** zero-copy form
  (MF2): `execute` seats the returned blob behind one `Arc` in a `Ref<Arc<_>>`
  leaf, so the megabyte blob is never copied and every downstream `refl`/`cong`
  transport bumps a refcount. A store is *not* a function (a miss ≠ "absent";
  federated backings), so the relational reading is the *correct* one, and a miss
  soundly proves nothing (needs a "this store is closed" axiom to conclude
  absence — see §3A-negation, F3).
- **`Hash : Op<Bytes, O256>` (pure `CanonRule`) → `canon` mints the functional,
  rewritable equation `⊢ hash(blob) = h` — but this form is NOT zero-copy (MF2).**
  `canon` (`eqn.rs:331-345`) owns a `Val<Bytes>` operand and **deep-copies the
  blob** (there is no "`canon` over `Ref<Arc>`" rule today), so the equation form
  costs an O(n) copy of the blob — unlike the `execute` membership form. It
  certifies *which* O256 addresses a given blob (a genuine equation you can rewrite
  with), at the price of owning its operand. (A `canon`-over-`Ref<Arc>` variant, to
  make the *equation* form zero-copy too, is possible **future work** if a
  rewritable zero-copy hash equation is ever needed.)

Content-addressing a *term* via the **membership** path (`execute` over a
`Rel<Serialize>`/`Rel<Blake3>`) runs over zero-copy `Ref<Arc<Term>>`/
`Ref<Arc<Bytes>>` leaves (F1) — the term is addressed without walking a
materialized tree *and* without copying the blob. This is the same "never
materialize" laziness as EG2 (`literal-endgame-design.md` §7: the megabyte
`bytes.cat` operand with 2 materialized nodes), now the base's *native*
content-addressing path. (The functional-equation path via `canon` gives you a
rewritable `⊢ hash=h` but, as above, owns and **copies** its `Val<Bytes>` operand
— the non-zero-copy corner, MF2.) Once the interner (MF3) exists, the canonical
`Arc` a serialized term already lives behind is exactly the leaf the membership
mint reuses.

**What precisely happens to Val / App / Dyn / CanonRule (the Op/Val
unification).**

- **`Val<C>` — retained as the primitive point**, and *stated* to be the nullary
  op `Op<In=(), Out=C>`. A one-line bridge `Point<C> = dyn Op<In=(),Out=C>` (and
  a blanket letting a nullary op stand where a point-expr is expected) documents
  the identity; **`Val` is not deleted** (deleting it is Architect A's flag-day).
  The unification is *real but lazy*: values and functions are uniformly `Op`,
  with `Val` the canonical nullary witness.
- **`App` — unchanged.** It is composition specialized to a point argument;
  fully general composition arrives with the calculus's `;`.
- **`Dyn<T>` — becomes the erased relation/point carrier** (`Arc<dyn
  Op<In=(),Out=T>>` for points; `Arc<dyn Op<In=I,Out=bool>>` for relations),
  the homogeneous type for heterogeneous collections (this is EG's deferred B2,
  now the natural home for a `Vec` of executed witnesses).
- **`CanonRule` — retained as the *functional* (deterministic-total) special
  case**; `Rel`/`execute` is the *relational* (general) case. `CanonRule ⟹ Rel`
  (a pure op's graph membership is derivable from its functional equation);
  the converse fails. Both stay in the base; each serves a north star (canon →
  the canonical hash; execute → the effectful store / WASM).

### 3A-negation. The admitted-axiom discipline (F3) — a USER soundness obligation

`execute` and any functionality/totality/closure axiom are **not "complementary
by construction"**; keeping them consistent is an *explicit soundness obligation
the user discharges*, and the framework does **not** enforce it. State this
precisely:

- **`execute` grants ONLY positive facts, and is sound for ANY `f`** — including a
  `run` that is nondeterministic (returns different `b` for the same `a` across
  calls) or partial (`Err`/no output on some `a`). Every minted `⊢ a Rel(f) b`
  records a pair that *was actually observed*; that pair is genuinely in the graph
  no matter how erratic `f` is. The base can therefore never mint falsity from
  `execute`.
- **Any NEGATIVE or UNIQUENESS conclusion requires an explicitly-admitted axiom.**
  To conclude `¬(a R b)`, or "`b` is *the* output of `a`" (functionality), or "`a`
  is out of the domain" (totality/closure), you must *admit an axiom* — a
  per-relation nullary `Rule` (§8.8) whose soundness is the **user's burden**,
  exactly like admitting any other axiom.
- **The two must be kept consistent BY THE USER, and the framework does not check
  it.** If you populate a relation `R` via `execute` with a **nondeterministic**
  `f` (can return two different `b` for one `a`) *and* also admit a
  functionality/uniqueness axiom for `R`, that axiom is simply **false**, and
  admitting a false axiom is *unsound — the user's error*, indistinguishable from
  admitting `⊢ False`. The base does not, and cannot, detect that your `f` is
  nondeterministic; asserting functionality about it is your assertion, not the
  framework's guarantee.

So the discipline is: **`execute` = positive-only, always sound; negation/
uniqueness = admitted axiom, sound iff the user's `f` actually has the asserted
property.** This is an *admitted-axiom discipline*, not an enforced invariant. Do
not read the calculus as "the framework rules out inconsistency here" — it rules
out *forging* a theorem, and it makes falsity axiom-only, but the *truth* of a
functionality/closure axiom about an untrusted `f` is on the person who admits it.
(This is the sound reading of the deferred `Evaluate` seam of
`closed-world-kernel.md`: a disequality/decision is an admitted axiom that a
relation is functional / total / closed — never auto-granted.)

### 3B. `Ty` in the base — the **generic** reflected `TyRep` sort (F7, MF1)

Add a **generic reflected type-representation** to the base. `Val<C>` is already
generic (`expr.rs:44-49`), so the base carries reflected type reps as `Val<C>`
leaves **without ever naming a concrete type** — the concrete `C` is chosen by the
*consumer*. **The base CANNOT name `core::Type`** (the crate hierarchy is
covalence-pure/base → covalence-core, so `base/trusted` must not depend on
`core`; `type TyRep = core::Type` in the base would be a circular dependency,
MF1). `core`, building on the base, supplies `C = core::Type`; the base itself
stays fully generic. Concrete object-language types enter as `Val<C>` **leaves at
the reflected type-rep sort**, and type constructors are generic ops that build
`App` spines over that sort:

```rust
// GENERIC in the base: `TyFn`/`TyApp` are polymorphic in the reflected sort `T`.
// The base names NO concrete type. (Alternatively these ops may be defined in
// `core` fixed at `core::Type` — but they may NOT live in `base/trusted` bound to
// `core::Type`, which would invert the base→core dependency.)
pub struct TyFn<T>(PhantomData<T>);  impl<T: 'static> Op for TyFn<T>  { type In = (T, T); type Out = T; }  // →
pub struct TyApp<T>(PhantomData<T>); impl<T: 'static> Op for TyApp<T> { type In = (T, T); type Out = T; }  // type-op application

// The consumer instantiates the sort. `core` (later, not the base) does:
//   type TyRep = core::Type;   // then uses TyFn<TyRep> / TyApp<TyRep>
// Phase 0 uses an in-base demo stand-in `struct TyRepDemo(u32);` for `C`.
```

The representation is picked ONCE and used everywhere (resolves the audit's F7
contradiction — no "marker `Ty` with one inhabitant" competing with `Val` leaves,
and no `In`/`Out` clash, because constructor `In`/`Out` are uniformly the
reflected sort `T`). A concrete type rep enters as `Val<C>` at that sort;
`TyFn<C>`/`TyApp<C>` produce `App` spines whose sort is again `C`. Distinct type
reps are distinct `Val<C>` leaves, so `⊢ a = a'` between them is *meaningful*: it
holds via `of_eq` exactly when the two `C` values are `Eq`-equal (`eqn.rs:284`),
and two *different* type reps are not provably equal (leaf equality proves no
disequality, but it also does not spuriously equate distinct leaves). Two payoffs:

- **Type equality/congruence/symbolic-transport come *free* from the existing
  calculus at the reflected sort.** `⊢ TyFn(a,b) = TyFn(a',b')` from `⊢ a=a'` and
  `⊢ b=b'` by **first combining** the two argument equations into a pair equation
  `⊢ (a,b) = (a',b')` via `cong_pair` (`eqn.rs:210`), **then** applying `cong_app`
  (`eqn.rs:192`) under the op `TyFn<C>` — no separate type-equality machinery in
  the middle (a real simplification; today `core` re-implements `Type`/`TypeKind`
  equality). Note `cong_app` clones the *op* `TyFn<C>` (cheap ZST), transporting
  the combined argument equation.
- **Leaf-elimination reuses the *same* symbolic mechanism at the reflected sort.**
  A concrete type rep enters as `Val<C>` *or* symbolically as the `TyFn<C>`/
  `TyApp<C>` spine over `Val<C>` leaves; `eq_mp`/`trans` transport it without
  materializing the tree — B1 (`literal-endgame-design.md`) applied at the
  reflected sort instead of `Term`. §5's EG5-subsumption note shows this subsumes
  the endgame.

**Scope note (F5).** `TyRep`, `TyFn`, `TyApp` are *ground first-order type
TERMS* — `App` spines over leaves, which the base grammar (`expr.rs`) fully
supports. They are the whole of `Ty`-in-base committed by THIS design. Type
*variables*, `TyAbs` binding, capture-avoiding `TyInst`, and kind-checking are a
**binder layer the base does NOT provide** and are deferred to the future
appendix (§A).

### 3C. HOL-ω middle — DEFERRED, NOT IN THIS PASS

**HOL-ω is scoped OUT of this design's committed scope (F4/F5).** The committed
scope of THIS design is *base relation-calculus + `TyRep`-in-base only* (§3A,
§3B). Everything about the HOL-ω *middle* — the kind system, type-operator
variables, rank-N type quantification, the `TyBeta`/`TyAbs`/`TyInst`/`TyAll`
rules, and the micro-Haskell front end — is **future / aspirational** and moved
to **Appendix A** (at the end of this doc). It is retained there as a direction,
with its two hard prerequisites stated plainly (a required rank stratification for
consistency; a real binder/kind middle layer the ground base does not provide)
rather than hand-waved as "free".

---

## 4. Architect C — relations in the middle, base stays a pure equality kernel (minimal-base)

**Thesis.** Keep the base the tiny equality kernel it is; put `Rel`, `execute`,
WASM, and content-addressing in the **middle** (HOL-ω), where a relation is a
*defined* HOL-ω type `In → Out → bool` and WASM execution is an admitted
*middle* rule. Base TCB stays minimal; the relation calculus is object-level HOL.

**Why it loses.** It **fails both north stars' "first-class in the *base*"
requirement.** If execution and hashing are middle rules, then (a) content-
addressing and WASM are *not* base primitives — a store/WASM proof drags in the
whole HOL-ω TCB even when no logic is involved; (b) the true/never-false
asymmetry is a *middle* property, not a *base* guarantee, so a second logic
(ACL2, ZFC) built on the base re-derives it; (c) the maintainer explicitly wants
the base to *be* the relation calculus (execution witnesses are the base's job).
C's genuine contribution — **keep the base TCB minimal** — is real and grafted:
the *positive calculus is ungated* (adds nothing to the manifest), and *only*
`execute` (per-function, enumerated) and axiom-gated negation touch trust. But
relations belong in the base. **Reject the placement, graft the minimalism.**

---

## 5. Judge — scoring and synthesis

Scores 1–5 (higher better), on the mission's axes.

| axis | A allegory-collapse | **B additive rel-layer** | C rel-in-middle |
|---|---|---|---|
| north stars served effectively & efficiently | 5 | **5** | 2 |
| soundness rigor (true/never-false + Op/Val unification, `Thm::new` sole gate) | 4 | **5** | 4 |
| base-TCB minimality | 3 | **5** | 5 |
| (future) HOL-ω/Haskell direction — *Appendix A only, not scored for this pass* | 4 | **5** | 4 |
| EG5 subsumption | 4 | **5** | 3 |
| migration realism (additive, reversible, real Phase 0) | 1 | **5** | 4 |
| **total** | 21 | **30** | 22 |

(The HOL-ω/Haskell row reflects each proposal's *future* fit; HOL-ω is deferred
to Appendix A and is **not** part of this design's committed scope — see F4.)

**Winner: B**, grafting:

- **from A**: the **allegory / calculus-of-relations vocabulary** (`Lift`, `;`,
  `°`, `∩`, `∪`, `¬`) and the **"equality = diagonal relation"** insight — kept
  as the *documented limit* the lazy Op/Val unification converges to, and the
  vocabulary B's positive calculus already realizes as intro rules.
- **from C**: **base-TCB minimalism** — the positive relation calculus is
  *ungated* framework methods (zero manifest entries, sound in every `L`); only
  `execute` (per-`Rel<F>`, enumerated) and axiom-gated negation are trusted
  additions.

**Why B is sound and additive (no fork).** It adds **zero** to existing base
behavior: `Val`/`Ref`/`App`/`Eqn`/`CanonRule`/the equality & bool calculus are
untouched; `execute` is a new gated mint through the *same* `Thm::new` choke
point as `canon`; the positive calculus is new methods. The Op/Val unification is
*stated* (Val = the nullary op) and *bridged* thinly, with the full collapse
(delete `Val`, `Expr := Op<(),_>`) deferred to a maintainer-gated stage — A's
flag-day is never forced. Soundness rests on `admits()` for the *gated* additions
plus **audit of every new `Thm::new` call site** (see the honest TCB-delta
below).

### Honest TCB-delta accounting (F8) — gating ⊥ trust

**Manifest-gating is ORTHOGONAL to trust.** Every function that calls the
`pub(crate) Thm::new` mint (`eqn.rs:73`) is IN THE TCB and must be audited,
*whether or not it is manifest-gated* — exactly as `prop`'s `and_intro`/`or_inl`/
`mp` are ungated yet trusted mint sites listed among the audited call sites at
`lib.rs:11-16` (`prop.rs:40-89`). It is therefore **wrong** to call the positive
relation calculus "zero trust / costless / trivially green because only `execute`
and negation are gated." The honest delta this design adds to the base TCB:

| new mint site | gated? | trust character |
|---|---|---|
| `execute` (§3A) | **yes** — `admits(TypeId::of::<Rel<F>>())` | new *external-trust* rule; per-`Rel<F>` enumerated; audit that it mints only the observed pair |
| `transpose` / `compose` / `join` / `meet` (positive calculus, §3A) | **no** (ungated methods) | **TRUSTED-BUT-UNGATED** mint sites — *in the TCB*, audited like `and_intro`; each must be sound-in-every-`L` (monotone, true-from-true, mints no falsity) |
| per-relation functionality/totality/closure **axioms** (§3A-negation, §8.8) | **yes** — admitted `Rule` | user-admitted; soundness is the **user's** burden (F3) |

So the base-TCB minimality claim is real but **must be stated precisely**: the
positive calculus adds *no manifest entries* and injects *no external trust*, but
it does add *audited-but-ungated `Thm::new` call sites* to the TCB — a genuine
(small, monotone, auditable) TCB cost, not "free." Only `execute` and the
negation axioms are *gated*; the positive operators are *ungated-yet-trusted*.
Each of these lines is a new entry in the crate-root audited-mint-site list
(`lib.rs:11-16`) when built.

**EG5 subsumption (axis it wins on).** The literal endgame's per-family symbolic
landers (`ToHolNat`/`Int`/`Bytes`/… each needing its own reify rule — the **float
wall**, `literal-endgame-design.md` §7) **dissolve**: in B, every native value is
`Val<C>` (a nullary op), symbolic-by-default; `TyRep` in the base extends the same
mechanism to type trees; `Dyn` (erased point/relation) is EG's deferred B2, now
the natural heterogeneous carrier. EG3–EG5 become *instances* of "Op/Val
unification + `TyRep`-in-base," not a separate ladder — one mechanism, no
per-family rules, no float wall.

### Coherence with the binding maintainer decisions (closed-world-kernel + EG)

- Base stays **closed-world / enumerable**: `execute` is a manifest-listed
  per-`Rel<F>` rule; the positive calculus is ungated (auditable as framework
  methods). No opacity, `Thm::new` still the sole mint.
- **No disequalities in the base** (today's state) is *promoted to the design
  invariant*: negative membership is axiom-only. The deferred `Evaluate`/decision
  seam is now *defined* as "an admitted axiom that a relation is
  functional/total/closed" — a **user** obligation, never auto-granted (F3).
- **`TyRep`-in-base** provides a **generic** reflected type-rep calculus (`Val<C>`
  leaves + generic `TyFn<T>`/`TyApp<T>` ops) that the base uses **without naming
  `core::Type`** (MF1 — base → core, never the reverse). Eventually `core` could
  reuse this calculus for its own `Type`/`TypeKind` equality — but that migration
  is **`core`-side and aspirational**, not committed here (the base cannot "reach
  into" `core`; any "replace core's equality" step happens in `core`, later). This
  is a *ground first-order* type-term layer only; the binder/kind layer is deferred
  (F5, §A).

---

## 6. PHASE 0 — the concrete, additive, reversible de-risking slice

**Goal.** Prove end-to-end, with **zero change to existing base/core behavior**,
that: (i) an untrusted function's *execution* mints a positive membership witness
and *cannot* mint falsity — **including for a NONDETERMINISTIC or PARTIAL `f`**,
the case that actually justifies `execute`'s existence (F6); (ii) both north stars
are served — a WASM-shaped run and a content-addressing run — with **O(1)
materialized nodes AND O(1) copies** over large I/O (zero-copy `Ref<Arc<_>>`
leaves, F1); (iii) the canon/execute duality holds (functional hash vs. effectful
store); (iv) the positive calculus (transpose) works as an ungated-but-trusted
method; (v) `TyRep`-in-base transports a type equation through the *existing*
calculus. All through `Thm::new`. Delete **nothing**.

**New code (all additive; existing files unchanged in behavior).**

1. **`crates/kernel/base/trusted/src/rel.rs`** (new module; `lib.rs` gains
   `mod rel; pub use rel::*;`):
   - `trait UntrustedFn: Any { type In; type Out; fn run(&self, a:&In) -> Result<Out, RelErr>; }`
   - `struct Rel<F: UntrustedFn>(pub F); impl<F> Op for Rel<F> { In=(F::In,F::Out); Out=bool; }`
   - `enum RelErr { Refused, Trapped(String), … }` (untrusted error, no trust).
   - `pub fn execute<L,F>(f: Rel<F>, a: F::In, lang: L) -> Result<Thm<L, App<Rel<F>,(Ref<Arc<F::In>>,Ref<Arc<F::Out>>)>>, Error>`
     where `F::In: 'static, F::Out: 'static` — **zero-copy leaves** (F1): seats
     both operands behind one `Arc` each (never copies the payload); gated on
     `TypeId::of::<Rel<F>>()`, mints via `Thm::new` (add one audited call-site
     line — a *gated* mint — to the `lib.rs:11-16` mint-site list, **and extend the
     closed mint-site enumeration in the `eqn.rs:7-9` docstring** — a new `rel`
     module now mints, so that "every call site is audited" set must name it; nit
     ii).
   - **Transpose** as an ungated-but-trusted method: define `struct
     Transpose<R>(R)` (a relation-op with swapped input) and
     `impl<L,R,A,B> Thm<L, App<R,(A,B)>> { pub fn transpose(self) -> Thm<L, App<Transpose<R>,(B,A)>>; }`
     — sound in every `L` (recombines a proven positive fact), no manifest entry,
     **but still a `Thm::new` call site ⇒ a TCB addition** (audited like
     `and_intro`; add one *ungated-trusted* line to the `lib.rs:11-16` list, F8,
     **and to the `eqn.rs:7-9` closed mint-site enumeration**, nit ii).
     (Compose/join/meet are the same pattern; Phase 0 ships only `transpose` to
     stay minimal, and documents the rest.)

2. **`crates/kernel/base/trusted/src/tyrep.rs`** (new module): the **generic**
   constructor ops `TyFn<T>`/`TyApp<T> : Op<In=(T,T), Out=T>` (F7, MF1). No rules
   — type reps transport through the *existing* `refl`/`cong_pair`/`cong_app`;
   concrete type reps enter as `Val<C>` leaves at the reflected sort. **Phase 0
   commits to an in-base concrete demo stand-in `struct TyRepDemo(u32);`** as `C`
   — the base **CANNOT** name `core::Type` (hierarchy is base → core, not the
   reverse; MF1), so the module + tests build in-base with **no `core`
   dependency**, exercising the identical `App`-spine transport at
   `TyFn<TyRepDemo>`. Full `core::Type` integration (`core` supplying `C =
   core::Type`, defining `type TyRep = core::Type`) is a **later step in `core`**,
   not Phase 0. The *representation decision* — leaves at one reflected generic
   sort, constructors `Op<(T,T),T>` — is what Phase 0 pins.

3. **Tests — `crates/kernel/base/trusted/src/tests.rs`** (append; or a new
   `rel_tests` module). A demo `struct RelCalc;` `impl Language for RelCalc` whose
   manifest admits exactly `Rel<Blake3Fn>`, `Rel<AddModFn>`, `Rel<CoinFn>`,
   `Rel<PartialFn>` (the enumerated new trust). Prove:
   - **`execute_nondeterministic_or_partial`** (MANDATORY — the test that
     *justifies* `execute`, F6) — `CoinFn: () -> u64` whose `run` returns a
     *different* value on successive calls (nondeterministic), and `PartialFn:
     u64 -> u64` whose `run` returns `Err(RelErr::Refused)` on some inputs
     (partial). Show: (a) `execute` on `CoinFn` still soundly mints `⊢ () Rel(Coin)
     b₀` for the *actually observed* `b₀`, and a *second* run observing `b₁ ≠ b₀`
     mints `⊢ () Rel(Coin) b₁` — **both true** (both pairs are in the graph),
     neither a functional equation; (b) you **cannot** derive functionality
     (`b₀ = b₁`) or any negation from these — there is no rule that mints it
     (§3A-negation) — so `canon`'s functional equation would here be *unsound*
     while `execute`'s membership is *sound*; (c) on a `PartialFn` input where
     `run` returns `Err`, `execute` returns `Err` and mints **nothing** — a
     partial `f` proves no absence. This is the property the whole design rests on,
     machine-checked.
   - **`execute_witnesses_wasm_shaped`** — `AddModFn: (u64,u64)->u64` (a
     deterministic-total stand-in for a WASM run); `execute` mints `⊢ (a,b)
     Rel(AddMod) c`; assert the *wrong* `c'` is **not** obtainable (no `execute`
     path, no falsity rule) — the never-false asymmetry, machine-checked.
   - **`execute_content_address_O1_copies`** — `Blake3Fn: Bytes->O256` wrapping
     `crates/lib/hash::Blake3`; feed a ≥1 MB blob; `execute` mints `⊢ blob
     Rel(Blake3) h`; a node-counting walk over the prop `Expr` returns **O(1)**,
     and the blob & hash sit in `Ref<Arc<_>>` leaves (F1) so a `refl`/`cong`
     transport of the theorem bumps a refcount rather than copying the megabyte —
     the content-addressing north star + EG2 laziness, machine-checked (assert the
     `Arc` strong-count increments, payload pointer unchanged).
   - **`canon_vs_execute_duality`** — the *same* Blake3 as a pure `CanonRule`
     mints the **functional** `⊢ hash(blob) = h` via `canon`; contrast with the
     effectful-store **membership** shape via `execute`. Documents which north
     star each mechanism serves — and that `canon` owns its `Val<Bytes>` and
     **copies** the blob, so only the `execute` membership form is zero-copy (MF2).
   - **`transpose_positive`** — from `⊢ a R b` derive `⊢ b R° a` by the
     ungated-but-trusted method.
   - **`tyrep_in_base_transports`** — with distinct type reps `a ≠ a'` as
     `Val<TyRepDemo>` leaves (the in-base demo `C`, MF1), `⊢ a = a'` ⟹
     `⊢ TyFn(a,b) = TyFn(a',b)` by combining via `cong_pair` then `cong_app` (nit
     i), with **no new rule** — the `TyRep`-in-base foothold. Also assert
     `⊢ a = a'` between *distinct* reps is **not** derivable (leaf equality via
     `of_eq` only fires when the two `TyRepDemo` values are `Eq`-equal), so the
     equation is *meaningful* (F7).

**What it proves.** The base natively mints WASM/content-addressing execution
witnesses (positive-only, **sound even under nondeterminism/partiality** — the F6
test), efficiently (O(1) nodes *and* O(1) copies via `Ref<Arc<_>>`), through the
sole `Thm::new` gate, with the positive calculus and `TyRep`-in-base working off
the *existing* machinery — de-risking every load-bearing claim of §3 in one small
slice.

**Why reversible & zero-behavior-change.** Two new files + a `mod`/`pub use` +
**audited mint-site lines** (one *gated* for `execute`, one *ungated-trusted* for
`transpose` — both real TCB additions per F8) + test additions. No edit to the
*behavior* of `expr.rs`/`op.rs`/`eqn.rs`/`lang.rs`/`prop.rs`/`matching.rs`.
`Val`/`Ref`/`App`/`Thm`/`CanonRule` untouched; the Op/Val collapse is **not**
attempted in Phase 0. The demo `RelCalc` language lives in tests, so **no
production manifest changes**. Deleting `rel.rs`/`tyrep.rs` + their `pub use` +
the tests returns the tree byte-identical. Fully additive — but note "the fmt/
deps gate is green" is **not** the same as "no TCB delta": the two new mint sites
*are* audited TCB additions (F8), just small and monotone.

---

## 7. Staged plan (additive first, collapse last)

- **Phase 0** (§6): `rel.rs` (`UntrustedFn`/`Rel`/`execute`/`transpose`) +
  `tyrep.rs` + the six tests (incl. the mandatory nondeterministic/partial test,
  F6). Additive, reversible. *The slice the orchestrator builds next.*
- **Phase 1** — the rest of the positive calculus (`compose`/`join`/`meet` as
  ungated-but-trusted methods) + a real `WasmRun` `UntrustedFn` over
  `crates/lib/wasm` and a `Store` `Rel` over `crates/store` (the two north stars,
  real backings). Additive. Each new operator is another audited `Thm::new` site
  (F8).
- **Phase 2 (DEFERRED — Appendix A, not this pass)** — the HOL-ω middle:
  kinds-as-sorts, type-operator ops, the `TyBeta`/`TyAbs`/`TyInst`/`TyAll` rules,
  the required rank stratification, and the micro-Haskell front end. This needs
  real binder/kind middle machinery the ground base does not provide (F5) and a
  consistency-critical rank discipline (F4); it is **out of committed scope** and
  specified only as a direction in Appendix A. Migrating `core` type-equality onto
  the base `TyRep` calculus (a ground-first-order step) *is* in scope and can
  happen independently of the HOL-ω binder layer.
- **Phase 3** — EG5 subsumption: drop `TermKind::{Nat,Int,SmallInt,Blob,Bool}`
  (values are `Val` nullary ops reached through a single polymorphic embed; the
  per-family reify rules + float wall dissolve). Maintainer-gated (irreversible).
- **Phase 4** — verified Haskell→WASM: compilation as a `Rel`, correctness as the
  relational inclusion `graph(compile ; wasm_eval) ⊆ graph(hol_eval)`, proved
  with `execute` witnesses. The big vision.
- **Phase 5** (maintainer-gated, one-way door) — the full Op/Val **collapse**
  (Architect A): `Val` retired to the nullary-op `Point`, `Expr := Op<In=()>`,
  equality re-based on the diagonal relation. Only once Phases 0–4 have proven
  the vocabulary; never forced.

**One-way-door note.** Phases 0–2 are additive/reversible. Phase 3 (literal
deletion) and Phase 5 (the collapse) touch the innermost TCB irreversibly — both
explicitly maintainer-gated, out of the additive track.

---

## 8. Open maintainer decisions

1. **Depth of Op/Val unification.** Recommend: **keep `Val` as the primitive
   nullary point**, *state* the `Op<(),C>` identity, bridge thinly; defer the
   full collapse (delete `Val`) to Phase 5. (Alternative: commit to A now —
   rejected as a flag-day.)
2. **Positive calculus: ungated methods vs. admitted rules.** Recommend
   **ungated framework methods** (transpose/join/meet/compose are monotone,
   sound in every `L`); only `execute` and negation are *gated*. **But be honest
   (F8): ungated ≠ untrusted** — each is a `Thm::new` call site *in the TCB*,
   audited like `and_intro`. "Base-TCB minimalism" means *no manifest entries and
   no external trust*, **not** "zero TCB delta." Confirm the ungated-but-trusted
   framing.
3. **`execute` must stay gated** (per-`Rel<F>` `admits`) — the WASM/store TCB
   stays enumerated. Confirm.
4. **Nondeterminism semantics of `Rel(F)`.** Recommend the **graph/membership**
   reading (any observed output ∈ graph; `execute` never mints a functional
   equation); reserve the functional equation for deterministic `CanonRule` ops
   (hash). **Consistency is a USER obligation (F3):** if you `execute` a
   nondeterministic `f` into `R` you must **not** also admit a functionality axiom
   for `R` — doing so admits a false axiom (the user's error). Confirm this is the
   intended WASM/store semantics *and* the admitted-axiom discipline.
5. **`TyRep` representation (F7, MF1).** Recommend a **generic reflected
   type-representation**: the base carries type reps as `Val<C>` leaves and
   provides generic constructors `TyFn<T>`/`TyApp<T> : Op<(T,T),T>` building `App`
   spines — **the base names no concrete type**; the consumer picks `C` (`core`
   supplies `C = core::Type`; the base CANNOT depend on `core`, so it stays
   generic). This is the *single* coherent representation — **rejecting** both a
   marker `Ty` with one inhabitant (no distinguishable reps) and a base-level
   `type TyRep = core::Type` / `TyFn::In=(core::Type,core::Type)` (a **circular
   base→core dependency**, MF1). §3B, §6, and this decision now all agree. Distinct
   `Val<C>` leaves are distinguishable, so `⊢ a = a'` between type reps is
   meaningful. Phase 0 uses a demo `TyRepDemo(u32)` for `C`; `core::Type`
   integration lands later, in `core`.
6. **HOL-ω kind placement — DEFERRED (F4/F5, Appendix A).** *Not decided in this
   pass.* The prior recommendation ("kinds = base sorts, no new middle machinery,
   simpler than plain HOL") is **retracted**: the ground base has no binders, so
   type variables / `TyAbs` / capture-avoiding `TyInst` / kind-checking are real
   deferred middle machinery, and HOL-ω needs a rank stratification for
   consistency. Reopen when HOL-ω is actually designed.
7. **`execute` bounds (F1).** `F::In: 'static`, `F::Out: 'static` (to seat behind
   `Arc` in a `Ref<Arc<_>>` **zero-copy** leaf — *not* `Val`, and *not* `F::In:
   Clone` over the payload; nothing clones the payload). `Eq` on operands only
   *where used as a `trans`/`eq_mp` middle* ("no Eq, no comparison"), and for
   `Ref<Arc<C>>` that middle-match uses the `Arc`'s pointee `Eq` (or `ptr_eq` on an
   interned store). Pin the exact bounds at implementation.
8. **Negation/`Evaluate` seam (F3).** The deferred disequality seam becomes "an
   admitted **axiom** that a relation is functional / total / closed" — a
   per-relation `Rule` the **user** admits, whose soundness is the user's burden,
   **never auto-granted** by the framework. This is where `¬(a R b)` and
   op-decision live (out of base TCB). Confirm the admitted-axiom placement.

---

## Appendix A — HOL-ω middle (FUTURE / ASPIRATIONAL — NOT THIS PASS)

**This appendix is out of the committed scope of this design (F4/F5).** The
committed scope is base relation-calculus + `TyRep`-in-base (§3A, §3B). What
follows is a *direction* for a later HOL-ω middle-language design, recorded so the
idea is not lost — **not** a specification to build now. Two prerequisites, stated
plainly, gate any future attempt; neither is "free from the base."

### A.1 — Required soundness constraint: rank stratification (F4)

HOL-ω (Homeier's HOL-Omega) extends HOL with a kind system, type-operator
variables, and **type quantification** (`TyAll`, `TyInst`). **Unrestricted
impredicative type quantification is INCONSISTENT over a HOL universe** (a
type-in-type / Girard-style paradox). So a future HOL-ω design **MUST** impose a
**rank stratification** on `TyAll`/`TyInst` — restricting which type quantifiers
may instantiate at which rank — as a *required soundness constraint*, fully
specified and discharged, not named as a "feature" and waved through. Until that
stratification is designed and proved to block the paradox, HOL-ω is **not** a
sound middle. (Homeier's system fixes ranks precisely for exactly this reason; any
port inherits that obligation.)

### A.2 — Required machinery: a real binder/kind middle layer (F5)

The base grammar (`expr.rs`) is **ground, first-order, and binder-free** — there
are **no variables, no binders, and no substitution** anywhere in it. HOL-ω needs
all of:

- **type variables** (a `TyVar` notion — absent from the ground base),
- **`TyAbs` binding** (type-operator abstraction — a binder the base lacks),
- **capture-avoiding `TyInst`** (type-operator instantiation — substitution under
  binders, which the base has no machinery for), and
- **kind-checking** (a judgement stratifying `ty`, `ty⇒ty`, … — a checker the
  base does not run).

**None of this comes "for free" from the base.** It is genuine middle-layer
machinery — a binder representation (de Bruijn / locally-nameless), a
capture-avoiding substitution, a kind-checker — that a future HOL-ω crate must
build. The earlier draft's claims that "kinds ARE base sorts, no new middle
machinery" and that HOL-ω is "simpler than plain HOL" are **retracted**: they
conflated *ground type TERMS* with the *binder/kind layer*.

**What the base DOES give (and what it does not):**

- **DOES:** ground first-order type *terms* — `TyFn<C>(a,b)`, `TyApp<C>(f,x)` as
  `App` spines over generic `Val<C>` reflected-sort leaves (MF1; `core` later
  picks `C = core::Type`), with equality/congruence for free from the existing
  calculus (§3B). This is real and in scope.
- **DOES NOT:** any binder, any type variable, any substitution, any kind
  judgement. These are the HOL-ω-specific middle layer, deferred here.

### A.3 — The direction (unchanged in spirit, now correctly scoped)

Retarget the middle from plain HOL to HOL-ω, using the base `TyRep` calculus for
the *ground* type-term layer and building the binder/kind layer (A.2) with the
rank discipline (A.1) on top. Rule delta vs the current CoreLang: Group A
(equality/congruence) reuses the base equality calculus at `TyRep` and `Term`;
add `TyBeta` (type-operator reduction), `TyAbs`/`TyInst` (kind-correct,
capture-avoiding), and rank-N `TyAll` intro/elim — **all built on the deferred
binder layer**, none inherited from the ground base.

**Micro-Haskell → HOL-ω (the `Monad` worked example)** — the eventual payoff: a
micro-Haskell dialect maps ~directly to HOL-ω, with a typeclass as a **rank-n
dictionary over a type-operator variable**, which HOL-ω's kind system + universal
types express directly.

| micro-Haskell | HOL-ω (future) |
|---|---|
| type `T` | ground type term of sort `TyRep` |
| `Maybe :: * -> *` | type operator: a `ty⇒ty` constant — needs the *kind* layer (A.2) |
| `class Monad m` | dictionary type operator `Monad : (ty⇒ty)⇒ty` + `LawfulMonad` predicate |
| `instance Monad Maybe` | term `dict : Monad Maybe` + proof `⊢ LawfulMonad Maybe dict` |
| `f :: Monad m => a -> m a` | rank-N `f : ∀(m:ty⇒ty). Monad m → …` (a `TyAll` type — needs A.1's rank discipline) |
| `do { x <- p; k x }` | `bind d p (λx. k x)` |

The big-vision endpoint — **compile that Haskell to WASM, verified by the
kernel** — is stated in the base relation calculus (§5, Phase 4) and does not
itself require HOL-ω; the HOL-ω middle is the *typing* front end, deferred here.

---

## Audit revision log

Eight HIGH findings from the adversarial audit, and how each was closed:

- **F1 — `execute` deep-copied owned `Val` leaves on the WASM/store hot path.**
  §3A + §6 + decision #7: `execute` now mints over **zero-copy `Ref<Arc<F::In>>`/
  `Ref<Arc<F::Out>>`** leaves (`expr.rs:55-64`, `Arc: TrustedDeref`), not
  `Val<C>`. Bound is `F::In/Out: 'static` (Arc handle), **not** `F::In: Clone`
  over the payload; `refl`/`cong` transports bump a refcount, never copy the
  buffer.
- **F2 — content-addressing was a hash *op*, not a hash-consed representation.**
  §0 + §3A: reframed as **hash-consing / interning** — the store's native
  representation gives one canonical `Arc` per O256 content hash, making `Dyn`'s
  `Arc::ptr_eq` (`expr.rs:147-170`) coincide with content equality. `Hash:
  Op<Bytes,O256>` remains the *computational witness* (`canon`), not the
  addressing mechanism.
- **F3 — nondeterministic `execute` vs. a functionality axiom sold as
  complementary.** New §3A-negation + decisions #4/#8: made the **admitted-axiom
  discipline** explicit — `execute` grants positive facts only (sound for any
  `f`); any negation/uniqueness is a **user-admitted axiom** whose soundness is the
  user's burden and is **never framework-enforced**; asserting functionality for a
  nondeterministic `f` is admitting a false axiom (the user's error).
- **F4 — HOL-ω rank discipline named as a feature, not a soundness constraint.**
  §3C reduced to a deferral pointer; moved to **Appendix A** with A.1 stating the
  **required rank stratification** (unrestricted impredicative type quantification
  is inconsistent over HOL). HOL-ω scoped **out** of committed scope; judge table
  + decision #6 updated.
- **F5 — HOL-ω binder/substitution/kind-checking hand-waved as "free."**
  Appendix A.2 acknowledges the base is **ground/first-order/binder-free**; type
  variables, `TyAbs`, capture-avoiding `TyInst`, kind-checking are **real deferred
  middle machinery**. Retracted "kinds ARE base sorts / simpler than plain HOL."
  Distinguished ground type *terms* (in scope) from the binder/kind layer (not).
- **F6 — Phase 0 only tested deterministic-total functions.** §6: added the
  **mandatory `execute_nondeterministic_or_partial` test** (a `CoinFn` returning
  different outputs across calls + a `PartialFn` returning `Err`) proving `execute`
  soundly mints observed membership yet cannot derive functionality/negation —
  the case that justifies `execute` over `canon`.
- **F7 — `Ty`-in-base specified incoherently (marker sort vs `Val<Type>`
  leaves).** §3B + §6 + decision #5 now agree on ONE representation: a reflected
  **`TyRep`** sort with real inhabitants (`Val<core::Type>` leaves), constructors
  `TyFn`/`TyApp : Op<(TyRep,TyRep),TyRep>` building `App` spines; distinct reps are
  distinguishable so `⊢ a = a'` is meaningful.
- **F8 — TCB accounting conflated "ungated" with "untrusted."** New §5 honest
  TCB-delta table + decisions #2 + §6/§7: the ungated positive calculus
  (transpose/compose/join/meet) calls `Thm::new` and is therefore **in the TCB as
  audited-but-ungated mint sites**, exactly like `prop`'s `and_intro`/`or_inl`
  (`lib.rs:11-16`, `prop.rs:40-89`). Gating is orthogonal to trust; "zero
  trust / trivially green" framing removed.

### Second pass — three precision/scoping findings (MF1–MF3)

The relation-calculus core is sound; these are precision/scoping corrections.

- **MF1 [high] — `type TyRep = core::Type` was a CIRCULAR base→core dependency.**
  `base/trusted` cannot name `core::Type` (hierarchy: covalence-pure/base →
  covalence-core). §3B, §5, §6.2, and decision #5 now specify a **generic**
  reflected sort: `Val<C>` leaves (`Val<C>` is already generic, `expr.rs:44-49`)
  + generic constructor ops `TyFn<T>`/`TyApp<T> : Op<(T,T),T>`; the base names no
  concrete type, the consumer picks `C` (`core` supplies `C = core::Type`, later,
  in `core`). **Phase 0 commits to an in-base demo stand-in `TyRepDemo(u32)`** so
  the slice builds with no `core` dependency; `core::Type` integration is a later
  `core`-side step. The "replace core's `Type`/`TypeKind` equality with the base
  calculus" framing (§5) is marked aspirational and relocated to `core`, not the
  base.
- **MF2 [med] — content-addressing zero-copy claim overreached.** Zero-copy is a
  property of `execute`'s **membership** witness `⊢ blob Rel(Blake3) h` over
  `Ref<Arc<_>>` **only**. The functional, rewritable hash **equation** `⊢
  hash(blob)=h` is minted by `canon` (`eqn.rs:331-345`), which owns a `Val<Bytes>`
  and **deep-copies** the blob — there is no `canon`-over-`Ref<Arc>` rule. §0.1,
  §3A, §6.3 now flag the equation form as **not** zero-copy (O(n) copy), reserve
  the O(1)-copy claim to the `execute` membership form, and note "canon over Ref"
  as possible future work.
- **MF3 [med] — interner asserted but unspecified/false today.** `Dyn::new` does
  `Dyn(Arc::new(e))` (`expr.rs:160`) — a fresh `Arc` per call — so
  structurally-identical terms are **not** shared and `Dyn` `ptr_eq` does **not**
  coincide with content equality. Chose option (b): §0.1/§3A now state the
  interning layer is **future work, NOT relied upon by Phase 0/1**, and the "`Dyn`
  ptr_eq = content equality" claim holds only once a content-hash-keyed interning
  layer is added.
- **Nits.** (i) §3B/§6.3 `⊢ TyFn(a,b)=TyFn(a',b')` now combines the two argument
  equations via `cong_pair` (`eqn.rs:210`) **before** `cong_app` (`eqn.rs:192`).
  (ii) §6.1 notes that adding `execute`/`transpose` mint sites must also extend the
  **closed** mint-site enumeration in the `eqn.rs:7-9` docstring, not just
  `lib.rs:11-16`.
