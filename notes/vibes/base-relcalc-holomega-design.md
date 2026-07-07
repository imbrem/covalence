# The relation-calculus base + HOL-ω middle — authoritative design

**Status:** AI-authored design panel (2026-07, branch `relcalc-design`). The
authoritative plan for the **base + middle-language redesign**: a base that is a
*calculus of relations-as-untrusted-functions* with `Ty` as a first-class base
sort, and a middle that is **HOL-ω** rather than plain HOL. Records three
architect proposals, a judge scoring, the synthesized winner, and a **concrete,
additive Phase-0 spec** the orchestrator will build next.

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

1. **Content-addressing** — hashing/store/term-addressing as base `Op`/`Rel`,
   addressing terms & data natively (no term materialization).
2. **WASM** — a WASM module run is a *subset of untrusted relations*: executing
   it witnesses `input → output`, i.e. `a R b = true`.

The load-bearing observation that ties them together: **both are untrusted
functions whose *execution* supplies positive facts and never negative ones.**
Running a hash gives you `hash(x) = h`; running a store lookup gives you
`addr ↦ blob` *if present*; running a WASM module gives you `a ↦ b` *if it
halts with `b`*. None of them can ever prove a *negative* — a store miss on one
backing says nothing (the blob may be on another), a non-halting module proves
nothing (halting problem). **The base is built around exactly this asymmetry.**

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

Three facts about this base decide the whole redesign:

- **F1 — `Op<In,Out>` is already the function sort; `CanonRule` already executes
  ops.** `canon` runs `f.eval(v)` and mints a **functional** equation. What is
  *missing* is the **relational** (partial / effectful / nondeterministic)
  execution rule and the calculus over relations.
- **F2 — `CanonRule` mints only a *functional* identity.** It cannot serve WASM
  or a federated store, which are *not* functions (nondeterministic / partial /
  present-on-some-backing). The relational reading `a R b` (b *is one* output of
  f on a) is sound where the functional reading `f(a)=b` is not.
- **F3 — the base already proves *no disequalities*** (`closed-world-kernel.md`
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
the proposition `a R b` is just the existing `App<R, (Val<In>, Val<Out>)>`, an
`Expr<Ty=bool>`. A *proven* membership is a `Thm<L, App<R, (Val,Val)>>`. The
existing `prop.rs`/`eqn.rs` calculus transports it for free.

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
/// Run untrusted `f` on ground input `a`. On `Ok(b)`, mint `⊢ a Rel(f) b`
/// (= `App<Rel(f), (Val(a),Val(b))>`, a bool prop). Gated on `Rel<F>`'s TypeId.
/// NEVER mints falsity — `Err`, or a different `b` next time, is simply unprovable.
pub fn execute<L: Language, F: UntrustedFn>(
    f: Rel<F>, a: F::In, lang: L,
) -> Result<Thm<L, App<Rel<F>, (Val<F::In>, Val<F::Out>)>>, Error>
where F::In: Clone {
    let id = TypeId::of::<Rel<F>>();
    if !lang.admits(id) { return Err(Error::NotAdmitted(id)); }
    let b = f.0.run(&a).map_err(|e| Error::RuleFailed(format!("{e:?}")))?;
    Ok(Thm::new(lang, App(f, (Val(a), Val(b)))))   // sole gate: Thm::new
}
```

This is `canon`'s sibling: same shape, same single choke point, same `admits`
gate — but it mints **graph membership** (`a R b`), which is sound for *any* `f`
(the pair was observed), where `canon`'s **functional equation** (`f(a)=b`) is
sound only for deterministic total `f`. Per-function TCB stays enumerated: each
executable relation is a `Rel<F>` entry in the language's manifest.

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
operands are native `Val` (the input/output buffers) — **no term
materialization**, so a megabyte-I/O run mints an O(1)-node theorem.

**North star #1 — content-addressing, made efficient & first-class, and the
canon/execute duality.** Two *distinct* mechanisms, both needed:

- **`Hash : Op<Bytes, O256>` is a pure `CanonRule`** (deterministic, total) →
  `canon` mints the **functional** `⊢ hash(blob) = h`. This is what makes `h`
  *the* content-address (canonical, a genuine equation you can rewrite with).
- **`Store : Rel<O256, Bytes>` is an effectful `Rel`** → `execute` mints the
  **membership** `⊢ addr Store blob` when a lookup succeeds. A store is *not* a
  function (a miss ≠ "absent"; federated backings), so the relational reading is
  the *correct* one, and a miss soundly proves nothing (needs a "this store is
  closed" axiom to conclude absence).

Content-addressing a *term* is `Hash ∘ serialize` where `serialize : Op<Term,
Bytes>` and the whole thing runs over `Val<Term>`/`Val<Bytes>` leaves held
natively — the term is addressed without walking a materialized tree. This is
the same "never materialize" laziness as EG2 (`literal-endgame-design.md` §7:
the megabyte `bytes.cat` operand with 2 materialized nodes), now the base's
*native* content-addressing path.

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

### 3B. `Ty` in the base

Add a base sort `Ty` (an opaque marker — like every sort, it needs no trait) and
**type constructors as ops**:

```rust
pub struct Ty;                                  // the sort of object-language types
pub struct TyFn;  impl Op for TyFn  { type In = (Ty, Ty); type Out = Ty; }  // →
pub struct TyBool; impl Op for TyBool { type In = (); type Out = Ty; }
pub struct TyApp; impl Op for TyApp { type In = (/*op*/, /*args*/); type Out = Ty; } // HOL-ω
```

Types are now base **terms of sort `Ty`**, built by `App` like everything else.
Two payoffs:

- **Type equality/congruence/symbolic-transport come *free* from the existing
  calculus.** `⊢ TyFn(a,b) = TyFn(a',b')` from `⊢ a=a'`, `⊢ b=b'` by `cong_app`
  — no separate type-equality machinery in the middle (a real simplification;
  today `core` re-implements `Type`/`TypeKind` equality).
- **Leaf-elimination reuses the *same* symbolic mechanism for `Ty`.** A concrete
  `core::Type` enters as `Val<Type>` *or* symbolically as the `TyFn`/`TyApp`
  spine over `Val` leaves; `eq_mp`/`trans` transport it without materializing the
  tree — B1 (`literal-endgame-design.md`) applied at sort `Ty` instead of
  `Term`. §4 shows this subsumes the endgame.

### 3C. HOL-ω middle

Retarget the middle from plain HOL (CoreLang, 26 rules) to **HOL-ω** (Homeier's
HOL-Omega: HOL + a **kind** system + **type-operator variables** + rank-N type
quantification). The base changes above make this *simpler than plain HOL*:

- **Kinds are base sorts; type operators are base ops.** Kind `ty` is the sort
  `Ty`; kind `ty ⇒ ty` is `Op<Ty,Ty>`. A type-operator variable `m : ty⇒ty` is a
  free variable at sort `Op<Ty,Ty>`. So HOL-ω's kind/type-operator layer is
  *just the base `Op`/`App` calculus at sort `Ty`* — **no new middle machinery**.
  This is *why* HOL-ω here is more elegant than plain HOL: plain HOL bolts a
  fixed set of type constructors + a separate type-equality onto `core::Term`;
  HOL-ω *inherits* the base's relation/equality calculus at `Ty` and gets type
  operators, type-level equality, and symbolic types for free.
- **Rule delta vs the current 26.** Group A (equality/congruence: `Refl`/`Sym`/
  `Trans`/`MkComb`/`Abs`/`BetaConv`/`EtaConv`) is unchanged in spirit but now
  *reuses* the base equality calculus at both `Ty` and `Term` (drop `core`'s
  private type-equality). Add the HOL-ω trio: **`TyBeta`** (type-operator
  application reduction), **`TyAbs`/`TyInst`** (kind-correct type-operator
  abstraction/instantiation), and **rank-N `TyAll`** intro/elim for universal
  types. `typedef` (abs/rep) generalizes to type-operator definitions. Net: a few
  added kind-directed rules, minus the deleted bespoke type-equality — a wash or
  a shrink in TCB, with strictly more expressive types.

**Micro-Haskell → HOL-ω (the `Monad` worked example).** The small vision: a
micro-Haskell dialect converts ~directly to HOL-ω.

| micro-Haskell | HOL-ω |
|---|---|
| type `T` | type (term of sort `Ty`) |
| `Maybe :: * -> *` | type operator: constant of kind `ty⇒ty`, i.e. sort `Op<Ty,Ty>` |
| `class Monad m where return::a->m a; bind::m a->(a->m b)->m b` | a **dictionary** type operator `Monad : (ty⇒ty)⇒ty` + a predicate `LawfulMonad : ∀(m:ty⇒ty). Monad m → bool` (the 3 laws) |
| `instance Monad Maybe` | a term `dict : Monad Maybe` + a proof `⊢ LawfulMonad Maybe dict` |
| `f :: Monad m => a -> m a` | rank-1: `LawfulMonad m d ⊢ f : α → m α`; rank-N: `f : ∀(m:ty⇒ty). Monad m → …` (a `TyAll` type) |
| `do { x <- p; k x }` | `bind d p (λx. k x)` |

The typeclass is a **rank-n dictionary over a type-operator variable** — exactly
what HOL-ω's kind system + universal types express directly, and *nothing else
does as cleanly*. This is the payoff: a Haskell subset (eventually most of it)
becomes a **native in-kernel language**, and the eventual big vision — **compile
that Haskell to WASM, verified by the kernel** — is stated in the base relation
calculus (§5).

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
| HOL-ω correctness + Haskell mapping | 4 | **5** | 4 |
| EG5 subsumption | 4 | **5** | 3 |
| migration realism (additive, reversible, real Phase 0) | 1 | **5** | 4 |
| **total** | 21 | **30** | 22 |

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
behavior: `Val`/`App`/`Eqn`/`CanonRule`/the equality & bool calculus are
untouched; `execute` is a new gated mint through the *same* `Thm::new` choke
point as `canon`; the positive calculus is new ungated methods (sound-in-every-L,
like `and_intro`). The Op/Val unification is *stated* (Val = the nullary op) and
*bridged* thinly, with the full collapse (delete `Val`, `Expr := Op<(),_>`)
deferred to a maintainer-gated stage — A's flag-day is never forced. Soundness
still rests on `admits()` alone (the sole gate is `Thm::new`, the sole new
trusted rule is `execute`, gated per-function).

**EG5 subsumption (axis it wins on).** The literal endgame's per-family symbolic
landers (`ToHolNat`/`Int`/`Bytes`/… each needing its own reify rule — the **float
wall**, `literal-endgame-design.md` §7) **dissolve**: in B, every native value is
`Val<C>` (a nullary op), symbolic-by-default; `Ty` in the base extends the same
mechanism to type trees; `Dyn` (erased point/relation) is EG's deferred B2, now
the natural heterogeneous carrier. EG3–EG5 become *instances* of "Op/Val
unification + Ty-in-base," not a separate ladder — one mechanism, no per-family
rules, no float wall.

### Coherence with the binding maintainer decisions (closed-world-kernel + EG)

- Base stays **closed-world / enumerable**: `execute` is a manifest-listed
  per-`Rel<F>` rule; the positive calculus is ungated (auditable as framework
  methods). No opacity, `Thm::new` still the sole mint.
- **No disequalities in the base** (today's state) is *promoted to the design
  invariant*: negative membership is axiom-only. The deferred `Evaluate`/decision
  seam is now *defined* as "an admitted axiom that a relation is
  functional/total/closed."
- **Ty-in-base** replaces `core`'s private `Type`/`TypeKind` equality with the
  base calculus at sort `Ty` — a middle simplification, additive (introduce `Ty`
  ops alongside; migrate `core` later).

---

## 6. PHASE 0 — the concrete, additive, reversible de-risking slice

**Goal.** Prove end-to-end, with **zero change to existing base/core behavior**,
that: (i) an untrusted function's *execution* mints a positive membership witness
and *cannot* mint falsity; (ii) both north stars are served — a WASM-shaped run
and a content-addressing run — with **O(1) materialized nodes** over large I/O;
(iii) the canon/execute duality holds (functional hash vs. effectful store); (iv)
the positive calculus (transpose) works as an ungated method; (v) `Ty`-in-base
transports a type equation through the *existing* calculus. All through
`Thm::new`. Delete **nothing**.

**New code (all additive; existing files unchanged in behavior).**

1. **`crates/kernel/base/trusted/src/rel.rs`** (new module; `lib.rs` gains
   `mod rel; pub use rel::*;`):
   - `trait UntrustedFn: Any { type In; type Out; fn run(&self, a:&In) -> Result<Out, RelErr>; }`
   - `struct Rel<F: UntrustedFn>(pub F); impl<F> Op for Rel<F> { In=(F::In,F::Out); Out=bool; }`
   - `enum RelErr { Refused, Trapped(String), … }` (untrusted error, no trust).
   - `pub fn execute<L,F>(f: Rel<F>, a: F::In, lang: L) -> Result<Thm<L, App<Rel<F>,(Val<F::In>,Val<F::Out>)>>, Error>`
     — gated on `TypeId::of::<Rel<F>>()`, mints via `Thm::new` (add one audited
     call-site line to the `lib.rs` mint-site list).
   - **Transpose** as an ungated method: define `struct Transpose<R>(R)` (a
     relation-op with swapped input) and
     `impl<L,R,A,B> Thm<L, App<R,(A,B)>> { pub fn transpose(self) -> Thm<L, App<Transpose<R>,(B,A)>>; }`
     — sound in every `L` (recombines a proven positive fact), no manifest entry.
     (Compose/join/meet are the same pattern; Phase 0 ships only `transpose` to
     stay minimal, and documents the rest.)

2. **`crates/kernel/base/trusted/src/ty.rs`** (new module): `struct Ty;` +
   `TyFn`/`TyBool` constructor ops. No rules — types transport through the
   *existing* `refl`/`cong_app`.

3. **Tests — `crates/kernel/base/trusted/src/tests.rs`** (append; or a new
   `rel_tests` module). A demo `struct RelCalc;` `impl Language for RelCalc` whose
   manifest admits exactly `Rel<Blake3Fn>`, `Rel<AddModFn>` (the enumerated new
   trust). Prove:
   - **`execute_witnesses_wasm_shaped`** — `AddModFn: (u64,u64)->u64` (stand-in
     for a WASM run); `execute` mints `⊢ (a,b) Rel(AddMod) c`; assert the *wrong*
     `c'` is **not** obtainable (no `execute` path, no falsity rule) — the
     never-false asymmetry, machine-checked.
   - **`execute_content_address_O1_nodes`** — `Blake3Fn: Bytes->O256` wrapping
     `crates/lib/hash::Blake3`; feed a ≥1 MB blob; `execute` mints `⊢ blob
     Rel(Blake3) h`; a node-counting walk over the prop `Expr` returns **O(1)**
     (the blob & hash sit in `Val` leaves, never a term tree) — the
     content-addressing north star + EG2 laziness, machine-checked.
   - **`canon_vs_execute_duality`** — the *same* Blake3 as a pure `CanonRule`
     mints the **functional** `⊢ hash(blob) = h` via `canon`; contrast with the
     effectful-store **membership** shape via `execute`. Documents which north
     star each mechanism serves.
   - **`transpose_positive`** — from `⊢ a R b` derive `⊢ b R° a` by the ungated
     method.
   - **`ty_in_base_transports`** — `⊢ a = a'` ⟹ `⊢ TyFn(a,b) = TyFn(a',b)` by
     `cong_app`, with **no new rule** — the Ty-in-base foothold.

**What it proves.** The base natively mints WASM/content-addressing execution
witnesses (positive-only), efficiently (O(1) nodes), through the sole `Thm::new`
gate, with the positive calculus and Ty-in-base working off the *existing*
machinery — de-risking every load-bearing claim of §3 in one small slice.

**Why reversible & zero-behavior-change.** Two new files + a `mod`/`pub use` +
one mint-site audit line + test additions. No edit to the *behavior* of
`expr.rs`/`op.rs`/`eqn.rs`/`lang.rs`/`prop.rs`/`matching.rs`. `Val`/`App`/`Thm`/
`CanonRule` untouched; the Op/Val collapse is **not** attempted in Phase 0. The
demo `RelCalc` language lives in tests, so **no production manifest changes**.
Deleting `rel.rs`/`ty.rs` + their `pub use` + the tests returns the tree
byte-identical. Fully additive; the full gate is trivially green.

---

## 7. Staged plan (additive first, collapse last)

- **Phase 0** (§6): `rel.rs` (`UntrustedFn`/`Rel`/`execute`/`transpose`) + `ty.rs`
  + the five tests. Additive, reversible. *The slice the orchestrator builds
  next.*
- **Phase 1** — the rest of the positive calculus (`compose`/`join`/`meet` as
  ungated methods) + a real `WasmRun` `UntrustedFn` over `crates/lib/wasm` and a
  `Store` `Rel` over `crates/store` (the two north stars, real backings).
  Additive.
- **Phase 2** — HOL-ω middle: kinds-as-sorts, type-operator ops at sort `Ty`,
  the `TyBeta`/`TyAbs`/`TyInst`/`TyAll` rules; migrate `core` type-equality onto
  the base `Ty` calculus. The micro-Haskell → HOL-ω front end (Monad worked
  example) as a `lang/` crate. Additive alongside plain CoreLang.
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
   sound in every `L`, inject no trust — like `and_intro`); only `execute` and
   negation are gated. Confirms base-TCB minimalism (graft from C).
3. **`execute` must stay gated** (per-`Rel<F>` `admits`) — the WASM/store TCB
   stays enumerated. Confirm.
4. **Nondeterminism semantics of `Rel(F)`.** Recommend the **graph/membership**
   reading (any observed output ∈ graph; `execute` never mints a functional
   equation); reserve the functional equation for deterministic `CanonRule` ops
   (hash). Confirm this is the intended WASM/store semantics.
5. **`Ty` representation.** Recommend an **opaque base marker sort + constructor
   ops** (base minimal; the concrete type algebra is middle/admitted), mirroring
   "sorts need no trait." (Alternative: a concrete base `Ty` enum — more base
   TCB.)
6. **HOL-ω kind placement.** Recommend **kinds = base sorts** (`ty` = `Ty`,
   `ty⇒ty` = `Op<Ty,Ty>`), so the kind layer *is* the base `Op`/`App` calculus.
   Confirm vs. a separate middle kind judgement.
7. **`execute` bounds.** `F::In: Clone` (to seat in `Val`); `F::Out: Clone`;
   `Eq` on operands only *where used as a `trans`/`eq_mp` middle* ("no Eq, no
   comparison"). Pin the exact bounds at implementation.
8. **Negation/`Evaluate` seam.** The deferred disequality seam becomes "an
   admitted axiom that a relation is functional / total / closed." Confirm this
   is where `¬(a R b)` and op-decision live (out of base TCB).
