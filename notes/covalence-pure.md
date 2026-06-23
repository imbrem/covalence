# covalence-pure — the base logic: starting design

> **STATUS: DESIGN SKETCH (starting blueprint).** A concrete starting point for
> `covalence-pure`: a simple, auditable, *fast* first-order logic on which
> everything else is built as **observers**. Grows into the vision of **one
> trusted logic + N trusted executors + accelerators**, all under user control
> and tracked in a *meta*-assumption set. Refines `kernel-design.md §11`
> (the narrow-waist direction) and `observers.md §7` (trusted observers);
> coheres with the assumption-tracking design in `soundness-audit.md §4`.

---

## 1. One logic, N executors, K accelerators

The whole system rests on three kinds of trusted thing, and *nothing else*:

```
   1 trusted LOGIC        covalence-pure: a small first-order logic (the TCB floor)
   N trusted EXECUTORS    0 at first; then 1 (WASM); then many (x86 containers, …)
   K trusted ACCELERATORS nat, int, bytes (later: list, set)
```

- The **logic** is the only thing trusted *unconditionally*. It is positive,
  concrete, first-order — auditable in one sitting.
- **Executors** and **accelerators** are trusted *by choice*. Each is a named
  assumption you opt into; the system records exactly which ones any given fact
  depends on. Starting from **zero** executors means: pure logic, every
  computational claim is an explicit assumption you must discharge or accept.
- **Every other logic** — HOL, ZFC, MLTT — is *not* trusted. It is an
  **executor module**: a program that, run under an executor (or interpreted),
  attests its theorems, and is **proved sound by the base logic**. HOL becomes
  "a `Fact` of Pure," exactly the narrow-waist move (`kernel-design.md §11.2`).

The discipline that makes this safe: **two assumption sets** (§4) — the ordinary
logical one, and a *meta*-assumption set recording which executors/accelerators
a fact leans on.

---

## 2. What the logic is

Deliberately weak and concrete. Pure reasons about **reified data** via **atomic
predicates** and chains them with **first-order implication**. It does *not*
reason about *meaning* (not WASM's reduction relation, not HOL theoremhood) —
only about opaquely-attested atomic facts and their first-order consequences
(`pure-narrow-waist-direction`).

### 2.1 Individuals — reified data (the meta-sorts)

A fixed, finite set of **meta-sorts**, each a kind of reified datum:

```
   Tm     a reified term (of some object logic — e.g. a HOL term)
   Ty     a reified type
   Bytes  the binary-data substrate (blobs, the byte/nat/int literals live here)
   Prog   a reified executor program (a WASM component, …)
   …       (extensible — but the set is small and finite)
```

These are HOLTm/HOLTy in `metatheory.md §5`, generalized: Pure's "individuals"
are *syntax and data*, never object-logic values. Crucially, Pure's own type
system is just these meta-sorts — it does **not** carry the object logic's rich
types (those are *data* of sort `Ty`, related to terms by the `HasTy` predicate).

### 2.2 Predicates — the syntactic judgements

A predicate is a relation over individuals. The load-bearing ones are exactly
the judgements that today live as hand-written Rust in `covalence-core`:

```
   Eq(a, b)            a and b are equal              (the substitution/βι facts)
   Subst(a, x, b, c)   [a/x]b = c                     (the substitution system)
   HasTy(a, A)         a : A                          (the typechecking system)
   IsThm(L, p)         p is a theorem of logic L      (object logics, incl. HOL)
   Runs(P, in, out)    program P on `in` yields `out` (executors)
   …
```

Each predicate instance is either **opaque** (uninterpreted — a hypothesis or a
conclusion to be discharged) or **observed** (attested by an observer, §3). Pure
itself knows nothing about *why* `Subst(a,x,b,c)` holds; an observer attests it.

### 2.3 The judgement form — a `Fact`

A Pure theorem is a `Fact`: a proven first-order sequent

```
   Γ ⊢ φ                 (built only through Pure's inference rules — LCF)
```

where `φ` is an atomic predicate or a **Horn implication** `ψ₁ ∧ … ∧ ψₙ ⟹ atom`
(possibly `∀`-closed over individuals). Horn is the sweet spot: enough to *chain*
observations (`Subst(...)`, then `HasTy(...)`, then conclude), nothing more — no
nested quantifier alternation, no higher-order. That weakness is what keeps Pure
trivially correct and re-hostable (`kernel-design.md §11.5`).

The minimal rule set (LCF constructors, each one-line-auditable):
`assume`, `imp_intro` / `imp_elim` (modus ponens), `and_intro` / `and_elim`,
`all_intro` / `all_elim` over individuals, `refl`/`sym`/`trans` for `Eq`, and
**`attest`** (§3) — the bridge from an observer to a `Fact`.

---

## 3. Observers — the universal mechanism

> The move the user asked for: the substitution system, the typechecking system,
> the HOL kernel — all become **observers** that *attest atomic predicates*.

An **observer** is a trusted Rust object that, given individuals, *computes* and
**attests** an atomic predicate by running code:

```rust
/// Attests atomic predicates by running trusted Rust. The relocated
/// ObsTrue/ObsEq/ObsImp substrate of covalence-core lives here, generalized.
trait Observer {
    /// The meta-assumption this observer's attestations carry (§4): "this
    /// observer is sound." Riding it into a Fact's meta-set is the entire
    /// trust cost of using the observer.
    fn meta_tag(&self) -> MetaTag;

    /// Attempt to attest `pred` (with these individual args). Returns the
    /// attested Fact (carrying meta_tag in its meta-set), or None to refuse.
    /// Refusing is always sound; a wrong attestation can only be unsound if
    /// `meta_tag` is later trusted — which is the user's explicit choice.
    fn attest(&self, pred: PredSym, args: &[Individual]) -> Option<Fact>;
}
```

Concrete observers, each replacing hand-written `covalence-core` machinery:

| Observer | Attests | Replaces |
|---|---|---|
| **SubstObserver** | `Subst(a,x,b,c)` — `[a/x]b = c` | `subst.rs` (run as an observation) |
| **TypeObserver** | `HasTy(a, A)` — `a : A` | `type_of` / typechecking |
| **NatAccel / IntAccel / BytesAccel** | `Eq(f(lits), result)` | `reduce_prim` / literal arithmetic |
| **WasmExecutor** | `Runs(P, in, out)` | (new) the executor substrate |
| **HolModule** | `IsThm(HOL, p)` | the HOL `Thm` API, lifted |

The key reframing: today the kernel *hard-codes* "this term has this type" and
"this substitution gives this result." In Pure these are **attestations** — a
`TypeObserver` *observes* `a : A`, a `SubstObserver` *observes* `[a/x]b = c`.
Pure's `attest` rule turns an observer's `Some(fact)` into a `Fact` carrying the
observer's meta-tag. The existing `Object`/`ObsEq`/`ObsTrue`/`ObsImp` types
(`covalence-core/src/term/observer.rs`) move to `covalence-pure` and *are* this
mechanism — they already mint facts soundly under the parametric ε-model.

---

## 4. The two assumption sets (the heart of it)

Every `Fact` carries **two** provenance sets — and keeping them separate is the
design's core idea.

```rust
struct Fact {
    asms: AssumptionSet,    // Γ — ordinary LOGICAL hypotheses (today's Thm.hyps)
    meta: MetaAssumptionSet, // M — which executors/accelerators/observers it trusts
    concl: Prop,
}
```

- **Assumption set `Γ`** — object-level hypotheses, discharged by `imp_intro`.
  Exactly today's `Thm` hypothesis context.
- **Meta-assumption set `M`** — a join-semilattice of **named meta-tags**: one
  per accelerator (`NatAccel`, `IntAccel`, `BytesAccel`), one per executor
  (`WasmExec`, later `X86Exec`…), one per object-logic module (`HolSound`), and
  one per observer-soundness assumption generally. Each rule **unions** `M` from
  its premises; `attest` **adds** the observer's `meta_tag`. Pure logical rules
  add nothing — `M` propagates exactly like `Γ` already does for `has_no_obs`.

### 4.1 User control: the base set is null-by-default

The user **chooses** which meta-tags to trust — the **base set** `B ⊆ all tags`.
The default interface treats `B` as **null**: a fact whose `M ⊆ B` displays as
unconditional, so everyday proving with nat/int/bytes/WASM enabled is
unburdened. But `M \ B` (anything outside your base) **rides explicitly**, and
`M` is always *queryable*:

- `fact.uses(WasmExec)` — "does this proof rely on the WASM executor?"
- `fact.meta_minus(base).is_empty()` — "is this fact provable in *my* trust
  base?" — a strictly sharper "bare-logic" check than today's `has_no_obs`.

**Starting from N = 0 executors** means `B` contains *no* executor tags: every
`Runs(...)` is then an explicit, undischarged meta-assumption — pure logic only.
Adding WASM (N = 1) is *adding `WasmExec` to `B`*. Adding x86 containers (N = …)
is adding more tags. The growth path is literally "grow `B`."

### 4.2 Discharge a meta-assumption by proving it

A meta-tag is **not permanent** — you can *discharge* it by proving the observer
sound, which is what makes "nat the accelerator = nat the definition" rigorous
and non-circular:

```
   discharge(NatAccel, proof) : strips NatAccel from M,
       provided `proof` itself does NOT use NatAccel.
```

Develop Peano arithmetic *without* the `NatAccel` observer (so the development's
`M` lacks `NatAccel`), prove it categorical / that the accelerator coincides with
the defined naturals, then `discharge(NatAccel, …)`. No circularity — `discharge`
rejects any proof whose own `M` contains the tag being discharged. This is
`observers.md §7.2` and `soundness-audit.md §4`, now stated as the two-set
mechanic. Same move discharges `WasmExec` (prove the bytecode meets `T_wasm` —
`metatheory.md §2`) and `HolSound` (prove HOL sound in Pure).

---

## 5. Other logics as executor modules

HOL is an **executor module**: a program/datatype that attests `IsThm(HOL, p)`,
proved sound by Pure. Two presentations, same end state:

- **Interpreted** — a `HolModule` observer runs the HOL kernel rules and attests
  `IsThm(HOL, p)`, carrying the `HolSound` meta-tag. `covalence-core`'s `Thm`
  becomes the witness behind that attestation — morally "`Thm` implements
  `Observer`." Core stays *mostly unchanged*; it gains a trait impl.
- **Reified** — HOL is a datatype inside Pure, `Derivable_HOL` an inductive
  predicate, soundness `IsThm(HOL,p) ⟹ ⟦p⟧` a Pure `Fact` (`metatheory.md §1`).

Either way: HOL is one module among peers (the WASM executor, the bytes
accelerator), and its trust is one meta-tag. The diversity of logics lives
*above* the waist; the waist (the HOL surface most consumers use) is shared; the
base logic *below* is the swappable substrate (`kernel-design.md §11.3`).

---

## 6. Porting `covalence-core` (the concrete first steps)

The order that yields a working `covalence-pure` while keeping core green:

1. **Stand up the crate** — `Individual` (the meta-sorts), `Prop` (atomic
   predicate + Horn implication), `Fact` (with `Γ` *and* `M`), the LCF rule set
   (§2.3), `MetaTag` + the two-set plumbing. *No executors, no accelerators
   yet* (N = 0, K = 0) — just the logic. Unit-test the rules.
2. **Relocate the observer substrate** — move `Object` / `ObsEq` / `ObsTrue` /
   `ObsImp` from `covalence-core/src/term/observer.rs` into `covalence-pure`,
   re-cast as the §3 `Observer` + `attest` mechanism. (Do this *after* the
   in-flight `covalence-hol` work merges — it touches core.)
3. **Substitution as an observer** — wrap `subst.rs`'s functions in a
   `SubstObserver` attesting `Subst(a,x,b,c)`. Cross-check: the observed `c`
   equals `subst_free`/`open`/`close`'s result (differential test, the
   `paranoid-mode` discipline).
4. **Typechecking as an observer** — wrap `type_of` in a `TypeObserver`
   attesting `HasTy(a, A)`.
5. **Accelerators** (K = 1, 2, 3) — `NatAccel`/`IntAccel`/`BytesAccel` attesting
   `Eq(f(lits), result)`, each with its meta-tag. This is `reduce_prim` relocated
   as observers; the literals (`Bytes` sort) are the substrate they compute over.
6. **HOL as a module** — give `covalence-core::Thm` an `Observer` impl attesting
   `IsThm(HOL, …)` (the narrow-waist lift). Core's public API is unchanged.
7. **The first executor** (N = 1) — `WasmExecutor` attesting `Runs(P, in, out)`,
   meta-tag `WasmExec`. Pair with the SpecTec-lowered `T_wasm` (`metatheory.md`)
   for the eventual `discharge(WasmExec, …)`.

Throughout: **keep the simple, obvious interpreter as the spec.** Every observer
must be demotable to "propose a result, the simple Pure core re-checks it"
(paranoid mode, `kernel-design.md §11.5`) — that's what bounds the TCB to the
logic alone and makes re-hosting (OCaml/JS) a matter of re-implementing the small
core.

---

## 7. The design decisions, stated plainly

- **Base logic = first-order Horn over reified-data meta-sorts.** Strong enough
  to chain attestations, weak enough to be trivially correct. Not the object
  logics' types — those are *data* related by `HasTy`.
- **Everything trusted-but-chosen is an observer carrying one meta-tag.**
  Substitution, typechecking, arithmetic, executors, HOL — uniform.
- **Two assumption sets.** `Γ` (logical) is today's `hyps`; `M` (meta) is the new
  tier — which executors/accelerators/observers a fact trusts. Default-null over
  a user-chosen base `B`; always queryable; discharge-by-proving (non-circular).
- **Growth = growing `B`.** 0 executors → 1 (WASM) → N (x86 containers), each a
  tag the user opts into. Accelerators (nat/int/bytes) are the same mechanism.
- **Other logics are executor modules proved sound by Pure.** HOL is `Thm`
  implementing `Observer`; the waist (HOL API) is shared, the substrate (Pure)
  is swappable.
