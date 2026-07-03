# Covalence — Observers and Validators

> **DESIGN SKETCH.** How *untrusted* code (a WASM executor, a "trust the
> bytes" backend, an external solver) feeds facts into the kernel's HOL model
> **without growing the TCB** — by routing every claim through a *validator*
> trusted only for a specific *observer type*. The computational metatheory
> this realizes is [`metatheory.md`](./metatheory.md); the broader
> base-logic / meta-assumption substrate is [`covalence-pure.md`](./covalence-pure.md).
>
> **Today vs. proposed.** The kernel already implements the **observer
> substrate** ([`kernel-design.md`](./kernel-design.md) §5.6,
> `crates/covalence-core/src/term/observer.rs`): the marker `trait Observer`,
> the per-type policy traits `ObsEq`/`ObsTrue`/`ObsImp`, the type-erased
> `Object` leaf (compared by `Arc` identity), and the rules
> `Thm::obs_eq`/`obs_true`/`obs_imp` — all sound under the parametric ε-model,
> none in the TCB. **Everything labelled *validator* below is proposed design,
> not yet code.**

---

## 1. The judgement: "I saw that"

The organizing notation from the sketch:

```
                        |> "i saw that"
   {given these inputs} |> "i see this"
   your metalogic:      {given these facts} |> "i see this fact"
```

`|>` is an **observation judgement**, distinct from logical entailment
`⊢`. An observer does not *prove* a fact; it *attests* to one. The whole
design exists to make attestation safe: an attestation is admitted into
the kernel only as a **scoped assumption** discharged against a trusted
validator, never as a global axiom. The equation that makes this precise:

```
   Γ ∪ observer  |>  P
   ===
   Γ ∪ {facts…}  |>  P
```

i.e. "Γ together with this observer attests P" is *defined* to mean "Γ
together with the concrete facts the observer asserted attests P." The
observer is a *named bundle of assumptions*, scoped to itself — exactly
the "scoped truths, no global lies" principle of
[`VISION.md`](./VISION.md).

---

## 2. Observer vs. validator

Two roles, with a sharp trust boundary between them:

- **Observer** — *untrusted*. Can **only assert** facts; it can never
  deny one. It is fed arbitrary, possibly interactive, witnesses by the
  user and turns them into asserted facts. **This role exists today:** in
  the kernel an observer is *any* Rust type (the marker `trait Observer`
  has a blanket impl for `Any + Send + Sync + Debug`), wrapped in a
  type-erased `Object` leaf that the kernel compares only by `Arc`
  pointer identity — so a misbehaving observer cannot corrupt kernel
  invariants.

- **Validator** — *trusted, but only for one observer type*. It decides
  which asserted facts are admitted. **This role exists today, in a
  specific form:** the per-observer-type **policy traits**
  `ObsEq`/`ObsTrue`/`ObsImp` (in `observer.rs`) *are* the validator — one
  policy per Rust observer type, deciding which observations the kernel
  rules `Thm::obs_eq`/`obs_true`/`obs_imp` will mint. Crucially, these
  policies are **not in the TCB**: any answer they return is sound under
  the parametric ε-model (`kernel-design.md` §5.6), because each Rust
  observer type gets an independent ε-family in the model. The *richer*
  validator — one that also manages a model, a precondition set, and
  frozen flags (§3) — is the **proposed** extension:

  ```rust
  // PROPOSED — not yet in the codebase. The realized core is the
  // ObsEq / ObsTrue / ObsImp policy traits in observer.rs.
  trait Validator<O: Observer> {
      fn register(&mut self, fact: Fact);          // observer pushes a fact
      fn validate(&self, facts: &Facts) -> bool;   // trusted admission check
  }
  ```

The pipeline is one-directional:

```
   WITNESS  ⟹  OBSERVER  ⟹  VALIDATOR  ⟹  FACTS (the HOL model)
  (arbitrary) (untrusted)  (trusted-for-O)  (scoped assumptions)
```

In today's kernel that pipeline is: an arbitrary Rust value (the
witness) becomes an `Object`/`Obs` leaf (the observer); its
`ObsEq`/`ObsTrue`/`ObsImp` policy (the validator) gates the `Thm::obs_*`
rules; and **facts that relate an observation to an ordinary term enter
via `Thm::assume`** — as explicit meaning axioms that stay visible in
every dependent theorem's hypotheses. Those hypotheses *are* the
"scoped assumptions" at the end of the pipeline, and the seed of the
precondition set in §3. There is deliberately **no kernel rule** that
silently asserts "this observation equals this real term."

---

## 3. What a validator may do

A validator is trusted to make exactly these decisions, each with a
clearly bounded soundness story:

**On a fact the observer asserts**, a validator may:

- **Accept no facts** — the null validator (trusts nothing).
- **Accept facts of a fixed shape** — e.g. only equations between *its
  own* constants: `{a1,…,an} ⊢ myConst e = myConst' e'`. It owns those
  symbols, so it can be trusted to relate them.
- **Accept-as-precondition** — for any fact it does not *fully* accept,
  admit it anyway but record it in the validator's **precondition set**
  `P`. The discharge rule is:

  ```
       precon(o) ⊢ P    ⟹    observer ⊢ P
  ```

  i.e. anything proved is only proved *under* the preconditions the
  observer needed — the assumptions never silently vanish. Today this is
  exactly what `Thm::assume` gives: an accepted-but-unverified fact is an
  added hypothesis, carried in the conclusion's hypothesis set until
  discharged. The proposed precondition set `P` is the first-class,
  per-validator aggregation of those hypotheses.

**On the model**, a validator may:

- **Add a constant** `myNewConst : someArbitraryType` to the model.
  (This is where "efficient bytes" introduces a constant per
  bytevector, "efficient nats" a constant per numeral, etc.)

**A validator can be queried** (trusted answers) for:

- the current **model** `M`,
- the current **preconditions** `P`,
- whether the model or preconditions are **frozen** (`mFrozen`,
  `pFrozen`).

So a validator's trusted state is the tuple **`(M, P, mFrozen, pFrozen)`**.
Freezing is what lets downstream proofs depend on a *fixed* model: once
`mFrozen`, no new constants appear; once `pFrozen`, no new assumptions.

---

## 4. Validators are kernel extensions

Each extension to the core kernel is a validator — that is the unifying
claim. Concrete instances:

- **Efficient bytes** — presents a constant for each bytevector, plus
  constants for builtin byte catenation, length, etc., with validated
  equations relating them. (Backs the kernel's `Blob` literal substrate
  story.)
- **Efficient nats** — a constant per numeral, with validated arithmetic
  equations. (Backs `TermKind::Int` / nat-lits.)
- **"I trust the WASM spec"** — a validator parameterized by a trusted
  WASM executor; it freely admits facts that follow from the spec under
  that executor's formal semantics, and supports *substituting the
  model* (swapping executors).

  ```rust
  // PROPOSED / illustrative — sketches a validator on top of the
  // existing ObsEq/ObsTrue/ObsImp policy substrate.
  impl ITrustTheWasmSpec<MyTrustedWasmExecutor> {
      fn validate(&self, facts: &Facts) -> bool {
          // admit anything following from the spec under this executor
      }
      fn substitute_model(&mut self) { /* swap executor model */ }
  }

  impl ITrustTheBytesObserver<BytesSystem> { /* … */ }

  impl BytesSystem {
      fn observe(&self) -> Facts { /* … */ }
  }
  ```

The point of "trust the WASM spec" is that it is the *bridge to the
computational metatheory*: today it is a trusted validator; the long-run
goal ([`metatheory.md`](./metatheory.md)) is to **replace the trust with
a proof** — `WASM(P, D, A) ⟹ ∃D'. ZFC(D', A)` — at which point the
validator stops being trusted and becomes a checker.

---

## 5. Composition

Observers and validators compose pairwise:

```
   V1 : O1     V2 : O2
   (V1, V2) : (O1, O2)
```

A composite validator is trusted exactly insofar as its components are;
its model is the union of their models, its preconditions the union of
their preconditions. This is what keeps the TCB *flat* as the catalogue
of observers grows — adding the 20th oracle does not enlarge the trust
surface of the first 19, it adds one independent, separately-auditable
validator. (Same flat-TCB property the VISION doc claims for the oracle
catalog.)

---

## 6. Relationship to the rest of the system

- **Surface syntax** — the facts an observer asserts, and the
  preconditions a validator records, are written in the
  [surface syntax](./surface-syntax.md); an observer-backed theory is a
  spec whose axioms are *attested* rather than *proved*.
- **Metatheory** — observers are the *computational* half of metatheory
  ([`metatheory.md`](./metatheory.md)); the "get rid of the oracles"
  program is precisely the migration of trusted validators into proved
  checkers.
- **Stores** — the natural home for a validator's frozen `(M, P)` is a
  content-addressed store ([`VISION.md`](./VISION.md)); a frozen model
  is just a blob, and "which executor backs this" is a manifest edge.

---

## 7. The endgame: the built-in literals *are* trusted observers

> **DIRECTION — not yet built.** This is the kernel-side face of the
> base-logic vision; the full treatment (one logic + N executors + K
> accelerators, the two assumption sets, discharge-by-proof) is
> [`covalence-pure.md`](./covalence-pure.md). Under it the `Obs`/`ObsEq`/
> `ObsTrue`/`ObsImp` substrate (§2) **moves out of `covalence-core` into
> `covalence-pure`** as the base logic's primitive, and `obs_imp` becomes the
> **lift** of a Pure implication into HOL ([`kernel-design.md`](./kernel-design.md)
> §11.2).

Today `Int`, `Bytes`, and the `Nat`/`succ` machinery are **built-in kernel
primitives** ([`kernel-design.md`](./kernel-design.md) §4, §5.7). The direction
collapses the distinction between "a built-in literal" and "a trusted
observer": **`Int`/`Bytes`/`Nat` become trusted observers**, the only
difference being that "this observer is sound" is an assumption carried as a
privileged built-in fast path rather than a hypothesis threaded through
`Thm::assume`. Same logical content, lower cost. Two consequences fall out.

### 7.1 Drop the `TermKind` enum

Matching terms on a fixed, closed `TermKind` enum is exactly what hard-wires
`Int`/`Bytes`/`Nat` into the kernel. The plan is to replace the enum with an
**open** way to match on terms (a trait / handle the kernel dispatches
through, rather than a closed sum). A literal is then just an observer leaf
with a privileged validator; adding — or *removing* — one is no longer a
kernel-enum edit, and the efficient numeric/byte primitives stop being a
fixed part of the term grammar.

### 7.2 Observer provenance → "this proof doesn't use `Nat`"

Once a literal is an observer, the set of observers a `Thm` depends on is
**visible** (the same way `Thm` already tracks hypotheses, and `has_no_obs`
exists today). That makes a new — non-first-class but sound — query
possible: **which observers did this proof actually use?** In particular we
can single out proofs that do *not* lean on the `Int`/`Bytes`/`Nat`
observers at all — proofs that hold in the bare logic.

That is what lets us **soundly identify `Nat` with its "real definition."**
Develop Peano arithmetic *without* the `Nat` observer, show that development
is categorical (the naturals are unique up to isomorphism), and conclude it
is safe to *identify* the efficient `Nat` observer with the defined
naturals — the observer becomes **known-sound by a proof, not assumed**.
This is the §4 "trust the WASM spec → prove it instead" pattern turned on
the kernel's own numeric primitives: the most-used observers earn their
trust the same way every other oracle does.
