+++
id = "N002Q"
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

# Covalence — Observers and Validators (superseded)

> **Historical design sketch.** Superseded by
> [`../kernel/substrate-rewrite.md`](../kernel/substrate-rewrite.md). Rows and
> observations do not mint facts; checked nucleus transitions are the authority
> boundary. This note remains as prior art for scoped trust reporting.
>
> How *untrusted* code (a WASM executor, a
> "trust the bytes" backend, an external solver) feeds facts into the kernel's
> HOL model **without growing the TCB** — by routing every claim through a
> *validator* trusted only for a specific *observer type*. The computational
> metatheory this realizes is [`metatheory.md`](../logics/metatheory.md); the
> broader base-logic / meta-assumption substrate is
> [`pure-design.md`](../kernel/pure-design.md).
>
> **Note on prior art.** An earlier kernel *did* implement an observer substrate
> (`trait Observer` + `ObsEq`/`ObsTrue`/`ObsImp` policy traits + `Thm::obs_*`
> rules, sound under a parametric ε-model). That surface was **removed** in the
> observer/literal purge: facts then entered as base-layer axioms / `IsThm`
> certificates rather
> than obs-rules. This doc is the *validator concept* that direction still wants;
> read it as design, not as a description of current code.

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
[`VISION.md`](../vision/VISION.md).

---

## 2. Observer vs. validator

Two roles, with a sharp trust boundary between them:

- **Observer** — *untrusted*. Can **only assert** facts; it can never
  deny one. It is fed arbitrary, possibly interactive, witnesses by the
  user and turns them into asserted facts. An observer is *any* Rust
  type, wrapped in a type-erased leaf the kernel compares only by `Arc`
  pointer identity — so a misbehaving observer cannot corrupt kernel
  invariants.

- **Validator** — *trusted, but only for one observer type*. It decides
  which asserted facts are admitted; it also manages a model, a
  precondition set, and frozen flags (§3):

  ```rust
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

Facts that relate an observation to an ordinary term enter as **explicit
meaning axioms** (an added hypothesis) that stay visible in every
dependent theorem's hypotheses. Those hypotheses *are* the "scoped
assumptions" at the end of the pipeline, and the seed of the precondition
set in §3. There is deliberately **no kernel rule** that silently asserts
"this observation equals this real term."

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
  // Illustrative validator sketch.
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
computational metatheory*: it starts as a trusted validator; the long-run
goal ([`metatheory.md`](../logics/metatheory.md)) is to **replace the trust with
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
  [surface syntax](../surface/surface-syntax.md); an observer-backed theory is a
  spec whose axioms are *attested* rather than *proved*.
- **Metatheory** — observers are the *computational* half of metatheory
  ([`metatheory.md`](../logics/metatheory.md)); the "get rid of the oracles"
  program is precisely the migration of trusted validators into proved
  checkers.
- **Stores** — the natural home for a validator's frozen `(M, P)` is a
  content-addressed store ([`VISION.md`](../vision/VISION.md)); a frozen model
  is just a blob, and "which executor backs this" is a manifest edge.

---

## 7. Literals as validators (superseded framing)

An earlier version of this doc proposed making the built-in literals
(`Int`/`Bytes`/`Nat`) into *trusted observers*. The chosen direction is
different: literals **denote** via uninterpreted `toHOL` base ops + `IsThm`
certificates, and the `TermKind::Int`/`Blob` leaves are being **deleted**, not
reclassified as observers (see
[`literal-endgame-design.md`](../kernel/literals/literal-endgame-design.md)).

Two ideas survive the reframing and stay relevant here:

- **Open term matching.** Replacing the closed `TermKind` enum with an open
  dispatch means adding/removing a literal carrier is not a kernel-enum edit.
- **Provenance → "this proof doesn't use `Nat`."** The set of accelerators a
  `Thm` leans on is *visible*, so a proof that avoids the `Nat`/`Int`/`Bytes`
  fast paths is identifiable. Develop Peano arithmetic *without* the accelerator,
  show it categorical, and *identify* the efficient `Nat` with the defined
  naturals — the accelerator becomes **known-sound by a proof, not assumed**
  (the §4 "trust the WASM spec → prove it instead" pattern turned on the
  kernel's own numeric primitives).
