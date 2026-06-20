# Covalence — Surface Language: theories, models, and the multi-stage compiler

> **STATUS: DESIGN SKETCH.** Unifies the `surface/` AST sketch and the working
> `script/` `.cov` tactic language into **one language**: a multi-stage compiler
> whose central first-class objects are **theories** and their **many models
> across many logics**. This is the concrete realization of
> [`frontend.md`](./frontend.md) §3 (terms-as-interpreted) and
> [`metatheory.md`](./metatheory.md) §7 (handler dispatch) — the "what's
> provable in which logic, on which language" workspace, made into a compiler.
>
> See also: [`surface-syntax.md`](./surface-syntax.md) (the surface *syntax*
> forms this builds on), the working `crates/covalence-hol/src/script/` (today's
> `.cov` tactic language — the eventual *low-level target* of this compiler),
> [`metatheory.md`](./metatheory.md) (reified object logics, morphisms),
> [`observers.md`](./observers.md) (untrusted handlers feeding the kernel).

---

## 1. The headline: a theory has many models, in many logics

A **theory** is an abstract signature + axioms — *the naturals*: `0`, `succ`,
`+`, `×`, with the Peano axioms. A **model** interprets that theory **into a
particular logic** via a **carrier**. The decisive point: one theory has *many*
models, and those models live in *different logics*.

For the theory `Nat`:

| model | logic | carrier | `0 ↦` | `succ ↦` |
|---|---|---|---|---|
| the naturals themselves | HOL | `nat` | `nat.zero` | `nat.succ` |
| naturals in nested PA | PA *(reified in HOL)* | PA's number sort | `PA.0` | `PA.S` |
| naturals in nested SOA | SOA *(reified in HOL)* | SOA's number sort | `SOA.0` | `SOA.S` |
| unary encoding | HOL | `list unit` | `nil` | `cons unit.nil` |

"**Nested**" PA / SOA means the model lives inside an object logic that is
*itself* reified in HOL ([`metatheory.md`](./metatheory.md) §1) — **models recurse
through the metalogic.** A statement about `Nat` is therefore not tied to one
realization; it is a thing you can *evaluate, prove, and transport* across all
these models. That is the whole point of making models first-class: the user
reasons about `Nat`, and the system tracks *where* (in which logic, on which
carrier) each fact has been established.

---

## 2. Why this *is* the effect system

Reasoning *in* a model means using that model's logic's **tactics** — rewriting,
unification, induction, reduction — and those differ per logic. Proving
`n + 0 = n`:

- in HOL `nat` — HOL nat-induction + `reduce`;
- in PA-reified — PA's induction **schema**, a derivation in `Derivable_PA`;
- in `list unit` — list induction + the encoding's lemmas.

The *same* surface tactic `(induct n)` must dispatch to the right handler for the
**active model's logic**. That dispatch *is* the algebraic-effect system of
[`metatheory.md`](./metatheory.md) §7.2 / [`frontend.md`](./frontend.md) §4: a
tactic **requests** "induct"; the **environment — fixed by the active model —
supplies the handler.**

So "a theory with many models across many logics" and "handler-dispatched
reasoning" are *two views of one mechanism*:

> **a model = (a logic's handler set) + (an interpretation of the theory into
> that logic).**

And dispatch has a standing preference: **always reach for an isomorphic model
when you can** (§4). Isomorphic models transport facts losslessly in both
directions, so the dispatcher routes each operation to the cheapest
representative of an isomorphism class rather than re-proving — `nat ≅ list unit`
means a fact proved in either is a fact in both.

The effect system is not an add-on to the many-models idea; it is what makes the
many-models idea *executable*.

---

## 3. The first-class objects (surface forms)

Illustrative — exact grammar TBD; all forms stay pure `#`-headed S-expressions
([`surface-syntax.md`](./surface-syntax.md) §1.3). They extend the existing
`surface::Builtin` set (`#theory`/`#decl`/`#clause`/`#def`/`#thm`/`#import`) with
`#logic`, `#model`, `#in`, `#transport`.

```scheme
;; A THEORY: abstract signature + axioms (exists today, generalized).
(#theory Nat
  (#tydecl (Nat #ty))
  (#decl (#sig zero Nat)
         (#sig succ (#fn Nat Nat))
         (#sig add  (#fn Nat Nat Nat)))
  (#clause (#rw (add zero n) n))
  (#clause (#rw (add (succ m) n) (succ (add m n)))))

;; A LOGIC: a named handler environment — the unifier, rewriter, reducer, and
;; induction principle installed; plus, for an object logic, its reified
;; derivability predicate.  (New.)
(#logic HOL …)     ;; HO unifier, reduce/delta, nat-induct
(#logic PA  …)     ;; FO unifier, the PA induction schema, Derivable_PA
(#logic SOA …)     ;; second-order arithmetic, reified

;; A MODEL: the theory interpreted INTO a logic via a carrier + an
;; interpretation map.  (New.)
(#model nat/self  : Nat #in HOL
  (#carrier nat)
  (#map (zero nat.zero) (succ nat.succ) (add nat.add)))

(#model nat/unary : Nat #in HOL
  (#carrier (list unit))
  (#map (zero nil) (succ (cons unit.nil)) (add append)))

(#model nat/pa : Nat #in PA
  (#carrier PA.num)
  (#map (zero PA.0) (succ PA.S) (add PA.plus)))

;; WORK IN A MODEL: tactics dispatch to its logic's handlers.  (New.)
(#in nat/unary
  (#thm add-zero (#concl (#eq (add n zero) n))
    (#by (induct n) …)))      ;; (induct n) => list-unit induction here

;; TRANSPORT a theorem across models/logics (metatheory.md §3 morphisms). (New.)
(#transport (Nat nat/pa => nat/self) add-zero)
```

The crucial property: `add-zero`'s *surface statement* is identical in every
`#model`; only the dispatched handlers and the resulting kernel obligations
differ. Proven once in a model — or in the abstract theory, transported — it is
available everywhere a morphism reaches.

---

## 4. Isomorphic models and the self-model (`hol-in-hol`)

### Prefer isomorphic models

Models of a theory are related by **morphisms** (§3, `#transport`); the strongest
morphism is an **isomorphism** — a structure-preserving, *invertible* translation,
so a fact transports *losslessly both ways*: `M ⊨ φ ⟺ M' ⊨ φ` whenever `M ≅ M'`.
The dispatch rule follows: **always reach for an isomorphic model when you can.**
Treat an isomorphism class as a *single logical object* and route each operation
to whichever representative is cheapest — prove `add-zero` in whichever of
`nat ≅ list unit` is easier, transport across the iso, and it holds in both. An
isomorphism is free transport in both directions; the dispatcher prefers it over
a one-way embedding or a re-proof.

Concretely, alongside the model registry the compiler keeps a registry of
**proved isomorphisms**; stage-3 dispatch, before doing work in model `M`, first
asks "is there an isomorphic `M'` where this is already proved, or cheaper?" (A
general — non-iso — morphism is still usable, but only with the directionality
and side-conditions it carries; an iso has neither.)

### `hol-in-hol`: the self-model (first-class)

The single most important model to support first-class is **`hol-in-hol`**: our
HOL metatheory reified *inside itself* — a datatype of HOL terms/formulas, a
`Derivable_HOL` derivability predicate, and a denotation back into the native HOL
we actually run ([`metatheory.md`](./metatheory.md) §1). It is the model where the
system **reflects on its own logic**: "HOL proves `P`" becomes the native HOL
theorem `HOL(⌜P⌝)`. Why it is load-bearing:

- It is the canonical home of the **native ⇄ reified correspondence** (soundness
  `HOL(⌜P⌝) ⟹ P` and representability `P ⟹ HOL(⌜P⌝)`) — the adequacy that makes
  the reified HOL *faithfully* model the real one. That correspondence is exactly
  the kind of (near-)isomorphism the dispatch rule wants: it lets work hop between
  *proving `P`* and *proving `HOL(⌜P⌝)`*.
- It is the **`ToHOL` reading** of the source-language picture
  ([`frontend.md`](./frontend.md) §3): a source term `S` interpreted "in HOL"
  lands in `hol-in-hol`.
- It is where `covalence-pure`'s `IsThm(theHOL)`
  ([`kernel-design.md`](./kernel-design.md) §11.2) is reified — the HOL observer
  lifted into a model.
- It is the base case for **HOL-to-X transport**: `HOL(A) ⟹ ZFC(A)`,
  `PA(A) ⟹ HOL(A)` ([`metatheory.md`](./metatheory.md) §3) all speak about
  `hol-in-hol`, so making it first-class is the prerequisite for the morphism
  layer between *every* logic and HOL.

So `hol-in-hol` is both a concrete model the user can work in and the **hub** the
model graph is organized around — the logic every other reified logic transports
through.

## 5. Lifting literals, data, and programs (the `covalence-pure` embedding)

A surface term doesn't only mention a theory's declared operations — it mentions
**concrete data**: numeric and string literals, raw bytes, content-addressed
references, and whole **computer programs** (WASM). The surface language gives
**first-class, model-relative lifting** for all of these, and the lifting
mechanism *is* `covalence-pure` ([`kernel-design.md`](./kernel-design.md) §11):
each literal/data form is a **trusted observer** that mints an opaque fact, lifted
into the active model's logic under a meaning assumption.

What lifts — *where appropriate* (a model declares which forms it supports, and
how):

| surface form | observer mints | carriers it can lift into |
|---|---|---|
| natural literal `42` | "the nat 42" | HOL `nat`; `list unit` (unary); PA numeral `S…S0` |
| integer literal `-7` | "the int −7" | HOL `int`; a ring carrier |
| string literal `"foo"` | "these code units" | HOL `list char`; `bytes`-as-UTF-8 |
| byte literal `b"…"` | "these bytes" | HOL `bytes`; `list u8` |
| content-addressed ref (an `O256`) | "the blob with this hash" | a store-backed carrier; an opaque handle |
| WASM program | "this component, run under `T_wasm`" | the executor-semantics carrier; an oracle |

Two things make this first-class rather than ad-hoc:

1. **It is model-relative.** Lifting `42` into the `nat` model is the kernel `nat`
   literal; into `list unit` it is a unary list; into a reified PA model it is the
   object numeral `S(S(…0))`. The *same* surface `42` dispatches to the model's
   declared lifter — the §2 effect dispatch, applied to literals instead of
   tactics. A model with no sensible lift for a form simply doesn't declare one;
   using that form there is a diagnostic, not a silent coercion.
2. **It is the `covalence-pure` lift, so it is trust-honest.** A lifter is a
   trusted observer ([`observers.md`](./observers.md) §7): efficient (the kernel's
   built-in `Nat`/`Int`/`Blob` literals are the fast representation) but, under
   paranoid mode ([`kernel-design.md`](./kernel-design.md) §11.5), demotable to a
   checked construction. A **content-addressed** lift is the store assumption
   discharged operationally; a **WASM** lift is the WASM observer (Track D), whose
   fact `run(B,x)=y` enters as a *scoped hypothesis* until discharged against the
   SpecTec-lowered `T_wasm`. Lifting a program is *not* "trusting the program" — it
   is minting an opaque observation and carrying its meaning as an assumption,
   exactly as §11.2 prescribes.

In surface form, a model's lifters sit alongside its interpretation map:

```scheme
(#model nat/unary : Nat #in HOL
  (#carrier (list unit))
  (#map  (zero nil) (succ (cons unit.nil)) (add append))
  (#lift (nat unary-of)))               ;; 42 ↦ a length-42 (list unit)

(#model bytes/hol : Bytes #in HOL
  (#carrier bytes)
  (#lift (byte id) (string utf8) (blob id) (content store-get)))

(#model wasm/oracle : … #in HOL
  (#lift (wasm (exec-under T_wasm))))    ;; a program ↦ its observed result
```

This is where `covalence-pure` becomes *visible in the surface*: literals, hashes,
and programs are not magic kernel built-ins but **lifted observations**, and the
model chooses how each lands.

## 6. The compiler: stages

`script/` today is a single replay pass (`run` → `check`). The proper language is
a **multi-stage compiler**; each stage produces typed IR, and errors are
**diagnostics with spans, propagated** (never panics):

```
  surface text
     │  1. PARSE        surface S-expr → surface AST  (+ source spans)
     ▼
  surface AST
     │  2. RESOLVE      names, imports, #theory/#logic/#model into scopes
     ▼
  resolved AST
     │  3. ELABORATE    HM type inference + desugar  +  MODEL/LOGIC RESOLUTION:
     │                  pick the active model, select its handler set, turn
     ▼                  model-relative tactic requests into handler calls
  core IR (logic-resolved, handler-annotated)
     │  4. LOWER        → low-level commands: the kernel-coupled core ops
     ▼                  (today's drv.rs rules + the obligations handlers emit)
  command stream
     │  5. CHECK        replay against the kernel → Thm  (or a future, per the
     ▼                  async-prover layer)
  checked theory
```

- **Stage 3 is where the effect dispatch lives.** It is the generalization of
  today's `Env` name-resolution + the `apply_unify`/`rw_unify` seams + the
  `infer.rs` elaborator: extended to *also* resolve which model is active and
  bind each tactic request to that model's logic's handler.
- **Stages 4–5 are essentially today's `.cov` backend** (`drv.rs` + `check` +
  `run_thm`). They stay; they become the compiler's *backend*, with the surface
  language compiling *down to them*.

---

## 7. Error handling and propagation

Today there is a flat `ScriptError` and a few panic paths (the nested-runtime
hazard that motivated `#spawn`). A proper compiler wants:

- **Spans everywhere.** Source extents carried from parse through every IR. The
  `surface/` AST already notes spans are "not yet carried" — this is the hook;
  add them at stage 1 and thread them.
- **A `Diagnostic` type** (severity, span, message, related notes) **accumulated
  and reported as a group**. The `LazyMap` already holds *deferred* errors à la
  Python's `ExceptionGroup` ([`SKELETONS.md`](../SKELETONS.md)) — generalize that
  into a diagnostics sink.
- **Staged, accumulating failure.** A stage yields *either* typed IR *or*
  diagnostics; later stages don't run on a hard error, but a stage reports *all*
  its independent errors at once (parse the whole file, list every syntax error
  — don't stop at the first).
- **Obligations as first-class values, not panics.** An unproved goal is not a
  crash but a *hole / obligation* threaded through — ties into the async-prover
  futures and the removed `#hole`/`#fill` (rebuild on this), so a partially
  elaborated theory is a normal, inspectable value.

---

## 8. Relationship to today's code (the migration)

| Today | Role in the compiler |
|---|---|
| `script/` — `Env`, `tactic.rs`, `drv.rs`, `infer.rs`, `check`/`run_thm` | the **low-level target + backend** (stages 3-elab-core, 4, 5); kept |
| `surface/` — `ast.rs`, `parse.rs`, `Builtin` | the **front** (stages 1–2); flesh out the AST with theories/logics/models + spans |
| `Env` namespace + `#register-ffi-tactic` + `apply_unify`/`rw_unify` seams | the **seed of the per-logic handler set** (stage 3 dispatch) |
| `infer.rs` HM elaborator | stage-3 type inference, generalized to carry an interpretation target |
| *(new)* a `Logic` / `Model` registry | the **middle** the compiler gains |

Nothing in `script/` is thrown away — it *becomes* the backend the surface
language compiles into. The TCB is unchanged: handlers emit kernel-checkable
obligations exactly as `.cov` rules do today.

---

## 9. Incremental plan (what to build first)

1. **De-panic the front.** Add source **spans** + a `Diagnostic` type through
   parse; convert `ScriptError` paths to accumulating diagnostics. (Pure
   plumbing; unblocks everything.)
2. **`#logic` / `#model` surface forms** — parse + resolve only, no dispatch yet
   (extend `surface::Builtin` + the AST + a `Model`/`Logic` registry, with the
   `#lift` clause of §5 and an isomorphism registry of §4).
3. **`#in model` swaps the active handler set.** A `Model` = (theory, a
   logic-handler `Env`, an interpretation map, its lifters); entering a model
   installs its handlers. Reuses the existing `Env`-as-dispatcher directly.
4. **Two *isomorphic* HOL models, one tactic, lifted literals.** Use
   `nat/self ≅ nat/unary` (both HOL — no new logic needed): wire `(induct n)` to
   dispatch *HOL-nat* vs *`list unit`* induction, wire the §5 lift of the literal
   `42` into each carrier, and prove the `nat ≅ list unit` **isomorphism** so a
   result transports across it (§4). Smallest end-to-end proof that dispatch +
   lifting + iso-transport all work — buildable today.
5. **Cross-logic models + `hol-in-hol`.** Stand up `hol-in-hol` as the hub (§4),
   then `nat/pa`, `nat/soa` once Track A's reified PA / SOA logics exist; now
   `(induct n)` dispatches to the PA/SOA induction *schema*, `#transport` moves
   results across the morphism graph, and the WASM/content lifts of §5 (Track C/D)
   come in. This is where "many models across many *logics*" becomes real.

Step 4 is the milestone to aim for first: the *same* `(induct n)` proving
`add-zero` across two *isomorphic* models of `Nat`, with `42` lifted into each
carrier and the result transported over the iso — the many-models, effect-system,
lifting, and iso-dispatch ideas end to end, on machinery that exists today.
