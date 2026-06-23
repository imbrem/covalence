# Covalence — Surface Language: theories, models, and the multi-stage compiler

> **DESIGN SKETCH — the canonical surface-language doc.** Unifies the
> `surface/` AST sketch and the working `script/` `.cov` tactic language into
> **one language**: a multi-stage compiler whose central first-class objects
> are **theories** and their **many models across many logics** — the
> realization of [`frontend.md`](./frontend.md) §3 (terms-as-interpreted) and
> [`metatheory.md`](./metatheory.md) §7 (handler dispatch). The
> signature/theory/model architecture and the consumability matrix are
> sharpened in [`theories-models-and-logics.md`](./theories-models-and-logics.md);
> the surface *syntax* forms are in [`surface-syntax.md`](./surface-syntax.md).

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

### 1.1 A theory's *order* bounds where it can be interpreted

Not every theory can be interpreted in every logic — and the dividing line is
the theory's **order**, which the compiler can *detect* from its signature and
axioms:

- A **first-order** theory quantifies only over individuals (its sorts), with
  first-order operations and axioms. It can be interpreted in **any** logic —
  every logic has individuals — so a fact proved in a first-order theory has
  *maximum reach* (this is the formal backbone of the "weakest sufficient
  logic = broadest applicability" idea, [`metatheory.md`](./metatheory.md) §2).
- A **higher-order** theory quantifies over functions or predicates. It can
  only be interpreted in a **higher-order** logic (one able to host that
  quantification — HOL, an elementary topos, …).

So order classification is a *gate on the model graph*: when the user asks for a
model of theory `T` in logic `L`, the compiler can say up front whether that is
even possible (`first-order(T)` ⟹ always; otherwise `L` must be higher-order).
Equational theories (`#clause`) are the most portable first-order case — they
interpret in every Cartesian category — which is why `#clause` stays the
distinguished equational form even though `#spec P` ([`surface-syntax.md`](./surface-syntax.md)
§3.1) admits arbitrary first-order propositions. "Detecting and handling
first-order theories specifically" is therefore not a special case bolted on; it
is the compiler reading off each theory's reach.

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
`#sig`, `#thy`, `#logic`, `#model`, `#in`, `#transport`.

### 3.0 `#sig` / `#thy` — signatures and theories (the surface↔script fusion)

There is **one language**: the `.cov` script language gains the theory-defining
forms, so surface and script are fused (not two languages). A **signature** is a
*name + sorts/families (kinded) + operations*; a **theory** is *a signature +
named axioms* — exactly the `Signature`/`Theory` data the `Logic` trait consumes
(`theories-models-and-logics.md §1`).

```scheme
(#sig Nat                          ;; NAME — also the content-address anchor (§ O256)
  (sort α)                         ;; type part: kind-ty carrier(s)…
  ;; (family m (-> ty ty))         ;; …and kind-ty→ty families (HOL-ω)
  (op zero α)                      ;; operations, typed over the sorts
  (op succ (-> α α))
  (op add  (-> α α α)))

(#thy NatTheory
  (over Nat)                       ;; a signature ref (`over`/`sig`), or inline (#sig …)
  (#spec add.zero (forall (a α) (= (add a zero) a)))        ;; a proof OBLIGATION,
  (#spec add.succ (forall (a α)(b α) (= (add a (succ b)) (succ (add a b)))))  ;; not a postulate
  (#spec induct  …))
```

**Files + typed import.** A **`.sig`** file *is* a `(#sig …)` body; a **`.thy`**
file *is* a `(#thy …)` body — like `.cov` but restricted to defining a single
signature/theory. You either inline the body — `(#thy (… contents …))` — or
import it **typed**: `(#import nat.thy #thy)` / `(#import nat.sig #sig)` (the
`#thy`/`#sig` tag says what kind of object you're importing, vs an untyped `.cov`
proof bundle). The typed import is what lets the compiler check, before
elaboration, that you imported a *theory* where a theory was expected.

These elaborate to the Rust `Signature`/`Theory` types; build the *syntax* as the
immediate follow-on once those types are pinned (don't fork the data shape).

### 3.0.1 The artifact taxonomy (file types)

`.cov` is the **general** format (it may contain any mix of `#def`/`#thm`/`#sig`/
…). Alongside it are **single-object, typed** files — each is the body of one
`#`-form — so a typed `(#import x.EXT #form)` knows what it's getting:

| ext | contains | surface form | one of |
|---|---|---|---|
| `.cov` | anything (general) | — | (mixed) |
| `.logic` | a **logic** (a language + rules, bundled — §3.0.5) | `(#logic …)` | a logic |
| `.sig` | a **signature** (name + kinded sorts/families + ops) | `(#sig …)` | a signature |
| `.thy` | a **theory** (a signature + named axioms) | `(#thy …)` | a theory |
| `.mod` | a **model** (an interpretation of a signature's language) | `(#model …)` | a model |
| `.thm` | a **proof of one statement** | `(#thm …)` | a theorem |

> **Punted (noted, not built):** the elaborated S-expression *IR* — the
> post-elaboration canonical form — may eventually get its own extension
> (`.cov.ir`, `.sig.ir`, …) distinct from the pre-elaboration surface text.
> Decide later; the surface forms above are the human-written layer.

### 3.0.2 A model interprets a *syntax*; "M ⊨ T" is a *theorem proved in a logic*

The decoupling (refines §1's "model = …"; full treatment in
`theories-models-and-logics.md §1`). A **logic** bundles two aspects: a
*language* (a typed grammar — what can be **stated**) and *derivability rules*
(what can be **proved**). Intuitionistic and classical FOL are two logics over
the *same language*, related by a language-iso — but we keep language + rules
bundled in the one `Logic` object rather than reifying a separately-shared syntax
(asking "same syntax?" by identity would be *evil* — it distinguishes isomorphic
languages; `theories-models-and-logics.md §1`). Then:

- A **model `M`** is an **interpretation of a logic's *language*** — concrete
  objects for the signature `S`'s sorts/families/ops. Pure semantics; *nothing
  about axioms*. It just realizes the vocabulary; models relate by iso-transport.
- A **theory `T`** is *also over `S`* — `S` + axioms (formulas in the language).
- **"`M` is a model of `T`" (`M ⊨ T`)** is a **`.thm`** — a proof, **carried out
  in a *logic***, that `M`'s interpretation *satisfies `T`'s axioms*. This is
  *the* load-bearing statement, and which logic it's proved in is part of it: a
  Heyting-valued `M` satisfies the intuitionistic `T`, a Boolean one the classical
  `T`.

So the artifacts separate cleanly: **interpret the vocabulary** (`.mod` realizes
a logic's language), **state the laws** (`.thy`), **prove the interpretation obeys
the laws in a logic** (`.thm`, `M ⊨ T`). A model of the signature can perfectly
well *fail* a given theory — that's a `.thm` that doesn't go through — and may
satisfy `T` under one logic but not another. The type system makes all of this
explicit rather than silent. (Seam realization: `Logic` + `Model` traits,
`theories-models-and-logics.md §1.1`.)

### 3.0.3 `#model` / `#models` — declaring a model and certifying satisfaction

```scheme
;; A MODEL of signature Nat — interprets the vocabulary at a carrier (.mod).
;; Pure semantics: a carrier + a term for each op (must typecheck with A := carrier).
(#model nat/self
  (of Nat)                       ;; interprets signature Nat
  (carrier nat)                  ;; A := nat
  (zero 0)                       ;; the op interpretations (the `0` literal IS nat.lit 0)
  (succ nat.succ)
  (add  nat.add)
  (induct induct))               ;; the induction handler, named by tactic ref

;; SATISFACTION — "nat/self models NatTheory" (M ⊨ T), a .thm. For each axiom of
;; NatTheory, the goal is the axiom INSTANTIATED at the model (A := carrier, op
;; symbols := interpretations) — built by RE-ELABORATING the axiom's stored sexpr
;; against the model's carrier+ops, not by term substitution. Each must be PROVED,
;; and its conclusion re-checked against that goal. Certifying it blesses the
;; model's env (ops + verified axioms + `m.induct`) for `(#in nat/self …)` dispatch.
(#models nat/self NatTheory
  (zero.add (#proof (lemma)))    ;; a (#proof …) when the goal is α-identical to a
  (add.zero (#proof (lemma)))    ;;   kernel lemma; a (#by …) tactic script otherwise.
  (succ.add (#proof (lemma)))    ;;   (`apply` can't match a still-∀-quantified goal,
  (add.succ (#proof (lemma))))   ;;    so direct lemma refs are the clean form here.)
```

> Sort variable spelled `A` (ASCII) in the implementation; `α` also parses. The
> `(from WITNESS)` form — `(#models nat/unary NatTheory (from unary))` — sources a
> host-supplied (Rust) witness env, keeping `nat/unary`'s heavy `unit`-singleton
> proofs in `models::unary` until ported to `.cov` (transitional; SKELETON'd).

`(#models M T …)` reads "M models T". It is the single load-bearing statement
type (§3.0.2). The model's env — abstract op names (`m.zero`/`m.add`/…) bound to
the interpretations, plus the verified axioms bound under the theory's axiom
names — is exactly what the abstract `add_comm.cov` proof dispatches over via
`(#in M …)` (the Track 1 mechanism, now sourced from the *declared* signature +
theory instead of a hand-built Rust env). The satisfaction proofs are
genuinely per-model (e.g. `nat/unary`'s `add.succ` needs the `unit` singleton),
so they live in the `(#models …)` block — or, transitionally, a host-supplied
witness `(#models nat/unary NatTheory (from unary-witness))` keeps a heavy Rust
proof (e.g. `models::unary`) in place until it's ported to `.cov`.

### 3.0.4 North stars (don't preclude these)

Two directions the forms above must stay compatible with — **architectural
constraints, not near-term work**:

1. **`.thy` is the elaboration target of a Haskell-like surface.** A `#type`
   declaration + function type signatures + defining equations
   ```haskell
   #type nat
   add :: nat -> nat -> nat
   add zero a        = a
   add a zero        = a
   add (succ a) b    = succ (add a b)
   ```
   elaborates to a `(#sig …)` + `(#thy …)`: the **`#type nat`** → the signature's
   `(sort nat)`; each `::` type signature → an `(op …)`; each defining equation →
   a **`#spec`** (an equational clause, with the *positional* LHS/RHS quantification
   rule — LHS pattern variables universally bound, RHS-only existential;
   `surface-syntax.md §4.1`). So `nat.sig`/`nat.thy` are *extractable from* such a
   file. Concretely (a longer example):
   ```haskell
   length :: list 'a -> nat
   length []        = 0
   length (x :: xs) = 1 + length xs
   ```
   elaborates to a `(#thy …)`: the `::` signature → the `(op length (-> (list 'a)
   nat))` declaration, and each defining equation → a **clause** (the surface
   AST's `#clause`/`#rw`, with the *positional* LHS/RHS quantification rule —
   LHS pattern variables universally bound, RHS-only variables existential;
   `surface-syntax.md §4.1`). So a theory's spec is *axioms and/or equational
   clauses*, and the clause form is what the pattern equations lower to. The
   `#sig`/`#thy`/`#model` forms are the **explicit, lower** layer this surface
   compiles down to — keep them expressive enough to be that target.
2. **Models are *synthesized*, not only declared.** Beyond hand-writing
   `(#model …)`, a **tactic takes a theory's sexpr and attempts to synthesize a
   model** — in HOL, or SOA, or PA — automatically, which is tractable for nice
   subclasses (equational/algebraic theories, decidable theories). Crucially,
   **`#inductive` is then subsumed**: declaring a datatype is "synthesize the
   *initial* model" of the (free/equational) theory of its constructors. So the
   `Model` object must be **producible by a tactic**, not only by `(#model …)`;
   `#model` is the manual producer, model-synthesis the automatic one, and both
   yield the same thing a `(#models …)` certificate certifies and `(#in …)`
   dispatches over. Concretely, in `.thy` files `#inductive` becomes two
   theory-level declaration forms — **`#data`** (inductive: the *initial* model /
   least fixpoint — constructors, induction, recursion) and **`#codata`**
   (coinductive: the *final* model / greatest fixpoint — destructors, coinduction,
   corecursion; e.g. streams). Each is sugar for "synthesize the initial / final
   model" of the relevant functor's theory — the two ends of the same
   model-synthesis machinery.
3. **Induction is a *type-indexed registry*, not a pile of tactics.** Don't grow a
   `nat_induct` / `list_induct` / `unary_induct` / … zoo of bespoke tactics.
   Instead, **each type tells you how to induct over it**: a registry keyed by type
   former (`nat`, `list 'a`, `tree 'a`, …) holds that type's induction (and
   recursion / case) principle, and a *single* generic `induct` tactic dispatches on
   the type of the variable it's given. This composes directly with north star 2:
   a `#data`/`#codata`-synthesized type **registers its induction/coinduction
   principle on creation**, so the generic `induct`/`coinduct` immediately works for
   it. (The current per-model `m.induct` handler in `models/` is the seed of this —
   generalize "the model supplies induction" to "the *type* supplies induction".)

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

### 3.0.5 `#logic` — declaring the logic a model/proof lives in

**A logic is *primarily a Rust trait*** (`theories-models-and-logics.md §1.1`:
the bundled `Logic` object — a *language* plus *rules*). The trait is a **code**
seam: its handlers embed real algorithms (unification, rewriting, induction,
model-checking), which is not data. Two consequences:

- **The metalogic is necessarily a native Rust impl** — HOL is the bootstrap
  floor, there is no lower level to *declare* it in. (Later a *reified* object
  logic can be a `Logic` whose handlers are HOL proofs; base HOL stays native.)
- **`(#logic …)` / `.logic` is a *derived data* layer**, not the primary form. It
  parameterizes a **generic** Rust `Logic` impl for a *family* of logics — the way
  `.thy` is data for a theory: it carries *parameters* (order class, literal
  policy, axiom/rule schemas), never handler *code*. It earns its keep exactly
  when a family with a shared generic impl appears (the first-order logics; the
  temporal cluster below) — not before, and *never* for registering the metalogic.

With that framing, the declarable object (consumed by a generic impl) looks like:

```scheme
(#logic HOL
  (order higher)                 ;; first | higher | omega — the LANGUAGE class
  (literals                      ;; literal POLICY (see below): kind → target sort
    (int    Int)                 ;;   an int literal elaborates at sort Int…
    (nat    Nat)                 ;;   a nat literal = a non-negative int, sort Nat
    (string String)
    (bytes  Bytes))
  (rules …))                     ;; the handler set (rewriter/unifier/induction/LEM/…)
```

`order` is where the eventual specialization lives — **first-order, higher-order,
HOL-ω** logics differ in their language class (the statability axis,
theories-models §3.1), so a `.logic` is the natural place to pick it. A model is
interpreted in a logic's language; the satisfaction `.thm` (`M ⊨ T`) is checked
*in a logic*; `(#in …)`/`(#models …)` run against the ambient logic.

**Literals split across two layers — get this right.** A `#logic` carries literal
*policy* (metadata), a `#model` carries literal *realization*:

- The **logic** says *which literal kinds it admits and at what target sort* — the
  `literals` block above. This is part of statability: a logic may admit no string
  literals, or place int literals at sort `Int`. (`nat` literal = non-negative
  `int` literal, one entry, per §1.1.)
- The **model** says *how a literal becomes a concrete carrier term* — the
  model-relative, fallible `lift_int`/`lift_string`/`lift_bytes` of §1.1. This
  *must* stay on the model, because two models of one theory in one logic lower
  `3` differently (`nat/self` → builtin `nat` literal; `nat/unary` → `cons
  unit.nil³ nil`). The logic fixes the *sort*; the model fixes the *value*.

So the responsibility chain for a literal `3` is: the **logic** admits it and
assigns sort `Nat`; the **model** realizes it as a carrier term. (Both are the
`covalence-pure` literal-as-lifted-observation mechanism, `covalence-pure.md §3`,
surfaced at the right layer.) For now there is one ambient logic (HOL, a native
trait impl); the declarable `.logic` layer matters once a *family* with a generic
impl is in play.

**The logic zoo — CTL / LTL / PCTL / CTL\*.** The temporal/probabilistic logics
are the motivating case for both halves above. As **trait impls**, each is a
`Logic` whose handler set *is a model checker* — a **decision procedure** over a
structure (a Kripke transition system for CTL/LTL/CTL\*, a Markov chain for
PCTL). That makes them the paradigm of "a decidable logic doubles as an
accelerator/handler": discharge a CTL fact into HOL by checking the model
checker's certificate, or attest it through the observer substrate
(`observers.md`) — a natural fit for a WASM oracle producing the witness. They are
attractive *early non-HOL* `Logic` targets precisely *because* they are decidable
(the handler is an algorithm, not a proof calculus). As a **family**, they share
heavily — temporal operators, Kripke semantics, the **modal μ-calculus** as a
unifying substrate (CTL/LTL/CTL\* all embed into it) — so a generic
`TemporalLogic` impl parameterized by fragment + structure type, with `.logic`
data picking the fragment, is exactly where exposing the declarable object pays
for itself.

**The unifying answer (user): a `#logic` *is* a Metamath database.** What the
declarable `.logic` data *is* — what parameterizes the generic `Logic` impl — was
the open question. The answer: a logic's axioms + inference rules **as
substitution schemas over `SExpr`**, i.e. a **Metamath database**
(`theories-models-and-logics.md §5.6`). The pure metavariable-substitution
metalogic is universal, so "define a logic" = "write a database", and the generic
`Logic` impl for the dominant family (anything that is *axioms + rules*) **is the
Metamath substitution engine**. Crate boundary (user): that engine — the
expression model, substitution, frame/DV, derivability `Derivable_L`, and the
`S`-rewrite transport — lives **first-class in `covalence-hol`** (it is core to
defining logics and doing metatheory); **`covalence-metamath` is demoted to the
format/IO reader** (compressed-proof decoding, `.mm` file parsing, `$[ $]` file
inclusion, set.mm ingestion) so that machinery doesn't clutter `covalence-hol`.
The Rust `Logic` *trait* still tops it (native impls like the metalogic itself,
model-checker handlers, …), but the **database is the data the common case
consumes**, and `Metamath-L ≅ native-L` (§5.6) is how native/HOL/WASM accelerators
plug in.

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
  concrete text  (infix, precedence, notation — what a human writes)
     │  0. READ         operator-precedence (Pratt) parse → canonical S-expr
     ▼                  (surface-syntax.md §1.5; the pure S-expr stays canonical)
  surface text  (canonical pure S-expr)
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

## 9. The registry API: scoped, never global

The dispatch of §2/§4 and the lifting of §5 need registries — of handlers,
models, logics, isomorphisms, transitivity rules. **None of them is global
state.** Every registry is a *value threaded through lexical scope*, registered
in place and brought into view with explicit `#open` / `#use` / `#in` — exactly
the discipline the working `Env` already uses for names. (A memoized *pure*
theory — today's `cov_theory!` `LazyLock` — is fine: it caches a deterministic
value, content-addressable, not mutable shared state. What is ruled out is a
mutable global *registry* two runs could observe differently.)

### Generalize the `Env`, don't add singletons

Today `script::Env` is an immutable persistent map (`imbl::HashMap`, O(1) clone,
copy-on-write) of `name → {const | lemma | tactic}`, scoped by
`#import`/`#open`/`#use`. The new registries are *more of the same* — additional
scoped bindings in the same resolution context, never a `static`:

```rust
// One scoped resolution context. Cloning is O(1) (persistent maps);
// "registering" returns a copy-on-write child, never mutates a global.
struct Context {
    names:  LazyMap<Entry>,   // consts / lemmas / tactics / models / logics /
                              //   isos / trans-rules — all name-addressable,
                              //   one #open / #use rule for everything
    active: HandlerSet,       // the handlers currently in force
}

struct Logic  { handlers: HandlerSet, derivable: Option<Reified>, /* … */ }
struct Model  { theory: Name, logic: Name, interp: Interp, lifters: Lifters }
struct HandlerSet { rewrite: Handler, unify: Handler, reduce: Handler,
                    induct: Handler, decide: Handler /* op → handler */ }
```

### Registration is in-place; scoping is explicit and reversible

- `(#open logic.HOL)` / `(#use M)` — merge a registry's bindings into the
  current scope (additive, shadowing): the *same* mechanism that opens a
  namespace today.
- `(#in model …)` — run the body in a **child** context with that model's
  logic's `HandlerSet` installed as `active`, then pop back out. Lexical,
  explicit, reversible — no ambient handler outlives its block.
- A handler is not a free-floating global you `register!()` at startup; it
  arrives **as part of a logic**, installed wholesale when you enter that
  logic's / model's scope. *"Register handlers in-place with explicit
  open/use"* is the whole API.

### Dispatch reads the current context, never a global

Stage-3 resolves "rewrite this" / "induct" / "lift `42`" against `ctx.active`;
`#comp`'s default handler is `ctx.active.rewrite` (or an explicitly
`#:by`-named one). The `apply_unify` / `rw_unify` seams that are *methods on
`Env`* today become `ctx.active.unify` / `.rewrite` lookups — the seam **is**
the registry entry. Because a proof's meaning is a pure function of its
lexically-visible `Context`, it is reproducible and content-addressable (the
context is a value you can hash); there is no hidden mutable global to make two
runs disagree.

### The one design fork

Keep the **named** registries (consts/lemmas/tactics/models/logics/isos/
trans-rules) in *one unified namespace* (extend today's `Entry` with the new
variants — one `#open`/`#use` rule for everything), but carry the
**operation-keyed handlers** in a `HandlerSet` installed *by a logic* rather
than naming each handler individually. Rationale: names want uniform
open/use/shadowing; handlers are selected by *operation* (and the active logic),
not by a user-written name, so bundling them per-logic is simpler and matches
"open a logic, its reasoning comes with it." (The alternative — separate typed
maps per registry — buys a little type-safety for a lot of parallel scoping
plumbing; not worth it, given the unified `Env` already works.)

## 10. Incremental plan (what to build first)

1. **De-panic the front.** Add source **spans** + a `Diagnostic` type through
   parse; convert `ScriptError` paths to accumulating diagnostics. (Pure
   plumbing; unblocks everything.)
2. **`#logic` / `#model` surface forms** — parse + resolve only, no dispatch yet
   (extend `surface::Builtin` + the AST + a `Model`/`Logic` registry, with the
   `#lift` clause of §5 and an isomorphism registry of §4).
3. **`#in model` swaps the active handler set — in a *scoped*, non-global
   `Context` (§9).** A `Model` = (theory, a logic-handler set, an
   interpretation map, its lifters); entering a model installs its handlers
   into a child context and pops back out. Reuses the existing
   `Env`-as-dispatcher (copy-on-write persistent maps) directly — no `static`
   registry anywhere.
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
