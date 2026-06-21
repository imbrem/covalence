# Covalence — Metatheory: Theories, Derivations, and Models

> **STATUS: DESIGN SKETCH — sharpened by the canonical docs.** This is the
> early sketch of "object theories + their derivations as first-class HOL
> objects." Its core mechanism — reify a logic as a datatype + a
> `Derivable_X` predicate + a denotation, prove `Derivable_X ⌜A⌝ ⟹ ⟦A⟧`
> internally — has since **landed** (`init/prop.rs`, the PA deep embedding)
> and been **sharpened** into the now-canonical framing: see
> [`theories-models-and-logics.md`](./theories-models-and-logics.md) §5.5
> (the two pillars + the PA→SOA→ZF chain) and **§5.6/§5.7 (Metamath as the
> shared logic-definition substrate / the thin waist)**, plus
> [`VISION.md`](./VISION.md) §1 (the three-layer stack) and
> [`surface-compiler.md`](./surface-compiler.md) §3.0 (the `#sig`/`#thy`/
> `#model`/`#logic` artifact forms). **Read those for the current design;
> read this for the *rationale* and the still-aspirational pieces** (the
> metavariable layering §5, the handler-dispatch effect framing §7, the
> design-compatibility audit §9).
>
> See also: [`observers.md`](./observers.md) (the computational half),
> [`surface-syntax.md`](./surface-syntax.md) (how theories are written),
> [`kernel-design.md`](./kernel-design.md) (the HOL kernel these object
> theories are built inside).

---

## 1. The core idea: theories _inside_ HOL

Our kernel is an HOL-Light-style metatheory. The plan is **not** to make
PA, ZFC, etc. new trusted logics — it is to **define each of them as an
ordinary datatype inside HOL**:

- a type of **formulas** of the object theory,
- an inductive **derivability** predicate `Derivable_X : formula → bool`,
- a **denotation** `⟦·⟧` mapping object formulas into HOL propositions
  under a chosen model.

Then the headline judgement of the sketch —

```
   HOL(A);   PA(A);   ZFC(A)
```

— is read as `X(A) ≜ ⊢_HOL Derivable_X ⌜A⌝`: "_A_ is a theorem of theory
_X_" is itself an ordinary HOL theorem about the reified object theory.
This is the reflective core of "metatheory is the default mode."

Concretely, the sketch's two layers for one theory:

```
   ( theory of peano arithmetic )      ;; the formulas + axioms of PA
   ( theory of PA _derivations_ )      ;; the inductive proof trees over them
```

---

## 2. Soundness: proving instead of trusting

> _Prove PA is sound under standard denotation: if ∃ derivation, then
> true._

The key theorem schema:

```
   ⊢_HOL   Derivable_PA ⌜A⌝   ⟹   ⟦A⟧      (under the standard model)
```

"If there exists a PA derivation of _A_, then _A_ holds." This is the
mechanism behind the OBSERVERS program of _getting rid of the oracles_
(`docs/observers.md`): instead of a validator _trusting_ a backend, we
prove its outputs sound under a formal semantics, and the trusted
validator collapses into an untrusted checker.

Its computational counterpart (the sketch's `WASM(P, D, A)` line):

```
   WASM(P, D, A)   ⟹   ∃ D'. ZFC(D', A)
```

"A WASM program _P_ run on data _D_ witnessing _A_" yields the existence
of a ZFC derivation _D'_ of _A_. The WASM run produces a _checkable
certificate_ (Alethe / DRAT / a reified derivation), and the kernel
checks the certificate — it never trusts the program. This is exactly
the "complex software enters by producing checkable certificates, not by
being formalized" claim of [`VISION.md`](./VISION.md).

---

## 3. Theory morphisms and transport

> `PA(A) ⟹ HOL(A) ⟹ ZFC(A)` &nbsp;&nbsp; `Isabelle[THRY](A) ⟹ THRY(A)`

Interpretations between theories are **proved theorems**, not trusted
glue:

- `PA(A) ⟹ HOL(A)` — every PA theorem is a HOL theorem (interpret PA's
  `nat` as HOL's `nat`); `HOL(A) ⟹ ZFC(A)` — interpret HOL inside ZFC.
  Chaining gives transport _up_ the strength hierarchy.
- This realizes the **reverse-math** discipline of the VISION doc: prove
  in the _simplest sufficient_ theory, then transport to wherever you
  want the statement-of-record. The morphism layer is MVP-scope there;
  it is the `(spec a |- spec b)` entailment question of
  [`surface-syntax.md`](./surface-syntax.md) §6.
- `Isabelle[THRY](A) ⟹ THRY(A)` — _importing_ from an external prover.
  An imported article is **not** trusted blindly (cf. the project's
  "no trust articles" stance); it is replayed/checked against our reified
  `THRY`, so an Isabelle theorem in theory `THRY` becomes one of ours
  only once `Derivable_THRY ⌜A⌝` is re-established here.
- `GT3(A)` / locale & context machinery, and model embeddings like
  `Nat → ZFSet`, are the longer-horizon items: first-class _contexts_
  and _locales_ over the reified theories.

### 3.1 Temporal and modal logics (LTL / CTL / CTL\*)

The temporal logics are object logics like any other — reified by the same
**datatype + derivability + denotation** recipe (§1), differing only in that
the *denotation* runs over **traces** (LTL — linear time) or **Kripke
structures / computation trees** (CTL, CTL\* — branching time) rather than a
single model. Their temporal operators (`◯`, `□`, `◇`, `U`, the path
quantifiers `A`/`E`) are **fixpoints**, so reifying them leans on the
list/stream and least/greatest-fixpoint machinery the catalogue is building
out.

The **decidable tiny start** is **regular languages / regular expressions**,
built over the [monoid theory](./surface-compiler.md) (`init/monoid.rs`):
a language is a set of words (monoid elements); concatenation lifts the monoid
op, and with union + Kleene star it is a **Kleene algebra** — the algebraic
core shared with ω-regular languages and LTL's automata-theoretic semantics.
It exercises the fixpoint (`star`) and the "structure-as-monoid" patterns the
full temporal logics need, on a fragment that stays decidable. See
`init/lang.rs`.

---

## 4. The LCF-style derivation API

> _Expose an LCF-style API for building derivations in some system `Thry`
> in our HOL._

For each reified object theory we expose **smart constructors** over its
derivation datatype — the LCF discipline, one level up:

- The _abstract type_ is "a value of type `Derivation_X`"; the only way
  to make one is via the inference-rule constructors of `X`.
- Building a derivation and checking `Derivable_X ⌜A⌝` are the _same
  act_, just as `Thm` in the kernel can only be built by the kernel
  rules.
- These constructors are written in the [surface syntax](./surface-syntax.md)
  `(by …)` proof vocabulary — they bottom out in ordinary HOL proofs
  about the reified `Derivable_X`, so **defining a new object logic adds
  no kernel TCB**: it is a definition + an induction principle, checked
  by the existing kernel.

This is the symbolic-metatheory analogue of the observer/validator
pipeline: there, _computational_ facts enter via checked certificates;
here, _symbolic_ facts enter via checked derivations.

---

## 5. The metavariable layering

The sketch lists three candidate layers of variables (the OBSERVERS
sketch, "how do we get rid of the oracles"):

```
   - Schemavars / Schematypes   (Isabelle-style, schematic)
   - Metavars   / Metatypes     (HOL — our metatheory)
   - Vars       / Types         (the current/object logic)
```

with metatype variables `α` _distinct from_ HOL object types, over which
we form first-order derivation trees `{a1,…,an} ⊢ conc`.

The purpose of that bottom schematic layer is specific and worth stating
plainly: **replace the kernel's complex, hand-written rules for
well-typedness, locally-nameless invariants, and unification with a
single, simple first-order logic.** In that FOL:

- **individuals are reified HOL syntax** — a variable is schematic of a
  fixed _meta-sort_ like `HOLTm` (a HOL term) or `HOLTy` (a HOL type),
  **not** of any particular HOL type;
- **predicates are the syntactic judgements** that today live as Rust
  code: `IsThm t`, `HasTy t τ`, `IsLocallyClosed t`, and friends.

So "this term is well-typed at τ", "this locally-nameless term has no
dangling de-Bruijn indices", "this is a theorem" stop being properties
enforced by bespoke kernel code and become **predicates with FOL
inference rules** — derivations, not Rust. Unification likewise becomes
ordinary first-order reasoning over `HOLTm`/`HOLTy` rather than a special
algorithm in the TCB.

> **The crucial difference from Isabelle/HOL: we do _not_ conflate
> meta-types with object types.** Isabelle/Pure is itself a typed
> metalogic whose type discipline does double duty for the object logic.
> Here the framework's _only_ "types" are the fixed, finite meta-sorts
> (`HOLTm`, `HOLTy`, `HOLThm`, …); HOL's own rich type system is just
> _data_ of sort `HOLTy` together with the `HasTy` predicate — it is not
> baked into the framework at all. The framework stays a dead-simple
> FOL; all the richness lives in ordinary predicates over reified
> syntax.

### 5.1 Decision: **start with two layers + HOL Light**

We **start with two layers**:

1. **Meta** — HOL Light, our metatheory (where reified theories,
   derivability predicates, and soundness theorems live).
2. **Object** — the current logic / theory being reasoned about (PA,
   ZFC, a user theory).

The **schematic FOL framework** described above is recorded as a
**potential future plan, not a commitment**. Its payoff is real —
collapsing the kernel's bespoke well-typedness / locally-closed /
unification machinery into one small first-order logic over reified
syntax, shrinking the TCB to "a FOL checker + the predicate rules." But
the cost is real too, and the kernel's current Rust rules work today.
Two layers are very likely enough for the MVP and quite possibly long
after; we adopt the framework only once the simplification clearly pays
for itself (e.g. when typing or unification rules start to sprawl).

### 5.2 Decision: **HOL Light now, HOL-ω maybe later**

The metatheory is **HOL Light** to begin with — rank-1 polymorphism,
the kernel we already have. A later move to **HOL-ω** (HOL with
type-constructor variables / higher kinds, à la `HOL_omega`) is a
_possible_, **independent** future — it is about the _object_ logic's
type system, orthogonal to the schematic FOL framework of §5.1 (which is
about _describing_ HOL's syntax in a simpler logic). We are explicitly
**not** building for HOL-ω now; the surface and metatheory designs
should avoid baking in assumptions that would make that migration
impossible, but should not pay for it up front either.

The _pull_ toward HOL-ω is the north star of
[`surface-syntax.md`](./surface-syntax.md) §1.1: we want the surface
layer to be a genuinely **Haskell-like language**, and a Haskell-like
language wants higher-kinded type constructors (functors, monads,
container types abstracted over their element constructor) as
first-class citizens. Rank-1 HOL Light models those one ground instance
at a time; HOL-ω lets us quantify over the type _constructor_ itself.
That is a want, not yet a need — we adopt it only when a concrete theory
we care about is unstatable without it.

**HOL-ω as an _alternative middle logic_.** The middle logic — the narrow
waist — is the _one logic shared across every implementation_; it is what
gives everything a common semantics ([`kernel-design.md`](./kernel-design.md)
§11.3), so it is emphatically **not** something individual implementations
vary. But _which_ logic plays that shared role is a project-level choice, and
HOL-ω is a candidate for it — not merely a future _object_-logic enrichment but
a possible replacement for the **shared waist itself**. The motivation is concrete: first-class
reasoning about **monads, monad transformers, and profunctors** wants to
quantify over the type _constructor_ (`m : ⋆→⋆`, `t : (⋆→⋆)→⋆→⋆`,
`p : ⋆→⋆→⋆`), which rank-1 HOL Light cannot. A theory of "all monads" or
"all profunctors" is exactly the kind of concrete, useful theory that is
_unstatable_ in rank-1 — the trigger this section names for adopting HOL-ω.

**What to build now, regardless.** The near-term move that pays off under
_either_ middle logic is to make **lists and monads first-class**: unblock
`list` structural recursion — the _syntax_ lynchpin
([`surface-compiler.md`](./surface-compiler.md), §8) — then build a rich
tactic/lemma layer for lists specifically and monad-shaped structure
generally. This is not throwaway work. The same code and surface
(the [`frontend.md`](./frontend.md) handler dispatch) later powers
**accelerated term-lists and term-sets** (efficient `covalence-pure`
observers over collections of terms, [`observers.md`](./observers.md) §7)
_and_ the **contexts / telescopes of type theory** (an MLTT context is a
list). Build the list & monad theory well once; reuse it for reified
syntax, collection acceleration, and type-theory contexts.

> **Why these are two independent bets, both deferred.** The schematic
> FOL framework (§5.1) simplifies _how we describe HOL itself_; HOL-ω
> enriches _the object logic's type system_. They are orthogonal — adopt
> either, both, or neither. The two-layer / HOL-Light path already proves
> PA/ZFC soundness, transport, and the WASM-certificate story without
> either. Per the project's "defer-as-guardrails" discipline, both are
> notes constraining today's design, not phases of their own: don't
> preclude them, don't pay for them.

---

## 6. Summary of judgement forms

| Form                              | Meaning                                           | Status                   |
| --------------------------------- | ------------------------------------------------- | ------------------------ |
| `X(A)`                            | `⊢_HOL Derivable_X ⌜A⌝` — _A_ is a theorem of _X_ | core                     |
| `Derivable_Prop ⌜A⌝ ⟹ ⟦A⟧`        | propositional logic sound, proved internally      | **done** (`init/prop.rs`) |
| `Derivable_X ⌜A⌝ ⟹ ⟦A⟧`           | soundness of _X_ under a model                    | core goal                |
| `PA(A) ⟹ HOL(A) ⟹ ZFC(A)`         | proved theory transport                           | MVP-scope                |
| `HOL ⊢ ToHOL(S) ⟹ ZFC ⊢ ToZFC(S)` | source-language lowering to many targets          | §8.1                     |
| `WASM(P,D,A) ⟹ ∃D'. ZFC(D',A)`    | computational certificate                         | post-MVP                 |
| `Isabelle[THRY](A) ⟹ THRY(A)`     | checked external import                           | post-MVP                 |
| `GT3(A)`, `Nat → ZFSet`           | locales/contexts, model embeddings                | future                   |

Throughout, the metatheory stays **HOL Light over two variable layers**,
and every object theory is admitted by _definition + checked proof_ — the
kernel TCB never grows to accommodate a new logic.

---

## 7. One surface for logic _and_ metalogic — handler-dispatched reasoning

The organizing engineering bet behind all of the above: **the machinery
for reasoning _in_ a logic and the machinery for reasoning _about_
logics are the same machinery.** A proof in PA, a proof in HOL, and a
proof of `PA(A) ⟹ HOL(A)` in our metatheory are all built from one
surface language, one elaborator, one tactic vocabulary — differing only
in _which handlers are installed in the environment_.

### 7.1 Why they must be shared

Object theories are reified _inside_ HOL (§1): a PA formula is HOL data
of sort `PAForm`, `Derivable_PA` is an ordinary HOL predicate, and
`PA(A)` is the HOL theorem `⊢ Derivable_PA ⌜A⌝`. So a "proof in PA" is
literally a HOL proof about `Derivable_PA` — it runs through the same
kernel rules and the same `(#by …)` tactic engine as any other HOL
proof. There is no separate PA prover to build; there is the HOL prover
plus the PA derivation constructors (§4). The same holds one level up:
the morphism `HOL(A) ⟹ ZFC(A)` is a HOL theorem about two reified
theories, proved with the same tactics. **Metalogic is not a second
system; it is the object system pointed at reified syntax.**

This is why "share as much syntax and tactic machinery as possible
between logic and metalogic" is a design _requirement_, not an
aspiration: anything not shared is a second prover we would have to build
and trust.

### 7.2 Reasoning as an algebraic effect, dispatched by the environment

A tactic engine performs a handful of _open-ended operations_ —
rewriting, unification, reduction/normalization, decision procedures. The
decisive design move is to treat each as an **algebraic effect**: the
tactic _requests_ "unify these two terms" or "reduce this term", and the
**environment supplies the handler**. Different logics — and different
problems within one logic — install different handlers:

- a **first-order** environment installs syntactic first-order
  unification;
- a **higher-order** environment installs (pattern) higher-order
  unification;
- a **dependent-type** environment installs a reducer that knows Π/Σ and
  definitional equality;
- a _domain_ handler installs an **arithmetic-aware unifier** that solves
  `Bits[n + m] =?= Bits[m + n]` by normalizing index arithmetic (the
  SAIL-style bitvector-spec use case), or a reducer JIT-compiled to WASM
  for a hot theory.

Soundness never depends on the handler: every handler ultimately emits a
_kernel-checkable_ obligation (a `Thm`, a rewrite witnessed by `=`, a
certificate the kernel re-checks — exactly the "pluggable computation" of
[`surface-syntax.md`](./surface-syntax.md) §1.1). A wrong or slow handler
costs time or fails; it cannot forge a theorem. So the _same_ surface
proof can be replayed under different handler sets, and the metalogic can
quantify over _which handler set corresponds to which object logic_.

### 7.3 Where this already exists in the code (the seed)

The `covalence-hol` script layer is the first, deliberately-small
instance of this design:

- **The environment is already the dispatcher.** `Env` resolves every
  proof-step head — tactic, rule, lemma — by name through one lazy
  namespace; installing a different `Env` swaps the available reasoning.
  Registering a host tactic (`#register-ffi-tactic`) is exactly "install
  a handler".
- **Unification is already a registered seam.** `Env::apply_unify`
  (lemma application) and `Env::rw_unify` (equation rewriting) are kept
  as _separate methods on the environment_ precisely so a logic- or
  domain-specific unifier can be registered later without touching the
  rules that call them. The arithmetic-aware `Bits[n+m]` unifier is a
  future `rw_unify` handler.
- **Computation is already pluggable** (`reduce`, `delta`, WASM deciders
  via observers) and produces kernel-checked equalities, never trusted
  normal forms.

The gap between today and the vision is _generality_ — one hard-wired
unifier, a handler set fixed per `Env` — not architecture. The
effect-handler framing is the name for finishing that generalization.

---

## 8. The first internal language: S-expressions → propositional logic

> **STATUS: DONE (and scaled).** This milestone landed as `init/prop.rs`
> (propositional logic reified + **proved sound internally**) and was then
> scaled to the **PA deep embedding** (`crates/covalence-hol/src/peano/`,
> `Derivable_PA ⌜A⌝ ⟹ ⟦A⟧` proved once by rule induction). The current,
> canonical account of this ladder is
> [`theories-models-and-logics.md`](./theories-models-and-logics.md)
> §5.5/§5.6. The description below is the original plan, kept for the
> end-to-end rationale.

Concretely, the **first** object language we build inside the metatheory
is the smallest one that exercises the whole pipeline end to end:

1. **Reify S-expressions in HOL.** Define an `SExpr` datatype inside the
   kernel (atoms + lists over `bytes`), with constructors and recursor —
   the same move as `defs/list.rs`, specialized to the syntax we already
   parse. This is the universal carrier for _all_ object-language syntax:
   every reified logic's formulas are `SExpr`s.
2. **Define propositional logic over it.** A `PropForm` predicate carving
   out the well-formed propositional formulas (variables, `∧ ∨ ¬ ⟹`), a
   `Derivable_Prop` inductive derivability predicate (a Hilbert system or
   natural deduction), and a denotation `⟦·⟧ : PropForm → bool` into HOL's
   own `bool`.
3. **Prove it sound _in the metalogic_.** Establish `⊢_HOL
Derivable_Prop ⌜A⌝ ⟹ ⟦A⟧` — the §2 soundness schema at its smallest.
   Propositional logic is _weaker_ than our HOL metatheory, so this proof
   is fully within reach: an induction over derivations, each case
   discharged by the kernel's existing propositional rules (`prop_eq`, the
   connective rules). **This is the first non-trivial metatheorem the
   system proves about a logic, using only itself.**
4. **Translate a subset of HOL into it.** A function `ToProp : HOLTm ⇀
PropForm` on the propositional fragment of HOL terms, with a theorem
   relating `⟦ToProp t⟧` back to `t` — the first _language morphism_ (§3),
   and the seed of the source-lowers-to-many-targets picture below.

This milestone is small but total: it touches reified syntax (1), an
object theory with its own derivations (2), a soundness theorem proved
internally (3), and a theory morphism (4). Everything larger — FOL, PA,
second-order arithmetic as multi-sorted FOL, ZFC, MLTT — is the same four
moves at greater scale.

### 8.1 The picture this generalizes to

The endgame the surface layer aims at: a user writes in a **source
language** that _lowers to several targets_. For a source term `S`, the
system tracks `ToHOL(S)` and `ToZFC(S)` as its interpretations, and
statements like

```
   HOL ⊢ ToHOL(S)   ⟹   ZFC ⊢ ToZFC(S)
```

are theorems **of our metalogic** (this HOL), which _also_ formalizes
`ToHOL` and `ToZFC` themselves. "Provable in which logic, on which
language" becomes an ordinary object of discourse — the unified surface
(`surface/mod.rs`, [`surface-syntax.md`](./surface-syntax.md)) is where a
term will be carried _together with its interpretations_, letting the user
ask the entailment questions of [`surface-syntax.md`](./surface-syntax.md)
§6 across logics. The S-expr → propositional-logic milestone is the
one-target, one-direction base case of exactly this.

---

## 9. Design compatibility audit

Which parts of today's design push _toward_ this vision, and which resist?

### Most compatible (the design already leans in)

- **Everything-reified-in-HOL.** The kernel is HOL with conservative
  extension (`define` / `new_type_definition`) and literals as data
  (`bytes`, `Int`). A new object logic is _a datatype + an inductive
  predicate + checked proofs_; the TCB never grows
  ([`kernel-design.md`](./kernel-design.md)). The single biggest enabler —
  exactly what §1/§8 need.
- **The environment-as-dispatcher script layer.** Name-resolved
  tactics/rules/lemmas through one `Env`, host-tactic registration, and
  unification kept behind `Env` methods (§7.3) — the effect-handler design
  is a generalization of what is already there, not a rewrite.
- **Pluggable computation with kernel re-checking.** `reduce`/`delta`,
  the observer/WASM-certificate substrate, `prop_eq` — all already
  "untrusted handler emits checkable obligation". Soundness is independent
  of the handler _today_.
- **Content-addressed fragments + S-expr serialization.** Object-language
  syntax wants a universal carrier and by-hash references; the store +
  canonical S-expr format are built for it.
- **The polymorphic-constant / `exists` machinery in the script layer.**
  Reasoning about reified syntax leans on schematic, polymorphic
  statements and existential derivability (`∃ derivation. …`); broadening
  the elaborator and rule set that way is directly on-path.

### Least compatible (friction to budget for)

- **One hard-wired unifier, fixed per `Env`.** `apply_unify`/`rw_unify`
  are _seams_ but there is still exactly one matcher, and the handler set
  is static for a given environment. True effect-style dispatch (multiple
  handlers, selected by goal/sort, composable) is unbuilt — the §7.2
  generality is the real work.
- **The elaborator is sync and monomorphic-by-default.** `infer.rs` is HM
  over a fixed kernel type grammar; it has no notion of "elaborate this
  term _in object language L_" or of metavariable layering (§5's schematic
  FOL). Multi-language surface terms (§8.1) need the elaborator to carry an
  interpretation target.
- **Rank-1 HOL Light.** Genuinely Haskell-like source languages and some
  object type systems want higher-kinded quantification (HOL-ω, §5.2);
  rank-1 models each instance separately. Deferred on purpose, but a real
  ceiling for the most ambitious targets (MLTT, functor-generic theories).
- **No reified `SExpr`/derivation datatypes yet.** §8 steps 1–2 are not
  started; `init/` has list/prod/etc. but not the syntax-of-a-logic layer.
  Green-field, though squarely within existing kernel capability.
- **Async/runtime ergonomics.** The cooperative async core is the right
  shape for handler dispatch and background deciders, but its rough edges
  (the nested-runtime hazard that turned `#compute` into `#spawn`) need to
  settle before heavy handler-driven workloads ride on it.

The throughline: **the foundation (reify-in-HOL, env-dispatched tactics,
checked-handler computation) is strongly aligned; the generality
(multi-handler effect dispatch, interpretation-aware elaboration, higher
kinds) is the deliberately-deferred work.** Nothing in the current design
has to be undone to get there — the gaps are all _additive_.
