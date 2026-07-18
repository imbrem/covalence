+++
id = "N001W"
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

# Dialects, orderings, UB, and the concatenative axis (discussion draft, agent-authored)

Response to: "we want multiple Lisp dialects *and orderings between them* (P valid in L is
valid in L' ⇒ we need a notion of UB); a small Lisp = a core L with all UB replaced by
(say) an error; alternatively/additionally morphisms between Lisps. At the bottom, start
with a maximally-simple ~sector-lisp with a metacircular interpreter. Also study Forsp
and FORTH." I think this is the *right* structure for the whole language plane, not just
Lisp — and it's the relation-calculus base applied to *evaluation* (dual to
`parsing-relations.md`, which applied it to syntax). Not committed.

## 0. The one-line thesis

A dialect is not a program — **a dialect is a semantics**, i.e. an evaluation *relation*
`Eval_L ⊆ Prog × Input × Output`. Once dialects are relations, everything you asked for
is already an operation in the base relation calculus (`rel.rs`):

| Your ask | Relation-calculus fact |
|---|---|
| ordering "P valid in L ⇒ valid in L'" | **relation inclusion** `Eval_L ⊆ Eval_L'` |
| UB (undefined behavior) | the pairs `(p,i)` with **no** `o` in `Eval_L` — the *slack* in the order |
| small Lisp = UB replaced by error | **totalization** `Eval_L ∪ (UB_L × {error})` — a `join` |
| morphisms between Lisps | `compose` with a **translation** relation `T ⊆ Prog_L × Prog_L'` |
| metacircular interpreter | a **fixpoint** program `metaEval` with `Eval_L(metaEval,⟨p,i⟩)=Eval_L(p,i)` |
| run a program | **`execute`** mints the positive fact `Eval_L(p,i,o)` |

So "orderings between dialects" isn't a new subsystem: it's `⊆`, `∪`, and `compose` on
evaluation relations — the same algebra `parsing-relations.md` uses for grammars. The
Lisp plane is the relation substrate wearing an operational-semantics hat.

## 1. A dialect = an evaluation relation (and why relations, not functions)

Mirror the parsing note exactly. Each dialect `L` is an **inductively-defined relation**
`Eval_L ⊆ Prog × Env × Value` (the impredicative-least-fixpoint shape:
`Eval_L p e v := ∀R. Closed_L(R) ⟹ R p e v`, one closure clause per eval rule — `car`,
`cdr`, `cons`, `cond`, `apply`, β, `label`/`Y`, …). Same machinery as the recursion
engine's `Graph`, the the `Wf` predicate, and the parse relations.

Why a **relation** and not a function, restating the parsing-note reasons for eval:

- **UB is literally partiality.** `(car 5)`, an unbound symbol, a diverging recursion —
  these are `(p,e)` with *no* `v`. A total HOL function would be forced to invent a value;
  a relation just leaves them out. UB = "not in the relation."
- **Nondeterminism is multiplicity.** An underspecified dialect (unspecified arg-eval
  order with effects) is a relation with *several* `v` for one `(p,e)`. Determinism =
  right-uniqueness, *proved* where it holds, not assumed.
- **Divergence is honest.** No fuel artifact; termination is a theorem about the relation,
  not a parameter baked into the object (same as parsing).

The executable interpreter (`TestLisp`, §Lisp-frontend-sketch §10.1) is the untrusted
`Rel(eval_fn)` accelerator; `execute` runs it and mints `Eval_L(p,e,v)`. Spec = relation
(trusted), executor = TestLisp (fast), derived partial function = `eval_L := ε v.
Eval_L p e v` on its determinism domain. Three views of one dialect — exactly the
parsing-relations story, transposed from parse to eval.

## 2. The ordering = relation inclusion (with a program embedding)

Define `L ⊑ L'` ("L' refines L") precisely:

> there is a program embedding `ι : Prog_L → Prog_L'` such that
> `∀ p e v.  Eval_L p e v  ⟹  Eval_L' (ι p) e v`.

When `ι` is the *inclusion* (L' is syntactically a superset — more special forms/prims),
this is just `Eval_L ⊆ Eval_L'` on shared syntax: **every program well-defined in L is
well-defined in L' with the same value.** That is exactly "P valid in L ⇒ valid in L'."

Two things this buys immediately:

- **UB is the slack that makes the order non-trivial.** Where `L` is UB at `(p,e)`, `L'`
  may define *anything* and still satisfy `⊑` (the implication is vacuous there). So the
  order is loose exactly at UB and tight exactly where behavior is specified. "Add a
  dialect above L" = "pin down some of L's UB (and/or add features), agreeing everywhere L
  already committed."
- **Refinement is the sub-poset of morphisms where `ι` is inclusion** (§4). So §2 and §4
  are one definition at two generalities: the *order* is the wide subcategory of
  inclusions inside the *category* of translations.

This is a real partial order on the relation lattice — and it's the same `⊆` your base
calculus already has (`meet`/`join`/subset in `rel.rs`).

## 3. UB, the safe core, and why it's a lattice (not a chain)

"A small Lisp = core L with all UB replaced by an error" is the **totalization**:

```
Eval_safe := Eval_L  ∪  { (p, e, error) : (p,e) is UB in L }
```

a `join` of `Eval_L` with the UB-set crossed to `{error}`. Facts:

- `Eval_L ⊆ Eval_safe`, so `L ⊑ Eval_safe`: the safe core is *above* the loose spec
  (more-defined). It is **total** (every `(p,e)` has a value — real or `error`) and
  **deterministic** if `L` was.
- **There are many totalizations, and they're incomparable.** "Fill UB with `error`" vs
  "fill UB with a specific implementation-defined behavior" vs "fill UB with `nil`" are
  distinct total refinements, each ⊒ `L`, none ⊑ another. So the dialect poset has a
  **loose bottom (max UB) and many maximal tops (the total refinements)** — a lattice
  with genuine width, not a chain. The "safe error-core" is *one designated top*: the
  totalization that maps every UB to a trapped `error`. (This is exactly the C-UB vs
  UBSan/"defined-behavior build" relationship, or unsafe-Rust vs safe-Rust, made
  first-class: safe = the error-totalization of the loose spec.)
- **Guards/contracts are partial totalizations.** ACL2's guard-verified functions are
  precisely "the fragment where we've *proved* we're inside `Eval_L`'s defined domain, so
  the totalization's `error` branch is provably dead." So the ACL2 discipline (§Lisp-
  frontend-sketch §10.5) *is* a statement in this order: guard verification = "this
  program stays in the ⊑-committed region, never hits UB."

This gives the UB story teeth: **UB is not a wart to avoid, it's the coordinate that
orders the dialects.** A maximally-loose spec at the bottom is a *feature*, because it's
the ⊑-least element every refinement sits above.

## 4. Morphisms between Lisps — the category, and correctness as a kernel theorem

General morphisms drop the "same programs" restriction: a **translation/compiler**
`F : L → L'` is a program map `T ⊆ Prog_L × Prog_L'` (plus a value map) that *preserves
meaning*:

```
Eval_L p e v  ∧  T p p'  ⟹  Eval_L' p' (F e) (F v)          (a simulation / homomorphism)
```

i.e. `T ; Eval_L' = Eval_L ; F` — a `compose` square in the relation calculus. Then:

- Objects = dialects (semantics relations); morphisms = meaning-preserving translations;
  **`⊑` (refinement) = the wide subcategory where `T` is the inclusion.** One structure.
- **Correctness of a translation is a theorem in our kernel.** `F` is untrusted (a
  compiler); the simulation square is the proof obligation, discharged over the carved
  `sexpr` semantics. This is compiler-correctness-as-a-`Thm`, and it's the same shape as
  "the gas parser agrees with the `Parse` relation" (`parsing-relations.md` step 5).
- This is the **object-logics plane** (`sketch-separation-thoughts.md`) specialized to the
  Lisp axis, and it's literally the **K framework** program (define languages as
  semantics; translations between them are certified) and the **observers substrate** (a
  dialect is an executor/observer; a morphism is a bridge carrying a proof). Lisp dialects
  are the concrete, small, demoable instance of all three.
- Useful morphism zoo to target: `sector-lisp ↪ small-scheme ↪ ACL2-ground`
  (inclusions/refinements); `ACL2-ground → HOL` (the certifying embedding —
  §Lisp-frontend-sketch §10.3); `scheme ⇄ CPS`, `scheme → SECD/bytecode` (compilers);
  and the cross-paradigm ones in §6.

## 5. The bottom: a maximally-simple sector-lisp with a metacircular interpreter

Start the poset at a **McCarthy/SectorLISP core** — the ⊑-least real Lisp:

- **7 primitives + λ + recursion**: `quote atom eq car cdr cons cond`, `lambda`, and
  recursion via `label` (or a `Y`/`fix` in the object language). That's the whole
  language. SectorLISP (Tunney/Ikuta) famously fits this in a 512-byte boot sector, no
  GC, because pure eval needs no persistent allocation.
- **Why it's the right bottom** — three reasons that matter for *us* specifically:
  1. **It's nearly already built.** Its data universe *is* our `sexpr`
     (`inductive/carved.rs`); `init/lisp.rs` already has `car/cdr/cons/consp/atom`. The
     bottom dialect is `init/lisp.rs`'s theory + `eq/cond/quote/lambda/label` eval rules.
  2. **It's small enough to *prove* runtime = logic.** The §10.1 `TestLisp = CertifiedLisp`
     agreement is only *tested* for big dialects; for the sector core it's a *theorem*
     (finite rule set, structural). So the bottom is where the two-evaluators story stops
     being a differential test and becomes a proof — the anchor of the whole tower.
  3. **The metacircular interpreter is the seed strange-loop.** SectorLISP's `eval`/`apply`
     is an *L-program* `metaEval`. The reflection equation
     `Eval_L(metaEval, ⟨quote p, e⟩) = Eval_L(p, e)` is a statable, provable **self-model**
     theorem — the Lisp instance of the "hol-in-hol self-model hub"
     (`surface-compiler-design`) and the WASM strange loop
     (`sketch-separation-thoughts.md`). Prove it once at the bottom and every dialect
     above inherits a reflective interpreter by transporting along `⊑`.
- **Then climb by refinement**: `+ numbers` (the literal-atom zoo, `atoms.md`), `+ strings/
  chars`, `+ tail calls`, `+ macros`, `+ error/condition system`, `+ guards` → landing at
  the ACL2 ground fragment (§Lisp-frontend-sketch §10.2). Each step is a `⊑` edge with an
  explicit UB-resolution, so the tower *documents its own semantics deltas*.

## 6. The concatenative axis: FORTH and Forsp are not just more dialects

FORTH and Forsp matter because they're the **concatenative** (stack) axis of the *same*
category — and the base relation calculus models concatenation *more* natively than it
models applicative eval. Studying them isn't a detour; it's finding the axis the
substrate was already built for.

### FORTH — a word *is* a stack relation, and that's the base `compose`
- A Forth word is a relation `Stack ⇀ Stack` (a partial function on the stack). A program
  is a **sequence of words = `compose` of stack relations**. Forth's core operation —
  concatenation/threading — is *exactly* the base calculus's `compose`, and *exactly* the
  parser's `rest`-threading (`parsing-relations.md`). Three things we already call
  `compose`: grammar sequencing, parser input-threading, Forth word composition. One op.
- **It's the minimal executor model.** A dictionary of words = a content-addressed store
  of stack relations (ties to content-addressing); threaded code = a program *as data* in
  that store. This is the cleanest possible `Rel(f)` executor: run the stack machine,
  `execute` mints `Run(word, s, s')`.
- **WASM is a stack machine.** So Forth is the toy model of the WASM-executor axis
  (`term-arena-vs-wasm`, the WASM strange loop): the concatenative IR whose semantics is a
  stack relation and whose acceleration is the real WASM engine. Forth → the substrate's
  executor story; Lisp → its applicative-logic story; they meet at the relation calculus.

### Forsp (xorvoid) — the bridge object between the two axes
- Forsp is a tiny language unifying **Forth's stack and Lisp's environment**, built on a
  call-by-push-value-flavored evaluation (quote/push a thunk, force/call it), with
  S-expression syntax. It is applicative *and* concatenative at once.
- Why it's important *categorically*: it's a **morphism-dense object** — a point where the
  applicative-Lisp axis and the concatenative-Forth axis are visibly inter-translatable
  (`lisp ⇄ forsp ⇄ forth` as meaning-preserving `F`s, §4). It's the concrete witness that
  "stack" and "environment" are two presentations of one calculus — which is the whole
  thesis that dialects live in *one* category, not two disconnected worlds.
- Practical payoff: Forsp is small enough to be an early **second paradigm** in the same
  REPL (a `TagSchema_forsp` + a stack evaluator), giving us a real cross-paradigm morphism
  to *certify* early — the smallest interesting instance of "compiler correctness as a
  `Thm`" (§4).

So the plane has **two axes meeting at the relation calculus**: applicative (Lisp,
`apply`/β, environments) and concatenative (Forth, `compose`, stacks), with Forsp on the
diagonal and `compose` as the shared spine. That's a much richer and more honest picture
than "a stack of Lisp dialects."

## 7. Where it all lands on the substrate (the consolidated table)

| Concept | Object | Base op / obligation |
|---|---|---|
| a dialect | `Eval_L ⊆ Prog×Env×Val` (inductive relation) | least-fixpoint (`Graph` shape) |
| run a program | positive fact `Eval_L(p,e,v)` | **`execute`** on `TestLisp` |
| UB at `(p,e)` | no `v` in `Eval_L` | (partiality) |
| ordering `L ⊑ L'` | `Eval_L ⊆ Eval_L'` (mod embedding `ι`) | **`⊆`** / relation inclusion |
| safe error-core | `Eval_L ∪ (UB_L×{error})` | **`join`** (totalization) |
| guard/contract | proof "stays in `Eval_L`'s domain" | a `Thm` (dead `error` branch) |
| translation `F:L→L'` | `T ; Eval_L' = Eval_L ; F` | **`compose`** square (a `Thm`) |
| deparse/pretty a program | `transpose` of the reader relation | **`transpose`** (parsing note) |
| metacircular interp | `Eval_L(metaEval,⟨p,e⟩)=Eval_L(p,e)` | fixpoint/self-model `Thm` |
| Forth word | `Stack ⇀ Stack` | **`compose`** (threading) |
| Forsp | applicative∩concatenative | morphisms both ways (`compose`) |
| determinism (partial fn) | right-uniqueness of `Eval_L` | `graph_det` technique |
| divergence | not-in-relation | termination = a `Thm`, not fuel |

Every row is an operation you already have or a `Thm` obligation in the existing kernel —
nothing here needs new TCB.

## 8. Where to start (build order, folds into §Lisp-frontend-sketch §8/§10.6)

1. **The sector core as `Eval_L₀`** — the McCarthy 7 + λ + `label` as an inductive eval
   relation over `sexpr`, reusing `init/lisp.rs`. `TestLisp` for it is trivial;
   prove `TestLisp = CertifiedLisp` for this fragment (the anchor theorem).
2. **The metacircular `eval` + its reflection theorem** — the seed strange loop; the most
   striking small demo (a Lisp that runs its own interpreter, *proved* faithful).
3. **One refinement edge** — `sector ⊑ small-scheme` (add numbers via the atom zoo + a
   couple of special forms), with its UB-deltas written as the `⊑` witness. Proves the
   *order* is real, not just asserted.
4. **The error-totalization** — `safe` as `join`, and a guard-style "no-UB" `Thm` for one
   function. Demonstrates "small safe core = UB→error" concretely.
5. **Forth (concatenative executor)** — a stack-relation evaluator; `compose` = threading;
   `execute`-certified runs. The second axis, minimal.
6. **Forsp (the bridge)** — a `lisp ⇄ forsp` translation with a certified simulation square
   (§4). The first cross-paradigm compiler-correctness `Thm`.

Steps 1–2 are the high-signal core (self-hosting proved Lisp on `sexpr`); 3–4 make
the *ordering/UB* first-class; 5–6 open the concatenative axis and the first real
morphism.

## 9. Open questions for us

- **Is `⊑` per-dialect-pair, or a single global lattice?** I lean: one relation lattice
  (`Eval_L` all live in `Prog×Env×Val` over a shared universal `sexpr`), so `⊑` is plain
  `⊆` and totalizations/joins are literal. Divergent *syntaxes* are handled by the
  embedding `ι` (a translation), keeping the core order as pure inclusion.
- **How much semantics do we make deterministic up front?** Effects/IO make `Eval_L` a
  genuine relation (nondeterministic); the pure applicative fragment is a partial
  function. Start pure/deterministic (sector + ACL2 ground), add the relational
  (nondeterministic) layer only when we model effects — and let *that* be where the
  full relation (not just partial-function) machinery earns its keep.
- **Forth's store = our content-addressed store?** A Forth dictionary is a
  content-addressable map of words; is it literally an instance of `cov:store`
  (`store-is-container`), making threaded code a store-resident program? Tantalizing and
  probably yes — worth a spike.
- **Where does the metacircular tower stop?** Sector-lisp's `metaEval` is level 1. Do we
  want the reflective tower (interpreter of interpreter of …) as an explicit
  construction, or just the single self-model theorem transported along `⊑`? (I lean:
  single theorem + transport; the tower is a corollary, not a primitive.)
- **Relation to the K matching fragment** (same open question as the parsing note): K's
  "syntax + semantics as relations, simple vs full matching" is this whole picture one
  level up (rewriting = relational, evaluation = a rewriting relation). Are the dialect
  eval-relations the *ground case* K generalizes, or an instance of K's rules? Probably
  ground case; the Lisp plane is the concrete seed for the K substrate.
