# The REPL returns *reduction* theorems, not equations — `(state, input) ~~> (state, output)`

Response to: the HOL kernel proves `⊢ P` for arbitrary `P`; for Lisp the REPL should
return `definitions ⊢ input ~~> output` (or `(definitions, input) ~~> output`) — a
**reduction-relation** theorem, not an equation. This (a) gives **nondeterminism without
general state** (AMB!), and (b) generalizes to a **three-theorem pipeline** —
`input_string PARSES input_sexpr` · `(state_in, input_sexpr) REDUCES (state_out,
output_sexpr)` · `output_string PARSES output_sexpr` — where `state` is `definitions` for
now but later carries a KV-store/memory, a print-log, etc.; and parsing itself can be
stateful (`(state, string) PARSES sexpr`) so the printer can do macro abbreviation. Not
committed. This *supersedes* the equational `⊢ input = nf` shape in the minimal-spec.

## 0. Why a relation, not an equation — the whole point in one move

`⊢ input = nf` (an equation) forces reduction to be a **function**: one input, one output,
deterministic, total-or-stuck. The moment you want **AMB** (`(amb 1 2 3)` may reduce to
`1`, `2`, *or* `3`) that's false — there is no single `nf`. So the honest object is a
**relation**:

```
Reduces  ⊆  (State × SExpr) × (State × SExpr)
```

and the theorem the REPL returns is a *membership* fact:

```
⊢ Reduces (state_in, input) (state_out, output)          -- written  (defs, input) ~~> (defs', output)
```

This is *exactly* the `Eval_L` relation from
[`lisp-dialects-and-order.md`](./lisp-dialects-and-order.md) — the dialects-as-relations
thesis, now cashed out as the REPL's return type:

- **nondeterminism = right-multiplicity.** `(amb 1 2 3)` gives three distinct valid
  `output`s for one `(state, input)`; the relation holds for all three; the REPL returns
  *one witness* (one branch) per `⊢`, and can enumerate the rest. No mutable state needed
  — the branching lives in the *relation*, not in a store.
- **stuck / UB = no witness.** `(car 5)` — no `output` with `Reduces (s,(car 5)) (s',out)`.
  Partiality is honest (no invented value), matching the UB story.
- **the equation is the special case.** When `Reduces` is deterministic and `state_out =
  state_in`, `⊢ (s,input) ~~> (s,output)` *is* `⊢ input = output` read off the relation.
  So the old shape is a corollary, not lost.

`Reduces` is an **inductively-defined HOL relation** (impredicative least fixpoint — the
`Graph`/`Wf`/`Eval_L` shape): `Reduces a b := ∀R. Closed(R) ⟹ R a b`, one closure clause
per reduction rule (`car`, `cdr`, `cons`, β, **`amb`** = *two/three* intro rules for the
same premise, δ-unfold a definition, …). The REPL is an **untrusted proof assembler**: it
builds a membership derivation from the intro rules; the kernel checks it. "Evaluate as a
theorem" = "discharge `⊢ Reduces (s,i) (s',o)` from the relation's introduction rules."

## 1. AMB — nondeterminism without general state (the fun part)

McCarthy's `amb` is the showcase because it needs *nothing* but the relation:

```lisp
λ> (amb 1 2 3)
1        ⊢ (defs, (amb 1 2 3)) ~~> (defs, 1)        ; one branch; :next for the rest
λ> (amb)
∅        ⊢ ¬∃o. (defs, (amb)) ~~> o                  ; failure = empty relation (a dead end)
λ> (+ 1 (amb 10 20))
11       ⊢ (defs, (+ 1 (amb 10 20))) ~~> (defs, 11)  ; :next ⟹ 21
```

Two intro rules `Reduces (s,(amb x y)) (s, x)` and `… (s, y)` — that's the entire
semantics. Backtracking search (SICP's `amb`) is *enumerating witnesses* of the relation;
`require`/`fail` is intersecting with a predicate (a `meet` in the relation calculus). This
is a genuinely striking demo: **a nondeterministic Lisp whose every result is a kernel
theorem**, with no store, no continuations-as-TCB — just the reduction relation having
more than one witness. And it's the smallest possible motivation for "relation, not
function," so it belongs early.

(Later, `amb` + a `state` component = full nondeterministic *stateful* search; but the
point is the *nondeterminism* comes for free from the relation, *before* state exists.)

## 2. The three-theorem pipeline (the real target shape)

A REPL step from a *string* to a *string* is a **composition of three theorems**:

```
Thm 1 (read):    ⊢ Parses  state_in   input_string   input_sexpr
Thm 2 (reduce):  ⊢ Reduces (state_in,  input_sexpr) (state_out, output_sexpr)
Thm 3 (print):   ⊢ Parses  state_out  output_string  output_sexpr
```

Read Thm 3 as: `output_string` is a *valid rendering* of `output_sexpr` under
`state_out` — so **deparse = choosing an `output_string` with `Parses state_out
output_string output_sexpr`**, i.e. a section of the parse relation's converse
(`parsing-relations.md` — `transpose`, the "printer is a chosen section" story). The three
theorems **`compose`** (`Parses ; Reduces ; Parses°`) into one certificate that the whole
line — text in, text out, state stepped — is sound. That composite is a single relation
`(State × String) ~~> (State × String)`, and it's literally the relation-calculus
`compose` of the three phases. This is the unification: **parse, reduce, and print are all
relations over one shared `State`, glued by `compose`.**

Why bother making *parsing* a theorem too (not just an untrusted `serde` step)? Because
then the REPL's output is a *fully certified* chain: nothing between the user's keystrokes
and the printed answer is un-witnessed. It also makes the printer's *state-awareness*
(macro abbreviation, §4) a certified fact, not a pretty-printing convenience that could
lie.

## 3. `state` — definitions now, a whole "world" later

`state` is a record threaded through `Reduces` (and consulted by `Parses`). Minimal = just
the environment; the generalization is the point:

| component | now | role | later |
|---|---|---|---|
| **defs** | ✅ live | the dictionary/environment (`#name`, `defun`) | — |
| **kv / memory** | hook | a mutable store/heap → `set!`, `ref`, arrays | real state (Forth's memory, `cov:kv`) |
| **log** | hook | an output/print accumulator → `(print x)` appends | effects, streaming output |
| **prng seed** | hook | deterministic randomness (thread a seed) | reproducible nondet |
| **trace** | hook | reduction provenance for `:trace` | proof-object export |

Crucial: **`Reduces` is state-*polymorphic*.** The pure applicative fragment leaves
`state_out = state_in` (nothing threaded); `define`/`#name` extends `defs`; `print`
appends to `log` so `output_string`/side-output derives from `state_out.log`; `set!`
mutates `kv`. Adding a component is adding reduction rules that touch it — *not* re-typing
the relation each time (make `State` an open record / a product you extend). This is the
Forth "state = stack + dictionary + memory" picture and the store-as-container picture
converging: the Lisp `state` is a small **world** the reduction relation transforms.

So the general shape the user wants is:

```
⊢ Reduces (world_in, input_sexpr) (world_out, output_sexpr)
```

with `world = { defs, kv, log, … }`, and **nondeterminism (AMB) orthogonal to it** — you
get either, or both, independently.

## 4. Stateful parsing → macro abbreviation in the printer

Generalize Thm 1/3 to `Parses ⊆ State × String × SExpr` — parsing/printing **consult the
state**. Payoffs:

- **Macro abbreviation on print.** If `#name two (cons 1 (cons 2 nil))` put `two` in
  `defs`, then `Parses defs "two" (cons 1 (cons 2 nil))` holds, so the *printer* may render
  the value as `two` (a shorter valid rendering under `defs`) — certified by Thm 3. The
  round-trip becomes **state-relative**: `"two"` and `"(1 2)"` are both valid renderings of
  the same sexpr *under a state that defines `two`*.
- **Reader macros / abbreviations.** `'x` ⇒ `(quote x)`, `` `(...) `` etc. are parse-state
  rules; new abbreviations are new `Parses` clauses, uniformly.
- **Honesty.** Because it's the *same* `Parses` relation in Thm 1 and Thm 3, an
  abbreviation the printer uses is one the reader accepts — parser/printer can't drift.

This is the parsing-relations note (`(state,string) ↔ sexpr`, deparse = transpose-section)
with `state` added, and it's why parse-as-relation (not a gas function) pays off here: the
converse + state give macro-aware printing *for free by symmetry*.

## 5. What changes in the minimal-spec (concretely)

- **Return type of `reduce`** is a `Thm` of `Reduces (state, input) (state', output)` (not
  `input = nf`). `Session::reduce(&mut self, x) -> Result<Thm, Error>` unchanged in
  signature; the *proposition* it proves changes. Minimal `State = Defs` (the dictionary).
- **`eval_cell`** returns the composite (Thm1·Thm2·Thm3); the printed line is
  `output_string` from Thm 3. `#show` reveals the reduction theorem; `#trace` the chain.
- **One nondeterministic builtin — `amb`** — ships in the minimal dialect to exercise the
  relation (with `:next` to enumerate further witnesses). `require`/`fail` optional.
- **`Parses` is a HOL relation**, minimal impl still backed by the untrusted reader/printer
  as the *witness generator* (`execute`-style: run the reader, mint `Parses …`), exactly
  the gas-parser-as-accelerator story — so we don't need the full relational grammar yet,
  just the relation as the *stated* proposition with the reader as its oracle.
- **State stays a record with `defs` live** and `kv`/`log`/… as documented-but-empty
  components, so `set!`/`print` slot in without a re-type.

## 6. Open questions

- **How much of `Parses` to certify in the minimal cut?** Full three-theorem chain, or
  Thm 2 (reduce) only for M-first, with Parse as an untrusted step promoted to Thm 1/3
  later? (I lean: reduce-theorem first, then wrap parse — but *design* the API for all
  three now so the return type doesn't churn.)
- **Witness enumeration UI.** `:next`/`:all` over `amb` — does the REPL hold a lazy stream
  of derivations (a resumable search), matching the async-prover `Env`? (Probably yes; the
  nondeterministic relation is the first real consumer of the cooperative scheduler.)
- **`State` as an open record vs a fixed product.** Extensible-record (row-typed) `world`
  vs a growing struct. Row-typed is cleaner for "add a component without re-typing" but
  heavier in HOL; start with a fixed small product `{defs, kv, log}` and widen later.
- **Negative/failure theorems.** `(amb)` ⇒ `⊢ ¬∃o. Reduces …` — mint it (needs the
  relation's *exhaustiveness*, an inductive-inversion lemma), or just report "no witness"
  untrusted for now? (Untrusted "stuck" for minimal; the refutation theorem later, same as
  the parsing-relations negative-fact discipline.)
