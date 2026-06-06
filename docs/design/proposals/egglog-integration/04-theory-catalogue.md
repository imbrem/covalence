# 04 — Theory catalogue

The load-bearing document for this proposal. A **catalogue entry** is
a (theory, decision question) pair where egglog is a good engine —
not the universe of egglog programs, but a curated patchwork of
small, well-understood problems we want to ship into the kernel.

Each entry stands on its own: its own signature, its own rule set,
its own decision question, its own replay handler. Adding an entry
does not touch the others. Subtracting an entry is a one-file
deletion. The catalogue grows as interesting problems present
themselves.

## What an entry must specify

Every entry below has the following shape. New entries should follow
the same template.

| Field | Meaning |
|---|---|
| **Status** | `proposed` / `in-catalogue` / `shipped`. All entries here are `proposed`. |
| **Signature** | Sorts and function symbols. The egglog encoding follows from these. |
| **Decision question** | What the user asks; what egglog returns. Pinned precisely (e.g., "does `s = t` follow from the theory's axioms plus a finite set of user ground equations?"), not "is this theory satisfiable?". |
| **Why egglog suits it** | Termination / saturation / proof-encoding rationale. If egglog doesn't decide the question — say so, and say what semi-decision behaviour we accept. |
| **Egglog encoding** | One-line sketch of the canonical egglog program shape. |
| **Kernel replay** | Which `EThm` rules carry the load, and any new ones needed. |
| **Caveats** | What's outside the entry's scope — common confusions, fragments excluded, known boundary cases. |
| **Layer fit** | A / B / both — which engineering layer instantiates the entry. |

## What makes a good entry

The criteria, in roughly descending order of importance:

1. **The question is genuinely decidable** (or has a clear
   semi-decision with a useful "don't know" answer). The catalogue
   is not a place for "egglog might saturate, let's see".
2. **The proof fragment is `program_supports_proofs`-eligible.**
   Layer A trips on this otherwise.
3. **The rule set is small.** Big rule sets are red flags for
   non-confluence, non-termination, or "this is actually a
   different problem".
4. **The decision question is *the user's* question.** Not "this is
   what egglog computes" but "this is what the user wants to know".
5. **The kernel rules already exist or are obvious.** Entries
   needing new `EThm` primitives are fine but should justify the
   addition.
6. **There is an interesting problem.** The catalogue is a place
   for *useful* theories, not exhibits. Each entry should be one
   the user would actually reach for.

## Status legend

* **proposed** — listed here; not yet committed to.
* **in-catalogue** — accepted in principle; awaiting implementation.
* **shipped** — implemented end-to-end (A or B) with tests.

All entries below are **proposed**.

---

## Entry 1: EUF — equality with uninterpreted functions

* **Status:** proposed
* **Layer fit:** A first; B from Phase 3
* **Signature:** A sort `U` (or several user sorts), arbitrary
  user-declared function symbols `f, g, …` over those sorts. No
  primitives.
* **Decision question:** Given a finite set of ground equations
  `Γ = {s₁ = t₁, …, sₙ = tₙ}` and two ground terms `s`, `t` over the
  signature, does `Γ ⊨ s = t` hold in the theory of equality with
  uninterpreted functions (i.e., is it derivable by reflexivity,
  symmetry, transitivity, and congruence from `Γ`)?
* **Why egglog suits it:** EUF is exactly what congruence closure
  decides; egglog's e-graph is a congruence closure data structure.
  Saturation is bounded by the number of subterms in `Γ ∪ {s, t}`.
  Every step in egglog's proof DAG is `Fiat` (for the ground
  equations), `Trans`, `Sym`, or `Congr` — no `Rule` or `MergeFn`
  appears, since EUF has no user rewrites.
* **Egglog encoding:**

  ```
  (sort U)
  (function f (U U) U)        ; one per user symbol
  (let a (...))               ; the terms in Γ ∪ {s, t}
  (union ...)                 ; one per ground equation
  (prove (= s t))
  ```

* **Kernel replay:** All four built-in axioms (`EThm::refl`,
  `sym`, `trans`, `cong`). Already present in `eprop.rs` or
  planned for the immediate next phases.
* **Caveats:** No quantifiers, no theory axioms beyond pure
  equality, no primitives. The moment a user wants `i64`
  arithmetic or array axioms, that's a different catalogue entry.
* **Why it's the first entry:** smallest possible end-to-end test
  of the entire pipeline. If the EUF entry doesn't ship cleanly,
  the scaffold is wrong.

---

## Entry 2: Pure equational theory over a fixed signature

* **Status:** proposed
* **Layer fit:** A first; B from Phase 3
* **Signature:** A fixed user-supplied signature `Σ` plus a fixed
  set of equational axioms `E = {l₁ = r₁, …}`. The signature and
  `E` are constant per entry instance; user input is the ground
  terms / extra ground equations.
* **Decision question:** Given user ground equations `Γ` and target
  ground terms `s, t`, does `E ∪ Γ ⊨ s = t` hold in the equational
  theory generated by `E ∪ Γ`?
* **Why egglog suits it:** When `E` is confluent and terminating
  (e.g., a Knuth-Bendix-completed monoid presentation, ring
  identities, boolean algebra, lattice laws), egglog's saturation
  *is* the decision procedure: two terms are equal iff they
  reach the same normal form. The proof DAG mixes `Rule`
  (each axiom firing) with `Fiat`/`Trans`/`Sym`/`Congr`. When `E`
  is non-confluent, egglog gives a semi-decision: "yes" with a
  proof, or "saturated without proof" (which we surface as
  "unknown" — not "no").
* **Egglog encoding:**

  ```
  (datatype T (op1 T T) (op2 T) …)     ; the signature
  (rewrite (op1 (op2 x) y) (op2 (op1 x y)))   ; one per axiom in E
  (let a (...))                        ; user ground terms
  (union ...)                          ; user ground equations Γ
  (prove (= s t))
  ```

* **Kernel replay:** Built-ins plus a `EThm::rewrite` handler per
  axiom in `E`. The `RuleCatalog` synthesises the handler from
  the rewrite's AST at theory-registration time (no per-entry Rust
  code needed beyond the `Theory` definition).
* **Caveats:** Per *instance* of this entry, `E` is fixed. Two
  different theories (monoids vs. boolean algebra) are two
  different catalogue instances, even though the entry template is
  the same. Termination of saturation depends on `E`; for
  non-terminating `E`, we run with a step budget and treat
  exhaustion as "unknown".
* **Recommended first instance:** monoid identities (associativity,
  left/right identity). Three rewrites, confluent + terminating,
  ships as a decision procedure.

---

## Entry 3: Theory of arrays

* **Status:** proposed
* **Layer fit:** A first; B in a later phase
* **Signature:** sorts `Arr`, `Idx`, `Elt`; function symbols
  `read : Arr × Idx → Elt`, `write : Arr × Idx × Elt → Arr`;
  equality on `Idx`.
* **Decision question:** Given user ground equations / disequalities
  over `read`/`write` terms, decide whether two `Elt` (or `Arr`)
  terms are equal in the theory of arrays with `select-over-store`
  and `select-over-different-store` axioms.
* **Why egglog suits it:** classic decidable theory; the two axioms
  saturate predictably, and the only branching is on `i = j`
  disequalities. Encodable via conditional rewrites guarded by
  `Idx` equality premises.
* **Egglog encoding:**

  ```
  (sort Arr) (sort Idx) (sort Elt)
  (function read  (Arr Idx) Elt)
  (function write (Arr Idx Elt) Arr)
  (rewrite (read (write a i v) i) v)
  (rule ((= (read (write a i v) j) r) (!= i j))
        ((union r (read a j))))
  …
  ```

* **Kernel replay:** built-ins + two user rewrites; one
  `EThm::rewrite_conditional` (with a disequality premise) is the
  only new wrinkle.
* **Caveats:** Index disequality is a first-class side condition;
  if the theory's interpretation of `Idx` is integers, this entry
  doesn't subsume linear arithmetic — combinations live in a
  separate entry.

---

## Entry 4: Theory of lists / algebraic datatypes

* **Status:** proposed
* **Layer fit:** A first; B in a later phase
* **Signature:** an algebraic-datatype declaration (e.g.,
  `(datatype List (nil) (cons Elt List))`) plus selector/recogniser
  functions (`head`, `tail`, `is-nil`, `is-cons`), plus standard
  operations (`append`, `reverse`, `length`).
* **Decision question:** Given user ground equations and target
  terms, decide equality in the equational theory generated by
  the constructor/selector laws and the operation defining
  equations (e.g., `(append nil ys) = ys`, `(append (cons x xs) ys)
  = (cons x (append xs ys))`).
* **Why egglog suits it:** the rules are confluent and terminating
  when oriented left-to-right; this is the classical equational
  theory of free algebras with some structural recursion. Egglog
  saturates and decides equality directly.
* **Egglog encoding:** straightforward `(datatype …)` + `(rewrite
  …)` per defining equation.
* **Kernel replay:** built-ins + user rewrites. No new primitives.
* **Caveats:** *Equational* decidability — not first-order over
  lists. Statements like `∀xs. append xs nil = xs` are *not* in
  the entry (no quantifiers); the user instantiates them at
  specific ground terms.

---

## Entry 5: Commutative-monoid / AC word problem

* **Status:** proposed
* **Layer fit:** A first; B once we have AC matching in the native
  runner (later)
* **Signature:** a sort `M` and a single binary operator `· : M × M
  → M` declared associative and commutative, plus a unit `e : M`.
* **Decision question:** Given generators `g₁, …, gₙ`, user ground
  equations (relations) `R` over those generators, and target
  terms `s, t`, decide `R ⊨ s = t` modulo AC.
* **Why egglog suits it:** the commutative-monoid word problem is
  decidable in polynomial time via reduction to vectors in `ℕⁿ`.
  Egglog with an AC-aware encoding handles this — *if* we choose
  the encoding carefully. The straightforward encoding uses an
  ordering on subterms; the egglog community has prior art here.
* **Egglog encoding:** TBD — either explicit AC rewrites
  (`(rewrite (· x y) (· y x))` + `(rewrite (· (· x y) z) (· x (· y
  z)))`), which is non-terminating in general but converges for
  bounded inputs, or a canonical-form encoding via `Vec` or a
  sorting function.
* **Kernel replay:** built-ins + AC rewrites. The replay path is
  identical to entry 2; the subtlety is in the *encoding*, not in
  the kernel.
* **Caveats:** Non-commutative monoid word problem is undecidable
  in general — different entry. Once egglog's saturation step
  budget is exhausted on an instance we treat as "unknown"; the
  entry's status remains "proposed" until we validate that real
  instances terminate.

---

## Entry 6: Confluent first-order term rewriting systems

* **Status:** proposed
* **Layer fit:** A first; B from Phase 3
* **Signature:** any user-supplied first-order signature plus a
  user-supplied TRS that is confluent and terminating (the user
  asserts this; we don't check).
* **Decision question:** decide equality of two ground terms under
  the TRS.
* **Why egglog suits it:** identical reasoning to entry 2, but the
  TRS is supplied by the user rather than fixed by the entry. This
  entry exists because users may have a particular TRS in mind (SK
  combinators, Knuth-Bendix-completed group presentations, β-reduction
  with explicit binders restricted to weak normalisation) and want
  the engine without curating it as a named entry.
* **Egglog encoding:** one `(rewrite …)` per TRS rule.
* **Kernel replay:** built-ins + user rewrites; the same handler
  shape as entry 2.
* **Caveats:** the **user asserts** confluence + termination. If
  they're wrong, egglog may diverge or report unsoundness for
  non-confluent fragments. This entry has a sharp "user's
  responsibility" boundary; the kernel still produces a sound
  `EThm` if egglog gives a proof, but failure to produce one
  doesn't mean "unequal" — only "didn't find within budget".

---

## Entry 7: Datalog reachability / transitive closure

* **Status:** proposed
* **Layer fit:** A first; B once Phase 4 (relations) lands
* **Signature:** primitive sorts (`i64`, or an opaque user sort
  with constants), a relation `edge : I × I`, derived relation
  `path : I × I`.
* **Decision question:** Given an explicit set of `edge` facts,
  decide whether `path(a, b)` holds (i.e., reachability in the
  finite directed graph).
* **Why egglog suits it:** classical Datalog. Seminaive
  evaluation is exactly the algorithm. Termination on finite
  inputs is automatic. The proof DAG is a single `Rule` firing
  per `path` derivation step.
* **Egglog encoding:**

  ```
  (relation edge (i64 i64))
  (relation path (i64 i64))
  (rule ((edge x y)) ((path x y)))
  (rule ((edge x y) (path y z)) ((path x z)))
  ; user facts:
  (edge 0 1) (edge 1 2) (edge 2 3) …
  (check (path 0 3))
  ```

* **Kernel replay:** built-ins + a `Rule` handler per Datalog
  rule. The handler instantiates the rule under egglog's reported
  substitution, builds the head atom in the arena, and unions it
  with `truth`. Premises are discharged by recursive replay.
* **Caveats:** depends on Phase 4 (relations in the kernel egraph)
  for Layer B. Layer A can ship earlier — egglog handles the
  saturation; we just replay.

---

## Entry 8: Lattice-valued dataflow analysis (constant propagation)

* **Status:** proposed
* **Layer fit:** A first; B much later
* **Signature:** sorts for program-point identifiers + an abstract
  value lattice (`⊥`, constants, `⊤`); a function `val : Point →
  AbsVal` with a `:merge` defined as the lattice join.
* **Decision question:** Given a program (encoded as a relation
  defining the control-flow + transfer-function rules), compute
  the abstract value at each program point.
* **Why egglog suits it:** `:merge` functions are exactly the
  egglog mechanism for lattice-valued analyses. The PLDI '23
  paper uses this as a worked example. The proof DAG mixes
  `Rule` (transfer-function firings) with `MergeFn` (lattice
  join at merge points).
* **Egglog encoding:** standard `(function val (Point) AbsVal
  :merge (join old new))` plus transfer rules.
* **Kernel replay:** built-ins + user transfer rules + a
  `MergeFn` handler that rebuilds the `join` expression under σ
  and applies it as a rewrite. The `join` itself is a kernel
  function in the entry's `Theory`.
* **Caveats:** depends on Phase 5 (merge functions + primitive
  sorts). The kernel rules for lattice join (`a ⊔ a = a`,
  associativity, commutativity, absorption) need to be
  EThm-provable — easy for finite lattices, more interesting for
  general ones. The "proof" we produce certifies the analysis
  result, not the soundness of the analysis as a whole; soundness
  is a separate meta-theorem (and a Layer C use case eventually).

---

## Open slots

The catalogue grows entry by entry, driven by interesting problems
the user actually wants to reach for. Plausible future entries
(notes only; not committed):

* **Finitely-presented group word problem** (decidable for several
  important sub-classes; egglog can saturate small examples).
* **Theory of bit-vectors at fixed width** — decidable, but the
  encoding likely lives outside egglog (bit-blast to SAT and use
  the SAT layer instead).
* **Knuth-Bendix-completed presentations of specific algebraic
  structures** — instances of entries 2 and 6.
* **Type inference / unification fragments** — Robinson-style,
  via Datalog (an instance of entries 7 + 4 combined).
* **Pointer analysis** (Andersen / Steensgaard) — Datalog +
  function-symbol abstraction.

Each future entry follows the template at the top of this file. A
proposed entry that turns out *not* to fit the template — vague
decision question, no termination story, no kernel replay — gets
rejected before any code is written.

## See also

* [`README.md`](./README.md) — proposal index and patchwork framing
* [`00-foundations.md`](./00-foundations.md) — egglog semantics + proof system
* [`01-commands.md`](./01-commands.md) — K/P/O eligibility for each command (a constraint on entries)
* [`03-integration-plan.md`](./03-integration-plan.md) — phasing: which entries land when, and the shared infrastructure that supports them
