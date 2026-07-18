+++
id = "N001S"
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

# ACL2 and Lisp as object logics

> **DESIGN SKETCH.** ACL2 (the Boyer–Moore computational logic) + Lisp (as an
> executor and its reasoning frontend) entering Covalence. Part of the
> `../logic-frontends.md` umbrella (four-artifact pattern, difficulty axes).
> Cousin: [`covalence-ml-naive-compiler.md`](../../sketches/covalence-ml-naive-compiler.md)
> (same "naive trusted core + mature untrusted mirror" pattern).

## 1. Why this is the first non-trivial frontend

The cheapest high-leverage member of the menu:

- **Statability: trivial.** ACL2 is first-order and essentially
  quantifier-free — no object-level binders. The waist's metavariable + DV
  substitution expresses it directly.
- **Strength: weak, in-HOL.** ACL2 is roughly primitive-recursive arithmetic +
  induction up to ε₀. HOL proves transfinite induction far past ε₀, so ACL2 has
  a genuine HOL model with no added strength — `+model` is cheap.
- **It forces the executor axis** — ground Lisp evaluation — reusable by every
  computational frontend (MLTT conversion, NuPRL reduction, WASM oracles).
  Building it in the logically-simplest setting de-risks it.

The ACL2 community books are a large verified corpus, so it's directly useful too.

## 2. Two faces of "Lisp support"

- **Lisp-as-executor** — a Lisp evaluator in the bottom layer (executors +
  content-addressing). Lisp ground terms *are* data; `eval` is a reduction. A
  small auditable interpreter (or naive Lisp→WASM compiler) is the trusted core,
  a mature Lisp rides alongside as an untrusted optimized mirror; agreement on
  test inputs discharges to consilience. Covalence's surface is already
  S-expressions (`covalence-sexp`, `.cov`), so `S` transport functions are
  themselves Lisp-flavored term rewriters.
- **Lisp-as-logic** — ACL2 *is* the logic of a pure first-order functional
  subset of Lisp. **ACL2 is the reasoning frontend for Lisp**; there's no
  separate "Lisp logic" to build. Reasoning about a Lisp program = stating it in
  `D_ACL2` and proving there.

They meet at **ground evaluation**: an ACL2 term with no free variables is
discharged by running it on the executor; executor-vs-ACL2-axiom correctness is
the admission ticket.

## 3. `D_ACL2` — the database

The four artifacts:

- **Definition** — a Metamath database = FOL + the ACL2 ground theory:
  - *Universe.* ACL2 objects (numbers, characters, strings, symbols, conses) as
    one inductive HOL type `Acl2Obj`; in the waist, the FOL signature
    `cons/car/cdr/consp/atom/equal/…` + defining axioms.
  - *Primitive axioms.* The ACL2 ground axioms (`car`/`cdr`/`cons` laws,
    arithmetic on `acl2-numberp`, `nil`/`t`, total-function conventions like
    `car nil = nil`).
  - *Definitional principle.* A recursive `defun` is admitted only with a
    measure proving termination — well-founded descent on the ACL2 ordinals
    (below ε₀). A conservative-extension rule; maps onto the kernel's existing
    `define` / `new_type_definition`.
  - *Induction.* Derived from the definitional principle's well-founded descent;
    in HOL, ordinary transfinite induction up to ε₀.
  - *Encapsulation.* Constrained functions (axioms about a symbol + a local
    witness) = a witnessed conservative extension — the `define`-with-witness
    pattern.
- **Native accelerator = the executor.** Ground `(f c₁ … cₙ) = v` goals are
  discharged by evaluation on the Lisp/WASM executor, transported across
  faithfulness.
- **Faithfulness `Metamath-ACL2 ≅ HOL-ACL2`.** HOL model: `Acl2Obj` datatype,
  total functions as HOL functions, ground axioms as HOL theorems, ε₀-induction
  as HOL induction, ordinals as a HOL ordinal-notation type. This model exists
  outright (weak strength) — the comfortable case.
- **Transport `S`.** ACL2 ↔ PA/SOA is natural (ACL2 arithmetic interprets into
  the reified logics in `peano/`); ACL2 ↔ a Lisp operational semantics is the
  executor-correctness theorem.

## 4. Importing ACL2 books

Like set.mm, ACL2 ships a machine-checked corpus. Replay as an untrusted
frontend: parse a book's events (`defun`/`defthm`/`encapsulate`), and for each
`defthm` construct `Derivable_ACL2 ⌜φ⌝` by re-deriving through the engine (the
"construct, don't trust" principle — we never trust ACL2's prover). Ground lemmas
collapse to executor evaluation.

## 5. Difficulty

- **Derivable: low.** First-order, no binders, conservative-extension machinery
  present. New pieces: the ACL2 object universe, the ε₀ ordinal/measure
  apparatus, the Lisp evaluator.
- **+model: low–moderate.** The HOL model is uncomplicated; the bulk is the
  ground-axiom catalogue + proving the executor sound vs the axioms.
- **Reusable dividend:** the executor (ground Lisp/WASM eval + its soundness
  protocol) and the conservative-extension-with-measure pattern both serve later
  frontends — why ACL2/Lisp is sequenced first.
