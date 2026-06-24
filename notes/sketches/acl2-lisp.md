# ACL2 and Lisp as object logics — the computational first-order frontend

> **STATUS: DESIGN SKETCH.** ACL2 (the Boyer–Moore computational logic) and Lisp
> (as an executor + the reasoning frontend for it) entering Covalence. A named
> north star (the "ACL2/Lisp" target). Part of the
> [`logic-frontends.md`](../logic-frontends.md) umbrella — see it for the
> four-artifact pattern and difficulty axes. The naive-compiler cousin is
> [`covalence-ml-naive-compiler.md`](./covalence-ml-naive-compiler.md) (same
> "naive trusted core + mature untrusted mirror" pattern).

---

## 1. Why this is the recommended first non-trivial frontend

ACL2 is the cheapest high-leverage member of the whole menu:

- **Statability: trivial.** ACL2 is *first-order* and essentially
  quantifier-free — no object-level binders. The waist's metavariable + DV
  substitution expresses it directly; none of the type-theory binding machinery
  is needed.
- **Strength: weak, in-HOL.** ACL2 is (roughly) primitive-recursive arithmetic
  extended with induction up to **ε₀**. HOL proves transfinite induction far past
  ε₀, so ACL2 has a *genuine HOL model* with no added strength — `+model` is
  cheap (umbrella §4 row "ACL2").
- **It forces the executor axis** — ground Lisp evaluation — which is reusable by
  every computational frontend (MLTT conversion, NuPRL reduction, WASM oracles).
  Building it here, in the logically-simplest setting, de-risks it.

So it exercises the *executor* and *in-HOL model* infrastructure with the least
logical risk, while being directly useful (the ACL2 books are a large verified
corpus).

## 2. The two faces of "Lisp support"

"Lisp" splits cleanly, and the split matters:

- **Lisp-as-executor** — a Lisp evaluator in the **bottom layer** (executors +
  content-addressing). Lisp ground terms *are* data; `eval` is a reduction. This
  is an executor mirror alongside WASM (cf. the naive ML→WASM sketch): a small,
  auditable interpreter (or a naive Lisp→WASM compiler) as the *trusted* core,
  with a mature Lisp riding alongside as an *untrusted optimized mirror*;
  agreement on test inputs discharges to consilience. Covalence's surface is
  already S-expressions (`covalence-sexp`, `.cov`), so homoiconicity aligns: `S`
  transport functions are themselves Lisp-flavored term rewriters.
- **Lisp-as-logic** — ACL2 *is* "the logic of a pure first-order functional
  subset of Lisp." So **ACL2 is the reasoning frontend for Lisp**; there is no
  separate "Lisp logic" to build. Reasoning about a Lisp program = stating it in
  `D_ACL2` and proving in that database.

The bottom-layer executor and the ACL2 logic meet at **ground evaluation**: an
ACL2 term with no free variables is discharged by *running it* on the executor,
and the executor's correctness vs. the ACL2 axioms is the admission ticket
("proven-WASM/Lisp compilation").

## 3. `D_ACL2` — the database

The four artifacts (umbrella §2) for ACL2:

**Definition.** A Metamath database = first-order logic + the ACL2 ground theory:

- **The universe.** ACL2 objects: numbers (rationals, complex-rationals),
  characters, strings, symbols, and conses. As a HOL datatype this is one
  inductive type `Acl2Obj`; in the waist it is the FOL signature
  `cons/car/cdr/consp/atom/equal/…` with their defining axioms.
- **Primitive axioms.** The ~dozens of ACL2 ground axioms (`car`/`cdr`/`cons`
  laws, the arithmetic on `acl2-numberp`, the `nil`/`t` booleans, total-function
  conventions — `car nil = nil`, etc.).
- **The definitional principle.** A recursive `defun` is admitted only with a
  **measure** proving termination — well-founded descent on the **ACL2 ordinals**
  (ordinal notations below ε₀). In the database this is a conservative-extension
  rule: a new function symbol + its defining equation, guarded by a termination
  obligation. This maps directly onto the kernel's existing `define` /
  `new_type_definition` conservative-extension machinery (covalence-core).
- **The induction principle.** ACL2's induction is *derived* from the
  well-founded descent of the definitional principle. In HOL it is ordinary
  well-founded/transfinite induction up to ε₀ — already within reach.
- **Encapsulation.** Introduce *constrained* functions (axioms about a symbol
  with a local witness proving consistency) = a witnessed conservative extension —
  again the `define`-with-witness pattern.

**Native accelerator = the executor.** Ground `Derivable_ACL2` goals of the form
"`(f c₁ … cₙ) = v`" are discharged by evaluation, not proof search: run on the
Lisp/WASM executor (§2), transport across faithfulness.

**Faithfulness `Metamath-ACL2 ≅ HOL-ACL2`.** The HOL model: `Acl2Obj` datatype,
total functions as HOL functions, the ground axioms as HOL theorems, ε₀-induction
as HOL induction, ordinals as a HOL ordinal-notation type. Down: certifies
`D_ACL2` is the real ACL2. Up: admits the executor and any native ACL2
proof-replay. **This model exists outright (weak strength)** — the comfortable
case.

**Transport `S`.** ACL2 ↔ PA / SOA is natural (ACL2's arithmetic interprets into,
and a fragment of, the PA/SOA reified logics already in `peano/`). ACL2 ↔ a Lisp
operational semantics is the executor-correctness theorem. The book corpus
becomes `Derivable_ACL2` facts transportable into HOL via the model.

## 4. Importing ACL2 books

Like set.mm, ACL2 ships a large machine-checked corpus (the community books).
The frontend pattern (umbrella §2, artifact #2) is *replay as untrusted
frontend*: parse a book's events (`defun`/`defthm`/`encapsulate`), and for each
`defthm` construct `Derivable_ACL2 ⌜φ⌝` by re-deriving through the engine — the
same "construct, don't trust" honesty principle used for set.mm (we never trust
ACL2's own prover; we certify existence of a derivation in `D_ACL2`). Ground
lemmas collapse to executor evaluation. The motivating benchmark mirrors the
`/metamath` import demo.

## 5. Difficulty summary

- **Derivable (the floor): low.** First-order, no binders, conservative-extension
  machinery already present. The genuinely new pieces are the ACL2 object
  universe + the ε₀ ordinal/measure apparatus + the Lisp evaluator.
- **+model: low–moderate.** The HOL model is uncomplicated (weak strength); the
  bulk is the ground-axiom catalogue + proving the executor sound vs. the axioms.
- **Reusable dividend:** the **executor** (ground Lisp/WASM eval + its soundness
  protocol) and the **conservative-extension-with-measure** pattern both serve
  later frontends. This is why ACL2/Lisp is sequenced first (umbrella §5).
