# ACL2 fidelity ledger — assumptions and deviations

What our embedding says ACL2 is, versus what ACL2 actually is. Every entry is a
**deliberate, recorded deviation**; nothing here is an accident. When a book
import behaves differently from real ACL2, the cause should be findable on this
list — if it isn't, that's a bug. Kept current as stages land; the per-stage
design notes (`acl2-s0-s3-design.md` §9.5, `acl2-s4-s6-design.md`,
`acl2-s5-design.md` §1.1) hold the rationale.

## The object universe (carrier)

- **Numbers are integers, not rationals** (until S8). Real ACL2: rationals +
  complex rationals. Ours: `int` only. `intval` coerces non-numbers to 0
  (matches ACL2's completion for the arithmetic fragment we cover); rationals'
  absence means `(/ 1 2)`-style books are out of fragment, and `o-p`'s
  coefficient positivity is over ints (recorded in the S5 design as
  ints-not-rats).
- **No characters or strings** yet (slotted when books need them; plan S0 note).
- **Symbols are bare byte-blobs, no packages.** Real ACL2 symbols are
  (package, name) pairs with `intern`/`symbol-package-name` semantics;
  `in-package` changes reader context. Ours: `asym "T"` etc.; `in-package` is
  tallied *skipped*; two symbols are equal iff their names are. Books relying on
  package discipline will mis-import — the reader should reject same-name
  cross-package tricks if we ever hit one.
- **`t := asym "T"`, `nil := anil`** — with a hard **translator contract: never
  emit `asym "NIL"`** (it would be a distinct, wrong object). The reader/encoders
  enforce this; new front-end code must too.

## The logic

- **Quantifier-free, as in real ACL2**; theorem-ness is `∀σ. eval φ σ ≠ anil`
  with the ∀ internalized in `sound_pred` (forced by INST — deviation from the
  prop ladder's free-valuation shape, recorded in S3 design).
- **The evaluator is total with `anil` for unknown heads**: `eval` of an
  application whose head is not a known row evaluates to `anil`. This is a
  *model* choice (real ACL2 terms are always well-formed applications of known
  functions); it is sound because derivability clauses only ever mention known
  rows, but it means eval-of-garbage is `nil`, not stuck.
- **Propositional layer is IF-form K/S/MP only** (Hilbert compiler,
  `hilbert.rs`); **no classical axiom yet** — the S5-designed `cases` row is
  specified but unimplemented (open SKELETONS entry). Positive gate proofs
  haven't needed it; some book defthms will.
- **`=`, `eql` are normalized to `EQUAL`** at translation (S5 design §1.1: the
  garbage-completion deviation — real ACL2 `=` has a numeric guard; guards are
  logic-irrelevant, so this is sound but coarser). `and`/`not`/`atom`/`<=`
  macro-expand at translation.
- **`lambda` is outside the eval/subst fragment** (S2 deviation, SKELETONS
  minor). ACL2 pseudo-terms include `((lambda …) …)`; ours are rejected at
  translation until a stage needs them (ACL2 lambdas are always closed, so the
  extension is mechanical but unforced so far).

## Events

- **defun admissibility (current)**: consp-guarded, single-formal, **depth-1
  car/cdr** structural descent only (stricter than real ACL2's measure-based
  principle, and stricter than the lang-side dialect's syntactic check —
  deviation recorded in the S4 design). Everything else is rejected-with-reason
  until S7 (measured recursion via `o<`/`wf_induct`). No mutual recursion, no
  `:measure` hints consumed yet.
- **defthm (current)**: proved only via (a) ground certificate evaluation, or
  (b) structural induction (S6 IND, init-side; book-pipeline wiring deferred).
  `:hints` and `:rule-classes` are **stripped and recorded**, never interpreted
  — real ACL2's rewriter/hint machinery is entirely absent; we prove or reject.
  IMPLIES-form goals parse but are rejected pending `transport_implies_open`.
- **Ordinals are ACL2-faithful** (`o-p`/`o<` as carrier functions matching the
  modern CNF definitions), modulo ints-not-rats coefficients. Well-foundedness
  is proved at full ε₀ (`wf`, `wf_induct` in `ordinal.rs`) — this part is
  *stronger* than an assumption: it's the theorem real ACL2 postulates.
- **Books**: reader accepts single-`;` comments only (no `#|…|#`, no `'x`
  reader macro — fixtures write `(quote x)`); `include-book` resolves relative
  to the including book, confined to the session book-root, `:dir` unsupported
  (skipped); `local` is processed then tallied *skipped* (not yet real two-pass
  local scoping); `encapsulate`/`defmacro`/`mutual-recursion` rejected with
  reasons. `in-package` skipped (see symbols).
- **Guards do not exist** for us (S12: record-only). This is *aligned* with the
  ACL2 logic (guards are extra-logical) but means guard-verification-dependent
  book structure (`mbe`, `ec-call`) is out of fragment.

## The soundness story (what a transported theorem means)

A tally row "transported" means: a hypothesis-free base-HOL kernel theorem
`⊢ ⟦φ⟧` exists, derived by (1) a `Derivable_ACL2` membership certificate built
clause-by-clause, (2) the rule-inducted soundness metatheorem for the exact env
in force, (3) `project_*` + `transport_equal[_open]`. No step trusts the Rust
front end: a wrong certificate fails kernel `imp_elim`; a wrong fold fails the
projection; the boundary re-checks `hyps().is_empty()`. "Admitted-in-dialect"
means weaker evidence (value-semantics reduction with defun-equation
hypotheses) — the tally never conflates the two.

**Env-relativity**: soundness is proved per extended env (each defun changes the
clause set). Transported theorems are absolute (closed HOL theorems); only the
*derivability* claims are env-relative.
