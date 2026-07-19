+++
id = "N001H"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:claude"
at = "2026-07-16T21:08:46+01:00"
source = "legacy"
agent = "claude"
harness = "claude"
+++

# ACL2 book front end — the first honest BOOK IMPORT pipeline (S11-lite)

*(AI-generated design note, 2026-07-16. Companion to
[`acl2-dialect.md`](./acl2-dialect.md) — the dialect this pipeline drives —
and to [`acl2-s0-s3-design.md`](./acl2-s0-s3-design.md) §9.5 /
[`acl2-s4-s6-design.md`](./acl2-s4-s6-design.md), which define the proving
machinery the pipeline reaches (or honestly declines to reach). Implementation:
`crates/lang/lisp/src/book.rs`; fixtures + tests under
`crates/lang/lisp/tests/books/` and `crates/lang/lisp/tests/book.rs`.)*

## 1. Scope

A **book** is a `.lisp` file of top-level ACL2 *events*, community-book style.
The pipeline

1. **reads** the file into events (the existing S-expression reader — no new
   parser),
2. **drives** each event through the existing [`Acl2Session`]
   (`crates/lang/lisp/src/acl2.rs`) — the same admissibility / proof
   discipline as the REPL, nothing new is trusted, and
3. **tallies** per-event outcomes into a report that *never* claims more than
   the theorems actually in hand.

This is deliberately the *lite* slice: a real import loop with an honest
scoreboard, not ACL2 certification. Everything the dialect cannot genuinely
prove or admit is a **recorded** skip/rejection with a reason — the report is
the demo artifact ("n/m defthms transported to closed base-HOL theorems, here
is exactly what fell out and why").

## 2. Reader (events, not a new parser)

`covalence_lisp::reader::read_book` parses a whole file with
`covalence_sexp::parse_smt` — the SMT-LIB dialect is the one whose trivia
rules match Lisp source (single-`;` line comments, `"..."` strings, `|...|`
symbols). The REPL's `read`/`read_one` (Covalence dialect, `;;` comments) is
unchanged.

Reader-level deviations from real community books (recorded, not hidden):

- **No `'x` reader macro** — the shared S-expression parser has no quote
  sugar; fixture books write `(quote …)` explicitly. A `'`-expanding trivia
  pass in `covalence-sexp` would be the fix (future work).
- **No `#|…|#` block comments**; `;` line comments only.
- **Case-sensitive, single package**: the dialect's spellings are lowercase;
  `(in-package …)` is parsed and recorded but is a no-op.

## 3. Event grammar

Per top-level form, classified by head (`book.rs::process_event`):

| event | handling |
|---|---|
| `(in-package "PKG")` | recorded, no-op (single-package slice) → **skipped** |
| `(include-book "name")` | resolve `name + ".lisp"` **relative to the including book's directory**, confined to the book root (§6); found → recursively processed into the same tally (cycle-safe: a canonical-path `seen` set makes re-inclusion idempotent, as in ACL2); missing → **skipped** dependency (not an error) |
| `(include-book "name" :dir …)` | **skipped** — no system/`:dir` book directory is configured in this slice |
| `(defun name (formals) body)` | `Acl2Session` admissibility (syntactic structural recursion) + install → **admitted** or **rejected** with the session's reason |
| `(defthm name goal :hints … :rule-classes … …)` | keyword arguments after the goal are **ignored but recorded** in the event's notes; the bare `(defthm name goal)` is driven through the session → **transported** / **admitted** / **rejected** (§4) |
| `(local event)` | contents **processed** (the inner event genuinely runs — a `local` defun is installed and usable by later events) but tallied **skipped**-as-local; an inner failure is a **rejection** (`local: …`) |
| `(encapsulate …)`, `(defmacro …)`, `(mutual-recursion …)`, any other head, non-list forms | **rejected** with a reason naming the unsupported event class |

`(defthm … (implies …))` goals *parse* fine as events; the prover slice then
rejects them (free variables need induction; `implies` is not a dialect head)
— they land in the tally as honest rejections, which is exactly what the
deliberately-mixed fixture pins.

## 4. Tally semantics (the honesty boundary)

Four outcome classes, one per event (nested include events carry their own
book path in the report):

- **transported** — a `defthm` that went through the reified
  certificate path (`Acl2Proof::Certificate`: `⊢ Derivable_ACL2 ⌜goal⌝` →
  soundness metatheorem → `transport_equal`) and whose stored theorem is the
  **hypothesis-free base-HOL model equation**. The pipeline *re-checks* this
  at the boundary: it retrieves the stored theorem and asserts
  `hyps().is_empty()` + the certificate provenance before classifying;
  anything else is downgraded to *admitted*. No code path claims
  "transported" without the theorem in hand.
- **admitted (in dialect)** — a `defun` installed (as a kernel *hypothesis*,
  never an axiom), or a `defthm` proved on the reduction path (a genuine
  kernel theorem whose hypotheses are exactly the `defun` equations used —
  the report says how many hypotheses ride).
- **skipped** — `in-package`, `include-book` dependencies (missing, `:dir`,
  already-included, or satisfied — a satisfied include is itself a skip whose
  *contents* are tallied as their own events), and `local` wrappers.
- **rejected (reason)** — inadmissible `defun`s, unprovable / refuted /
  free-variable `defthm`s, unsupported event forms, malformed events, and
  include paths that try to escape the book root. Processing **continues**
  after a rejection (best-effort tally; deviation from ACL2's fail-fast
  certification, recorded here) — later events that depended on a rejected
  one fail with their own reasons.

The report renders a per-event table plus a summary line
(`k/n defthms transported, … admitted, … skipped, … rejected`).

## 5. What is deferred (recorded in `crates/lang/lisp/SKELETONS.md`)

- **Induction-backed defthms.** The kernel-side S6 route exists and is gated
  (`covalence-init` `init/acl2`: `s6_env`/`Acl2Session::admit_defun` +
  `hilbert::derive_under` + `derive_ind` + `transport_equal_open`; see
  `hilbert.rs::t_app_assoc_gate`), but the *premise builders* there are
  hand-written per theorem (~150 bespoke deduction-compiler steps for
  app-assoc: unfold `defun`s under `if-true`/`if-false`, `CongImpl` chains,
  IH splicing). Wiring the book pipeline onto it needs a generic
  premise-builder (a small object-level simplifier over the Hilbert
  step language: defun unfolding + equality chaining + IH use, per candidate
  induction variable) — genuinely out of this slice's scope, so
  free-variable `defthm`s (e.g. the fixture's `app-assoc`, `len2-app`)
  are **honestly rejected naming induction**, not half-wired. This is the
  single highest-value follow-up.
- Everything §2–§3 marks: `'` reader sugar, `encapsulate` / `defmacro` /
  `mutual-recursion` / other event classes, `:dir` book directories,
  two-pass `local` semantics (we run pass 1 only: local events persist in
  the session; nothing is undone at end-of-book), packages,
  `:rule-classes` semantics (recorded, never interpreted).

## 6. Surface + confinement

`#book <path>` in the `acl2` dialect (`session.rs`) runs the pipeline in the
session's ACL2 sub-session and prints the tally. Paths are **session-relative
and confined**: a `Session` carries a book root (default: the process working
directory, canonicalized; `Session::set_book_root` to override). Resolution
rejects absolute paths and any `..` component lexically, then canonicalizes
and requires the result to stay under the canonical root (symlink-safe) — so
the server's `/api/lisp` endpoint (which forwards cells to `eval_cell`)
cannot be used to read or traverse outside the directory the server was
started in. `include-book` resolution inside a book applies the same
confinement (an escaping include is a rejected event).
