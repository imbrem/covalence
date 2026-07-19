+++
id = "N003X"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:codex"
at = "2026-07-19T00:00:00+01:00"
source = "corpus-analysis"
agent = "codex"
harness = "codex"
+++

# ACL2 x86isa: corpus-derived import roadmap

## North star and honesty boundary

The north star is not “recognize every `defthm` form.” It is:

> Load the complete x86isa development, reproduce its event world (including
> generated events and linked books), and transport every logical theorem in
> that world to a hypothesis-free Covalence kernel theorem, with no admission,
> skipped proof obligation, or hidden trust expansion.

“Every theorem” must be measured **after** ACL2 macro expansion and
`make-event`, not by source grep. The source contains quoted event templates,
local events, generated instruction families, and macros that emit theorems.
Conversely, `include-raw`, trust tags, execution attachments, XDOC, guards, and
tables are not theorem axioms. They need faithful world/evaluation handling but
must not be counted as transported theorems.

There is no honest short cut from an ACL2 certified book to a Covalence
theorem. ACL2 certificates and `@useless-runes` files do not contain
foundational proof objects. Running ACL2 may be used as an **untrusted event
normalizer/oracle**, but its success cannot mint a kernel theorem. Full
acceptance therefore needs either:

1. reconstruction of ACL2 proofs in the reified soundness ladder, including
   rewriting, induction, linear/nonlinear arithmetic, meta/clause processors,
   GL, and functional instantiation; or
2. an independently checked proof certificate exported by instrumented ACL2.

The practical plan uses both: build native reconstruction for the common core,
then define a small explicit certificate language for expensive processors.
The certificate checker and its soundness theorem are the boundary; ACL2,
macro expansion, SAT solvers, and generators remain untrusted.

## Corpus snapshot

Measured 2026-07-19 at ACL2 community-books commit
`2dbf2b63bb9a27070c8573d72c16c04a4809c8d1`, under
`books/projects/x86isa`, excluding generated `.sys` files:

| slice | `.lisp` files | source lines | lexical top-level forms |
|---|---:|---:|---:|
| all x86isa | 190 | 162,032 | 4,987 |
| `machine/` | 106 | 91,234 | 2,003 |
| `proofs/` | 54 | 54,127 | 2,058 |
| `tools/` | 15 | 11,515 | 259 |
| `utils/` | 7 | 2,610 | 222 |
| `portcullis/` | 4 | 1,106 | 387 |

The checked-in analyzer is
`scripts/analyze-acl2-books.pl`. It is deliberately lexical: it handles line
comments, nested block comments, strings, and escaped symbols, but it neither
reads ACL2 packages nor macroexpands. Its numbers are prioritization evidence,
not a certification manifest.

### Authored event surface

Most frequent top-level heads:

| head | count | implication |
|---|---:|---|
| `defthm` | 847 | ordinary theorem reconstruction is the central gate |
| `local` | 654 | certification-pass scoping/world rollback is mandatory |
| `define` | 541 | `std::define` expansion, guards, returns, and generated theorems |
| `include-book` | 494 | linking is not peripheral |
| `defconst` | 442 | evaluated constants and sharp-dot dependencies |
| `defthmd` | 369 | theory enable/disable state affects proof replay |
| `def-inst` | 205 | x86 instruction generation is macro-driven |
| `make-event` | 168 | static source interpretation cannot enumerate the world |
| `defun` | 149 | recursive admission and executable definitions |
| `def-sdm-instruction-section` | 136 | generated catalogue/table events |
| `defmacro` | 130 | source-local macro environment |
| `defsection` | 117 | event containers and local theory changes |
| `defun-nx` | 115 | non-executable logical functions |
| `defthm-using-gl` | 68 | bit-blasting/certificate path |
| `defbitstruct` | 53 | FTY/bit-field generated APIs and laws |
| `in-theory` | 53 | ACL2 theory state is proof-relevant |
| `encapsulate` | 45 | constrained functions and local witnesses |

There are also 24 `defxdoc`, 17 `defthm-unsigned-byte-p`, 15 `def-ruleset`,
eight `assert!-stobj`, seven `defprod`, six `def-gl-thm`, four `defund`,
three trust-tag events, two `defines` groups, and isolated `defpun`,
`defaggregate`, `defequiv`, `deftheory`, `include-raw`, and `table` events.

Lexically counting **all** list heads (including quoted templates) finds 2,222
`defthm` and 530 `defthmd` occurrences. This is a useful upper-pressure signal,
not the final denominator. The final event manifest must be emitted by the
normalization stage and pinned by source hash.

### Term language and primitive pressure

High-frequency list heads include `cons` 6,517, `equal` 6,179, `mv-nth` 3,658,
`mv` 2,841, `and` 2,733, `implies` 2,465, `the` 2,896, `loghead` 1,654,
`ash` 1,263, `logand` 1,202, `b*` 1,128, `unsigned-byte-p` 958, `logtail`
855, `mbe` 665, `logext` 652, `logior` 606, `natp` 572, and `list` 513.
Other required families include:

- control/binding: `let`, `let*`, `cond`, `case`, `case-match`, `mv-let`,
  short-circuit `and`/`or`, `when`, lambda, declarations;
- ACL2 numerics: arbitrary integers, rationals, complex rationals, `floor`,
  `mod`, `truncate`, `expt`, signed/unsigned-byte predicates, and the complete
  logical bit-operation family;
- records/state: `xr`, `xw`, nested stobj access, arrays/bigmem, multiple
  values, `state`, and read-over-write/write-over-write laws;
- execution/logical duality: 665 lexical `mbe` heads and 22 `ec-call` heads;
  logical import must select and prove the `:logic` meaning while preserving a
  separately labelled executable fast path;
- theorem language: forced hypotheses, bind-free/meta rules, congruence and
  equivalence rules, rule classes, theory expressions `e/d` and `e/d*`, and
  hints.

Reader pressure is immediate: approximately 18,913 hexadecimal literal tokens,
3,169 sharp-dot occurrences, 419 x86-oriented `#u...` tokens, 101 binary
literals, and 50 character-reader occurrences. Exact counts are lexical and
include documentation/templates. Sharp-dot is especially important:
`portcullis/sharp-dot-{defuns,constants}.lisp` intentionally establishes the
read-time environment used by the machine books.

The 2026-07-19 reader/world slices convert `#b`/`#o`/`#x` and x86isa
underscore-tolerant `#u[bodx]` integer tokens to decimal evaluator numerals,
preserve character and package-qualified tokens, and expand `#.form`
structurally to `(sharp-dot form)`. The theorem-neutral ordered world evaluator
loads all constants and generated register constants from
`portcullis/sharp-dot-{defuns,constants}.lisp`; it evaluates sharp-dot data but
does not admit definitions or mint theorems. Other package-installed dispatch
readers and feature conditionals remain explicitly open.

The importer integration gate at community-books commit `2dbf2b63` processes
the constant world in source order, recursively tallies generated events with
their `make-event` provenance, and classifies computation separately from
theorem authority. The full linked portcullis report has 539 rows, 381
read-time-world rows, and 56 unresolved rows. Relative to the prior importer,
the 346 authored `defconst` plus 15 authored `make-event` forms no longer
contribute unresolved rows (a direct unresolved delta of at least -361), while
15 emitted `defconsts` rows become newly visible and successful.

The next X2 slice installs ordinary quasiquoted `defmacro` templates with
plain required and final `&rest` parameters. Macro calls expand recursively as
untrusted event data and retain call provenance; computational macro bodies,
`&key`, `&optional`, destructuring, and other unsupported lambda lists reject
explicitly. On the pinned `utils/utilities.lisp` closure the manifest has 622
rows, 42 linked macro definitions, and 156 unresolved rows. Five x86 utility
template definitions (`mk-name`, `forced-and`, `globally-disable`, and the two
show-status macros) move out of the unresolved class, a direct delta of -5;
the three computational macros (`defuns-np`, `n-size`, `ntoi`) remain honest
rejections.

The first instruction-generator gate follows the actual `def-inst` chain:
`machine/decoding-and-spec-utils.lisp` defines one conditional quasiquoted
macro with one required parameter and ACL2 `&key` defaults; 205 authored calls
use it. The world now supports this faithful keyword subset (quoted defaults,
unknown/duplicate-key rejection) and expands the scalar `x86-invlpg` call to
its generated `define`, retaining macro-call provenance. Loading its real book
also exposed a linker constraint: x86 relative includes legitimately use
`../`; these are now allowed only when canonicalization remains inside the
independently configured root, so symlink confinement remains intact. The
scalar closure gate now traverses 2,146 rows with one `def-inst` and 361
unresolved rows. Its generated extended `std::define` successfully normalizes
in inventory mode, including typed binders, the declaration preceding its
options, `:guard-hints`, `:returns`, its body, and the trailing `///` section.
Across the concurrent X2/event-expansion work the observed unresolved count
fell from 440 to 361 (-79); the one-row removal of the generated
`x86-invlpg` definition is directly attributable to this slice. The leading
remaining rows are the sparse checkout's absent `xdoc/top`, the
supplied-p/destructured keyword lambda list of `def-generic-rule`, and
constrained signatures inside `encapsulate`.

The next macro-fidelity slice implements `&optional` and `&key` defaults and
supplied-p variables, ACL2 guard-bearing formals, and explicit
keyword-to-variable designators. This installs the real `def-generic-rule`
instead of rejecting it. The current scalar snapshot is 2,355 rows and 402
unresolved rows after concurrent event-expansion work; this closure contains
no calls of `def-generic-rule`, so its directly attributable unresolved delta
is exactly -1 (403 to 402 with the rest of that snapshot held fixed).
Constrained `encapsulate` signatures are consequently the first
implementation blocker after the sparse-checkout `xdoc/top` edge.

The first full-top `make-event` pass aggregates rejection reasons instead of
sampling isolated failures. At its baseline, `x86isa/top` had 1,054 unresolved
rows, including 366 failed `make-event` rows; 136 used a dotted generator call,
and the next generator families stopped at small list predicates or x86's
`mk-name` convention. Recoverable `define` events now also install
theorem-neutral read-time functions, dotted calls apply their constructed
argument lists, and the evaluator supports `true-listp`, `consp`, `atom`,
`mbt`, `eq`/`eql`, `mk-name`, and b*'s `?name` binding convention. Generated
forms still re-enter the ordinary importer and receive no theorem authority.
The measured top manifest falls to 928 unresolved rows (-126 overall), while
failed `make-event` rows fall from 366 to 225 (-141); newly visible generated
events account for the difference. The dominant remaining family is the 136
keyword-bearing `def-sdm-instruction-section-fn` calls, which requires
read-time `define` keyword formals and its catalogue helpers rather than a
special-case admission.

Keyword-formal read-time `define` calls now bind guarded keys and defaults,
including dotted calls from `def-sdm-instruction-section`. The catalogue path
also has multiple-value and conditional b* binders, section-number string
parsing, and a bounded view of the authored pre-opcode maps. This expands the
plain catalogue sections with ordinary table-event provenance and reduces the
full-top manifest from 928 to 791 unresolved rows (-137). Of the 136 original
catalogue calls, 21 now expand and 115 remain: 106 stop in the
symbol-name/explicit-mnemonic path, with the remainder requiring feature and
promoted-instruction helpers. This is a measured intermediate gate, not a
claim that all catalogue entries are reconstructed yet.

The next normalization sequence replays the official sibling certification
prelude (`top.acl2`) before `top.lisp`, so the import begins in the same
sharp-dot constant world as ACL2 certification. Proper ACL2 lists use flat
world storage and the importer evaluates on a fuel-bounded dedicated worker
stack, avoiding recursive cons-spine clone/drop failures. The x86 state field
inventory, save/restore definitions, catalogue feature filters, escaped
mnemonic aliases, non-mutual FTY containers, and all unsigned LSB-first
`defbitstruct` aggregates now expand. `std::define` prepwork, optional/keyword
formals, multiple returns, post-body metadata, and type prescriptions preserve
their generated theorem obligations. Bounded world queries expose only
registered signatures and define return metadata; they mint no theorem.

At the current gate the manifest has 2,590 logical definitions, 3,852 logical
theorems, 2,459 proof-control rows, 612 execution/documentation rows, 1,802
read-time-world rows, and 336 unresolved dependencies. The theorem count grew
because previously hidden generated obligations are now visible; it is not a
claim that those theorems are transported. Finalized opcode maps are now
installed as generated data and their selection/dispatch consumers operate on
flat lists iteratively, so the official gate remains inside its 32 MiB bounded
worker stack. The largest remaining generated-event clusters are nested `b*`
destructuring, `defaggregate`/`defenum` world primitives, and book-relative
file/platform queries.

### State and generated events

x86isa does not spell a simple `defstobj` in this subtree. `machine/state.lisp`
constructs `*x86isa-state*` and passes it through `make-event`/Centaur
`defrstobj2`, with bigmem/nested-stobj support. This generates the x86 state,
accessors, updaters, recognizer, and laws. Treating `make-event` as an ignored
container would silently omit the model.

The source also uses:

- 168 top-level `make-event` forms, 140 in `machine/`;
- 130 source-local `defmacro` forms, including `def-inst`,
  `def-sdm-instruction-section`, exception-checking, memory access, flag, and
  serialization families;
- at least one `with-local-stobj`, two `defattach`, seven `verify-guards`
  occurrences, 21 lexical `table` heads, and two `include-raw` events;
- FTY `defprod`/`deftypes`/`deflist`/`defoption`, `defbitstruct`, and
  `defaggregate`;
- GL theorem and rewrite events.

This divides support into three explicit semantics:

1. **logical world events**, which may contribute definitions/theorems;
2. **proof-control events**, which affect reconstruction but not formulas;
3. **execution/documentation events**, which may be recorded or separately
   executed but cannot add logical authority.

## Include graph

The authored corpus contains 861 lexical `include-book` edges from 185 of 190
files:

| edge kind | occurrences | resolution |
|---|---:|---|
| relative | 384 | 383 resolve inside x86isa; one crosses to `projects/codewalker` |
| `:dir :system` | 428 | community-book root |
| `:dir :utils` | 22 | x86isa `utils/` |
| `:dir :proof-utils` | 23 | x86isa `proofs/utilities/` |
| `:dir :machine` | 4 | x86isa `machine/` |

There are 319 distinct `(directory,target)` pairs. The hottest system
dependencies are `centaur/bitops/ihs-extensions` (102 edges),
`centaur/bitops/signed-byte-p` (41), `arithmetic-5/top` (37),
`arithmetic/top-with-meta` (29), `centaur/gl/gl` (16),
`centaur/bitops/ihsext-basics` (15), `arithmetic-3/top` (11),
`centaur/bitops/equal-by-logbitp` (9), and `std/lists/nthcdr` (9).

The dependency closure is therefore broader than x86isa. It includes at least:

- Centaur bitops, GL, FTY, `defrstobj2`, bigmems, and memoization;
- ACL2 arithmetic-3/5 and meta arithmetic;
- `std` lists, strings, IO, utilities, bitsets, alists, and testing;
- clause processors, rulesets, supporters, raw includes, and XDOC;
- RTL floating-point books, executable loaders, Codewalker, and Kestrel
  arithmetic.

Link success must report a **closed transitive graph**, content hashes, named
directory map, cycle/idempotence handling, local visibility, trust tags, and
every unresolved/dynamic include. Counting a source file as loaded while one
of these dependencies is skipped is a failed gate.

## Staged gates

Each gate has two scores: `events normalized / events expected` and
`theorems transported / logical theorems emitted`. “Accepted” means a stored,
hypothesis-free kernel theorem; definitions and nonlogical events have their
own tallies.

### X0 — Reproducible corpus manifest

- Pin ACL2/community-book commit and configured roots.
- Parse all 190 x86isa Lisp sources with zero recovery/skips.
- Emit reader-feature and static include inventories.
- Run an instrumented ACL2 normalization pass that records every expanded
  event, local/global scope, package, formula, rule class, generated-event
  parent, and dependency hash.
- Diff the normalized manifest deterministically in CI; never execute
  expansion output as trusted Rust.

Gate: 190/190 source parse; 861/861 lexical edges classified; normalized
manifest reproducible across two clean runs.

### X1 — Closed linking and ACL2 world mechanics

- Finish package-aware symbols, portcullis order, named directories, extension
  probing, local pass semantics, include idempotence, theory state, tables,
  constants, and event containers.
- Separate logical, proof-control, execution, and documentation outcomes.
- Load the transitive closure of `utils/` and `portcullis/` before the machine.

Gate: `portcullis/utils.lisp` and `utils/structures.lisp` reach zero unknown or
skipped logical events; link report is transitively closed.

### X2 — Macro/event normalization

- Implement enough ACL2 evaluation to expand ordinary `defmacro`, `make-event`,
  `make-event` state queries, `std::define`, FTY, `defbitstruct`,
  `defrstobj2`, instruction generators, and sharp-dot constants.
- Prefer an external ACL2 normalizer first, captured as an untrusted,
  hash-pinned event stream; replace pieces in-process only when useful.
- Preserve expansion provenance so a failure names the source macro and
  generated event.

Gate: Covalence’s normalized manifest matches ACL2’s for
`machine/state.lisp`, one scalar instruction book, and one generated SIMD
instruction family.

### X3 — Definitional universe needed by x86

- Complete measured and mutual recursion, `defines`, `defun-nx`, `defpun`,
  `mbe` logical branches, multiple values, rationals/complex rationals, bit
  primitives, arrays/records, and abstract/nested stobj logical models.
- Prove conservative admission for generated record/stobj APIs; do not add
  accessors as axioms.
- Support `encapsulate`, `defchoose`/`defun-sk`, and functional instantiation.

Gate: every definition in `machine/state.lisp` and
`machine/decoding-and-spec-utils.lisp` is conservatively admitted, and all
generated state read/write laws transport.

### X4 — Core ACL2 proof reconstruction

- Make the existing premise builder cover simplification, conditional
  rewriting, induction schemes, executable-counterpart normalization,
  forward chaining, type prescriptions, congruence, forced hypotheses,
  linear arithmetic, and theory/ruleset control.
- Reconstruct proofs from rune traces/event summaries, with deterministic
  failure diagnostics and proof budgets.
- Keep rule classes proof-control-only: each theorem is proved before its
  rules are installed.

Gate: all logical theorems in `utils/`, then a leaf instruction spec, transport
with no assumptions. Track proof time and certificate size per theorem.

### X5 — Bitvector and arithmetic certificate processors

- Add kernel-checked certificates for bit blasting, normalization of
  `loghead`/`logtail`/`logext`, signed/unsigned bounds, and GL/SAT results.
- Formalize/check each clause-processor transformation; SAT can supply DRAT/
  LRAT-style evidence but cannot be trusted.
- Add nonlinear arithmetic and RTL rational/floating-point support where the
  dependency closure demands it.

Gate: all `defthm-using-gl`/`def-gl-thm` events in a selected instruction
family transport, including negative tests with corrupted certificates.

### X6 — Executable x86 machine

- Close the whole `machine/x86.lisp` include DAG and instruction dispatch.
- Prove the logical definitions independently of raw Lisp, attachments, and
  trust-tagged execution accelerators.
- Expose execution only as an optimization validated against the logical
  model; never let `include-raw`, `defattach`, or host IO enter theorem trust.

Gate: load a concrete byte sequence, execute one and then many instructions,
and prove the resulting state equation through the logical x86 model.

### X7 — Program proofs

Progress through proof books by dependency/feature:

1. factorial/pow-of-two/popcount leaf examples;
2. application-view memory utilities and Codewalker examples;
3. system-view paging and marking/non-marking views;
4. dataCopy/zeroCopy/wordCount and loader-backed examples;
5. the complete `proofs/top.lisp` closure.

Gate at each rung: normalized-event parity with ACL2, 100% logical theorem
transport, zero admitted formulas, zero unresolved logical dependencies.

### X8 — Full x86 development support

- `top.lisp`, `proofs/top.lisp`, tools, virtualization, and relevant Linux
  books load together in a persistent content-addressed world.
- Incremental edits invalidate exactly the dependent book certificates.
- Diagnostics preserve source/generated-event provenance and ACL2 package
  names.
- Performance is practical for development: cache normalized worlds and
  theorem certificates, measure scaling, and prevent superlinear relinking.

Final gate: a clean import and an incremental edit/certify cycle both complete
with 100% logical-theorem transport and an unchanged kernel/TCB closure.

## Immediate work order

The live top-level inventory gate currently sees 11,651 classified rows:
3,852 logical theorems, 2,590 logical definitions, 2,459 proof-control rows,
612 execution/documentation rows, 1,802 read-time-world rows, and 336
unresolved logical dependencies. These are importer rows, not yet
ACL2-normalized event parity, and therefore are a progress denominator rather
than an acceptance claim.

1. Preserve the completed stack-safe finalized opcode-map path and extend the
   same flat-list discipline to newly exposed dispatch generators.
2. Close the remaining generated-event primitives (`defaggregate` string
   construction, `defenum` mode queries, the catalogue documentation binder,
   paging `loop$` scope, and explicitly modelled host-file/platform queries).
   Keep failed ACL2 `raise` calls as failures.
3. Complete S7 measured recursion in proof order. W0/W1 represent guarded
   measured call sites, while W2/W3 validate exact body closure obligations and
   use full-ε₀ well-founded induction to prove graph totality and determinacy.
   Next compile real ACL2 ruler/body syntax into those obligations, then derive
   W4--W6 choice, uniqueness, and defining equations. No recursive admission is
   exposed before those gates.
4. Turn the current parser/linker inventory into the external, hash-pinned X0
   ACL2-normalized event manifest. Use it to expose events hidden behind FTY,
   `defrstobj2`, instruction macros, and state-querying `make-event`.
5. Extend the S6 theorem path from structural induction into theory-aware
   rewriting, executable-counterpart normalization, linear arithmetic, and
   mutual/measured induction. Report transported, admitted, skipped, and
   rejected theorems separately.
6. Model the generated x86 state conservatively, then implement bitvector
   primitives and a checked GL/SAT certificate path in parallel.
7. Maintain a dashboard by normalized event kind and rejection reason. The
   primary number is never source files loaded; it is
   `hypothesis-free kernel theorems / emitted logical theorems`.

## TCB and dependency policy

No x86 feature justifies widening the trusted kernel or admitting an ACL2
formula. New normalizers, ACL2 subprocesses, macro evaluators, SAT/SMT/GL
engines, raw Lisp, and execution attachments remain outside the TCB. Only
small proof/certificate checkers backed by proved soundness theorems may
convert their output into Covalence theorems. Any dependency or TCB closure
change is a separately reviewed gate with generated dependency-delta review.
