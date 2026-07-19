+++
id = "N0045"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:codex"
at = "2026-07-19T00:00:00+01:00"
source = "green-island-program"
agent = "codex"
harness = "codex"
+++

# ACL2 green islands and corpus completion

## Goal and acceptance boundary

A green island is a pinned upstream ACL2 book closure for which Covalence
accounts for every normalized event and turns every exported logical theorem
into a hypothesis-free NativeHol theorem. Parsing, macro expansion, hint
selection, induction discovery, and corpus analysis remain untrusted. They may
propose replay data but cannot produce theorem authority.

An island is complete only when:

1. every logical dependency is present, confined, and content-identified;
2. every normalized event has source and generated-event provenance;
3. every logical definition has conservative checked evidence;
4. every exported theorem is stored as an exact, hypothesis-free NativeHol
   theorem;
5. there are no admitted formulas or unresolved logical dependencies;
6. theorem-neutral documentation, proof controls, and execution attachments
   are explicitly classified;
7. malformed or corrupted replay evidence fails closed; and
8. a downstream book can query and use the imported theorem identities.

Loading files or inventorying theorem forms is not theorem import.

### Dependency interfaces

Small logical books often include large XDOC books solely to attach
documentation. Recursively treating that source as part of the logical
denominator makes a two-theorem fixer book inherit hundreds of unrelated
documentation and macro events. Conversely, silently ignoring an include
would make the completeness claim meaningless.

The first islands therefore have two independently reported boundaries:

- the **logical export boundary** contains the target book, every definition
  and theorem on which its exports depend, and a content-identified interface
  for theorem-neutral includes; and
- the **source closure boundary** recursively accounts for every event in
  every included source book.

A theorem-neutral interface is acceptable only when its classification is
explicit, pinned to the included content, and checked to export no logical
definition or theorem used by the target. It is not a theorem certificate and
does not raise the source-closure score. The initial `nfix`/`ifix` milestone is
complete at the logical export boundary, but is not yet a strict green island;
closing or certifying XDOC remains separately visible work. Later library
islands must replace interfaces with imported library artifacts or full source
closure.

## Completeness levels

Progress is reported monotonically for each pinned closure:

| level | gate |
|---|---|
| L0 Source | target bytes and dependency-interface bytes are present and hashed; reader succeeds |
| L1 World | include closure and normalized event stream are complete |
| L2 Definitions | every logical definition has checked conservative evidence |
| L3 Theorems | every exported theorem is a closed NativeHol theorem |
| L4 Library | theorem identities, statements, dependencies, and provenance are queryable |
| L5 Reuse | a downstream book checks using the imported library |

The dashboard reports exact numerators and denominators at every level. A book
does not inherit a higher level merely because a dependency reached it.

The implementation additionally distinguishes `SourceClosureStatus::Recursive`
from `Interfaced { verified }`. `is_logical_green_island` permits only verified
theorem-neutral interfaces; `is_green_island` remains the stronger recursively
processed source-closure claim.

## Island sequence

1. `std/basic/nfix` and `std/basic/ifix`: four fixing theorems. This forces
   checked open implication and predicate transport and introduces definitions
   used broadly in x86 books.
2. `std/lists/acl2-count`: five theorems over ACL2's default termination
   measure. This connects the existing ordinal/well-foundedness foundation to
   ordinary book replay.
3. `std/lists/append` and its closure: the first recognizable library island,
   exercising local lemmas, conditional rewriting, induction, congruences,
   tables, and theory control.
4. Signed/unsigned-byte and bitvector foundations selected from the x86
   dependency closure.
5. One leaf x86 instruction family, then one concrete state transition.

The full x86 top manifest remains a broad compatibility and performance
benchmark in parallel; its inventory count is never substituted for an L3
score.

### Current measured frontier

- `std/basic/nfix` and `std/basic/ifix` are 4/4 logical-green against exact
  target hashes and the exact
  `xdoc/constructors.lisp` SHA-256
  `c58a403e94ab4c86c0dfa0da2477b29189cfc49bb3b1a0ca2a6949a89a38b793`.
  Their report records the closed `TransparentDefsection` capability and
  remains non-source-green.
- `std/lists/acl2-count.lisp` is the first strict source-green candidate:
  revision `2dbf2b63`, SHA-256
  `952499bebe748a4411377644ea6b47208a38f496fd908812099e49af35df8ab1`,
  six source events, no includes, and five theorem exports. Its checked
  recursive definition is now in the production ACL2 environment. The
  measured theorem baseline is 0/5; after surface expansion of `and`, `not`,
  `>`, `<=`, and `>=`, the remaining blockers are checked inequality/measure
  reasoning rather than reader or linker compatibility.

## First island design: IFIX/NFIX

The upstream logical definitions are modeled conservatively:

```lisp
(ifix x) = (if (integerp x) x 0)
(nfix x) = (if (natp x) x 0)
```

Their deep model constants are definitions, not axioms. Their user rows are
installed only after the existing row checker re-pins the encoded bodies to
the model equations. The two guarded equality theorems use checked implication
transport. The two predicate-totality theorems require an open holds transport
that validates the projected derivation's exact shape and closes all object
variables.

### Gate

- Official sources at community-books revision
  `2dbf2b63bb9a27070c8573d72c16c04a4809c8d1` load verbatim:
  `nfix.lisp` SHA-256
  `79e853d1e85aa8539a57b50a50586bca53d094c73f40cfae3450d11427524310`
  and `ifix.lisp` SHA-256
  `f9614f59dfd1857b45f1d5739bd81df56f5bd0f1b2ce03937379daed2a69fb49`.
- `nfix-when-natp`, `natp-of-nfix`, `ifix-when-integerp`, and
  `integerp-of-ifix` are 4/4 closed NativeHol theorems.
- Exact statements and empty hypothesis sets are checked independently.
- False unguarded fixes, malformed projections, missing/duplicate bindings,
  and mismatched definitional rows fail.
- No new axioms, oracle hooks, unsafe code, mint sites, dependencies, or TCB
  leaves.

### Risks

- Adding user rows can shift clause indexes used by proof tests. Prefer a
  named prelude extension whose exact row order is tested.
- A generic predicate transport must reject equality/implication projections
  rather than silently reinterpret them.
- The sparse corpus may omit XDOC dependencies. Completeness reports must
  distinguish an absent theorem-neutral dependency from a closed upstream
  source closure; the strict gate uses a complete pinned closure.

### Out of scope

- General rewriting or ACL2 hint fidelity.
- Measured or mutual recursive admission.
- Persistence/content addressing beyond exposing the report fields needed by
  a later library store.
- Claiming completeness for `std/basic`, community-books, or x86 from this
  four-theorem island.

## Road to full ACL2

Corpus completion is tracked as a matrix, not a single percentage:

- reader feature coverage;
- dependency/link closure;
- normalized event parity against ACL2;
- ordered-world event coverage by exact head;
- conservative definition coverage by admission principle;
- closed theorem coverage by proof mechanism;
- unsupported rune, clause-processor, and hint families;
- proof time, certificate size, and cache behavior;
- negative/corruption coverage; and
- TCB/dependency deltas.

The executable tracker makes this matrix repeatable against any pinned
checkout:

```sh
cargo run -p covalence-lisp --features hol --example acl2_progress -- \
  /path/to/community-books REVISION BOOK...

# Fast event/world compatibility census, without attempting proofs:
cargo run -p covalence-lisp --features hol --example acl2_progress -- \
  --inventory /path/to/community-books REVISION BOOK...
```

Its deterministic `acl2-progress-v1` TSV distinguishes target from recursive
closure counts, replay from inventory mode, logical-green from strict
source-green, theorem-neutral interfaces, load failures, and sorted blockers.
The output is untrusted progress evidence: theorem numerators originate only
from `BookReport` events that already crossed checked replay.

The authoritative final gate is: every selected ACL2 distribution and
community book has deterministic normalized-event parity, every logical
definition is conservative, every exported theorem has a closed checked
NativeHol theorem, downstream reuse succeeds, and the TCB contains no ACL2
parser, search procedure, normalizer, external prover, or raw execution path.
