# AGENTS.md — Implementation Context

Context for AI coding agents working on this project. Read fully before writing code.
The companion [`ARCHITECTURE.md`](./ARCHITECTURE.md) has the full rationale; this
file is the operational distillation: what to build, what is sacred, and what
*looks* like a bug but isn't. For build commands, crate layout, and conventions
see [`CLAUDE.md`](./CLAUDE.md).

---

## What this is, in one breath

A theorem prover **and** version-control system on a shared content-addressed substrate.
The trusted core is a tiny LCF kernel for a HOL variant. Everything powerful (oracles,
formats, foreign systems, fast storage) lives **outside** the core and is sound only
because the core can re-check it. The store mounts as a real Unix filesystem.

The recurring pattern, which you will implement **seven+ times**: **simple trusted core +
arbitrarily clever untrusted layer + soundness by re-checkability against the core.** When
you find yourself adding cleverness to a trusted component, stop — the cleverness belongs
outside, behind a checkable certificate.

---

## The single most important rule

> **Well-formedness is PURELY SYNTACTIC. It must never depend on what is provable.**

A type/term is well-formed by structural recursion that inspects *no* assumption set and
*no* provability. This is *why* the empty context is not privileged and *why* there is no
axiom/oracle/assumption distinction. If you are writing a well-formedness or kernel-rule
check and you reach for "is this provable in the empty context," you have introduced a
soundness hole — rework it (see the disjunct trick below).

---

## TCB boundary — memorize this

**INSIDE the TCB (must be tiny, simple, audited; bugs = false facts):**
- The LCF kernel: term/type representation (arenas), the inference rules, the union-find
  over arena indices, freeze/hash.
- The store's **read/write primitive** and its **Merkle-witness verifier** (a false read
  must *fail to hash up*, not merely be unlikely).
- The **merge certificate checker** (simple: every input row appears in result or in a
  marked conflict; every result row comes from an input; roots hash).
- The **format-validity meaning-axiom shape** and **keyed-identity construction**.

**OUTSIDE the TCB (may be arbitrarily clever, may even be wrong — caught by re-check):**
- All decision procedures (sound, not complete; may be nondeterministic).
- All oracles (WASM executor, other executors, signatures, ZKPs, content lookup).
- The merge *algorithm* (only its certificate is checked).
- SQLite / Parquet / DuckDB overlays (caches & export; re-checkable vs the prolly tree).
- The commutative-diagram API, the surface compiler, all elaboration & bookkeeping.
- The namespace/mount machinery (it's just conservative Horn-clause assertion).

If a task would grow the INSIDE list, flag it and propose a certificate-checked OUTSIDE
design instead.

---

## Kernel primitives (the trusted list — keep it ~8–10)

**Structural primitives (lock these):**
- `pair` / `FST` / `SND` — three flat slot-native equations.
- `unit` — terminal object, record tail.
- `DOWHILE` — Elgot iteration; strictly more expressive than `ITER`.
- carriers `bits` / `blob` — machine-backed; `bits` handles ALL FFI integer traffic.

**Derived (NOT primitive — native `(tag,a,b)` representation, no speed loss):**
- `sum` / `INL` / `INR` / `CASE` (tagged pair over `bool`); `option` (`unit + A`);
  `sexpr` / `CONS` / `CAR` / `CDR` (`μX. atom + X×X`); `ITER` (from `DOWHILE` + counter);
  `num` / `ZERO` / `SUCC` (Peano — **derived**, for reasoning only).

> **Do NOT make `num` primitive.** Unary `SUCC` would make a 64-bit count 2⁶⁴ nested
> cells. FFI integers are a `bits` concern. (Confirm-and-lock decision.)

Promote to primitive ONLY if (a) underivable, or (b) the representation is unachievable by
derivation. Primitive status buys nothing but speed-you-already-have and adds trusted
axioms.

---

## Content-addressing & identity conventions

- **Type-operator identity** = `(normalized P, declared tyvar order)` — NOT the
  user-facing name. A name is a namespace binding pointing at the address. Same `P`,
  different declared order ⇒ different hash (correct).
- **Tyvar order** is **user-declared at def-time** for interfaces (type operators,
  polymorphic constants); **canonical** (occurrence-over-normal-form) for internal
  machinery (serialization, auto-gen). Store each slot as `(tyvar, kind)`, `kind` default
  `*` (forward-compat for HOL-Omega without a schema change). Placement: declared params
  first (declared order), canonical-generalized after.
- **Canonical freeze:** same theory ⇒ same hash regardless of derivation order. Thread the
  ONE canonical tyvar ordering uniformly through operator formation, constant polymorphism,
  and serialization — divergence here means the same object hashes differently by path.
- **Typed-value identity** = `BLAKE3_keyed(key = format_id, data = payload)`. Format is the
  KEY, never bytes in the preimage (domain separation, no concatenation ambiguity).
- **Names** = `Name256` = `blob` of length 32, **opaque** (no intrinsic meaning; the
  consuming column/position interprets it). `Name256` is a well-known UUID-format primitive.
- **Format ids** = 256-bit; infinite formats by **nesting** (`keyed(Outer, keyed(Inner,
  payload))`), not by widening. A **domain-split bit** separates assigned/well-known
  (authority-plane) from spec-hash-derived (content-plane) ids.

---

## The disjunct trick (typedef without provability dependence)

Subset types form **unconditionally**. For `subset P`:
1. `abs (rep a) = a` (unconditional)
2. `rep (abs x) = x ↔ (P x ∨ ¬∃y. P y)`  ← disjunct replaces the nonemptiness side-condition

Side-conditions on `P` (all syntactic): **locally closed** (no escaping de Bruijn
indices), **`fv(P) = ∅`** (a free *term* var would make the type context-dependent — the
real hazard), free *type* vars allowed (⇒ polymorphic type operator). `new_specification`:
expose the disjunct, stop discharging. `new_type`/infinity: flat standing assumptions
(they inspect no assumption set, so they're fine).

---

## Naming, mounting, and the filesystem view

- A namespace is a **prefix-indexed relation**. `enter` = curry (fix first column);
  `mount` = extend under a fresh prefix. **Union is the only combinator.**
- **`mount Q at P` ≡ `∀x. Q(x) ⇒ P(x)`** — sound for free because the body is an oracle
  relation (conservative Horn clause; "everything true" is a model). Meaningful only once
  `Q` is grounded. Implement mounts as *exactly* this axiom assertion; no special kernel
  support needed.
- **Two-layer import** = "key K claims kernel V says B": keep the **signature/identity
  fact** (who said it, evidence) SEPARATE from the **translation V→root** (what it means,
  proof). Do not fuse them.
- Backing op for `mount` is SQLite `ATTACH DATABASE ... AS prefix` (cross-DB joins =
  profunctor composition). `SQLITE_MAX_ATTACHED ≈ 125` is the real ceiling — route large
  mount graphs through a virtual table.
- Filesystem projection of `Relation[fn₁,fn₂,fn₃ | A,B,C,D]`:
  - left filenames → directory path; `.self` at the leaf → the table `(A,B,C,D)` (node's
    own data);
  - **symbolic columns → symlinks** (target = address; **dangling is normal**),
    **materialized → files/cells**; `st_mode` is the fact-kind discriminator;
  - `unit` = existence = empty-schema `.self` (≠ empty directory, which has no `.self`).

---

## Profunctor model (why left/right differ)

`R[α,β]` is a profunctor: **left = contravariant (addresses you consume)**, **right =
covariant (references you produce)**.
- **`repr_addr` (key) is universal**; injective only *within scope* (by authority |
  assumption | construction).
- **`repr_val` (faithful content) is optional**, needed only where you *materialize*.
  **Storing facts about symbolic β is the normal case** — most things are never
  materialized.
- **Merkle = iterated profunctor composition**: a level's `repr_val` becomes the next
  level's `repr_addr` (hash feeds navigation); composition is the coend over the shared
  blob. **Composition is address-level; materialization is value-level; independent.**
- **VCS ops = the functorial action**: rename/rebase precompose left; blob re-encode
  postcompose right. A **Git repo is the self-addressing special case** (every left
  `repr_addr` is itself content-addressed).

---

## Storage: the VCS native format

- TCB structures: **Git-like trees** (paths/left columns) + **Dolt-style prolly-tree
  tables** (data/right tuples). Content-defined chunking ⇒ canonical root ⇒
  dedup/diff/merge.
- **Reads carry Merkle witnesses.** **Merges are untrusted + certificate-checked.**
  **Conflicts are preserved-and-marked, never silently shadowed.**
- Overlays (untrusted, re-checkable): **SQLite** = live working set / index; **Parquet +
  DuckDB** = frozen/committed columnar artifacts (the "git object"). *Commit* = freeze
  live table → content-addressed columnar blob; *checkout/mount* = attach it. The
  frozen/live seam IS the commit/checkout seam.

---

## Formats are a plane, not machinery

- `valid(format, data)` is an **oracle relation**; validation is a sound-not-complete
  decision procedure. A format **spec is itself data** under a meta-format; bottoms out in
  one human-inspected **root format**.
- **Validity is keyed**: validity facts are minted by a format-specific validator; the
  keying is the proof the id belongs to that format. Never assert bare `valid(id)` for an
  id whose keying you didn't witness. Keep `id ⇒ payload_hash` (CAS, re-checkable) separate
  from `id ⇒ valid` (oracle fact).
- **Carrier + refinement is the universal "type vs blob" answer**: `blob` is the universal
  carrier; every type is a carrier (tuple) + an optional validity refinement (a format).
  Strong-typed and loose are the *same value* with/without the proof attached; conversion
  is forget (free) / checked-inject — never reserialization.

---

## "Looks like a bug, but is intended" — do NOT "fix" these

- **Dangling symlinks** in the mount: expected. Means "facts-about-β held, content not
  materialized." Not an error.
- **Empty directories vanish on round-trip** (`FS→DB→FS`): intended. A prefix exists iff a
  row exists at/below it. Empty dirs are scratch, not state.
- **`.` and `..` ignored entirely:** POSIX noise; never facts. Real node-fact lives in
  `.self`.
- **"No collisions" returning FALSE for a store with the SHAttered PDFs:** correct —
  honest degradation. The scoped per-repo theorem can still hold; don't paper over it.
- **A merge that refuses to pick a winner and instead records both rows as a conflict:**
  intended. Shadowing one side is the forbidden "namespace global lie."
- **Same `P` with different declared tyvar order producing two different hashes / no
  dedup:** correct — they're genuinely different operators.
- **The kernel "letting" you assert `∀x. Q(x) ⇒ P(x)` for an unknown `Q`:** intended and
  sound (conservative oracle-head Horn clause) — that's how `mount` works.
- **Decision procedures that say "I don't know" / fail rather than deciding:** intended —
  they're sound-not-complete by design.
- **`num` being slow / Peano:** intended; use `bits` for performance-sensitive integers.

---

## Cross-cutting invariants (grep tags)

- `SYNTACTIC-WF` — well-formedness never inspects provability. (§2.1)
- `NO-GLOBAL-LIE` — assert scoped truths about named artifacts, never false universals.
- `HASH-INDEXED` — meaning-axioms keyed to a specific binary by hash, never by name.
- `SAFE-AXIOM` — added implications have own-authority oracle relations as heads only.
- `CANON-FREEZE` — same theory ⇒ same hash; one threaded tyvar order.
- `MIN-KERNEL` — union-find audited or certificate-emitting.
- `EDGE-DIR` — strength/equiconsistency edges carry valid direction in their type.
- `UNION-ONLY` — the only namespace combinator.
- `CONFLICT-PRESERVE` — conflicts marked inconsistent, never shadowed.
- `VERIFIABLE-READ` — store reads carry Merkle witnesses; false reads fail to hash.
- `CERT-MERGE` — merges untrusted, checked by a simple trusted checker.
- `KEYED-VALIDITY` — typed values are keyed-BLAKE3; format absorbed into identity.
- `CARRIER-REFINEMENT` — types = carrier + optional refinement; names are opaque 32 bytes.
- `THREE-CORNERS` — keep computation / proof / evidence distinct; never collapse.

---

## Suggested build order

1. **Substrate:** content-addressed blob store with verifiable (Merkle-witness) reads;
   BLAKE3 incl. keyed mode; `Name256`/`blob` carrier + refinement.
2. **Kernel:** arenas + union-find theorems + freeze/hash; the ~8–10 primitives
   (`pair`/`unit`/`DOWHILE` + `bits`/`blob`); syntactic well-formedness; disjunct-trick
   typedef; tyvar ordering + content-addressed type identity; derive `sum`/`option`/
   `sexpr`/`ITER`/`num`.
3. **Oracles:** opaque-relation discharge; hash-indexed meaning-axioms; WASM executor as
   the first oracle; store/eval reflected in.
4. **Namespace/VCS:** prolly-tree tables + Git-like trees; mount-as-implication; FUSE
   mount with `.self`/symlink/`st_mode` conventions; untrusted SQLite overlay +
   certificate-checked merge.
5. **Format plane:** `valid(format,data)` oracle; keyed-identity minting; well-known format
   registry; root format.
6. **Metalogic layer:** internal logics as HOL theories; embedding/equiconsistency edges;
   the commutative-diagram API; the surface compiler (IR + pluggable backends + commutativity
   checker).
7. **Quantitative + base-shift:** `L_prob` internal logic; functorial base-shift —
   **build the *internal* re-hosting variant first** (embed-and-transport; real base stays
   HOL).

---

## Open decisions an agent should surface rather than silently resolve

- `num` derived / `bits`-for-FFI — **confirm and lock** before finalizing the kernel.
- Cone vs apex-free commutative diagrams (default: cone at a silvered node).
- WasmCert import vs own semantics vs multiple independent semantics (spec-level mirrors).
- Frequentist vs subjective probability nodes (likely both, segregated).
- **Internal vs external base-shift** — resolve before "kernel-2" (default internal).
- Cross-store composition: hard hash-agreement vs translatable `repr_addr ≅` edge.
- Format refutation: monotone-valid-only (default) vs explicit `invalid`/refuter.
- Provenance maps `f`: restricted to a verified-by-consensus class vs arbitrary +
  independent-`f'` re-derivation.

When in doubt: prefer the choice that keeps the TCB smaller and pushes cleverness behind a
checkable certificate.
