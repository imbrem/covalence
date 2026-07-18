+++
id = "N0027"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:claude"
at = "2026-07-14T21:26:19+01:00"
source = "legacy"
agent = "claude"
harness = "claude"
+++

# Bitvector (QF_BV) verification — roadmap

*Direction, 2026-07-14. Long-term vision: kernel-checked bitvector reasoning
(the substrate for WASM verification — `i32`/`i64` **are** bitvectors). The
through-line: **BV bitblasts to SAT**, so the kernel-checked SAT replay
(`crates/kernel/sat`, sequent backend) is the BV foundation. Grounded in the
`bitvector-roadmap` research workflow.*

## The route decision: build our own bitblaster

Two candidate pipelines; we pick the second.

- **cvc5 Alethe BV** — rejected as primary. cvc5 emits a *monolithic* Alethe
  proof for QF_BV (no embedded DRAT/LRAT SAT certificate): each BV op becomes a
  `bv_bitblast_step_*` rule, the boolean refutation is unrolled into Alethe
  `resolution`, and small problems carry ~33 boolean-circuit `hole` rewrites the
  current `HolAletheBridge` can't discharge. Consuming it means re-deriving the
  whole BV rule family *and* a boolean-circuit normaliser. No SAT certificate to
  reuse.
- **Our own bitblast → SAT → sequent replay → lift** — chosen. Bitblast the BV
  goal to CNF ourselves (recording the `boolean-var ↔ (BV term, bit)` map), run
  CaDiCaL `--plain` → LRAT, replay the bit-level `⊢ ⊥` through the **existing
  `RupReplay` + sequent backend, 100% unchanged**, then lift to a BV-level
  theorem via proved per-op circuit equivalences. This reuses the SAT scale work
  directly and is why hardening SAT matters.

## What already exists (the substrate)

- **Closed-literal BV discharger — complete.** `FixedWidthCert`
  (`eval/src/rules.rs:376` → `certs.rs:529` → `base/eval/src/fixed.rs`) reduces
  every ground `uN`/`sN` op to a kernel-checked `⊢ op ⌜a⌝ ⌜b⌝ = ⌜r⌝`: 8 widths
  (u8/16/32/64, s8/16/32/64), full WASM op set (add/sub/mul/div/rem, and/or/xor/
  not/neg, shl/shr, lt/le/gt/ge, zext/sext, to/from Nat/Int), exact QF_BV
  constant-folding semantics (wrapping mod 2ⁿ). This is the closed-BV oracle.
- **BV type scaffolding.** `bits := list bool`, `uN := {v:bits | len v = N}`,
  `sN := uN` (`core/src/defs/bits.rs`), widths 1..512. Enough to *state* `uN`
  goals; a `list bool ≅ nat` iso is available for the arithmetic circuits.
- **The SAT pipeline** — `RupReplay` + the (landing) sequent backend; the
  `SatProblem`/`ClauseBackend` three-plug-point API a `BvBitblastBackend` slots
  into.

Missing: proved *laws* over `uN` ops; a `bit : uN → nat → bool` extraction op;
the bit-blast circuit equivalences; the bit-level→BV-level lift.

## Staged plan

- **S0 — closed-literal floor (anchor).** `⊢ bvadd/bvult ⌜a⌝ ⌜b⌝` for u8/u32/u64
  via `FixedWidthCert`, as a test. No SAT. Pins `uN` + the eval certs as the
  ground truth the lift must agree with. (Fully-closed facts are *not* a pipeline
  milestone — they skip SAT.)
- **S1 — bit-extraction op.** `bit : uN → nat → bool` (index the underlying
  `bits`) + defining equations + a closed-instance eval cert (the `bytes.at`
  pattern). The vocabulary the whole lift is stated over.
- **S2 — `BvBitblastBackend` + first circuit equivalence (THE first milestone).**
  A `SatProblem`/`ClauseBackend` sibling that emits Tseitin CNF for the
  *combinational* ops (`bvxor`/`bvand`/`bvor`/`bvnot` — one clause set per bit, no
  carry) and records `Var(i) → (BV term, bit j)`. Prove the trivial per-bit
  equivalences (`bit(bvxor a b, j) = bit(a,j) XOR bit(b,j)`). **First milestone:**
  a 4-bit UNSAT gate refutation (e.g. `x = a⊕b ∧ x ∧ ¬a ∧ ¬b`) → CaDiCaL `--plain`
  LRAT → `RupReplay` → `{clauses} ⊢ ⊥` → discharge each clause from its
  equivalence → reductio to a BV-level `⊢ G`. Smallest thing exercising every
  seam (bitblast → real SAT → replay → lift) while deferring the hard proof.
- **S3 — ripple-carry `bvadd` + `bvult`/`bveq`.** `bit(bvadd a b, j)` = full-adder
  carry recurrence; the compare circuits. The bulk of the proof effort (leans on
  the `list bool ≅ nat` iso).
- **S4 — swappable circuit discharger.** Factor the lift's oracle behind the
  `order.rs` `Discharger` pattern, so it runs eval-backed *and* eval-TCB-free
  (induction) alike.
- **S5 — scale + WASM capstone.** Cache/solver-fallback front; widths to u32/u64;
  `bvmul`/`bvudiv`/`concat`/`extract`; and a **WASM `i32`/`i64` arithmetic
  property** proved kernel-checked end to end — the capstone.

## The one genuinely-hard piece

The **circuit equivalences + the lift**: each BV op's Tseitin clauses must be
proved *equivalent* to the op's bit-level definition (combinational ones are
trivial; `bvadd`'s carry chain is the real work, S3), and the bit-level `⊢ ⊥`
must lift to a BV-level `⊢ G` by discharging every emitted clause from its
equivalence + a reductio. Everything else reuses existing machinery.
