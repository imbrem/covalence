# EG5 preflight — literal-leaf deletion plan

Readiness analysis for the irreversible EG5 stage: deleting
`TermKind::{Nat, Int, SmallInt, Blob, Bool}` from `crates/kernel/hol/core`.
Scope from [`literal-endgame-design.md`](./literal-endgame-design.md) §4 +
[`../tcb/tcb-holomega-roadmap.md`](../tcb/tcb-holomega-roadmap.md) Front A.

**Status: UNBLOCKED-WITH-DECISIONS; the deletion itself is NOT executed.** EG3a/
EG3b/A3 prep is landed; the S1 bytes swap was attempted and honest-stopped (below).

## Maintainer decisions (the unblock)

Two decisions resolve the former blockers:

1. **Nat's structural target is a *binary* (log-sized) encoding, not a unary
   `zero`/`succ` tower.** Dissolves the O(value) perf wall — `0xD800` lowers to a
   ~16-deep binary term, not a 55k-node succ-tower.
   `init/src/init/nat_binary.rs` already carries the `double n = 2n` / `succ` binary
   normal form with surjectivity proved; that is the intended `ToHolNat` structural
   unfolding target.
2. **`SmallInt` becomes another `toHOL` *leaf*** — a `ToHolSmallInt` op over
   `Val<SmallIntLiteral>` (like `ToHolNat`/`ToHolInt`), with **no structural
   unfolding rule**. No structural partner ⇒ no exclusivity-guard pairing ⇒ deletable
   as a plain `toHOL` denotation. f32/f64 store as SmallInt bit-patterns (`ToHolF32`/
   `F64` leaf ops already exist), so they ride along. `SmallInt` is barely used, low
   churn. This decouples the **float-lander gap** from the one-way door: unlanded
   float facts keep their leaf denotation, they are not stranded.

So the guard-pairing + structural-unfolding story applies to **nat, int, bytes
only** (the three families carrying both a `*Val` reify rule and a future structural
`*Mk`/`Zero`/`Succ`/`Nil`/`Cons` rule); smallint/float stay leaf-only.

## The deletion surface (shape, not exhaustive site list)

- **Kernel-internal — dies by deletion (compile-enforced):** the 5 enum variants +
  their constructors (`Term::{blob, nat_lit, int_lit, small_int}` + `u8..s64`
  wrappers); the leaf arms in hash/Debug/wf/type_of; ~10 no-op leaf match blocks in
  `subst.rs`. `truth()`/`falsity()`/`as_bool` **repoint in place** to the `tru`/`fal`
  specs (EG3b) — API-preserving. `SmallIntLiteral`/`IntTag` survive as `Lit::Small`
  currency (native value, no term leaf) — must move out of the `TermKind` orbit.
- **The `Lit` facade** (`core/src/thm/lit.rs` — the single build/recognize
  chokepoint) flips its `to_term`/`from_term`/`hol_type` targets; consumers never
  move (by design). `Nat`→binary structural, `Int`→canonical `mkInt` pair,
  `Bytes`→`bytesNil`/`bytesConsNat` chain, `Bool`→`tru`/`fal`, `Small`→a
  `ToHolSmallInt` leaf.
- **Eval-tier atomic swap:** OUT of `eval_rules!` (same-family commit) —
  `ToHolNatVal`, `ToHolIntVal`, `ToHolBytesVal`. `ToHolF32Val`/`ToHolF64Val` **stay**
  (reify to the `ToHolSmallInt` leaf, unguarded). IN — `ToHolNatZero`/`ToHolNatSucc`
  (over the **binary** form), `ToHolBytesNil`/`ToHolBytesCons`, `ToHolIntMk`, the
  `ToHolSmallInt` leaf. `ZeroLitCert` dies with the `Nat` literal (object-level `⊢
  zero=⌜0⌝`, not part of the base-tier contradiction pair). Family cert rules stay,
  conclusions flip implicitly via `Lit::to_term`.
- **Core rules:** `NatInduct` base check `nat_lit(0)`→`zero()`; `ZeroNeSucc` drops the
  literal arm (already dual-accepting since A3). `core-manifest.txt` unchanged (names
  only, still 25).
- **Downstream (untrusted):** ~220 direct constructor sites across `covalence-init`
  (60 files) + traits/alethe/haskell/tests; ~115 `nat_induct`/`zero_eq_succ` refs
  whose base-premise shape flips `⌜0⌝`→`zero`; content-address-changing hash tag arms
  (tags documented unstable, no persisted-compat).

## Atomic-swap execution plan

**Pre-commits (additive, reversible):**

- **P1 — guard extension (DONE).** `tohol_unfolding_rules_are_exclusive` originally
  covered only the nat pair. The identical base-tier `⊢False` class exists per family
  (`ToHolIntVal + ToHolIntMk ⇒ Val(int_lit) = Val(mkInt-term)` via sym+trans — false
  definitional Eq). Extended to a per-family table for **nat/int/bytes**; **not**
  smallint/float (leaf-only) or the object-level `ZeroLitCert`. Adding a structural
  `*Mk` rule for a family REQUIRES dropping that family's `*Val` in the same commit —
  the guard fires at `cargo test` otherwise.
- **P2 — facade sweep (in progress).** Migrate every downstream direct constructor/
  recognizer onto the eval `mk_*`/`as_*` facade so post-sweep `grep Term::nat_lit`
  outside core + `thm/lit.rs` is zero. Mechanical, testable, reversible; shrinks the
  swap commits to the facade flip. (init literal-ctors already 72→6.)
- **P3 — wasm32 CI job** (below) established BEFORE any swap so swap commits are
  wasm32-gated.

**The swap — per-family staging is legal** (each family's transitional/structural
rules are exclusive *within* the family; families don't interact). Golden
`eval-manifest.txt` regenerates at each swap (net 17 → ~16); `core-manifest.txt`
untouched; `tcb-audit.json` at S5. The exclusivity guard is the atomicity tripwire.

- **S1 — bytes swap.** *Attempted 2026-07-11 → HONEST-STOP, nothing landed.* The
  preflight's "clean low-blast-radius single stage" was wrong, for three compounding
  reasons:
  1. **The guard forbids any additive intermediate.** Admitting
     `ToHolBytesNil`/`Cons` while `ToHolBytesVal` still lives trips the guard
     (correct). All-or-nothing within the family.
  2. **The concrete cert family is coupled to the blob literal.** `bytes_cat/len`
     symbolic landers mint concrete `BytesCert` (LHS from `Lit::Bytes::to_term()`, RHS
     a raw `Term::blob`), then build the `transport_symbolic` reification `⊢ symbolicE
     = Val(blob)` by reifying each `ToHolBytes(Val bs)` **through `ToHolBytesVal`**.
     With `*Val` gone, `ToHolBytes(Val bs)` unfolds (Nil/Cons) to a cons-chain, NOT
     `Val(blob)`, so the `eq_mp` match no longer closes. Fixing it needs EITHER **(a)**
     flip the WHOLE bytes cert family to a structural RHS (`bytes_cert`/`lit_eq`/
     `coercion` + docstrings + `Lit::Bytes::to_term/from_term` + ~17 downstream sites),
     carrying a NEW bytes-structural-injectivity audit obligation (`⟨struct a⟩=⟨struct
     b⟩ ⇔ a=b`; sound for `abs/nil/cons[u8]` iff `abs` is injective on the list image
     and u8 elements are canonical), OR **(b)** a new admitted structural↔blob bridge
     rule — a dead end (not derivable from existing machinery; merely relocates the
     `*Val` denotation, needing its own exclusivity reasoning).
  3. **The genuine structural target needs a bytes structural theory that does not
     exist.** `bytesConsNat`/`bytesAt` are declaration-only (no `nat ↔ u8`); the honest
     denotation is `abs_bytes(nil[u8])` / `abs_bytes(cons[u8] ⟨b:u8⟩ (rep_bytes …))`
     over real `list u8` constructors — but the `Blob ↔ list u8` bridge + list-recursion
     lemmas are the exact gap flagged in `eval/SKELETONS.md`. A substantial init-level
     proof development, not a single swap.

  **Next attempt: path 2(a)** (flip the whole bytes cert family to structural, with
  the injectivity audit paragraph) — budget it as a real multi-file core+eval+init
  stage. Path 2(b) is a dead end. **Int (S2) has the identical structure and the same
  2(a) shape, so solving bytes designs the int template.**
- **S2 — int swap.** `ToHolIntMk` in, `ToHolIntVal` out, `Lit::Int` flips to the
  **canonical** pair form, int landers rewritten. Carries the int-disequality audit
  note in `LitEqCert`'s docstring (see risks).
- **S3 — smallint/float swap.** UNBLOCKED via decision 2. `SmallInt`/f32/f64 become
  plain `toHOL` **leaves** — no structural rule, no guard pairing. `Lit::Small` flips
  to a `ToHolSmallInt` op; `ToHolF32Val`/`F64Val` keep reifying to the bit-pattern
  leaf. Does NOT touch the exclusivity guard; writable today.
- **S4 — nat + bool swap (the big one).** `ToHolNatZero`/`ToHolNatSucc` in — over the
  **binary** `nat_binary` form; `ToHolNatVal` out (guard forces same commit);
  `Lit::{Nat, Bool}` flip; `truth()`/`falsity()`/`as_bool` repoint to `tru`/`fal`;
  `NatInduct`/`ZeroNeSucc` to `zero`-form; EG3b bridge deleted; init induction/
  normal-form consumers repaired. Binary encoding keeps moderate-magnitude numeral
  proofs log-sized (no 55k-node towers). Where the init semantic churn concentrates.
- **S5 — the deletion commit (irreversible).** Delete the 5 variants + constructors +
  all leaf arms + `ZeroLitCert` + `kind_name`/`hash`/`sexp` literal arms; relocate
  `SmallIntLiteral` to the `Lit` orbit; regen `tcb-audit.json` (`termKindVariants`
  →14) + `bun run deps`. rustc enumerates every residual site.
- **S6 — Cluster A (separate follow-on).** Empty `core/src/defs/` of the D3 residue
  type chain (`bits`/`int`/`bytes`/`unit` + carrier closure) into eval; the
  `exists`/`and` connective residue stays (L4-gated, `forall_spec`/`and_spec` pointer
  identity).

## wasm32 32/64-bit divergence audit

Precedent: `nat.shr` keyed off `usize` — a **wasm32-only `⊢False`** invisible to
green 64-bit CI. EG5 is the only Front-A stage the roadmap marks
wasm32-adversarial-audit-gated.

1. **Static sweep (before S1):** audit every `usize`/narrowing cast on the
   swap-touched trust surface — `base/trusted` CanonRule gates, `covalence-pure-eval`
   rules (`shl`/`shr`/`pow` refusal guards, `bytes` at/slice indices), `eval/certs.rs`
   dispatch, and **especially the new structural builders**: the `Nat`→binary and
   `Bytes`→cons-chain loops MUST iterate on the bignum/buffer, never a `usize`-truncated
   count (a truncated count = a wrong term = a false minted equation).
2. **Differential job:** run the `covalence-pure-eval` semantics suite +
   `covalence-hol-eval` cert/structural tests on `wasm32-wasip1-threads` under
   wasmtime; pin boundary KATs straddling 2^31/2^32 bit-for-bit against native.
3. **Adversarial pass (the gate proper):** per family, attempt to mint `⊢False` on
   wasm32 through inputs whose `usize`-narrowed images collide. Multi-agent format
   (green tests don't catch this class).
4. **Gate:** S1–S4 do not merge until the job is green on both targets and the
   static-sweep findings are recorded.

## Risks remaining after unblocking (want maintainer eyes, not blockers)

- **Int disequality under the quotient.** `LitEqCert`'s `F` direction rests on
  "distinct literals denote distinct values"; `mkInt` pair forms are NOT injective
  (`mkInt(1,0) = mkInt(2,1)`). Sound only if `Lit::Int(i).to_term()` emits the
  **canonical** representative and the cert refuses non-canonical operand shapes —
  needs an explicit audit paragraph in the S2 commit.
- The wasm32 class on the new structural builders.
- One-way-ness itself: deleted public ctors + re-addressed content hashes + a manifest
  swap with no reverse migration.

## Bottom line

The mechanical deletion surface is fully enumerated and compile-enforced; core's own
literal coupling is ~10 walker arms, 5 constructors, 2 rule checks (the facade +
EG3b + A3 prep did their job). The swap is per-family stageable with the extended
guard as tripwire. Both former design inputs are decided (`SmallInt`/f32/f64 stay
`toHOL` leaves; nat numerals are binary). The real remaining cost is the per-family
*structural theory + whole-cert-family flip + injectivity audit* (path 2(a)), best
run as a dedicated orchestrated push with the structural theories built first — NOT a
facade flip. Remaining prep (P2 sweep, P3 wasm32 job) is additive.
