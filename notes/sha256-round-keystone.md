# SHA-256 round — the universality keystone

> **STATUS: SKETCH (design probe).** The smallest demo that, if it lands,
> exercises *every* mechanism of the verified-WASM + import-fuel thesis
> end-to-end, on the **cheap** import (set.mm — no Dedukti, no model beyond a
> definitional one). Instantiates [`roadmap.md`](./roadmap.md) Phase C/D and
> realizes the assumption-ledger of [`soundness-audit.md`](./soundness-audit.md)
> §4. Companion to [`VISION.md`](./VISION.md) §3 (oracles as theorems) and
> [`refactor-plan.md`](./refactor-plan.md) (the `covalence-pure` executor base
> this sits on).

---

## 0. The keystone, and what it falsifies

**Prove a WASM implementation of one SHA-256 compression round equal to the
FIPS 180-4 spec, with the hard algebra step discharged by a fact imported from
set.mm.**

One round — not all 64, not the message schedule. Full SHA-256 is *compose the
round 64× then fold the schedule* — scale, not new mechanism. The round is the
slice where every load-bearing claim of the strategy is either demonstrated or
breaks.

If the round lands, these are validated together:

1. **Verified WASM (the engine).** We can state `exec_wasm(B, in) = spec(in)`
   and discharge it — WASM enters as a *theorem*, not a trusted oracle.
2. **Import delivers fuel (the universality bet).** A theorem we did *not*
   prove — a modular-arithmetic ring fact sitting in set.mm — actually closes a
   step we could not otherwise close.
3. **Transport works.** A set.mm statement (over `ℤ mod 2^32`) is re-stated and
   used in the WASM-domain theory (over `u32`) soundly.
4. **The assumption ledger is honest.** The final `Thm` carries visible
   provenance: `Axiom(Con(GT))` (set.mm's base) + `Obs(T_wasm)` (the WASM
   semantics) + the instruction-level denotation facts.

If it *doesn't* land, the keystone tells us *which* of those broke and why —
that is its purpose. §6 is written to make the failure modes legible in
advance.

---

## 1. The spec — one round (FIPS 180-4)

Given the 8-word state `(a,b,c,d,e,f,g,h)` and schedule word `Wₜ`, round
constant `Kₜ` (all `u32`, all arithmetic mod `2^32`):

```
Ch (x,y,z) = (x ∧ y) ⊕ (¬x ∧ z)
Maj(x,y,z) = (x ∧ y) ⊕ (x ∧ z) ⊕ (y ∧ z)
Σ0(x)      = ROTR²(x) ⊕ ROTR¹³(x) ⊕ ROTR²²(x)
Σ1(x)      = ROTR⁶(x) ⊕ ROTR¹¹(x) ⊕ ROTR²⁵(x)

T1 = h + Σ1(e) + Ch(e,f,g) + Kₜ + Wₜ        (mod 2^32)
T2 = Σ0(a) + Maj(a,b,c)                      (mod 2^32)

a' = T1 + T2      e' = d + T1
b' = a            f' = e
c' = b            g' = f
d' = c            h' = g
```

The keystone proof obligation is the **`T1` add-chain** (the densest part and
the natural home of the set.mm fact); `T2`, `Maj`, and the register shuffle are
strictly easier (fewer terms, pure bitwise) and follow the same pattern. Prove
`T1`; the rest is composition.

---

## 2. The WASM implementation

A representative bytecode for `T1` (WAT; `i32.add` wraps at `2^32` by spec, so
it *is* mod-`2^32` addition — `i32.rotr`/`i32.xor`/`i32.and`/`i32.const` are
spec'd bitwise ops):

```wat
;; Σ1(e) = rotr(e,6) ^ rotr(e,11) ^ rotr(e,25)
local.get e   i32.const 6   i32.rotr
local.get e   i32.const 11  i32.rotr   i32.xor
local.get e   i32.const 25  i32.rotr   i32.xor          ;; ⟶ Σ1(e)

;; Ch(e,f,g) = (e & f) ^ (~e & g)
local.get e   local.get f   i32.and
local.get e   i32.const -1  i32.xor  local.get g  i32.and  i32.xor ;; ⟶ Ch

i32.add              ;; Σ1(e) + Ch
local.get h   i32.add
local.get K   i32.add
local.get W   i32.add            ;; ⟶ T1  (left-nested: ((((Σ1+Ch)+h)+K)+W))
```

### §2.1 The prerequisite — `T_wasm` (HONEST: unbuilt, likely the real long pole)

To state *any* of this we need a WASM operational semantics `T_wasm` giving a
denotation to each `i32` word instruction: `⊢ ⟦i32.add⟧ = λa b. (a + b) mod 2^32`,
etc. **This does not exist today.** `covalence-spectec` is an AST + *grammar*
wrapper only (binary format parsing, regular-grammar fragments); there is no
operational-semantics theory, and its own SKELETONS flags the CFG stratum as
the headline gap. The refactor-plan's `covalence-eval` (WASM acceleration) is
Phase E — *after* the product.

So the keystone's *enabling* work is not the import — it is **standing up a
minimal `T_wasm` for the `i32` word-op fragment** (add/sub/mul, and/xor/or,
shl/shr/shr-s, rotl/rotr, const, local get/set). That is a real, bounded
formalization, but it is where the effort and the time actually sit. Treat the
import (§4) as the *cheap* thing we are validating once there is an engine to
burn fuel in. **Confirm what `T_wasm` scaffolding, if any, exists before
estimating; right now assume none.**

The carrier it lands into *does* exist: `u32` is already a `defs` type
(`crates/covalence-core/src/defs/bits.rs`) — a subtype of `bits := list bool`
carved by a length-32 predicate. So `T_wasm`'s target type is in place.

---

## 3. The proof, factored

**Obligation.** `⊢ ∀ (a..h,K,W : u32). exec_wasm(B, (a..h,K,W)) = T1_spec(a..h,K,W)`.

The WASM-symbolic-execution side unfolds `B` under `T_wasm` to a concrete
bitvector expression `E_bytecode`. The obligation reduces to
`⊢ E_bytecode = E_spec`, then closes by **equational rewriting**. That rewrite
factors into three kinds of step:

| Sub-lemma | Discharged by | Mechanism |
|---|---|---|
| each `i32.*` instruction = its bitvector op | `T_wasm` denotation rules | WASM semantics (§2.1) |
| `((((Σ1+Ch)+h)+K)+W) = h + Σ1 + Ch + K + W` (any paren/order) | **set.mm modular-`2^32` ring facts** (assoc + comm of `+ mod 2^32`) | **IMPORT + transport (§4)** |
| `Σ1`, `Ch` unfold to the spec's `⊕/∧/¬/ROTR` form | bit-list lemmas over `u32`, or set.mm `bits` theory | native / second import |
| register shuffle / `T2` | trivial rewrites | kernel tactics |

The **bold row is the keystone of the keystone**: the one step that genuinely
needs an *imported* fact, because associativity/commutativity of mod-`2^32`
addition is exactly the kind of thing you do *not* want to re-prove by hand,
and exactly the kind of thing set.mm has sitting proven.

---

## 4. The import + transport (the fuel)

### The specific imported fact

The WASM chain adds left-to-right; the spec writes `T1` as a flat 5-term sum.
Closing the gap needs **`+ mod 2^32` is associative and commutative** — i.e.
the modular-arithmetic ring/group structure on `ℤ/2^32ℤ`. set.mm proves modular
arithmetic is a commutative ring (its `mod` theory: distributivity over `+`,
`modaddmod`-style reassociation). **Locate the exact `*.mod` ring lemma** during
execution (don't assume the label); the load-bearing claim is only that *such*
facts exist there, which they do.

### Transport: the definitional-tier case (why set.mm is the right validator)

set.mm states the fact over **integers mod `2^32`**; the WASM-domain theory
states it over **`u32 = bits` of length 32**. These are not syntactically the
same carrier, so transport is a real step — but the model is *definitional*: the
standard **bits ↔ integer-value correspondence** (`val(bs) = Σ 2ⁱ·bsᵢ mod 2^32`)
is a bijection, and set.mm *also* has bit machinery (`df-bits` et al.) on its
side. So:

- **Tier 3 (faithful transport)** is *cheap here*: prove `val : u32 ↔ ℤ/2^32ℤ`
  is a ring isomorphism (a bounded theorem over the 32-bit list), then every
  set.mm ring fact transports through it. One bridge theorem; many facts ride.
- Contrast with the **future CIC/HOL** import ([`Dedukti` framing],
  [roadmap §Phase B/D]): there the model is `CIC ↪ GT` (universes-as-Grothendieck-universes),
  a real relative-consistency proof — *not* definitional. set.mm is the cheap
  validator precisely because its carrier aligns with `u32` by a bijection.

### The three tiers, mapped onto this concrete fact

1. **Assume.** Take "mod-`2^32` `+` is assoc/comm" as a scoped `Postulate`,
   justified by `Con(GT)`. Cheapest; no proof object. Enough to *close the
   round* on day one.
2. **Re-check.** set.mm *has* the proof term; `metamath::verify_all` already
   checks all of set.mm in ~1 min. `mm_import::import_theorems` /
   `mm_replay::replay_prop` construct `⊢ Derivable ⌜S⌝` from a verified
   assertion. Lift that to the ring fact (generalising beyond prop is the
   schema-database replay — roadmap Phase B's follow-on).
3. **Faithful transport.** Prove `val` is a ring iso; the set.mm ring lemma
   becomes a first-class `u32` theorem. Strongest; the bridge is bounded.

### The assumption ledger

The final `Thm` carries: `Axiom(Con(GT))` (whatever set.mm fact we leaned on,
at tier 1/2) **+** `Obs(T_wasm)` (the WASM semantics — an executor assumption,
the one entry-per-executor trust of VISION §3) **+** the `T_wasm` instruction
denotations. A consumer who distrusts `T_wasm` sees it in the ledger and gets
nothing; one who accepts it gets a proven round. This is §4 of
[`soundness-audit.md`](./soundness-audit.md) made operational — and it is also
what makes the *import* honest: the set.mm dependency is a named, dischargeable
assumption, not silent trust.

---

## 5. The demo a stranger sees

```sh
$ cov check sha256_round.cov
proven: round_t1  ⊢ ∀ a..h K W. exec_wasm(0x<B_hash>, …) = T1_spec(…)
  provenance: Axiom(Con(GT))   ← set.mm lemma "mod-2^32 add is a comm ring"
              Obs(T_wasm)       ← i32 word-op fragment
```

One sentence pitch: *"this WASM is proven to implement the SHA-256 round, and
the algebra that made the proof close was not written here — it was imported
from set.mm."* If a reader believes that artifact, the universality thesis is
no longer prose.

---

## 6. The honest risks this is designed to surface

The keystone is a *probe*; these are the findings it is built to produce, and
each should change the plan if it fires:

1. **`T_wasm` is the long pole, not the import.** §2.1. If standing up even the
   minimal `i32` fragment is large, the bottleneck is WASM semantics, and the
   "import is cheap" framing is correct but *not the schedule-determining*
   fact. Size this first.
2. **The fuel may split across sources.** set.mm's strength is the *additive*
   ring facts; the *bitwise* facts (rotation, XOR/AND tautologies) may be more
   naturally native to Covalence's `u32`-as-`bits` (structural induction on the
   list) than to set.mm's integer-modular theory. If so, **SHA-256's real
   imported fuel is narrow** (the add-reassociation only), and a more
   *arithmetic*-heavy WASM target (modular exponentiation, a small bignum) would
   exercise import harder. Finding this is a win — it tells you which primitive
   to use to *showcase* import.
3. **The best free word-arithmetic library may be HOL's, not set.mm's.** HOL
   Light / HOL4 have the canonical bitvector/`words` theory (used for ARM
   semantics). If set.mm's modular fuel proves thin at the right grain, the
   keystone naturally pulls in `hol.mm` as a second (still-cheap) import — a
   useful datapoint for the import roadmap, not a failure.
4. **Native-vs-imported fraction.** If the round proof turns out to be 90%
   hand-authored `.cov` tactics and 10% imported fact, the universality thesis
   was not really tested. Track the ratio; the goal is a step that *cannot*
   close without the import.
5. **`.cov` authoring-regime perf.** The round proof is authored in `.cov`,
   which is the kernel-tactic path that blows up without hash-consing
   ([SKELETONS.md] #2). `set.mm`'s ~1-min number is the *wrong* regime to cite
   as evidence this is fine. If authoring the round is painfully slow, that
   revisits the hash-consing thread — but only if the proof is hand-heavy (see #4).

---

## 7. Sub-steps (sequencing — cheapest-falsifying-first)

0. **Size `T_wasm`.** Confirm nothing exists; scope the minimal `i32` word-op
   fragment. *This is the schedule-determining unknown.*
1. **Spec as a `.cov` `#thy`.** `T1_spec` (and `Ch`/`Σ1`/`Maj`) over `u32`,
   using the existing `defs/bits.rs` `u32`. State the obligation.
2. **`T_wasm` denotation lemmas** for the instructions the round uses
   (`add`, `rotr`, `xor`, `and`, `const`, `local.get`). Smallest set that
   covers §2's bytecode.
3. **The keystone-of-the-keystone:** import *one* modular-add ring fact from
   set.mm (`mm_import`), transport it to `u32` via the `val` iso, and use it to
   close *one* sub-lemma (the add-chain reassociation). If this step works, the
   thesis is demonstrated; everything else is completion.
4. **Complete the round** (`Σ1`/`Ch` unfold, `T2`, shuffle). Composition only.
5. **(Later, out of keystone scope)** 64-round fold + message schedule; the
   `Kₜ` constants as a verified lookup; the full `compress` oracle as a
   license-to-run (VISION §3).

---

## 8. Open questions

- Does the `covalence-pure` executor base (refactor-plan §2) want to *own*
  `T_wasm`, or does `T_wasm` live in `covalence-eval` / a `wasm/` domain group?
  The observer→pure rewrite should settle where executor semantics live — keep
  the keystone's `T_wasm` placement consistent with that.
- Tier choice for the set.mm fact on day one: ship the round at **tier 1**
  (assume the ring fact, `Con(GT)` in the ledger) to land fast, then upgrade to
  tier 2/3? Recommend yes — the ledger makes tier-1 honest, and it de-risks the
  demo.
- Is the `val : u32 ↔ ℤ/2^32ℤ` ring-isomorphism already partially proven
  anywhere in `defs/bits.rs` / the `bits` machinery, or is it greenfield? Check
  before sizing step 3.
- Certificate-checker alternative: for the *additive* step, a QF_BV SMT
  discharge (`(#by (smt))`) would also close it without set.mm — but that
  *bypasses* the import thesis. Keep SMT as the fallback sledgehammer, not the
  primary path, so the keystone actually tests import.
