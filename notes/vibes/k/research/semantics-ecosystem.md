# The K semantics ecosystem: what's alive, what's frozen, what imports

> **STATUS: RESEARCH SURVEY (AI-drafted, web-sourced).** Researched 2026-07-13
> via live fetches of primary sources; claims individually marked with
> certainty. Cross-checked by an independent verification pass; corrections
> applied.

Scope: a tiered survey of the public K semantics (KEVM/Kontrol, KWasm and its
derivatives, KMIR, RISC-V; the dormant and frozen repos), per-repo licenses and
K-version pins, the shape of KWasm's configuration vs SpecTec's official-spec
formulation, and the practicalities of importing any of it. Star counts, push
dates, release tags, and K pins were all checked live on 2026-07-13 and rot
quickly — treat them as a dated snapshot.

## Three tiers

**Tier 1 — active, tracks current K** (current K release: v7.1.337,
2026-06-18 **[high]**): KEVM + Kontrol, KWasm (+ Komet, mx-semantics), KMIR,
RISC-V.

**Tier 2 — dormant but recent-K-era**: KPlutus, KAVM, IELE.

**Tier 3 — frozen, will NOT kompile with modern K**: c-semantics, x86-64.

## Tier 1: the active set

### KEVM and Kontrol

[KEVM](https://github.com/runtimeverification/evm-semantics) is the flagship
production semantics: BSD-3-Clause, pushed 2026-07-02, 585 stars, 1029
releases (latest v1.0.921), K pinned to **7.1.337** — exactly the latest K
release **[high]**. Structure: `evm.md` (configuration + transition rules),
`evm-types.md` (256-bit words/wordstacks), `gas.md`, `schedule.md`,
`serialization.md`, plus `abi.md`/`buf.md`/`edsl.md` for symbolic verification;
Python tooling is `kevm-pyk` **[high]**. Concrete execution on the LLVM
backend, symbolic on the Haskell backend; tested against Ethereum's official
test suite **[medium]** (README-sourced, not independently re-run). Paper:
"KEVM: A Complete Formal Semantics of the Ethereum Virtual Machine" (CSF 2018)
**[high]**.

[Kontrol](https://github.com/runtimeverification/kontrol) is KEVM + Foundry
packaging: BSD-3-Clause, pushed 2026-06-24, 118 stars, with CI integration and
a hosted service (KaaS) **[high]**. Real engagements: Optimism's pausability
mechanism, Lido Dual Governance (2024), Cork Protocol (2025)
([example projects](https://docs.runtimeverification.com/kontrol/learn-more/example-projects))
**[high]** — though the verification pass flags that Cork was exploited for
$11M in May 2025 via its Uniswap V4 hook, which RV's engagement had left out of
scope, so it is not the clean win the engagement list suggests. The broader
client list (EigenLayer, Uniswap, Gnosis, Morpho, Polkadot) is plausible but
was not independently re-verified **[medium]**.

### KWasm — and why its shape matters to us

[KWasm](https://github.com/runtimeverification/wasm-semantics) is actively
maintained: not archived, pushed 2026-07-13 (the day of this survey), 105
stars, release v0.1.156 (May 2026), K pinned to **7.1.329** — current 7.1.x
generation **[high]** (pin verified, an actual kompile was not run). License is
**University of Illinois/NCSA** — GitHub's API reports "NOASSERTION" but the
[LICENSE file](https://github.com/runtimeverification/wasm-semantics/blob/master/LICENSE)
is explicit NCSA, copyright 2009-2019 UIUC; permissive, import-compatible
**[high]**. (The README's dependency list — Z3 4.8.15, llvm-8, openjdk-8 — is
visibly stale legacy text; the modern build path is pykwasm/kdist.)

The K sources live at **`pykwasm/src/pykwasm/kdist/wasm-semantics/`** —
`wasm.md` (configuration + transition rules), `wasm-data.md` (data
structures), `numeric.md` (numeric operator functional rules), `test.md`
(execution harness) — **not** the repo root, whose `wasm.md` 404s **[high]**.
`wasm.md` defines four modules: `WASM-SYNTAX`, `WASM-COMMON-SYNTAX`,
`WASM-INTERNAL-SYNTAX`, `WASM` (the researcher pass initially listed three;
verified as four against the file) **[high]**.

**Configuration shape** (verified directly in
[wasm.md](https://raw.githubusercontent.com/runtimeverification/wasm-semantics/master/pykwasm/src/pykwasm/kdist/wasm-semantics/wasm.md);
the cell architecture has been stable for years) **[high]**:

- `<instrs>` — the instruction sequence — plus an explicit **`<valstack>`**
  (typed operand stack, values like `<i32> 42`; binary ops pop operands by
  pattern-matching the stack);
- `<curFrame>` with `<locals>` and `<curModIdx>`;
- `<moduleInstances>` of `<moduleInst>` cells;
- `<mainStore>` with `<funcs>`/`<tabs>`/`<mems>`/`<globals>`/`<elems>`.

Control flow uses administrative `Label`/`Frame` items spliced into `<instrs>`
(internal instructions `#block`, `#loop`, `#br`, …); `#br(N)` scans `<instrs>`
for the Nth label and restores its saved stack **[high]**.

This is **materially different from SpecTec's official-spec formulation**
(evaluation contexts / admin instructions inside a single instruction sequence,
values *in* that sequence, store threaded as a record). A Covalence
KWasm↔SpecTec relation will therefore be a **nontrivial simulation between two
state representations, not a syntactic match** — but both are small, explicit
rule sets, which is favorable **[high]**.

KWasm's only substantial academic writeup is Rikard Hjort's Chalmers MSc thesis
["Formally Verifying WebAssembly with KWasm"](https://odr.chalmers.se/handle/20.500.12380/300761)
(2020); no conference paper is cited in the README **[medium]** (a negative
existence claim). It was used for Ewasm/Ethereum 2.0 and Substrate verification
work 2019-2020 **[medium]**.

KWasm is the substrate for two live products **[high]** (that they *derive
from* KWasm's configuration is **[medium]** — from project knowledge, not
re-verified in-repo): [Komet](https://github.com/runtimeverification/komet)
(Stellar/Soroban contracts, BSD-3, pushed 2026-07-09) and
[mx-semantics](https://github.com/runtimeverification/mx-semantics)
(MultiversX, pushed 2025-11-10). This reuse is evidence the cell structure is
the stable core.

### KMIR and RISC-V

[KMIR](https://github.com/runtimeverification/mir-semantics): active,
BSD-3-Clause, pushed 2026-06-26, 47 stars, latest v0.4.225 (June 2026), K
pinned to 7.1.337 (current); consumes Rust **Stable MIR** via a
`stable-mir-json` submodule; funded by Polkadot OpenGov and Solana **[high]**.
Overwhelmingly Python (the `kmir` CLI: run/prove/show/view/prune); the K
semantics files are ~1.5% of the codebase **[high]**.

[riscv-semantics](https://github.com/runtimeverification/riscv-semantics)
("kriscv"): young (7 stars) but active — BSD-3, pushed 2026-06-18 **[high]**;
relevant as an ISA-level K semantics alongside the frozen x86-64 one.

## Tier 2: dormant

- **[KPlutus](https://github.com/runtimeverification/plutus-core-semantics)**
  (Untyped Plutus Core, `uplc.md` + `kplc` runner, conformance tests against
  the reference implementation): BSD-3-Clause, 27 stars, last push 2024-06-26
  **[high]**; no dedicated academic paper found **[medium]**.
- **[KAVM](https://github.com/runtimeverification/avm-semantics)** (Algorand
  AVM/TEAL, py-algorand-sdk + PyTeal integration): BSD-3-Clause, 15 stars, last
  push 2025-10-01 — likely maintenance/CI; the effort effectively ended with
  the Algorand grant **[medium]** (maintenance-status inferred from push dates).
- **[IELE](https://github.com/runtimeverification/iele-semantics)** (a
  register-based, LLVM-style blockchain VM designed semantics-first in K for
  IOHK/Cardano; VM and verifier auto-generated from the K spec): last push
  2023-07-20, 131 stars, license "Other" per the API **[high]**. Paper:
  Kasampalis et al., ["IELE" (FM 2019)](https://link.springer.com/chapter/10.1007/978-3-030-30942-8_35)
  **[high]**; Cardano's KEVM/IELE sidechain effort has wound down **[medium]**.

## Tier 3: frozen (will not kompile with modern K)

- **[c-semantics](https://github.com/kframework/c-semantics)** — lives under
  the `kframework` org (`runtimeverification/c-semantics` 404s): NCSA license,
  328 stars, not archived but effectively frozen — last push 2022-02-01
  **[high]**. Provides `kcc`, a GCC drop-in that detects undefined behavior
  (UB programs "get stuck"), covering C11/C18, 3305 commits; papers:
  Ellison & Roșu POPL'12, Hathhorn/Ellison/Roșu PLDI'15 ("Defining the
  Undefinedness of C") **[high]**. Its README itself states the maintained
  continuation is RV's commercial **RV-Match** (upgraded to primary-sourced by
  the verification pass) **[high]**. It almost certainly does **not** kompile
  with current K 7.1.x — frozen years before the K 6/7 series, no
  `deps/k_release`-style pin; importing means resurrecting a ~2021 K toolchain
  or a porting project **[medium]** (inference from the freeze date). The
  semantics is large: thousands of rewrite rules across translation + execution
  phases **[medium]**.
- **[X86-64-semantics](https://github.com/kframework/X86-64-semantics)** —
  NCSA license (UIUC copyright), 179 stars, last push 2020-03-04; the README
  **explicitly pins K to a 2019 commit** (`45a4243a…`) and states it is
  incompatible with K master due to MInt (machine-integer polymorphic sort)
  changes — a forked K is recommended **[high]**. Coverage: 3155 instruction
  variants / 774 mnemonics of the Haswell user-level ISA, validated by
  co-simulation against hardware (7000+ instruction tests + GCC torture suite);
  found bugs in the Intel manual. Paper:
  [Dasgupta et al., PLDI 2019](https://dl.acm.org/doi/10.1145/3314221.3314601)
  **[high]**.

## Import practicalities

- **Licensing is uniformly friendly**: everything actively maintained by RV is
  BSD-3-Clause; the UIUC-lineage repos (c-semantics, X86-64-semantics, KWasm's
  LICENSE) are University of Illinois/NCSA. GitHub's API reports "NOASSERTION"
  for the NCSA ones, but the LICENSE files are unambiguous **[high]**.
- **K pinning**: all active RV semantics pin K via a **`deps/k_release`** file
  (KWasm 7.1.329; KEVM and KMIR 7.1.337), install via the `kup` package
  manager, and ship their K sources inside Python packages (`kevm-pyk`,
  `pykwasm`, `kmir`) as a **kdist** embedding the `.k`/`.md` files **[high]**
  (K releases roll every few weeks; the pattern is stable).
- So the natural import surface for a Covalence K/KORE frontend is **kompiled
  K 7.1.x definitions from the kdist packages** for the active tier — and a
  separate **legacy-K story (or an explicit skip)** for c-semantics and x86-64,
  which predate the scheme entirely **[high]**.

## What this means for Covalence

- The active tier is small and coherent: KEVM/Kontrol, KWasm(+Komet/mx), KMIR,
  kriscv — all BSD-3/NCSA, all pinned to current K 7.1.x, all reachable
  through the same kdist/`deps/k_release` packaging. That is the tier to
  target; one import pipeline covers all of it.
- **KWasm is the strategic overlap** with our SpecTec front end
  (`notes/vibes/logics/wasm-spec.md`): relating KWasm's cell-tree
  configuration to SpecTec's eval-context formulation is a *simulation proof*
  between two small explicit rule sets — a concrete, bounded first
  metatheorem for a K frontend, and exactly the "two independent renderings
  agree" mirror evidence we already want for WASM.
- The frozen crown jewels (c-semantics, x86-64) are paper-validated and
  permissively licensed but **stuck on 2019-2021 K**; any plan that needs them
  is a porting project, not an import. Don't gate the K frontend on them.
- Version pins, push dates, and star counts in this doc rot in weeks; the tier
  boundaries and packaging pattern are the durable content.

## Sources consulted

- https://github.com/runtimeverification/wasm-semantics
- https://api.github.com/repos/runtimeverification/wasm-semantics
- https://raw.githubusercontent.com/runtimeverification/wasm-semantics/master/deps/k_release
- https://github.com/runtimeverification/wasm-semantics/blob/master/LICENSE
- https://raw.githubusercontent.com/runtimeverification/wasm-semantics/master/pykwasm/src/pykwasm/kdist/wasm-semantics/wasm.md
- https://github.com/runtimeverification/evm-semantics
- https://api.github.com/repos/runtimeverification/evm-semantics
- https://raw.githubusercontent.com/runtimeverification/evm-semantics/master/deps/k_release
- https://github.com/runtimeverification/kontrol
- https://api.github.com/repos/runtimeverification/kontrol
- https://kontrol.runtimeverification.com/
- https://docs.runtimeverification.com/kontrol/learn-more/example-projects
- https://runtimeverification.com/blog/kontrol-integrated-verification-of-the-optimism-pausability-mechanism
- https://github.com/runtimeverification/publications
- https://github.com/runtimeverification/mir-semantics
- https://api.github.com/repos/runtimeverification/mir-semantics
- https://raw.githubusercontent.com/runtimeverification/mir-semantics/master/deps/k_release
- https://api.github.com/repos/runtimeverification/riscv-semantics
- https://api.github.com/repos/runtimeverification/komet
- https://api.github.com/repos/runtimeverification/mx-semantics
- https://github.com/runtimeverification/plutus-core-semantics
- https://api.github.com/repos/runtimeverification/plutus-core-semantics
- https://api.github.com/repos/runtimeverification/avm-semantics
- https://runtimeverification.com/blog/runtime-verification-brings-formal-verification-to-algorand
- https://github.com/runtimeverification/kavm-demo
- https://api.github.com/repos/runtimeverification/iele-semantics
- https://link.springer.com/chapter/10.1007/978-3-030-30942-8_35
- https://runtimeverification.com/blog/iele-a-new-virtual-machine-for-the-blockchain
- https://github.com/kframework/c-semantics
- https://api.github.com/repos/kframework/c-semantics
- https://github.com/kframework/c-semantics/blob/master/LICENSE
- https://github.com/kframework/X86-64-semantics
- https://api.github.com/repos/kframework/X86-64-semantics
- https://raw.githubusercontent.com/kframework/X86-64-semantics/master/LICENSE.md
- https://dl.acm.org/doi/10.1145/3314221.3314601
- https://fsl.cs.illinois.edu/publications/dasgupta-park-kasampalis-adve-rosu-2019-pldi.html
- https://odr.chalmers.se/handle/20.500.12380/300761
- https://runtimeverification.com/blog/k-kwasm-kewasm-gitcoin-grant
- https://api.github.com/repos/runtimeverification/k/releases/latest
- https://kframework.org/projects/
