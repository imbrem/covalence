# notes/vibes/ — the AI-generated design corpus (index)

The docs are pared to the **current design**. Everything removed in the
pre-HOL-cleanup pass lives on `backup/pre-hol-cleanup` (`git checkout
backup/pre-hol-cleanup -- <path>`).

## Canonical design

The load-bearing docs. Read these first.

| Doc | What it covers |
|---|---|
| [`VISION.md`](./VISION.md) | The system vision — metatheory-as-default, the three-layer stack (executors → HOL → internal Metamath thin waist), scoped truths, the mirror principle. |
| [`kernel-design.md`](./kernel-design.md) | `covalence-core`, the TCB: term/type representation, the inference-rule surface, the non-computational primitive rules, the `defs/` catalogue. **Read first if touching the kernel.** |
| [`type-hierarchy.md`](./type-hierarchy.md) | The equality hierarchy and the `defs/` type catalogue (nat/int/rat/real/bytes/list/stream/option/result, → f32/f64). |
| [`roadmap.md`](./roadmap.md) | What's next: time-to-product for the Metamath vision (verify all of set.mm in GT; analysis in SOA). Its "Active refactor" links the three docs below. |
| [`refactor-plan.md`](./refactor-plan.md) | The in-flight three-layer kernel reorg: introduce `covalence-pure`, split `covalence-hol`, regroup crates. |
| [`next-stage-breakdown.md`](./next-stage-breakdown.md) | Execution breakdown of the root [`REFACTOR.md`](../plans/next-stage.md) (next stage, post-main-merge): docs split → tooling foundations → hierarchical crate migration → WASM roadmap; sequencing, pilot, open decisions. |
| [`pure-design.md`](./pure-design.md) | **Current** `covalence-pure` design: the value-directed `MThm<K,P,S>` kernel (`Stmt`/`MThm`/`Rule`/`Derive`), nuclei & bridges, TCB modules, content-addressing (store-as-world) + federation. Supersedes the *presentation* in `covalence-pure.md`. |
| [`closed-world-kernel.md`](./closed-world-kernel.md) | **Current kernel direction**: first-order theories in the type system — `Sort`/`Op`/`Expr`, `Rule`, parameter-free `Language` with coherence-unique rule trees, a sealed/derived `Uses`/`Extends`, an enumerable TCB manifest. Soundness by *uniqueness of implementation* (no opacity). HOL + Nat/Int/Bytes/Text as layered languages; supersedes the opaque-context/`IsThm` story for the kernel. |
| [`pure-hol-and-build-plan.md`](./pure-hol-and-build-plan.md) | AI-drafted detailed plan: build-system ladder (artifact registry → buck2 spike → cog) + the observer/literal purge (HOL → textbook HOL Light; Nat/Int/Bytes as base-language axioms; obs/ quarantine crate + dep-freeze CI). |
| [`covalence-fol.md`](./covalence-fol.md) | **Sketch** for the HOL fan-out: a `covalence-fol` crate above `covalence-pure` — typed representations + FOL-with-equality (`HasTy`/`EqAt`/`IsOp`/`IsImpl`); replaces HOL observers + constants via `ToHOL`. |
| [`covalence-pure.md`](./covalence-pure.md) | Earlier base-logic blueprint: one trusted logic + N executors + K accelerators, everything-as-observers, the two assumption sets (logical + meta-assumption). Ideas still valid; map onto `pure-design.md`. |
| [`crate-graph.md`](./crate-graph.md) | Dated snapshot of the internal crate dependency graph (layering, inversions). |
| [`soundness-audit.md`](./soundness-audit.md) | Dated audit of the kernel TCB: the trusted base inventory, gaps/risks, and the assumption-tracking design. |

## Design sketches

Aspirational — the authoring layer *above* the kernel, and deployment. Clearly
marked as not-yet-built where they are.

| Doc | What it covers |
|---|---|
| [`frontend.md`](./frontend.md) | The frontend & UX vision: a single surface tracking terms as interpreted across many logics; reasoning as handler-dispatched algebraic effects. |
| [`surface-compiler.md`](./surface-compiler.md) | The canonical surface-language design: theories with many models across many logics, the `#sig`/`#thy`/`#model`/`#logic` forms, the multi-stage compiler. |
| [`surface-syntax.md`](./surface-syntax.md) | The high-level S-expression authoring syntax (rationale + still-aspirational reach). Concrete forms are canonical in `surface-compiler.md` §3.0. |
| [`theories-models-and-logics.md`](./theories-models-and-logics.md) | Design record: the signature → theory → model architecture, within-logic model multiplicity, two-axis consumability, Metamath as the shared logic-definition substrate, the PA→SOA→ZF chain. |
| [`metatheory.md`](./metatheory.md) | Object theories + their derivations as first-class HOL objects; theory morphisms/transport; the metavariable layering. |
| [`logic-frontends.md`](./logic-frontends.md) | Umbrella plan + difficulty matrix for bringing external systems in as object logics over the Metamath waist (MLTT/HoTT/NuPRL, ACL2/Lisp, LF/Dedukti); per-family sketches in `sketches/`. |
| [`wasm-spec.md`](./wasm-spec.md) | The WebAssembly-spec front end (`covalence-init/src/wasm`): lower SpecTec AST S-expressions into `Derivable_R` relations (dual to the Metamath front end), toward WASM acceleration via trace certification. |
| [`observers.md`](./observers.md) | How untrusted code feeds facts into the kernel's HOL model without growing the TCB (the `Observer`/`ObsEq`/`ObsTrue`/`ObsImp` substrate + the proposed validator layer). |
| [`web-kernel.md`](./web-kernel.md) | Running the kernel in the browser: the `category.wiki` north star, `.cov` articles, the deployment seam, federation. |
| [`sketches/`](./sketches/) | Scratch sketches and per-subsystem task/status notes (reorganized separately). |

## Reference / notes

| Doc | What it covers |
|---|---|
| [`cov-project.md`](./cov-project.md) | Compiling a multi-file `.cov` project (the dependency-resolving loader, the Rust↔`.cov` boundary). |
| [`peano-arithmetic-plan.md`](./peano-arithmetic-plan.md) | DONE — pointer to the landed PA deep embedding; live status in `crates/covalence-hol/src/peano/SKELETONS.md`. |
| [`sha256-round-keystone.md`](./sha256-round-keystone.md) | SKETCH — the universality keystone: prove one WASM SHA-256 round equal to the FIPS spec, with the hard step discharged by a fact imported from set.mm. The smallest demo that tests the verified-WASM + import-fuel thesis end-to-end. |
| [`wasm3-rust.md`](./wasm3-rust.md) | Dated research note: WebAssembly 3.0 in Rust, backing the `web-kernel.md` async decision. |
