# The WebAssembly-spec front end (`covalence-init/src/wasm`)

Bring the **WebAssembly specification** into the kernel by lowering [SpecTec] —
the DSL the spec is written in — into kernel objects, "construct, don't trust",
with the long-term goal of **WASM acceleration**: use a real WASM engine as an
untrusted oracle and *certify* its behaviour against the spec's own semantics.

**Input surface.** SpecTec **AST S-expressions** — the elaborated, type-checked
AST the upstream OCaml SpecTec compiler emits — parsed by
`covalence_spectec::parse::parse_defs` / `ast::parse_spectec_stream` into a
`Vec<SpecTecDef>`. There is **no `.watsup` frontend** here and none is planned;
we consume the elaborated AST directly. `covalence-spectec` is an **untrusted
driver** (like `covalence-metamath`): nothing in `wasm/` grows the TCB.

## Why this mirrors the Metamath front end

Metamath (`covalence-init/src/metalogic`) and SpecTec are **dual**:

- Metamath ships **proofs to replay** → each `$p` is replayed step-by-step
  through the kernel into `⊢ Derivable_L ⌜S⌝`.
- SpecTec ships **a specification to define** — inductive relations, functions,
  syntax, grammars. There are no proofs to replay; instead each SpecTec relation
  *is* an inductively-defined predicate.

So `wasm/` reuses the **same impredicative rule-induction engine**
(`metalogic::{RuleSet, derivable, rule_induction, derive_via_closed}`) — not for
replay, but to turn each SpecTec relation into a `Derivable_R` predicate. A WASM
typing derivation or reduction sequence is then a *value of that predicate*,
identical in shape to a Metamath `Derivable_L` witness. `metalogic::toy` is the
hand-written template; `wasm::relation` is the data-driven version.

## Two legs (the mirror)

There are **two lowerings**, and their agreement is the confidence (Phase F's
commutative diagram, pulled forward):

- **Leg A — syntactic** (`encode` + `relation`, built): SpecTec → an uninterpreted
  free term algebra over `Φ = nat` → `Derivable_R`. Judgements are pure syntax;
  the "our-prover native" semantics. Great for the inductive *structure* of the
  typing/reduction relations; blind to what functions/side-conditions *mean*.
- **Leg B — denotational** (`syntax`/`function`/`denote`, planned): SpecTec →
  **genuine typed HOL**. `Typ` → real HOL types (via `crate::init`), `Dec`
  functions → real recursive `define`s + computation rules, relations → HOL
  inductive predicates *over those types*. This is the direct `SpecTec ⟶ HOL` and
  the only way to give meaning to side conditions (`if`/`let` premises = decidable
  function predicates) and metafunctions.

`SpecTec ⟶ our-prover` (leg A, via `Derivable_R`) and `SpecTec ⟶ HOL ⟶
HOL-in-our-prover` (leg B) should agree — two independent renderings landing on
the same judgements is the mirror-principle evidence.

## Grounding: the real spec + live coverage

`covalence_spectec::wasm::get_wasm_spectec_ast()` ships the WebAssembly **3.0**
spec pre-elaborated: ~972 defs — 207 types, 125 relations, 462 functions, 231
grammars (the typing system `*_ok`/`*_sub`, and reduction `Step`/`Step_pure`/
`Step_read`; `Instr_ok` alone has 110 rules). `wasm::spec` inventories it and
`spec::coverage_report` is the live progress metric. Leg A currently lowers **274
rules / 64-of-125 whole relations**; the remaining skips are *entirely*
side-condition (221) and iterated (63) premises — i.e. exactly what **leg B** and
list recursion unlock.

No WASM 1.0/2.0 AST is separately bundled; "start with WASM 1" = work the feature
*subset* (e.g. the numeric `*_ok` relations) out of the 3.0 dump first.

## The mapping: `SpecTecDef` → kernel

| `SpecTecDef` | WASM-spec role | lowers to | via |
|---|---|---|---|
| `Rel` / `Rule` | judgements: `⊢ instr : ft`, `s;f;e ↪ s';f';e'` | impredicative `Derivable_R`, one clause per `rule` | `wasm::relation` over `metalogic` |
| `Typ` | syntax (`valtype`, `instr`, `store`, …) | reified inductive datatype | `crate::init` engine *(todo)* |
| `Dec` (functions) | metafunctions (`expand`, `default_`, …) | recursive `define` + computation rules | *(todo)* |
| `Gram` | binary/text format | byte-predicate / CFG recognizer | `crate::grammar::spectec` (CFG stratum *todo*) |
| `Rec` | mutual-recursion group | mutually-inductive predicate/datatype | grouped forms of the above |

The `Rel`/`Rule` row is the heart and the reason the metalogic engine is the
right substrate.

## The encoding (`wasm::encode`)

A SpecTec `SpecTecExp` → a term over an **uninterpreted free term algebra**,
carrier `Φ = nat` — the same recipe as `metalogic::mm_database`, but
tree-structured:

- binary combinator `app : nat → nat → nat` (`st$app`), attaches an argument to
  a node head;
- one `nat` **constant** per constructor/atom (`st$c$…`);
- each SpecTec **variable** (rule metavariable) `x` is the free var `st$v$x : nat`.

`f(a, b)` ⟶ `app (app st$c$f ⌜a⌝) ⌜b⌝`. Because `app` and the constants are
uninterpreted and metavariables are variables, **HOL substitution = SpecTec
substitution on the nose**, so a rule clause instantiates by `Thm::all_elim`
(no denotation, no β-redex). Collisions could only lose faithfulness, never mint
a false `Thm` — the kernel re-checks every step.

## The relation lowering (`wasm::relation`)

Each `SpecTecRule { e, prs }` of relation `R` becomes one closure clause

```text
  ∀ x…. d ⌜prem₀⌝ ⟹ … ⟹ d ⌜premₖ⌝ ⟹ d ⌜concl⌝
```

over `Φ = nat`. Every judgement is `encode::tag`-ged with its **relation name**,
so cross-relation premises `R'(e)` are just `d (rel.R' ⌜e⌝)` under one shared `d`
— which is what lets a single combined rule set span the whole mutually-referential
WASM type system. Two entry points:

- `rule_set(def)` — one relation, **all** rules (errors if any can't be lowered):
  the "is this whole relation expressible" view. `derive(rs, i, n, args, ders)`
  applies rule `i` to build a `⊢ Derivable ⌜concl[args]⌝` witness (toy `Even`
  deriving `⊢ Derivable ⌜rel.Even (succ² zero)⌝`).
- `spec_rule_set(defs)` — the whole spec as **one** combined rule set, **skipping**
  rules it can't lower yet and returning a `LoweringReport` of what it dropped
  (sound but incomplete; no silent truncation).

## Phasing

1. **Leg A: syntactic encoding + relations** *(done)* — `wasm::encode` is total
   over `SpecTecExp`; `wasm::relation` lowers single + combined (whole-spec) rule
   sets with cross-relation premises; `wasm::spec` grounds it in the real 3.0 dump
   (274 rules / 64-of-125 relations). Remaining leg-A gap: iterated (`…*`) premises
   (list recursion over premises).
2. **Leg B: denotational typed HOL** *(next — the user-requested "explicit HOL
   terms")*. `Typ` → real HOL types (via `crate::init` inductive engine), `Dec`
   functions → recursive `define`s + computation rules, relations → HOL predicates
   over those types. Unlocks the 221 skipped **side-condition** rules (a side
   condition is a decidable function predicate). Modules: `wasm/{syntax,function,
   denote}.rs`.
3. **Grammars** — finish the **CFG stratum** in `grammar/spectec` so the binary
   decoder covers whole `gram` productions (`grammar/spectec/SKELETONS.md`).
4. **WASM acceleration (the payoff, roadmap Phase E/F).** With `Step`/typing as
   predicates and reduction functions with computation rules, a real WASM engine
   (`covalence-wasm` / wasmtime) is an **untrusted oracle** exactly like a Metamath
   proof: it runs the module fast and emits a trace; we replay/certify the trace
   step-by-step against the reduction relation. Execution-as-proof,
   construct-don't-trust.
5. **Mirror-principle confidence (roadmap Phase F).** Cross-check leg A
   (`SpecTec ⟶ our-prover`) against leg B (`SpecTec ⟶ HOL ⟶ HOL-in-our-prover`);
   two independent renderings agreeing is the evidence.

## Trust boundary

Same as Metamath: the SpecTec AST is untrusted input, the kernel re-checks every
construction, and a `Derivable_R` witness is pure syntactic data (`has_no_obs()`,
no hypotheses). Bugs in `wasm/` cost faithfulness/completeness, never soundness.

Related: `notes/metatheory.md` (derivations as first-class objects),
`notes/roadmap.md` (Phase E/F), `crates/covalence-init/src/wasm/SKELETONS.md`
(open increments). `covalence-spectec` crate details in the **crate-map** skill.

[SpecTec]: https://github.com/Wasm-DSL/spectec
