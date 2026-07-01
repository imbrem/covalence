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

over `Φ = nat`: `concl = ⌜e⌝`, each same-relation `SpecTecPrem::Rule` premise is
`d ⌜·⌝`, and `x…` are the rule's metavariables (universally quantified, i.e. the
`all_elim` order). `rule_set(def)` returns the `metalogic::RuleSet`; `derive(rs,
i, n, args, premise_ders)` applies rule `i` to build a
`⊢ Derivable_R ⌜concl[args]⌝` witness. First landed instance: a toy `Even`
relation deriving `⊢ Derivable_Even ⌜Even (succ² zero)⌝`.

## Phasing

1. **Expr/syntax encoding** *(expr done; syntax pending)* — the reusable
   foundation. `wasm::encode` covers the structural core; `Typ` → reified
   datatypes via `crate::init` is next.
2. **Relations → `Derivable_R`** *(inductive core done)* — lift real WASM
   judgements (start with a small closed one, e.g. `⊢ valtype ok`). Grow premises
   past the inductive-only base: `if`/`let` side conditions (need the function
   layer), cross-relation premises (multi-`d` rule set), iterated `…*` premises.
3. **Functions + grammars** — recursive `define` for metafunctions; finish the
   **CFG stratum** in `grammar/spectec` so the binary decoder covers whole `gram`
   productions (`grammar/spectec/SKELETONS.md`).
4. **WASM acceleration (the payoff, roadmap Phase E/F).** Once `Step`/typing are
   `Derivable_R` predicates and reduction functions have computation rules, a
   real WASM engine (`covalence-wasm` / wasmtime) is an **untrusted oracle**
   exactly like a Metamath proof: it runs the module fast and emits a trace; we
   replay/certify the trace step-by-step against the reduction relation.
   Execution-as-proof, construct-don't-trust.
5. **Mirror-principle confidence (roadmap Phase F).** Cross-check
   `SpecTec ⟶ our-prover` against `SpecTec ⟶ HOL ⟶ HOL-in-our-prover`; two
   independent lowerings agreeing is the evidence.

## Trust boundary

Same as Metamath: the SpecTec AST is untrusted input, the kernel re-checks every
construction, and a `Derivable_R` witness is pure syntactic data (`has_no_obs()`,
no hypotheses). Bugs in `wasm/` cost faithfulness/completeness, never soundness.

Related: `notes/metatheory.md` (derivations as first-class objects),
`notes/roadmap.md` (Phase E/F), `crates/covalence-init/src/wasm/SKELETONS.md`
(open increments). `covalence-spectec` crate details in the **crate-map** skill.

[SpecTec]: https://github.com/Wasm-DSL/spectec
