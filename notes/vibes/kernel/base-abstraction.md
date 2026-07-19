+++
id = "N000V"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:claude"
at = "2026-07-13T20:42:09+01:00"
source = "legacy"
agent = "claude"
harness = "claude"
+++

# Abstracting the base implementation seam (Track C design note)

**Status:** landed on branch `base-abstract` (2026-07-10). Companion inventory:
[`base-api-surface.md`](./base-api-surface.md). Relations vision:
[`base-relcalc-holomega-design.md`](./base-relcalc-holomega-design.md) (Front D)
and [`tcb/tcb-holomega-roadmap.md`](./tcb/tcb-holomega-roadmap.md) (Fronts D/E).

Maintainer directive: *abstract away the particular implementation of `base/` as
much as possible — we want to refactor it severely later to move all
computations into untrusted relations and eventually have all axioms statable
as simple propositions involving these relations — this will also let us e.g.
dump a TCB to SQLite.*

## 1. What landed (all additive, zero TCB delta)

| piece | where | what it pins |
|---|---|---|
| inventory | `notes/vibes/kernel/base-api-surface.md` | what core/eval *actually* consume, file:line, trust-bearing vs vocabulary vs unused |
| facade | `crates/kernel/base/src/api.rs` (`covalence_pure::api`) | the SUPPORTED consumer surface, with the stability CONTRACT |
| algebra sketch | `crates/kernel/base/src/algebra.rs` (`CertificateAlgebra` + `EqnKernel`) | the certificate algebra any base must provide, in code |
| SQLite dump | `crates/app/tcb-db` (`covalence-tcb-db`) | TCB-as-data: languages/rules/configs/mint-sites round-tripped through a `.db` |

Nothing in `crates/kernel/base/trusted/` changed; the facade crate cannot reach
`Thm::new`, so the audit target is untouched (`scripts/tcb-audit.mjs` roots are
`trusted/src` only). Consumers were deliberately **not** migrated — that
mechanical rewrite waits for the in-flight core work to merge (recorded in
`crates/kernel/base/SKELETONS.md`).

## 2. The load-bearing observation

The inventory shows the consumed surface is already almost the abstract
algebra. Outside `crates/kernel/base/`, the entire workspace touches exactly:

- **the certificate**: `Thm` + `prop`/`lift`/`refl`/`sym`/`trans`/`eq_mp`/
  `cong_app`/`cong_pair`;
- **the gates**: `apply` (every HOL rule, every cert rule), `canon` (one site:
  `HolApp`), `Language`/`Manifest`/`RuleRecord`/`Rule`/`CanonRule`, `Error`;
- **the vocabulary**: `Expr`/`Op`/`App`/`Val`/`Eqn` (+ `F32`/`F64` leaves).

Everything else in the base — leaf-equality injectors, `Ref`/`Dyn`, the pure
bool theory, `MatchApp`/`Rewrite`, the Phase-0 relation calculus, the HOL-ω
reflection — has **zero external consumers** today. The severe refactor's
degrees of freedom are therefore already large, and the facade makes the line
explicit instead of implicit.

## 3. The abstraction, in code

`CertificateAlgebra` (GAT `Thm<L, P>`, carrier-ZST implementations) captures
the three capabilities the tower needs:

1. **mint-by-admitted-rule** — `apply`/`apply0`/`canon`, gated on
   `Language::admits` of the rule's own `TypeId`;
2. **equality transport** — the ungated calculus, sound in every language;
3. **positive relation facts** — `execute`/`transpose`/`compose`, the
   positive-only discipline of `rel.rs`.

`EqnKernel` implements it for the current base by one-line delegation (so the
impl is trivially faithful); `tests/algebra.rs` includes a consumer function
generic over the algebra — the shape `covalence-core`'s mint glue takes after
migration. The **vocabulary and the trust enumeration are deliberately NOT
abstracted**: `Expr`/`Op`/`Language`/`Rule` are the narrow waist every tier
states its propositions in. Abstracting them would buy generality nobody asked
for at the cost of making the seam unreadable (`covalence-fol` note's "no
speculative TCB generality" rule).

## 4. How the relations base implements the same algebra

Front D/E target state: **all computation = untrusted relation evaluation;
all axioms = simple propositions `Computation(i, o) ⟹ SomeRelation(i, o)`.**

- `execute` is already the primitive (landed, `rel.rs:102`): run the untrusted
  `f`, observe `(a, b)`, mint `⊢ (a, b) ∈ Rel(f)` — sound for any `f`.
- `apply` becomes *schematic-axiom instantiation* (Front E): an admitted rule
  is an admitted **proposition with schema variables** (`Expr<Ctx>` +
  `Var<N>`/`CtxSort`), and `decide` shrinks to "pick a substitution"; the
  gate (`admits` on the rule identity) and the signature are unchanged.
- `canon` becomes **derived**: `LiftFn<F: CanonRule>` (Front D Part 1) wraps
  the op as an `UntrustedFn`; a run gives `⊢ (a, b) ∈ Rel(LiftFn(f))`; the
  admitted functionality axiom `Rel(LiftFn(f))(i, o) ⟹ (f(i) = o)` +
  instantiate + `mp` gives the same `Eqn` conclusion. Functional vs relational
  becomes *which theorem you ask for*, one substrate.
- transport is untouched — it is model-independent.

At that point the per-language TCB is: **the relation identities it admits +
the schematic propositions it admits.** Both are *data* — which is the bridge
to the SQLite payoff.

## 5. TCB-to-SQLite: today's PoC, tomorrow's real thing

`covalence-tcb-db` dumps today's closest machine image of the TCB — the golden
manifests (`docs/deps/{core,eval,builtins}-manifest.txt`) and the audit
(`docs/deps/tcb-audit.json`) — into a STRICT-schema `.db` (`languages`,
`language_rules`, `configs`, `mint_sites`), with an exact round-trip asserted
in tests plus semantic queries ("is `Refl` admitted by `CoreLang`?", "are all
mint sites inside `trusted/src`?", "is the base `unsafe`-free?").

What changes after the relations refactor: the dump's *source* stops being
repo artifacts and becomes the manifests themselves — a rule row becomes
`(relation id, schematic proposition)` where the proposition is a serialized
ground/schema expression, because that is all an axiom *is* in the target
state. The schema gains a `propositions` table and (per roadmap Front D R2/R3)
the relation *graph* tables (`rel_edges` keyed by content addresses). The R3
discipline is already stated in the crate docs and must survive: **reload
returns rows, not theorems** — recovering `⊢ a R b` needs re-execution or an
R4 attestation axiom. Never hand back a forged `Thm`.

## 6. What the severe refactor MUST preserve (the facade contract)

- Everything re-exported by `covalence_pure::api`, with its meaning:
  unforgeable `Thm`, the ungated transport calculus, `apply`/`canon`
  signatures, `Language`/`Manifest` trust enumeration, `Rule`/`CanonRule`
  gating on the rule's own `TypeId`, the `Expr`/`Op`/`App`/`Val`/`Eqn`
  vocabulary, `F32`/`F64` bit-exact leaves.
- The soundness one-liner: every `Thm<L, _>` derivable from `tree(L)` + the
  universal calculus; `admits(r) ⟹ r ∈ tree(L)`; minting gated at runtime.
- The positive-only invariant of relation facts (no `¬(a R b)` without an
  admitted axiom) — a STANDING soundness invariant per base SKELETONS.
- The manifest-as-golden-file discipline (and hence the SQLite dump's inputs).

## 7. What it need NOT preserve

- The *implementation* of leaf equality (`of_eq`/`Clone`-duplication framing),
  `Ref`/`Dyn`/`TrustedDeref`, the pure bool theory as `Thm` methods, the
  `MatchApp`/`Rewrite` seam, `apply_rewrite`'s shape-erased conclusion, the
  in-base float op *inventory location*, the `TyC`/`KindC` demo reps — no
  external consumer exists (inventory §C).
- `canon` as a *primitive* (it may become derived; signature stays).
- The `Rule::decide` *authority* (it may shrink to substitution-picking under
  schematic axioms; gate and signature stay).
- The number/location of `Thm::new` mint sites — the relations base wants
  *fewer* (ideally: `execute` + instantiation + transport only). The audit
  (`tcb-audit.json` → `mint_sites` table) is the ratchet to watch.

## 8. Migration order (when the freeze lifts)

1. Rewrite core/eval imports to `covalence_pure::api` (mechanical; the facade
   is already exactly their import set).
2. Port core's `mint!` glue and eval's `mint` helper to
   `CertificateAlgebra<B = EqnKernel>` — behavior-identical, proves the trait
   is sufficient in anger (expect small trait adjustments; it is a sketch).
3. Only then start Front D Parts 1–3 behind the trait (`LiftFn`, `StoreRel`,
   parser-as-`Rel`), with the golden manifests + tcb-db dump tracking every
   admits-set change.
