# End-to-end K reduction demo — scope, architecture, roadmap

> **STATUS: SCOPE + DESIGN (AI-drafted, web-sourced 2026-07-14).** The plan for
> the medium-term north star: *demo the basic K tutorial languages end-to-end*
> (parse a program → reduce it → get a `⊢ KReduces` theorem), on the way to
> *importing large K developments and reducing terms in them*, with **K a
> first-class input format + IR on par with Metamath**. Research is
> certainty-tagged; the implementation plan is a proposal. Resume here.

Companions: [`../../design/k-frontend.md`](../../design/k-frontend.md) (the
KORE-ingestion + F0–F4 decision record), [`research/`](./research/) (the sourced
K surveys), the code in `crates/lang/k` (frontends) and
`crates/kernel/hol/init/src/k` (lowering).

## 1. Where we are (built, on branch `k-frontend`)

- **KORE frontend** (`covalence-k`: `ast`/`parse`/`sexpr`/`fragment`) — parses
  kompile's elaborated `definition.kore`, classifies axioms, extracts
  `RewriteRule`s. Untrusted, kernel-free.
- **`.k`-source grammar frontend** (`covalence-k::kdef`) — winnow parser for
  `syntax` (BNF) declarations → S-expr IR → `covalence_grammar::Cfg` (with the
  swappable `SortResolver` for builtin sorts). Parses the real LAMBDA/IMP
  tutorial grammars. **Skips `rule` sentences** (grammar only, so far).
- **Reduction lowering** (`covalence-init::k`):
  - `encode` — KORE configuration patterns → free term algebra over `Φ = nat`
    (`app`/`con`/`metavar`), same recipe as `wasm::encode`.
  - `reduce` (F0) — single steps as tagged unary `Derivable_KStep` judgements
    via `metalogic::apply`.
  - `relation` (F2) — **`KStep : Φ→Φ→bool`** + **`KReduces = KStep*`** on the
    binary inductive engine `metalogic::binary`; `prove_step`/`prove_reduces`
    give `⊢ KReduces a b`. Headline test: `⊢ KReduces ⌜count(0)⌝ ⌜done⌝`,
    hypothesis-free.

**The gap to a demo:** we can *state and prove a reduction if handed the rule +
witnesses*, but there is no **matcher** (find which rule fires where + the
substitution), no **congruence** (step a redex buried in a term), no **driver**
(iterate to a normal form), and no **rule reader** (`.k` rules are skipped; no
KORE semantics vendored). Those four are the demo.

## 2. The demo target (sourced, verified)

**First target: K tutorial Lesson 1.2 (`k-distribution/k-tutorial/1_basic/02_basics`)**
— `colorOf` / `contentsOfJar` **[high]**. It is (as close as K gets to) **pure
first-order constructor rewriting**: no binders, no hooks, no cells, no
`requires`. Exact rules (verbatim):

```k
syntax Color ::= Yellow() | Blue()
syntax Fruit ::= Banana() | Blueberry()
syntax Color ::= colorOf(Fruit) [function]
rule colorOf(Banana())    => Yellow()
rule colorOf(Blueberry()) => Blue()
// LESSON-02-E: a variable + single-arg constructor
syntax Container ::= Jar(Fruit)
syntax Fruit ::= contentsOfJar(Container) [function]
rule contentsOfJar(Jar(F)) => F
```

**Caveat (load-bearing):** these are **`[function]` rules** — fired *anywhere a
subterm matches*, via congruence — **not** top-level `<k>`-cell rules. That is
*exactly* what our `app`-congruence + first-order matcher does. `contentsOfJar(Jar(F)) => F`
is the case that exercises the matcher's variable substitution. Trivially
extends to Lesson 1.6-A (`isBlue(_) => true/false`, where `true`/`false` are just
imported nullary `Bool` constructors — no hook invoked). **[high]**

**Two hand-written standalone demos** (no tutorial dependency, fully
first-order, good for a *top-level* `KStep` where the whole config rewrites):

```k
module PEANO
  syntax Nat ::= "z" | s(Nat) | plus(Nat, Nat) | mult(Nat, Nat)
  rule plus(z, N)    => N
  rule plus(s(M), N) => s(plus(M, N))
  rule mult(z, N)    => z
  rule mult(s(M), N) => plus(N, mult(M, N))
endmodule           // plus(s(s(z)), s(z)) →* s(s(s(z)))

module BOOLSIMP
  syntax B ::= "tt" | "ff" | and(B,B) | or(B,B) | neg(B)
  rule and(tt, X) => X      rule and(ff, X) => ff
  rule or(tt, X)  => tt     rule or(ff, X)  => X
  rule neg(tt) => ff        rule neg(ff) => tt
endmodule           // and(or(tt,ff), neg(ff)) →* tt
```

Both are confluent + terminating; Peano shows recursion/depth. Recommendation:
**demo Lesson 1.2 (it is a real tutorial language) and PEANO (shows depth)**.

**The boundary (defer):** Lesson 1.7 = `requires` + a comparison hook (`>=Int`);
Lesson 1.13 = `<k>` cell + `~>` KSequence + freezers; Lesson 1.14 + IMP =
`strict`/heating-cooling + `Int`/`Bool` hooks + `Map` state; LAMBDA = capture-
avoiding substitution `E[V/X]` + binders. None reachable with the current
machinery. **[high]**

## 3. Faithfulness — how much K we can skip and stay honest

- **`rule LHS => RHS` at top level = ordinary term rewriting is a *faithful
  special case* of K, not an approximation** **[high]**. A bare (cell-less) rule
  is completed onto the top of the default `<k> $PGM ~> . </k>` cell and applies
  at the *root* of the k-cell head.
- **"apply any rule whose LHS matches any *subterm*, repeat" faithfully models
  K's `[function]` / `[anywhere]` rules** (which is what Lesson 1.2 uses) **[high]**.
  For genuine top-level rules it is faithful only if we also model the k-cell
  rooting — so for PEANO (top-level) we either root at the config or write the
  rules to walk structure; for Lesson 1.2 (function rules) subterm rewriting is
  exactly right.
- **K rewriting is *not* confluent/deterministic in general** **[high]**: when
  several rules match, K picks nondeterministically (`krun --search` explores
  all). For a *deterministic* evaluator (each config has a unique redex — true of
  all three demo languages) reduction order doesn't matter and we can skip *all*
  cell/heating/freezer machinery. Record this as an explicit assumption of the
  driver; a non-confluent language needs a search driver later.

## 4. The layered API architecture (maintainer directive, 2026-07-14)

Build the reduction engine as **trait layers**, each delegating to a slightly
lower one, bottoming out at HOL-omega — so *intense low-level rewrites leave the
high-level APIs alone*, and the **mid layer is reusable** (SpecTec/WASM
reduction is the same shape). See [[k-api-layering]].

```
┌─ HIGH  (K-shaped, per-frontend)  ── KSession / trait KReduce
│        "reduce this program to a value"; speaks configs/rules/→*.
│        Mirrors MmSession. Delegates to ▼
├─ MID   (reusable — the ask)      ── metalogic::rewrite  (NEW)
│        A generic term-rewrite relation over the app-combinator free algebra:
│          · Step : T→T→bool with GENERIC congruence + one base clause per rule
│          · Reduces = Step*
│          · trait Matcher (first-order match lhs↦subterm ⇒ substitution+path) — swappable
│          · driver  normalize(term, fuel) → ⊢ Reduces term nf
│        SpecTec's ↪/Step reduction instantiates the SAME trait. Delegates to ▼
├─ LOW   (relation primitive)      ── metalogic::binary  (exists)
│        RuleSet2 / derive_mixed / Premise / derivable2 / rule_induction2
│        (impredicative least-fixpoint binary relations). Delegates to ▼
└─ BASE  (kernel)                  ── HOL-omega Thm: all_elim/imp_elim/forall/apply
```

**The congruence trick that makes the mid layer clean & finite:** every node
encodes as `app(app(con(sym), a), b)`, so **two generic congruence clauses over
`app`** suffice for an *open* constructor set:

```
∀ f x f'. KStep f f' ⟹ KStep (app f x) (app f' x)    // step in the head spine
∀ f x x'. KStep x x' ⟹ KStep (app f x) (app f x')    // step in an argument
```

A redex anywhere in the tree lifts to the root by threading these along the path
the matcher returns. No per-constructor congruence, no fixed signature.

## 5. Implementation roadmap (concrete, ordered)

1. **Mid layer `metalogic::rewrite`** (reusable). A `RewriteSystem` built on
   `RuleSet2`: base clauses (from encoded `(lhs, rhs)` rule pairs) + the two
   `app`-congruence clauses; `Reduces = Step*`. A `Matcher` trait
   (`fn match_at(&self, lhs: &Term, subject: &Term) -> Option<Subst>`) with a
   default first-order impl over the `app`/`con`/`metavar` algebra. A driver
   `normalize(subject, fuel) -> ReducesThm` that: finds a redex (leftmost-
   innermost) via the matcher, `prove_step` at the root of the matched subterm,
   lifts through the congruence clauses along the path, and `prove_reduces`-folds
   the chain. Metatheorem hooks via `rule_induction2` (determinism/progress —
   later).
2. **Refactor `k::relation` onto the mid layer** — `KStep`/`KReduces` become a
   thin K-shaped instantiation; the congruence/matcher/driver come from
   `metalogic::rewrite`. (This is the "high delegates to reusable mid" step; keep
   `k::relation`'s public surface stable so this is invisible above.)
3. **`.k` rule reader** — extend `covalence-k::kdef` to parse the minimal rule
   fragment (EBNF in §6): `rule TERM => TERM [requires T] [attrs]`, variables as
   free leaves, over the grammar's constructors. `[function]`/`[anywhere]`
   parsed-and-noted (they only change *where* rewriting happens — subterm vs
   config-root — which the driver already does). Defer cells/`~>`/nested `=>`/
   substitution/`?X`. Now a whole `.k` (grammar + ground rules) is readable.
4. **`KSession` (high layer)** — MmSession's peer: holds a K definition (rules
   from `.k` via #3, or KORE via the existing `fragment` path), parses a program
   config against the grammar (or takes an encoded term), and `reduce`s it to
   `⊢ KReduces program nf`. This is the demo surface (and a `/k` REPL later, over
   the merged `repl-core` stack).
5. **Demo** — Lesson 1.2 (`colorOf`/`contentsOfJar`) + PEANO + BOOLSIMP: vendor
   the `.k` (Lesson 1.2 is literate-in-README, so transcribe it; PEANO/BOOLSIMP
   are ours) under `examples/`, and a test/CLI that prints `⊢ KReduces
   colorOf(Banana()) Yellow()`, `⊢ KReduces plus(s(s(z)),s(z)) s(s(s(z)))`, etc.
6. **Then the ladder** (each unlocks more tutorial languages): (a) `requires` +
   a Bool side-condition evaluator + one comparison hook → Lesson 1.7; (b) hook
   theories (`Int`/`Bool`/`Map` → catalogue types with computation rules, the F1
   work) → arithmetic; (c) the `<k>` cell + `~>` KSequence + freezers + strictness
   heating/cooling → Lesson 1.13/1.14, IMP; (d) capture-avoiding substitution +
   binders → LAMBDA. Each is a new mid-or-high layer; the demo surface (#4) is
   unchanged.

## 6. Minimal `.k` rule EBNF (for step 3, sourced)

```ebnf
RuleSentence ::= 'rule' [ '[' Label ']' ':' ] RuleBody
                 [ 'requires' Term ] [ 'ensures' Term ] [ AttrList ] ;
RuleBody     ::= Term ;                       (* one top-level LHS => RHS *)
Term         ::= AppTerm '=>' AppTerm | AppTerm ;
AppTerm      ::= Constructor '(' [ Term (',' Term)* ] ')'   (* app(app(con(sym),..)..) *)
               | Variable | Literal | Constructor ;         (* nullary ctor / leaf *)
Variable     ::= Ident [ ':' Sort ] | '_' [ ':' Sort ] ;
AttrList     ::= '[' Attr (',' Attr)* ']' ;   (* function/anywhere/owise/priority: parse+note *)
```

Deferred (parse-skip or reject with a clear message): cells `<k>`/`<state>`,
`...` ellipsis, `~>` sequences, *nested/local* `=>` (arrow inside a constructor),
`?X`/`!X`/`@X`, substitution `E[R / X]`. **[high]**

## 7. K as a first-class IR — on par with Metamath (framing)

The parallel is exact and the codebase is most of the way there **[high]**:

| Metamath | K |
|---|---|
| `.mm` database | kompiled `definition.kore` (elaborated matching-logic IR) |
| `covalence-metamath` parser → `Database` | `covalence-k` KORE parser → rules |
| `MmSession` replays a proof → `⊢ Derivable_DB` | **`KSession`** reduces a term → `⊢ KReduces` |
| proof replay | term reduction |
| shared `metalogic` rule-induction engine | same engine (`binary`) |

- **Interchange = vendored kompiled KORE golden fixtures** (like we vendor
  set.mm), one K version pinned per semantics — **not** an in-process kompile
  step **[high]**. Real large K projects (KEVM, KWasm) ship `.k`/`.md` source and
  kompile *locally* via pyk `kdist`; they do **not** distribute KORE. So for
  "import a large development" we vendor its kompiled KORE.
- **Sizes are set.mm-comparable** (parse-and-replay budget): tutorial IMP
  ~1.1 MB, fun ~1.9 MB, kool ~2.9 MB, a KEVM slice ~8.8 MB vs set.mm ~50 MB
  (**[medium]** — only the ~1 MB prelude floor + one ~1.14 MB file independently
  reverified this pass; the rest are plausible extrapolations).
- **Matching-logic anchor:** KORE rules are applicative-matching-logic axioms;
  reducing a term = building an AML/reachability proof. RV's CAV'21 pipeline
  emits **Metamath** proofs of K executions checked against a ~245-line AML
  formalization — so "K reduction certified in our kernel" is *literally* RV's
  pipeline, with our internal-Metamath waist as the trust base **[high]**. The
  eventual unifier of both frontends is an AML-in-Metamath database on the waist
  (see [`../logics/logic-frontends.md`](../logics/logic-frontends.md)).

## 8. Sources

- k-tutorial 1_basic: `02_basics`, `06_ints_and_bools`, `07_side_conditions`,
  `13_rewrite_rules`, `14_evaluation_order` READMEs (raw.githubusercontent.com,
  runtimeverification/k @ master).
- K user manual `docs/user_manual.md` (rule structure, `requires`/`ensures`,
  `anywhere`/`function`, priorities).
- pl-tutorial LAMBDA/IMP (`1_k/{1_lambda,2_imp}`); KEVM/pyk `kdist` packaging.
- Prior corpus: [`research/`](./research/), RV CAV'21 "Towards a Trustworthy
  Semantics-Based Language Framework via Proof Generation"
  ([`research/proof-generation.md`](./research/proof-generation.md)).
