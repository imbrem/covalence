# TCB → HOL-ω Roadmap

*Agent-authored design synthesis (notes/vibes/). Reconciles five architect
fronts (A–E) into one staged program. Concrete file/type references are the
architects'; this document does not invent beyond them.*

---

## 1. Context & Vision

The goal is to simplify the Covalence trusted computing base toward a
**textbook HOL-ω middle language**, with most code written Haskell-style above
the kernel, and a **base layer that is a relation calculus with untrusted
computation**. The long-term punchline is schema variables + a
`Computation ⇒ Relation` metatheorem that certifies WASM (and other executor)
traces with *one* admitted axiom instead of one per run.

Four layers frame everything below:

- **Base** (`covalence-pure-trusted`, `crates/kernel/base/trusted`): a ground,
  first-order, **binder-free** `Expr` grammar (`expr.rs`) over an open
  `Op<In,Out>` vocabulary (`op.rs`). Sole mint is `pub(crate) Thm::new`
  (`eqn.rs:75`); audited call sites enumerated at `lib.rs:11-33`
  (`mintSites: 18`). Two evaluation mints exist: `canon` — functional equation
  `⊢ App<F,Val(v)> = Val(F.eval(v))`, gated on `F: CanonRule` (`eqn.rs:331-348`)
  — and `execute` — positive relation membership (`rel.rs:102`). A generic
  reflected type-rep already landed (`tyrep.rs`: `TyFn`/`TyApp`).
- **Core** (`covalence-core`, `crates/kernel/hol/core`): HOL-Light-shaped,
  rank-1 HOL. `TypeKind` (`ty/ty.rs:29-75`) has `TFree` type variables but **no
  kinds, no ranks, no `TyAll`/`TyAbs`**. Terms are locally-nameless de Bruijn;
  α-equivalence is structural `==`. TCB = 26 `Rule<CoreLang>` ZSTs
  (`thm/rules.rs`), gated by `core_admits` (`thm/lang.rs:125`), tier-generic
  over `HolTier`.
- **Eval** (`covalence-hol-eval`): derivation tier (`derived.rs`, `certs.rs`,
  `tohol.rs`); `evalManifest: 16`.
- **Init / above** (`covalence-init`, parsers, theories): untrusted library
  code emitting `Term`s and `Result<Thm>`s the kernel checks.

The vision decomposes into two nearly-vanilla design commitments and one
non-vanilla exception:

- Middle becomes vanilla HOL-ω. **The rank-stratification constraint on
  `TyAll`/`TyInst` is a hard soundness requirement, not a feature** —
  unrestricted impredicative type quantification is inconsistent
  (Girard/type-in-type) over a HOL universe carrying choice.
- The one deliberately non-vanilla thing is **DEFS**: definitions are values
  (Arc-identity `Def`, fresh tokens in `decide`), never a global mutable
  signature table. This already satisfies "avoid global state" and HOL-ω
  inherits it unchanged.
- Base stays binder-free; kinds are binder-free too (`κ ::= ⋆ | κ⇒κ`), so a
  reflected kind sort and total decidable kind/rank checkers fit the ground base
  as inert ops + `CanonRule`s.

Grounding snapshot (`tcb-audit.json`, 2026-07): `termKindVariants: 18`,
`coreManifest: 26`, `evalManifest: 16`, `mintSites: 18`, base+HOL
`defsCoupling: 37`, base+HOL src ≈ 6361 lines.

---

## 2. Near-Term Implementation Program (additive-first, audited)

Drawn from Front A (leaf-removal + `defs/` out of `hol/core`) and Front B
(HOL-ω base constructors). **Guiding invariant: zero base-TCB delta** — every
new rule mints through the existing `covalence_pure::apply` gate; base
`mintSites` stays 18 except the explicitly-deferred EG4 (`Dyn` transport) and
Front B's three `CanonRule` mints (monotone, enumerated). Additive/reversible
stages first; irreversible maintainer-gated doors last.

### Front A — leaf removal + defs-out

**Endgame:** `covalence-core` = textbook equality-HOL — the 26-rule manifest
shrinks to equality/subst core + `SelectAx` + `define`/`new_type_definition` +
`nat_induct` + nat freeness (`succ_inj`, `zero_ne_succ`), `FalseElim` derived;
`core::Term` has **no literal leaves**; `core/src/defs/` gone.

| Stage | Move | TCB delta | Reversible? | Gate |
|---|---|---|---|---|
| **EG3a — `Zero` leaf** | Add `TermKind::Zero` + `Term::zero()` (`term.rs`); rewire `ZeroNeSucc` (`rules.rs:529`) and `NatInduct` (`rules.rs:569`) off `Term::nat_lit(Nat::zero())`. Nat = `Zero`+`Succ` as freely-generated constructors. | `termKindVariants` 18→19; `coreManifest` 26 (no new rule) | additive (+downstream `nat_lit(0)`→`zero()` migration) | low-risk |
| **EG3b — `T`/`F` defined; `FalseElim` derived; connectives → `CoreLang`** | `T := (λp:bool.p)=(λp:bool.p)`, `F := ∀p:bool.p` via core `Define` (cached `LazyLock<Def>` in eval). `truth()` derives at `Thm<CoreLang>` off `LitEqCert` → the whole connective calculus in `eval/src/derived.rs` drops from `EvalThm` to `CoreLang`. `FalseElim` removed from core, re-derived (`{F}⊢p` = assume `F`, unfold, `spec`). | `coreManifest` 26→**25** (primitive removed); tier drop; `termKindVariants` 19 | semi (representation flip ripples through `as_bool`/`bool_lit`) | **maintainer** |
| **DEFS-OUT (sequent-reshape)** | Reshape `SuccInj`→`{succ m=succ n}⊢m=n`, `SelectAx`→`{p x}⊢p(ε p)` (drops `hol_imp`); `ZeroNeSucc`→connective-free ex-falso form (harder — flag). Drop `imp`/`not` builders from `hol.rs:31-58`. | `coreManifest` flat; `defsCoupling` 37→~29 | reversible in-kernel (+downstream proof migration) | maintainer-visible |
| **Close float-op lander gap** | Add symbolic landers for `sub`/`div`/`min`/`max`/rounding/compares/converts (no lander yet, `thm/SKELETONS.md:26-29`). | eval-tier addition | additive | maintainer (go/no-go for EG5) |
| **EG5 — delete 5 literal leaves + manifest swap** | Admit permanent structural `toHOL` unfolding rules (`ToHolNatZero/Succ`, `ToHolBytesNil/Cons`, `ToHolIntMk`) and **in the same commit** drop the transitional `*Val` reify rules — the `tohol_unfolding_rules_are_exclusive` guard (`rules.rs:793-803`) forbids co-admission (would mint `⊢False`). Then delete `TermKind::{Nat,Int,SmallInt,Blob,Bool}` + ctors + Cluster A of `defs/` (literal-type chain). | `termKindVariants` 19→**14**; `evalManifest` ≈ flat; `coreManifest` unchanged; base+HOL ≈ 6361→~4.6k lines | **NO — one-way** (deletes public ctors, changes term hashing/content-addresses, one-way manifest swap) | **maintainer** |

**Residual `defs/` blocker (honest wall):** `thm/mod.rs:1055-1066`
(`forall_spec()`) and `typedef.rs:102` (`and_spec()`) recognize
existentials/conjunctions by spec-handle pointer identity for `spec_ax` /
`new_type_definition`. Sequent-reshaping cannot remove an **existential**
conclusion, so a minimal `exists`/`and` vocabulary stays as core residue until
**L4 (ε/rep/abs endgame — not this front)**.

**Deferred (NOT this front): EG4 — `Dyn` base transport.** Heterogeneous
collections of symbolic theorems (`Vec<Thm>` with different operand shapes) need
erasure to `Thm<L, Dyn<Term>>`; `Dyn` is pointer-eq, so `eq_mp`/`trans` cannot
rewrite structurally-equal different-allocation `Dyn`s. Fixing this is a **new
base-TCB method** (the one place this program touches the innermost TCB).
Deferred, maintainer-gated, build only if a real consumer needs it.

### Front B — HOL-ω base constructors (additive, reversible)

Realizes "add Ty + KIND constructors and rules at the BASE." All stages are new
modules + `pub use`; kinds are binder-free so they are a perfect fit for the
ground base; kind/rank synthesis are total decidable functions, hence
`CanonRule`s — the middle's kind/rank checker becomes a *consumer of
base-minted equations* rather than trusted middle code.

| Stage | Move | TCB delta | Reversible? |
|---|---|---|---|
| **B-K1 — reflected Kind sort** | New `crates/kernel/base/trusted/src/kind.rs`: `KStar<K>` (`() → K`), `KArrow<K>` (`(K,K) → K`) as inert `Op`s, mirroring `tyrep.rs:43-76` (hand-written `Copy/Clone/Eq/Debug`, never `derive` — would spuriously demand `K: Clone`). Kind equality/congruence come free from `refl`/`cong_pair`/`cong_app`. | **none** (inert ops, no `Thm::new` added) | delete module |
| **B-K2 — higher-rank Ty ctors** | Extend `tyrep.rs`: `TyBound<T>` (de-Bruijn tyvar), `TyAll<T,K>` (`(K,U32,T)`), `TyAbs<T,K>` (`(K,T)`). Structural eq on de-Bruijn spines **is** α-equivalence — no α-machinery. Malformed spine is *inert*, not *unsound*. | **none** (inert ops) | revert additions |
| **B-K3 — KindOf/RankOf/RankLe** | `CanonRule`s over in-base demo rep `Cdemo`: `⊢ kindof(τ)=κ`, `⊢ rankof(τ)=r`, `⊢ (r≤s)=T`. `KindOf` must return `None` on ill-kinded input, never a wrong kind. | three gated `canon` mints; +3 lines at `lib.rs:11-33` (monotone) | delete impls + manifest entries |
| *(core-side, later)* | wire `C = core::Type` so base CanonRules serve `core` (one-way base→core dep; core-side step, not a base change). | — | — |

Honest note: B-K3 *computes and certifies* kind/rank; it does **not** enforce
the stratification. Enforcement (the `TyInst` side-condition) is middle-level —
see §3 / Front-B-sketch below.

### Near-term ordering (Fronts A + B interleaved)

1. **B-K1 → B-K2 → B-K3** (base, additive, ship first; zero/monotone TCB delta).
2. **EG3a** (`Zero` leaf) — additive.
3. **EG3b** (`T`/`F` defined, `FalseElim` derived, connectives → `CoreLang`) —
   maintainer-gated, removes a primitive (26→25).
4. **DEFS-OUT sequent-reshape** — removes imp/not coupling.
5. **Close float-op symbolic-lander gap.**
6. **EG5** (swap + delete 5 leaves + Cluster A) — single irreversible
   maintainer-gated door; only stage requiring wasm32-adversarial audit.
7. Residual `defs/` empties as L4 / ε-rep-abs lands.

Steps 1–4 are additive-first and independently mergeable.

---

## 3. Long-Term Vision (design sketches)

*All of §3 is DESIGN SKETCH. None to be built now. Each front is marked.*

### Front C — Haskell-in-HOL-ω (micro-Haskell surface → HOL/HOL-ω)

**Reachable now with ZERO TCB delta** (untrusted `covalence-init`; kernel sees
only monomorphic HOL terms). Parser type stated once:
`Parser α := bytes → option (α × bytes)` (= `StateT bytes Option`); all monad
pieces already exist as eval defs. `sexpr_parse.rs:297` already defines
`opt_bind` (option-monad bind) and `list_body` (`:306`) is hand-desugared
`do`-notation — the surface language makes that structure the *source*.

- **Stage H0 — combinator library as HOL terms** (`init/combinator.rs`, new):
  `pure`/`bind`/`map`/`alt`/`satisfy`/`token`/`between` + monad/alternative
  **laws** proved at each concrete element type (rank-1 poly fine); re-express
  `span_digits`/`parse_nat` on top. TCB delta 0; audit = each law lemma
  hyp-free.
- **Stage H1 — typeclasses by compile-time dictionary passing:** `struct
  MonadDict { pure: Term, bind: Term }`; `instance Monad Maybe` = Rust value;
  `LawfulMonad_M` a HOL predicate at fixed carrier `M`. `f :: Monad m => …`
  compiles to `fn(dict) -> Term` monomorphized per instance. `do{x<-p;k x}` →
  `bind d p (λx. k x)`. TCB delta 0. **Honest limit:** laws proved once *per
  instance*, not abstractly; rank-n Haskell (`runST`) inexpressible — that gap
  is exactly what HOL-ω buys.
- **Stage H2 — general recursion via ε, gated defining-equation:**
  `rec_eps(F) := ε g. ∀x. g x = F g x` (always well-typed); **separate**
  `fixpoint_eq(F, exists_proof: Thm) -> Result<Thm>` returns `⊢ f x = F f x`
  **only** when handed an unforgeable `∃g.∀x. g x = F g x` (WF recursion on a
  measure, e.g. `length input`). Uses existing `Thm::select_ax`; TCB delta 0.
  **The one real soundness hazard in this front:** `fixpoint_eq` must never mint
  unconditionally — emitting the equation without the `∃`-proof admits a false
  axiom for non-terminating `F` (≡ `⊢False`). API shape (proof as required
  argument) makes it un-hittable.
- **Generalized patterns → ε:** pattern `p(x₁..xₖ)` against `s` lowers to
  `ε(x₁..xₖ). s=⟦p⟧`, guarded by coverage `∃(x₁..xₖ). s=⟦p⟧`. Same admitted-axiom
  hazard as H2; untrusted-compiler work once H2's discharge discipline lands.

**DESIGN-SKETCH future (genuine TCB delta) — the HOL-ω middle:** the *general*
theory of monads/optics with laws proved once over abstract `m` requires
abstracting over type operators, which rank-1 HOL cannot state.

| micro-Haskell | HOL-ω | kernel delta |
|---|---|---|
| `Maybe :: *→*` | `ty⇒ty` type-operator constant | kind layer (new `TypeKind`, kind-checker) |
| `class Monad m` | `Monad : (ty⇒ty)⇒ty` + `LawfulMonad` | type-operator variables (`TFree` at kind `*⇒*`) |
| `f :: Monad m => a → m a` | `f : ∀(m:ty⇒ty). Monad m → …` | `TyAll`/`TyInst` + rank stratification |
| `do{x<-p;k x}` | `bind d p (λx. k x)` | none (= H1) |

Migration honesty: H0–H2 surface is *unchanged* even in the HOL-ω future — the
additive stages are not throwaway; HOL-ω only replaces per-instance dictionaries
with once-and-for-all abstract law theorems and unlocks rank-n signatures.

### Front B-sketch — the HOL-ω middle in `core` (TCB-touching, gated)

Not additive; changes `Type`/`TypeKind` and the rule catalogue; maintainer-gated.

- **Type structure:** annotate `TFree` with `(Kind, Rank)`; add `TyBound(u32)`,
  `Kind (KStar | KArrow)`, `TyAll(Kind, Rank, Type)`, `TyAbs(Kind, Type)`.
  `Tycon`/`Spec`/`FreshTyCon` gain declared kinds (all currently rank-0/⋆ ⇒
  backward-compatible). `type_of`/`check_sequent` (`rules.rs:65-85`) gain an
  integrated kind check consuming base-minted `KindOf`/`RankOf` (B-K3).
- **New rules vs the current 26:** `TyBeta` (`⊢ (TyAbs κ.τ)σ = τ[σ/0]`),
  `TyGen` (`TyAll`-intro, α∉Γ), and **`TyInst`** (`TyAll`-elim, generalizes
  `InstTFree`) — **requires `rank(σ) ≤ r` and `kind(σ) = κ`**.
- **`TyInst`'s rank side-condition is THE soundness-critical rule.** Rank
  formula `rank(∀α:κ:r.τ) = max(r+1, rank(τ))`; `InstTFree` is the rank-0 case
  (existing proofs preserved). Discharge the arithmetic via a base-minted
  `⊢ (rankof(σ)≤r)=T` premise (B-K3 `RankLe`), keeping it out of the middle TCB.
  The `manifest_matches_golden` guard (`rules.rs:812`) is the tripwire: no
  higher-rank rule enters `CORE_MANIFEST` until stratification is proven against
  the **full** rule set (esp. `SelectAx`/`bool`).

### Front D — relation calculus as all computation

**Landed already exceeds the design doc's Phase 0:** `rel.rs` has
`UntrustedFn`/`RelErr::{Refused,Trapped}`/`Rel<F>`; `execute` (`rel.rs:102`,
gated on `TypeId::of::<Rel<F>>()`, zero-copy `Ref<Arc<_>>` leaves); the **entire
positive calculus** (`Transpose`/`Compose`/`Join`/`Meet`, `rel.rs:128-311`,
complement deliberately absent); mandatory tests in `rel_tests.rs`. The base
**is** a relation calculus today.

- **Part 1 — `Lift : CanonRule → Rel` (IMPLEMENT-NOW-capable):** one untrusted
  wrapper (upstream of base, e.g. `covalence-pure-eval`):
  `LiftFn<F: CanonRule>` with `run = self.0.eval(a).ok_or(RelErr::Refused)`.
  `execute(Rel(LiftFn(f)),a,lang)` mints membership `⊢ a Rel(LiftFn(f)) b`;
  `canon(f,a,lang)` mints the equation `⊢ f(a)=b`. Functional vs relational
  becomes *which theorem you want*, one substrate. TCB delta: **zero new mint
  sites** (reuses `execute`'s gate); one `admits` entry per `Rel<LiftFn<F>>`.
  - *DESIGN-SKETCH one-way door:* the full **Op/Val collapse** (delete `Val`,
    `Expr := Op<(),_>`, equality = diagonal relation; re-derive
    `refl`/`sym`/`trans`/`cong` as coreflexive sub-allegory of Δ). Never forced;
    the limit the lazy `Lift` bridge converges to.
- **Part 2 — persisting the relation graph (the maintainer's stated payoff):** a
  minted `⊢ a Rel(f) b` is content-addressable — `RelEdge { rel_id: O256,
  addr_in: O256, addr_out: O256 }`, operands as blobs in `ContentStore<O256>`
  (`store/core/src/lib.rs:109`; `covalence_hash::O256`).
  - **R2 — `StoreRel` (buildable-soon):** `StoreRel(Arc<dyn ContentStore>)` with
    `run(k) = self.0.get(k).ok_or(RelErr::Refused)`; `execute` mints
    `⊢ addr Rel(Store) blob`. A miss soundly proves nothing. SQLite backing
    already exists (`store/core/src/sqlite.rs`). TCB delta: one `admits` entry.
  - **R3 — durable graph as cache/hint (zero TCB):** write operand blobs + edge
    rows, reload edge set. **Mints nothing.** *Load-bearing audit obligation:*
    reload returns **bytes/edges, not theorems** — recovering `⊢ a Rel(f) b`
    needs re-execution (cheap for `LiftFn`) or R4 attestation. Never hand back a
    forged `Thm`.
  - **R4 — attestation (DESIGN-SKETCH):** per-relation `Attested<K>` axiom keyed
    on a trust-store key turns a persisted edge into a theorem without recompute.
    New trust = admitted axiom; needs the PKI/`facts` module (does not exist).
- **Part 3 — migrating existing computation:** parsers are natural `Rel`
  citizens (`init/{nat_parse_bytes,int_parse,json_parse}.rs` are
  `bytes→Option<AST>`; failure = `Refused` proves nothing). **Arithmetic certs
  stay functional deliberately** (`hol/eval/src/certs.rs` — HOL rewriting needs
  the equation, not a graph edge; `Lift` lets them *also* be viewed relationally
  when a membership fact is wanted). **WASM:** `Rel(WasmRun{module})` over
  `crates/lib/wasm`; trap = `Err` proves nothing; `compose` chains runs; verified
  compilation = relational inclusion `graph(compile;wasm_eval) ⊆ graph(hol_eval)`.
- **Part 4 — trust story (positive-only):** `execute` grants only observed graph
  pairs, sound for *any* `f`; can never mint `¬(a R b)`. Every
  negative/uniqueness/functionality conclusion is an **admitted axiom** (user's
  burden). Persistence does not weaken this; only R4 adds trust, through the
  ordinary admitted-axiom door.
- **Recommended order:** R1 `LiftFn` → R2 `StoreRel` → R3 `RelGraphStore` cache
  → parser-as-`Rel` demo → WASM `UntrustedFn`. R4 + full Op/Val collapse are
  DESIGN-SKETCH, gated on PKI/facts + maintainer sign-off.

### Front E — `Expr<Ctx>` schema variables, pattern matching, `Computation ⇒ Relation`, WASM

**Entirely LONG-TERM DESIGN-SKETCH.** The punchline the base was shaped toward:
turn the per-computation axiom problem into *one* schematic theorem + a matching
rule.

- **The generalization:** `pub trait Expr<Ctx = ()>` recovers today's grammar as
  `Expr<()>` with zero churn. `Var<const N: usize>` = a metalanguage **schema
  variable** (ZST index, NOT a HOL variable, NOT a binder). `CtxSort<N>` assigns
  sorts; `Var<N>: Expr<Ctx>` only where `Ctx: CtxSort<N>`. **`Ctx = ()` has no
  `CtxSort<N>`, so `Var<N>` is not an `Expr<()>`** — variables disallowed in the
  ground grammar, as required. `Thm<L, P, Ctx = ()>` gains a context tier; the
  entire ground calculus is defined **only on `Thm<L,P,()>`** — a context-theorem
  is inert (type-level firewall).
- **Two new primitives:** `Inst<Ctx,Sigma>` (type-directed instantiation,
  `Out: Expr<(), Ty=Self::Ty>` sort-preserving by construction) and
  `instantiate<Sigma>(self, s) -> Thm<L,P::Out,()>` (schema ∀-elim, sound for
  **any** well-sorted σ; sole gate `eqn.rs:75`). `Match<Ctx,Target>` is the
  type-directed dual (seed: existing `MatchApp`, `matching.rs:30`).
- **`Computation(i,o) ⇒ SomeRelation(i,o)` metatheorem:** lives in
  `Ctx=(In,Out)`, `P := App<Rel<F>,(Var0,Var1)> => App<SomeRel,(Var0,Var1)>`.
  Enters as **one admitted schematic axiom** (`Rule<L>` with `Concl` relaxed to
  `Expr<Ctx,Ty=bool>`). Discharge per run: (1) `execute` mints ground
  `⊢ Rel<F>(i,o)`; (2) untrusted `Match` picks σ; (3) `instantiate(σ)` ⇒
  `⊢ Comp(i,o)=>Rel(i,o)`; (4) `prop::mp` ⇒ **`⊢ SomeRelation(i,o)`**. Every run
  reuses the *same* axiom — no new axiom/manifest entry per computation.
- **WASM instantiation:** `Rel(F)=Rel(WasmRun)`, `SomeRel = WasmSpec`; schema
  `∀ i o. WasmRun(i,o) ⇒ WasmSpec(i,o)` (user asserts executor implements spec,
  differential-fuzzed out of band). Zero-copy `Ref<Arc<_>>` leaves ⇒ O(1)
  certificate per trace. `compose` handles chaining.
- **Optional smallest de-risking probe (IMPLEMENT-NOW, zero TCB):** a type-level
  `schema.rs` adding `Var`, `CtxSort`, the `Expr<Ctx=()>` default, and
  `Thm<_,_,Ctx=()>` — **no mint site, no `Inst`, no `Match`**. Proves
  source-compatibility. Audit: confirm `Expr<()>` still rejects `Var<N>` and no
  ground signature changed meaning. Rollback: byte-identical.

---

## 4. Dependency / Sequencing Map

**Can proceed in parallel now (additive, low/zero TCB delta):**

- Front B base ctors: **B-K1 → B-K2 → B-K3** (independent of Front A).
- Front A additive stages: **EG3a → EG3b → DEFS-OUT reshape → float-lander gap**.
- Front C untrusted: **H0 → H1 → H2 → generalized-patterns** (all in
  `covalence-init`, orthogonal to base/core work).
- Front D lower rungs: **R1 `Lift` → R2 `StoreRel` → R3 cache → parser-as-Rel**.
- Front E's optional type-level probe (`schema.rs`).

**Hard sequencing (must precede):**

- Front A: `EG3a, EG3b, DEFS-OUT-reshape, float-lander-gap` **all precede EG5**
  (EG5 needs every core-rule literal reference already removed *and* all
  big-literal consumers routed through symbolic landers).
- Front A: EG5 (irreversible) **precedes** deletion of `defs/` Cluster A.
- Front A: residual `defs/` (`exists`/`and` vocabulary) **gated on L4**
  (ε/rep/abs endgame) — not in this program.
- Front B: **B-K3 precedes** wiring `C = core::Type`, which precedes the
  core-side HOL-ω middle.
- Front B-sketch (HOL-ω middle) **gated on the rank-stratification soundness
  proof** — nothing enters `CORE_MANIFEST` first.
- Front C's full abstract-monad payoff **requires** Front B-sketch (HOL-ω middle
  with type-operator variables + `TyAll`/`TyInst`).
- Front D: R2 (real `ContentStore` backing) roughly precedes R3 (cache) and the
  WASM `UntrustedFn`; R4 attestation **gated on** the PKI/`facts` module.
- Front E: `execute`/`StoreRel`/`WasmRun` (Front D R1/R2 + WASM) **precede** the
  `Computation ⇒ Relation` discharge; Front E's `Inst`/`Match`/schema-axiom are
  DEFER (full audited design pass, maintainer-gated); the shape-erased general
  matcher is DEFER-hard (a wall).

**Reconciled overlaps / tensions (flagged):**

- **Ty/base grammar — Fronts B and E both touch it.** B adds reflected
  *type/kind* ops (`kind.rs`, `tyrep.rs`) for the HOL-ω object language; E adds a
  *metalanguage* `Var<const N>` + `Ctx` parameter to the whole `Expr` grammar.
  These are orthogonal in intent (object-type reflection vs. schema variables)
  but **both edit `expr.rs`/`tyrep.rs`-adjacent sealed grammar** — coordinate so
  E's `Expr<Ctx=()>` default and B's new inert ops land without churn conflict.
  No semantic conflict: B's ops are ground (`Expr<()>`), E's `Var<N>` is excluded
  from `Ctx=()`.
- **Computation — Fronts A and D both touch it.** A removes literal leaves and
  moves arithmetic to symbolic `toHOL` (kernel `canon` equations); D keeps
  arithmetic certs functional *deliberately* and adds a *relational view* via
  `Lift`. These agree: `certs.rs` stays on `canon`; D's `Lift` is an additive
  alternate reading, not a migration. No tension.
- **`Val`/literal direction — A vs D's Op/Val collapse.** A deletes literal
  `TermKind` leaves (core term rep); D's full Op/Val collapse (delete base `Val`)
  is a separate, never-forced base-level sketch. Independent layers (core term
  rep vs base `Expr`); do not conflate. Both are one-way doors flagged
  maintainer-gated.

---

## 5. Open Soundness Questions / Walls (collected from all fronts)

1. **[B, C] Rank stratification for HOL-ω is a hard consistency constraint.**
   Unrestricted impredicative `TyAll` is inconsistent (Girard/type-in-type) over
   a HOL universe carrying `SelectAx`/choice. `TyInst` must **reject**
   `rank(σ) > r`; the consistency argument must be re-run against the **whole**
   rule set (esp. `SelectAx`/`bool`), not `TyInst` in isolation, and
   adversarially audited (the "mint ⊢False through the safe API" class). No
   higher-rank rule may enter `CORE_MANIFEST` until this is specified + proven.
2. **[A] The EG5 exclusivity swap is the single highest-risk near-term change.**
   Admitting structural `toHOL` unfolding rules and dropping the `*Val` reify
   rules **must be one same-commit swap** — the
   `tohol_unfolding_rules_are_exclusive` guard (`rules.rs:793-803`) exists
   because co-admission mints `⊢False`. Must reproduce every fact
   `LitEqCert`/`NatArithCert`/`SuccCert` produced, on **all inputs including
   wasm32** (the 32/64-bit divergence class that previously slipped past green
   tests). Irreversible.
3. **[D] Reload ≠ free theorems (central persistence risk).** A persisted
   `RelEdge` is a *hint*; recovering `⊢ a Rel(f) b` requires re-execution or an
   admitted R4 attestation axiom. Any design that "loads a cache and returns a
   `Thm`" is a `⊢False` hole. Compounded by: (a) `rel_id ≠ TypeId` — `execute`'s
   gate is process-local `TypeId`, unstable across builds, so persistence needs a
   *content* identity per relation, an audit-sensitive table (new TCB the moment
   R4 trusts it); (b) R4 attestation keyed on a content address needs an
   **injective serializer** — a collision makes the axiom unsound.
4. **[C] ε-recursion / generalized-pattern coverage obligation.** `fixpoint_eq`
   and pattern desugaring are sound only if the existence/coverage `∃`-proof is
   *always* discharged before the defining equation is used — emitting it
   unconditionally admits a false axiom for non-terminating `F` (≡ `⊢False`).
   Mitigated by making the proof a required argument, but it is the sharp edge of
   that front.
5. **[E] Schema-variable trusted-grammar surface (deepest TCB surface of any
   front).** Forgery via a lying match is contained (`instantiate` is ∀-elim
   sound for any well-sorted σ; the matcher is untrusted and a wrong σ fails the
   structural `Eq` in `mp`/`eq_mp`, `eqn.rs:177`). Capture is vacuous
   (binder-free base). The genuine new trusted surface is the `Inst`/`Match`
   recursion — every arm must be exhaustive over the sealed grammar and
   sort-preserving. **The wall:** the clean shaped path works only when the
   target shape is statically known (holds for `execute` outputs); the general
   shape-**erased** case (`Box<dyn Expr>`/`Dyn<T>`, no `derive(Eq)`) needs either
   a trusted structural-eq decision procedure or a trusted `dyn` substitution
   walk — materially larger TCB, deferred-hard, not solved.
6. **[A] `defs/` existential residue (L4-gated).** `forall_spec()`
   (`thm/mod.rs:1055-1066`) and `and_spec()` (`typedef.rs:102`) recognize
   existentials/conjunctions by spec-handle pointer identity; sequent-reshaping
   cannot remove an existential conclusion, so a minimal `exists`/`and`
   vocabulary stays in core until the ε/rep/abs (L4) endgame.
7. **[A] EG4 `Dyn` structural transport is the one base-TCB delta on the near
   program.** Structural `eq_mp` for `Dyn` operands is a new innermost-TCB method
   requiring its own soundness audit; deferred, build only on real demand — do
   not improvise.
