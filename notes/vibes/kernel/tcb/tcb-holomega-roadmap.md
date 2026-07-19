+++
id = "N001A"
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

# TCB → HOL-ω Roadmap

Agent-authored synthesis reconciling five architect fronts (A–E) into one staged
program. File/type references are the architects'. Companion:
[`literal-endgame-design.md`](../literals/literal-endgame-design.md) (the leaf
mechanism), [`eg5-preflight.md`](../literals/eg5-preflight.md) (the EG5 swap plan).

Status note: fronts B-K1/B-K2/B-K3 and stages EG3a/EG3b/A3 have **landed**;
several §3 sketches remain unbuilt. Grounding numbers below are the snapshot at
authoring; check `tcb-audit.json` for live counts.

## 1. Context & vision

Goal: simplify the TCB toward a **textbook HOL-ω middle language**, most code
written Haskell-style above the kernel, and a **base that is a relation calculus
with untrusted computation**. Long-term punchline: schema variables + a
`Computation ⇒ Relation` metatheorem certifying WASM (and other executor) traces
with *one* admitted axiom instead of one per run.

Four layers:

- **Base** (`covalence-pure-trusted`, `crates/kernel/base/trusted`): a ground,
  first-order, **binder-free** `Expr` grammar over an open `Op<In,Out>` vocabulary.
  Sole mint is `pub(crate) Thm::new` (`eqn.rs`). Two evaluation mints: `canon`
  (functional equation `⊢ App<F,Val(v)> = Val(F.eval(v))`, gated on `F: CanonRule`)
  and `execute` (positive relation membership, `rel.rs`). Generic reflected
  type-rep landed (`tyrep.rs`: `TyFn`/`TyApp`).
- **Core** (`covalence-core`, `crates/kernel/hol/core`): HOL-Light-shaped, rank-1
  HOL. `TypeKind` has `TFree` but **no kinds, ranks, `TyAll`/`TyAbs`**. Terms
  locally-nameless de Bruijn; α-equivalence is structural `==`. TCB = the
  `Rule<CoreLang>` ZSTs, gated by `core_admits`, tier-generic over `HolTier`.
- **Eval** (`covalence-hol-eval`): derivation tier (`derived.rs`, `certs.rs`,
  `tohol.rs`).
- **Init / above**: untrusted library code emitting `Term`s and `Result<Thm>`s.

Two nearly-vanilla commitments + one exception:

- Middle becomes vanilla HOL-ω. **Rank stratification on `TyAll`/`TyInst` is a hard
  soundness requirement, not a feature** — unrestricted impredicative type
  quantification is inconsistent (Girard/type-in-type) over a HOL universe carrying
  choice.
- The deliberately non-vanilla thing is **DEFS**: definitions are values
  (Arc-identity `Def`, fresh tokens in `decide`), never a global mutable signature
  table. HOL-ω inherits this unchanged.
- Base stays binder-free; kinds are binder-free too (`κ ::= ⋆ | κ⇒κ`), so a
  reflected kind sort + total decidable kind/rank checkers fit as inert ops +
  `CanonRule`s.

## 2. Near-term program (additive-first, audited)

Front A (leaf-removal + `defs/` out of `hol/core`) and Front B (HOL-ω base
constructors). **Guiding invariant: zero base-TCB delta** — new rules mint through
the existing `covalence_pure::apply` gate; base mint sites stay fixed except the
explicitly-deferred EG4 (`Dyn` transport) and Front B's three enumerated `CanonRule`
mints. Additive/reversible first; irreversible maintainer-gated doors last.

### Front A — leaf removal + defs-out

Endgame: `covalence-core` = textbook equality-HOL — the manifest shrinks to
equality/subst core + `SelectAx` + `define`/`new_type_definition` + `nat_induct` +
nat freeness, `FalseElim` derived; `core::Term` has no literal leaves; `defs/` gone.

| Stage | Move | Reversible? | Gate | Status |
|---|---|---|---|---|
| **EG3a — `Zero` leaf** | `TermKind::Zero`+`Term::zero()`; rewire `ZeroNeSucc`/`NatInduct` off `nat_lit(0)`. Nat = `Zero`+`Succ` freely-generated. | additive | low-risk | **DONE** |
| **EG3b — T/F defined; FalseElim derived; connectives → CoreLang** | `T:=(λp.p)=(λp.p)`, `F:=∀p:bool.p` via `Define`; `⊢T` at `Thm<CoreLang>`; connective calculus drops to CoreLang; `FalseElim` removed, re-derived. | semi | **maintainer** | **DONE** (26→25) |
| **DEFS-OUT (sequent-reshape)** | Reshape `SuccInj`→`{succ m=succ n}⊢m=n`, `SelectAx`→`{p x}⊢p(ε p)`; `ZeroNeSucc`→connective-free ex-falso. Drop `imp`/`not` builders. | reversible in-kernel | maintainer-visible | **DONE** (coupling 37→29) |
| **Close float-op lander gap** | Symbolic landers for `sub`/`div`/`min`/`max`/rounding/compares/converts (only add/mul exist). | additive | maintainer (go/no-go for EG5) | OPEN |
| **EG5 — delete 5 literal leaves + manifest swap** | Admit permanent structural `toHOL` unfolding rules and **in the same commit** drop the transitional `*Val` reify rules — the `tohol_unfolding_rules_are_exclusive` guard forbids co-admission (would mint `⊢False`). Then delete `TermKind::{Nat,Int,SmallInt,Blob,Bool}` + Cluster A. | **NO — one-way** (deletes ctors, changes hashing/content-addresses) | **maintainer** | OPEN — see `eg5-preflight.md` |

**Residual `defs/` blocker:** `forall_spec()`/`and_spec()` recognize
existentials/conjunctions by spec-handle pointer identity for `spec_ax` /
`new_type_definition`. Sequent-reshaping cannot remove an *existential*
conclusion, so a minimal `exists`/`and` vocabulary stays as core residue until
**L4 (ε/rep/abs endgame)**.

**Deferred: EG4 — `Dyn` base transport.** Heterogeneous collections of symbolic
theorems (`Vec<Thm>` with different operand shapes) need erasure to `Thm<L,
Dyn<Term>>`; `Dyn` is pointer-eq, so `eq_mp`/`trans` cannot rewrite
structurally-equal different-allocation `Dyn`s. Fixing this is a **new base-TCB
method** — the one place this program touches the innermost TCB. Build only if a
real consumer needs it.

### Front B — HOL-ω base constructors (additive, reversible) — **DONE**

Adds Ty + KIND constructors and rules at the BASE. Kinds are binder-free (perfect
fit for the ground base); kind/rank synthesis are total decidable functions, hence
`CanonRule`s — the middle's kind/rank checker becomes a *consumer of base-minted
equations* rather than trusted middle code.

- **B-K1 — reflected Kind sort** (`kind.rs`): `KStar<K>` (`()→K`), `KArrow<K>`
  (`(K,K)→K`) as inert `Op`s, mirroring `tyrep.rs` (hand-written `Copy/Clone/Eq/
  Debug`, never `derive` — would spuriously demand `K: Clone`). Kind equality/
  congruence come free from `refl`/`cong_pair`/`cong_app`. **Zero TCB.**
- **B-K2 — higher-rank Ty ctors** (`tyrep.rs`): `TyBound<T>` (de-Bruijn tyvar),
  `TyAll<T,K>` (`(K,U32,T)`), `TyAbs<T,K>` (`(K,T)`). Structural eq on de-Bruijn
  spines **is** α-equivalence — no α-machinery. Malformed spine is *inert*, not
  *unsound*. **Zero TCB.**
- **B-K3 — KindOf/RankOf/RankLe** (`kindcheck.rs`): `CanonRule`s over an in-base
  demo rep (`TyC`/`KindC`): `⊢ kindof(τ)=κ`, `⊢ rankof(τ)=r`, `⊢ (r≤s)=T`.
  `RankOf` uses `rank(∀α:κ:r.τ)=max(r+1,rank τ)` with `saturating_add` (conservative
  direction). **KindOf MUST return `None` on ill-kinded input, never a wrong kind**
  (a wrong kind → false rank premise → defeats the `TyInst` gate). Three gated
  `canon` mints; audited SOUND. Computes/certifies but does **not** enforce
  stratification — that is the middle-level `TyInst` side-condition (§3).

## 3. Long-term vision (design sketches)

All of §3 is DESIGN SKETCH; none to be built now.

### Front C — Haskell-in-HOL-ω

**Reachable now with ZERO TCB delta** (untrusted `covalence-init`; kernel sees only
monomorphic HOL terms). Parser type: `Parser α := bytes → option (α × bytes)` (=
`StateT bytes Option`); the monad pieces already exist as eval defs (`sexpr_parse.rs`
already has `opt_bind` + hand-desugared `do`).

- **H0 — combinator library as HOL terms:** `pure`/`bind`/`map`/`alt`/`satisfy`/… +
  monad/alternative laws proved at each concrete element type (rank-1 fine).
- **H1 — typeclasses by compile-time dictionary passing:** `MonadDict {pure, bind}`;
  `instance Monad Maybe` = Rust value; `do{x<-p;k x}` → `bind d p (λx. k x)`. Laws
  proved once *per instance*; rank-n Haskell (`runST`) inexpressible — the gap HOL-ω
  buys.
- **H2 — general recursion via ε, gated defining-equation:** `rec_eps(F) := ε g. ∀x.
  g x = F g x` (always well-typed); **separate** `fixpoint_eq(F, exists_proof)`
  returns `⊢ f x = F f x` **only** when handed an unforgeable `∃g.∀x. g x = F g x`.
  **The one real soundness hazard:** `fixpoint_eq` must never mint unconditionally
  (would admit a false axiom for non-terminating `F` ≡ `⊢False`). API shape (proof
  as required argument) makes it un-hittable. Generalized patterns → ε carry the
  same coverage obligation.

The *general* theory of monads/optics with laws proved once over abstract `m` needs
abstracting over type operators, which rank-1 HOL cannot state — the HOL-ω middle.
H0–H2 surface is unchanged even in that future; HOL-ω only replaces per-instance
dictionaries with abstract law theorems and unlocks rank-n signatures.

### Front B-sketch — the HOL-ω middle in `core` (TCB-touching, gated)

Changes `Type`/`TypeKind` + the rule catalogue; maintainer-gated.

- **Type structure:** annotate `TFree` with `(Kind, Rank)`; add `TyBound(u32)`,
  `Kind (KStar | KArrow)`, `TyAll(Kind, Rank, Type)`, `TyAbs(Kind, Type)`.
  `Tycon`/`Spec`/`FreshTyCon` gain declared kinds (currently rank-0/⋆ ⇒
  backward-compatible). `type_of`/`check_sequent` gain a kind check consuming
  base-minted `KindOf`/`RankOf` (B-K3).
- **New rules:** `TyBeta`, `TyGen` (`TyAll`-intro, α∉Γ), and **`TyInst`**
  (`TyAll`-elim, generalizes `InstTFree`) — **requires `rank(σ) ≤ r` and `kind(σ) =
  κ`**.
- **`TyInst`'s rank side-condition is THE soundness-critical rule.** `rank(∀α:κ:r.τ)
  = max(r+1, rank(τ))`; `InstTFree` is the rank-0 case. Discharge the arithmetic via
  a base-minted `⊢ (rankof(σ)≤r)=T` premise (B-K3 `RankLe`). The
  `manifest_matches_golden` guard is the tripwire: no higher-rank rule enters
  `CORE_MANIFEST` until stratification is proven against the **full** rule set (esp.
  `SelectAx`/`bool`), Homeier-HOL-Omega-aligned.

### Front D — relation calculus as all computation

**Landed already exceeds the design's Phase 0:** `rel.rs` has
`UntrustedFn`/`RelErr::{Refused,Trapped}`/`Rel<F>`; `execute` (gated on
`TypeId::of::<Rel<F>>()`, zero-copy `Ref<Arc<_>>` leaves); the entire positive
calculus (`Transpose`/`Compose`/`Join`/`Meet`, complement deliberately absent). The
base **is** a relation calculus today.

- **Part 1 — `Lift : CanonRule → Rel`** (implement-now-capable): one untrusted
  wrapper `LiftFn<F: CanonRule>` with `run = self.0.eval(a).ok_or(Refused)`;
  `execute` mints membership, `canon` mints the equation. Functional vs relational =
  which theorem you want, one substrate. Zero new mint sites. *One-way-door sketch:*
  the full **Op/Val collapse** (delete `Val`, `Expr := Op<(),_>`, equality =
  diagonal relation) — never forced; the limit the lazy bridge converges to.
- **Part 2 — persist the relation graph:** a minted `⊢ a Rel(f) b` is
  content-addressable (`RelEdge { rel_id, addr_in, addr_out }`, operands as blobs in
  `ContentStore<O256>`). **R2 `StoreRel`** (buildable-soon): `execute` mints `⊢ addr
  Rel(Store) blob`; a miss soundly proves nothing. **R3 durable graph** (zero TCB):
  reload returns **bytes/edges, not theorems** — recovering `⊢ a Rel(f) b` needs
  re-execution or R4. Never hand back a forged `Thm`. **R4 attestation** (sketch):
  per-relation `Attested<K>` axiom keyed on a trust-store key; needs the PKI/`facts`
  module.
- **Part 3 — migrate computation:** parsers are natural `Rel` citizens (failure =
  `Refused` proves nothing). **Arithmetic certs stay functional deliberately** (HOL
  rewriting needs the equation; `Lift` lets them *also* be read relationally). WASM:
  `Rel(WasmRun{module})`; trap = `Err`; verified compilation = relational inclusion
  `graph(compile;wasm_eval) ⊆ graph(hol_eval)`.
- **Part 4 — trust story (positive-only):** `execute` grants only observed graph
  pairs, sound for *any* `f`, never mints `¬(a R b)`. Every negative/uniqueness/
  functionality conclusion is an admitted axiom (user's burden). R4 alone adds trust,
  through the ordinary admitted-axiom door.
- **Order:** R1 `LiftFn` → R2 `StoreRel` → R3 cache → parser-as-`Rel` demo → WASM.
  R4 + full Op/Val collapse are sketch, gated on PKI/facts + maintainer sign-off.

### Front E — `Expr<Ctx>` schema variables, matching, `Computation ⇒ Relation`, WASM

**Entirely LONG-TERM SKETCH.** Turn the per-computation axiom problem into *one*
schematic theorem + a matching rule.

- **Generalization:** `pub trait Expr<Ctx = ()>` recovers today's grammar as
  `Expr<()>`. `Var<const N: usize>` = a metalanguage **schema variable** (ZST index,
  NOT a HOL variable/binder). `CtxSort<N>` assigns sorts; `Var<N>: Expr<Ctx>` only
  where `Ctx: CtxSort<N>`. **`Ctx = ()` has no `CtxSort<N>`, so `Var<N>` is not an
  `Expr<()>`** — variables disallowed in the ground grammar. `Thm<L, P, Ctx = ()>`
  gains a context tier; the ground calculus is defined **only on `Thm<L,P,()>`** — a
  context-theorem is inert (type-level firewall).
- **Two new primitives:** `Inst<Ctx,Sigma>` (type-directed, sort-preserving by
  construction) + `instantiate<Sigma>` (schema ∀-elim, sound for any well-sorted σ).
  `Match<Ctx,Target>` is the dual (seed: existing `MatchApp`).
- **`Computation(i,o) ⇒ SomeRelation(i,o)` metatheorem:** lives in `Ctx=(In,Out)`;
  enters as **one admitted schematic axiom**. Per run: `execute` mints ground `⊢
  Rel<F>(i,o)`; untrusted `Match` picks σ; `instantiate(σ)` ⇒ `⊢ Comp⇒Rel`; `mp` ⇒
  `⊢ SomeRelation(i,o)`. Same axiom every run — no new axiom/manifest entry per
  computation.
- **WASM:** `Rel(F)=Rel(WasmRun)`, `SomeRel = WasmSpec`; schema `∀ i o. WasmRun(i,o)
  ⇒ WasmSpec(i,o)` (user asserts executor implements spec, differential-fuzzed out of
  band). Zero-copy leaves ⇒ O(1) certificate per trace.
- **De-risking probe (implement-now, zero TCB):** a type-level `schema.rs` adding
  `Var`, `CtxSort`, the `Expr<Ctx=()>` default, `Thm<_,_,Ctx=()>` — no mint site, no
  `Inst`/`Match`. Proves source-compatibility.

## 4. Sequencing

**Parallel now (additive, low/zero TCB):** Front B base ctors (DONE); Front A
additive stages (EG3a/b/DEFS-OUT DONE, float-lander gap OPEN); Front C untrusted
(H0→H1→H2, all in `covalence-init`); Front D lower rungs (R1→R2→R3→parser-as-Rel);
Front E's type-level probe.

**Hard sequencing:** Front A `EG3a, EG3b, DEFS-OUT, float-lander-gap` all precede
EG5 (irreversible), which precedes deleting `defs/` Cluster A; residual `defs/`
gated on L4. Front B-K3 precedes wiring `C = core::Type`. Front B-sketch gated on
the rank-stratification proof (nothing enters `CORE_MANIFEST` first). Front C's full
abstract-monad payoff requires Front B-sketch. Front D R4 gated on PKI/facts. Front
E's `Inst`/`Match`/schema-axiom deferred (full audited pass); the shape-erased
general matcher is a wall.

**Flagged tensions:** Fronts B and E both edit `expr.rs`/`tyrep.rs`-adjacent sealed
grammar (B adds *object-type* reflection, E adds a *metalanguage* `Var<N>` + `Ctx`)
— orthogonal in intent, coordinate on churn. Fronts A and D both touch computation
(A moves arithmetic to symbolic `toHOL` canon equations; D keeps certs functional +
adds a *relational view* via `Lift`) — agree, no migration. A's literal-leaf
deletion vs D's Op/Val collapse are independent layers (core term rep vs base
`Expr`), both one-way doors, maintainer-gated.

## 5. Open soundness walls

1. **[B, C] Rank stratification for HOL-ω is a hard consistency constraint.**
   `TyInst` must **reject** `rank(σ) > r`; the consistency argument must be re-run
   against the **whole** rule set (esp. `SelectAx`/`bool`) and adversarially audited.
   No higher-rank rule enters `CORE_MANIFEST` until specified + proven.
2. **[A] The EG5 exclusivity swap is the highest-risk near-term change.** Admitting
   structural `toHOL` unfolding rules and dropping `*Val` **must be one same-commit
   swap** (the guard exists because co-admission mints `⊢False`). Must reproduce
   every fact on **all inputs including wasm32** (the 32/64-bit divergence class that
   slipped past green tests). Irreversible.
3. **[D] Reload ≠ free theorems.** A persisted `RelEdge` is a *hint*; recovering `⊢ a
   Rel(f) b` needs re-execution or an admitted R4 axiom. "Load a cache and return a
   `Thm`" is a `⊢False` hole. Compounded by `rel_id ≠ TypeId` (process-local, unstable
   across builds → needs a content identity) and R4 needing an injective serializer.
4. **[C] ε-recursion / pattern coverage obligation.** `fixpoint_eq` + pattern
   desugaring are sound only if the existence/coverage `∃`-proof is *always*
   discharged before the equation is used. Mitigated by making the proof a required
   argument.
5. **[E] Schema-variable trusted-grammar surface (deepest TCB surface).** Forgery via
   a lying match is contained (`instantiate` is ∀-elim; a wrong σ fails structural
   `Eq` in `mp`/`eq_mp`). Capture is vacuous (binder-free base). The new trusted
   surface is the `Inst`/`Match` recursion — every arm exhaustive + sort-preserving.
   **The wall:** the clean path needs the target shape statically known; the general
   shape-**erased** case (`Box<dyn Expr>`/`Dyn<T>`, no `derive(Eq)`) needs a trusted
   structural-eq procedure or `dyn` subst walk — materially larger TCB, deferred-hard.
6. **[A] `defs/` existential residue (L4-gated).**
7. **[A] EG4 `Dyn` structural transport is the one base-TCB delta on the near
   program.** Build only on real demand — do not improvise.
