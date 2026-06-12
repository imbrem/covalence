# Stacked Pure + HOL MVP

> **STATUS: HISTORICAL — Pure layer fully collapsed into pure HOL.**
> Canonical reference is [`docs/kernel-design.md`](../../../kernel-design.md).
>
> This document originally described a strict two-layer split: a tiny
> Pure-only TCB (`covalence-pure`) with HOL as an untrusted layer
> above. The `kernel-design` branch first absorbed the Pure crate
> into `covalence-core`, then collapsed the Pure meta-layer entirely:
>
> - `TermKind::Imp / All / Eq` (Pure meta-connectives) — **deleted**.
> - `HolOp::Trueprop` — **deleted**.
> - `TypeKind::Prop`, `Type::prop()`, `Type::is_prop` — **deleted**.
> - The Pure-HOL bridge axioms (`eq_reflection`, `forall_reflection`,
>   `imp_reflection`) — **deleted**.
> - Every kernel axiom EXCEPT `nat_induction` — **deleted** (those
>   facts are derivable from `nat_induction` + the rule set +
>   `define`; until the WASM-proof rewrite, downstream consumers
>   postulate them via `Thm::assume(body)` with a self-hyp audit
>   trail).
>
> The current state is **pure HOL Light**: the 10 HOL Light primitive
> inference rules + 8 well-known derived rules added as kernel
> primitives ("easily auditable" derivations recorded in each
> docstring) + `weaken` + `define` + `new_type_definition` + the
> accelerated reduction rules (`reduce_prim`, `unfold_term_spec`)
> + the observer rules + `nat_induction`. The TCB sits around
> 3 KLoC of safe Rust.
>
> Sections below describe an intermediate revision (HOL folded but
> Pure-meta still present). For the *current* design read
> [`docs/kernel-design.md`](../../../kernel-design.md); for the
> evolution history, keep reading.
>
> Sibling to the [layered-framework
> proposal](../layered-framework/README.md). That proposal describes a
> ~700–800 LoC kernel with Store as a framework primitive and a wide
> conceptual surface (authorities, observations, ElidePolicy, federation,
> meta-trust vs trust set). This proposal is the *minimal* MVP version of
> the same shape — single document, ML-style data, no arena, no content
> addressing, no Store-as-primitive. The intent was to ship the smallest
> defensible bottom layer we could integrate with the rest of the system
> *first*, then grow upward. That goal is now substantially met.
>
> Read this before any of `02-framework.md` /
> `03-authority.md` / `04-store.md` — those add complexity that the MVP
> does not need. They become reachable refinements *after* this lands.
>
> This is the most explicit **Larry Paulson / Isabelle-Pure homage**
> in the repo: a tiny Pure substrate plus HOL as the kernel-level
> object logic, with everything else layered on top. In the vocabulary
> of [`../../../institution-map.md`](../../../institution-map.md), the
> Pure-shaped meta-logic is the candidate meta-institution and HOL is
> the default object institution — but they now live in the same
> trusted crate.

---

## 1. The two layers as landed

```
              ┌─────────────────────────────────────────────┐
              │  covalence-shell (bootstrap, untrusted)     │
              │  - OnceCell anchors for stdlib constants    │
              │  - BlobSource impl (memory / sqlite / git)  │
              │  - Prover-API adapter, NotImplemented stubs │
              └────────────────┬────────────────────────────┘
                               │ depends on
              ┌────────────────▼────────────────────────────┐
   Shell     │  covalence-hol (untrusted)                  │
              │  - HOL Light builder API (HolLightCtx,      │
              │    PureHol, the kernel traits)              │
              │  - nat_axioms / int_axioms (Thm::assume     │
              │    postulates with audit-trail hyps)        │
              │  - Content hashing (BLAKE3-keyed)           │
              │  - Canonical S-expression syntax            │
              │  - Subset types via disjunct trick          │
              │  - WASM-oracle adapter (observation axioms) │
              └────────────────┬────────────────────────────┘
                               │ depends on
              ┌────────────────▼────────────────────────────┐
   TCB       │  covalence-core (no unsafe)                 │
              │  - Term/Type: Arc<Node>, ML-style           │
              │  - 8 LF rules + equality (refl/cong/β/η)    │
              │  - define + new_type_definition             │
              │  - HOL primitives folded in:                │
              │      TermKind::Bool(bool)                   │
              │      TermKind::HolOp(HolOp, Type)           │
              │        — Eq, Imp, Not, And, Or, Iff,        │
              │          Forall, Exists, Select, Trueprop   │
              │  - Bona-fide HOL axioms (empty hyps):       │
              │      Thm::nat_induction                     │
              │      Thm::eq_reflection                     │
              │      Thm::forall_reflection                 │
              │      Thm::imp_reflection                    │
              │  - Observer hooks (obs_eq/obs_true/obs_imp) │
              │    for non-HOL observer systems             │
              │  - Bytes / Nat / Int as kernel-primitive    │
              │    types/terms                              │
              └─────────────────────────────────────────────┘
```

**TCB = `covalence-core`.** A bug in `covalence-hol` (the HOL Light
builder, the postulated `nat_axioms` / `int_axioms`, the disjunct
trick) cannot produce a false `Thm`. A bug in the WASM oracle adapter
cannot produce a false `Thm`. Soundness reduces to `covalence-core`'s
rule and axiom set, reviewed module-by-module.

### Why HOL ended up in the TCB

The original sketch treated HOL as a strict layer above Pure. The
fold trades a little extra reviewed code for two real wins:

- **`nat_induction` is a real axiom.** If induction were a
  `Thm::assume` postulate, every downstream theorem that used
  induction would carry the induction axiom as a hypothesis
  forever. That made the audit trail honest but the proof terms
  noisy — and the noise compounded as more induction principles
  (over `int`, `bool`, future `define_type` outputs) accumulated.
- **HOL is the substrate for internal logics.** When you internalize
  PA, ZF, Tarski reals, or HOL-inside-HOL, the meta-theorems live
  in `bool` and `nat` from this kernel. Putting HOL in the kernel
  means internal logics inherit the kernel's `bool` reasoning
  machinery for free.

The observer machinery (`obs_eq`, `obs_true`, `obs_imp`) is *not*
gone — it remains as the kernel's pluggable computational hook
for **other** observer systems (Store membership, BLAKE3 identity,
WASM oracle outputs, …). HOL is no longer one of those; it's the
substrate they all live over.

---

## 2. The TCB — `covalence-core`

Isabelle/Pure–shaped logical framework with HOL folded in. Small
enough that a reviewer can hold the rule set in their head; the
HOL-specific additions are concentrated in one module
(`hol.rs`) and four axiom rules.

### 2.1 Data: ML-style `Arc<Node>`

No arena, no `TermId`, no hashing. A term is a plain Rust value; two
α-equivalent terms compare equal by structural recursion. Sharing via
`Arc` is an incidental optimization — never load-bearing.

```rust
use std::sync::Arc;
use smol_str::SmolStr;
use bytes::Bytes;
use covalence_types::{Nat, Int};

#[derive(Clone, Hash, PartialEq, Eq)]
pub struct Term(Arc<TermKind>);

#[derive(Hash, PartialEq, Eq)]
enum TermKind {
    // Pure meta-level
    Bound(u32),                            // de Bruijn
    Free(SmolStr, Type),                   // named free var
    Const(SmolStr, Type),                  // declared / defined constant
    App(Term, Term),
    Abs(BinderHint, Type, Term),           // λx:τ. body
    Imp(Term, Term),                       // meta-implication φ ⟹ ψ
    All(BinderHint, Type, Term),           // meta-universal ⋀x:τ. body
    Eq(Term, Term),                        // meta-equality t ≡ u
    Def(Def),                              // Arc-identity defined constant

    // Kernel-primitive value types
    Blob(Bytes),                           // BUILTIN: first-class bytes
    Nat(Nat), Int(Int),                    // arbitrary-precision literals
    Prim(Prim),                            // builtin function (NatArith, …)
    Bool(bool),                            // HOL true / false

    // HOL primitives, folded in
    HolOp(HolOp, Type),                    // Eq, Imp, Not, And, Or, Iff,
                                           // Forall, Exists, Select, Trueprop

    // Observation leaf (for non-HOL observer systems)
    Obs(Object, Type),
}

#[derive(Clone, Hash, PartialEq, Eq)]
pub struct Type(Arc<TypeKind>);

#[derive(Hash, PartialEq, Eq)]
enum TypeKind {
    TFree(SmolStr),                                  // type variable
    Prop,                                            // kind of metaprops
    Bytes, Nat, Int,                                 // primitive value types
    Fun(Type, Type),
    Tycon(SmolStr, Vec<Type>),                       // structural tycon
    TyConObs(Object, BinderHint, Vec<Type>),         // identity-based tycon
                                                     // (typedef minted)
}
```

**Why blobs are a kernel primitive.** Big data must be representable in
the logic without us copying it. `Blob(Bytes)` lets the kernel reference
a byte sequence by Arc-share; structural equality is byte equality,
which is cheap when the Arcs share. The kernel *does not* hash blobs —
that's an upper-layer concern (`covalence-hash` outside the TCB). The
kernel just gives us a way to talk about arbitrary bytes inside terms.

**Why `Nat`/`Int`/`Bool` are kernel primitives.** Same argument: big
data (arbitrary-precision arithmetic, large boolean computations)
needs first-class representation. `Thm::reduce_prim` decides closed-form
arithmetic on `NatArith`/`IntArith`/`BytesCat`/… by reflexivity, so the
kernel knows that `Prim::NatArith(Add) (Nat 2) (Nat 3) ≡ Nat 5` without
the user having to derive successor unfoldings.

### 2.2 Theorems

```rust
#[derive(Clone)]
pub struct Thm {
    hyps:  Ctx,      // structurally-shared BTreeSet<Term>, each of kind prop
    concl: Term,
}
```

`Thm` has no public constructor. The only way to obtain one is by calling
a kernel rule. Soundness is constructional in the LCF sense.

### 2.3 The rule set

Eight LF rules + six equality rules + β + η + `inst_tfree` +
`define` + `new_type_definition` + observation hooks + the four
bona-fide HOL axioms.

```
[φ] ⊢ φ                                                    (assume)

Γ ∪ {φ} ⊢ ψ                       Γ ⊢ φ⟹ψ      Γ' ⊢ φ
─────────────  (imp-intro)        ──────────────────────  (imp-elim / MP)
Γ ⊢ φ ⟹ ψ                              Γ ∪ Γ' ⊢ ψ

Γ ⊢ φ(x)    x ∉ FV(Γ)             Γ ⊢ ⋀x:τ. φ(x)    ⊢ t : τ
─────────────────────  (all-i)    ──────────────────────────  (all-e)
Γ ⊢ ⋀x:τ. φ(x)                          Γ ⊢ φ(t)

Γ ⊆ Δ                             Γ ⊢ p ≡ q     Γ' ⊢ p
──────────  (weaken)              ─────────────────────  (eq_mp)
Γ ⊢ φ                                  Γ ∪ Γ' ⊢ q
given Γ ⊢ φ

⊢ t ≡ t  (refl)    Γ⊢t≡u, Γ'⊢u≡v ⇒ Γ∪Γ'⊢t≡v  (trans)    sym
(cong-app, cong-abs)        ⊢ (λx.M) N ≡ M[N/x]  (β)     ⊢ λx.f x ≡ f  (η, x∉FV(f))

c fresh, d closed, d:τ
──────────────────────  (define)        and  inst_tfree(α, σ, Thm)
⊢ c ≡ d

Γ ⊢ P x                                ⊢ Prim p applied to literals reduces
─────────────────  (new_type_def)      ─────────────────────────────────  (reduce_prim)
⊢ abs∘rep = id_τ                              ⊢ lhs ≡ rhs
⊢ P r ⟹ rep(abs r) ≡ r
⊢ rep(abs r) ≡ r ⟹ P r

Bona-fide HOL axioms (each ⊢ … with empty hyps):
   ⊢ Trueprop (∀P:nat→bool. P 0 ∧ (∀n. P n ⟹ P (succ n)) ⟹ ∀n. P n)   (nat_induction)
   ⊢ ⋀x y:'a. Trueprop (x = y) ≡ (x ≡ y)                                (eq_reflection)
   ⊢ ⋀P:'a→bool. (⋀x. Trueprop (P x)) ≡ Trueprop (∀x. P x)              (forall_reflection)
   ⊢ ⋀P Q:bool. (Trueprop P ⟹ Trueprop Q) ≡ Trueprop (P ⟹ Q)            (imp_reflection)

Observer hooks (sound under parametric ε-model, policy in user code):
   obs_eq<O: ObsEq>     — equate two obs-headed applications
   obs_true<O: ObsTrue> — assert a prop-typed obs application
   obs_imp<O: ObsImp>   — emit a lazy implication chain
```

Plus the observer mechanism (next section) for non-HOL systems.

### 2.4 Observer systems (non-HOL)

The pluggable computational hook. HOL no longer lives here — it's
in the kernel above. What remains is the **per-Rust-type observer
policy**, sound under a parametric ε-model regardless of what any
particular policy returns.

```rust
pub trait Observer: Any + Send + Sync + Debug {}
impl<T: Any + Send + Sync + Debug> Observer for T {}

pub trait ObsEq: Observer {
    fn obs_eq(&self, other: &Self, my_args: &[Term],
              other_args: &[Term], hint: Option<&dyn Hint>) -> bool;
}

pub trait ObsTrue: Observer {
    fn obs_true(&self, args: &[Term], hint: Option<&dyn Hint>) -> bool;
}

pub trait ObsImp: Observer {
    fn obs_imp(&self, args: &[Term], hyps: &[Term],
               hint: Option<&dyn Hint>) -> bool;
}

impl Thm {
    pub fn obs_eq<O: ObsEq>(e1: Term, e2: Term, hint: …) -> Result<Thm>;
    pub fn obs_true<O: ObsTrue>(expr: Term, hint: …) -> Result<Thm>;
    pub fn obs_imp<O: ObsImp>(expr: Term, hyps: Vec<Term>, hint: …) -> Result<Thm>;
}
```

The kernel compares `Obs` leaves by `Arc` pointer identity (via
`Object`) — never by the user's `Eq`. A misbehaving observer impl
cannot corrupt the kernel's `Ctx` invariants or compromise soundness.

**Soundness story.** Different Rust observer types `O`, `O'` get
independent ε-families in the model: any `(obs O)(args…)` whose
final Pure type is τ interprets to `ε_O(τ)`, and `obs_eq`/`obs_true`
return either-answer-sound. So a policy choice — or a bug — in
`Blake3System` cannot affect equations involving `StoreSystem`. The
kernel's downcast check ensures the policy is only invoked when the
heads downcast to the requested type.

**Intended consumers.** Store membership (`StoreSystem`), BLAKE3
identity (`Blake3System`), WASM oracle outputs, future SAT/SMT
bridges. *Not* HOL — HOL's primitives are kernel-native now, so
HOL theorems are produced via `Thm::nat_induction`, the reflection
axioms, and the regular LF rules.

### 2.5 What's deliberately absent

- No content addressing (no `O256`, no `ContentHash`, no Phase H).
- No `BlobStore`, no `BlobSource`, no IO of any kind.
- No signature verification.
- No WASM engine.
- No egraph, no union-find, no Phase P EProp/EThm.
- No `Decision::Sat/Unsat`.
- No `serde` on `Thm`. No serialization at all.
- No standard library beyond the bootstrap primitives. `define_type`
  for non-`nat` recursive types lives in `covalence-hol`.

These all live above the line and are added as untrusted upper layers.

### 2.6 Module shape

| Module        | Purpose                                                       |
|---------------|---------------------------------------------------------------|
| `term.rs`     | `Term`/`Type`, `TermKind` (incl. `Bool`/`HolOp`), smart ctors |
| `subst.rs`    | β/η, capture-avoiding substitution, `inst_tfree`              |
| `ctx.rs`      | `Ctx`: structurally-shared hypothesis context                 |
| `builtins.rs` | Closed-form reduction for `Prim`/`Bool` literal applications  |
| `hol.rs`      | Cached HOL axiom-conclusion terms (consumed by `thm.rs`)      |
| `thm.rs`     | `Thm`, LF + equality + `define` + `new_type_definition`        |
|              | + observer hooks + the four bona-fide HOL axioms              |
| `error.rs`    | `thiserror` errors                                            |

Direct deps: `covalence-types` (`Nat`/`Int`), `smol_str`, `bytes`,
no `im` (the `Ctx` abstraction wraps `Option<Arc<BTreeSet<Term>>>`).
No `unsafe`, no IO, no Tokio, no WASM, no signature crate.

---

## 3. The shell — `covalence-hol`

Untrusted. Two roles after the fold: a **HOL Light builder API**
over `covalence-core`'s folded-in primitives, plus the
**term/type serialisation** layer (content hashing + canonical
S-expression syntax) absorbed from the deleted `covalence-pure-shell`.

A bug anywhere in this crate cannot produce a false `Thm` — the worst
it can do is build an unintended-but-well-formed term, or fail to
construct the theorem you wanted.

### 3.1 What this crate adds

1. **`HolLightCtx` / `PureHol`** — builder structs that produce HOL
   terms via the kernel's `HolOp`/`Bool` primitives. The `HolLightTerms`
   and `HolLightTypes` traits give the canonical constructor surface
   (`mk_eq_at`, `mk_forall_at`, `mk_imp`, etc.) so downstream code
   doesn't deal in raw `HolOp(_, _)` values.

2. **Postulated stdlib axioms** (`nat_axioms`, `int_axioms`) —
   theorems introduced via `Thm::assume`, with self-hyp audit trail.
   These are *not* bona-fide kernel axioms; they're convenience
   postulates that downstream code can grep for. Definitional axioms
   (`op ≡ recursor base step args`) are preferred over derived facts
   like commutativity / associativity, which are proved on top.

3. **The 10 HOL Light rules**, derived — `REFL`, `TRANS`, `MK_COMB`,
   `ABS`, `BETA`, `ASSUME`, `EQ_MP`, `DEDUCT_ANTISYM_RULE`, `INST`,
   `INST_TYPE`. None of them are kernel primitives; each is a
   sequence of core rule calls in `pure_hol.rs`. Most reduce to
   one-line calls through the four bona-fide reflection axioms.

4. **Subset types** — via the disjunct trick (see
   [`ARCHITECTURE.md`](../../../../ARCHITECTURE.md) §2.4); wraps
   `Thm::new_type_definition` with a `Q := λx. P x ∨ x = ε P`
   synthesis so the inhabitedness witness is reflexive and the
   user doesn't supply one. **Status:** planned; the kernel rule
   is in place but the wrapper isn't yet built (see
   [`next-stages.md`](./next-stages.md) §A).

5. **`define_type` / inductive types** — the construction that takes
   a recursive type spec (`PTerm = Zero | Suc PTerm | …`) and
   returns the type, constructors, injectivity theorems, induction
   principle, and recursor. **Not yet built**; this is the gate to
   the internal-logic work (PA, semiring, HS, internal HOL).

6. **Content hashing (`hash.rs`) and canonical S-expression syntax
   (`sexp.rs`)** — formerly in `covalence-pure-shell`. The kernel
   does not hash terms; this layer provides BLAKE3-keyed hashing
   and the dialect-aware sexp serialisation used by every shell crate.

### 3.2 The standard library is BLAKE3-keyed blobs

The HOL stdlib is a directory of blobs. Each blob is an S-expression
script (the `covalence-sexp` dialect already exists in the repo) that
issues a sequence of Pure operations to materialise one entry:

- a type constructor declaration,
- a constant definition (which yields a `Thm` for the unfolding equation),
- a derived theorem (a sequence of HOL rule calls producing a `Thm`).

The shell layer drives loading via a `BlobSource`:

```rust
pub trait BlobSource: Send + Sync {
    fn get(&self, key: blake3::Hash) -> Result<Bytes>;
}

pub struct StdRef(pub blake3::Hash);

pub struct HolStd {
    cache: RwLock<HashMap<StdRef, StdEntry>>,
}

pub enum StdEntry {
    TyCon { name: SmolStr, arity: u32 },
    Const { name: SmolStr, ty: Type, defn: Thm },
    Theorem(Thm),
}

impl HolStd {
    pub fn load(
        &self,
        ctx: &mut covalence_hol::HolLightCtx,
        source: &dyn BlobSource,
        key: StdRef,
    ) -> Result<&StdEntry>;
}
```

Two consequences:

- **Swapping the stdlib** is a matter of a different set of blobs over
  the same TCB. ZFC instead of HOL? Different blobs. Different
  foundational choice? Different blobs.
- **Reproducibility** comes from blob bytes + a fixed Pure kernel
  binary. The BLAKE3 hashes are content addresses outside the TCB;
  they don't need to match across consumers, only across instances
  trying to reproduce the same theorem.

The kernel binary commits to **one** BLAKE3 hash — the *manifest hash* —
which is a blob listing the BLAKE3 hashes of every stdlib entry. The
manifest is loaded once during bootstrap; everything else is reachable
from it. That single hash is the only "trust anchor" baked into the
binary.

### 3.3 WASM observation oracles

WASM oracles live above the kernel. They're how we extend the prover
with computational evidence (decide procedures, hash functions,
signature checks, anything we can package as a WASM component) without
growing the TCB. They're built on the kernel's observer hooks
(`obs_true`/`obs_imp`/`obs_eq`) plus user-asserted meaning-axioms.

Concretely: each oracle family is a `Rust` type implementing
`ObsTrue` / `ObsImp`; instances of that type appear as `Term::obs`
leaves. The policy method runs the WASM component and decides
whether to mint the theorem.

```rust
pub struct WasmOracle {
    component_hash: blake3::Hash,           // identifies the component
    runner: Arc<dyn WasmRunner>,            // backed by covalence-wasm
}

impl ObsTrue for WasmOracle {
    fn obs_true(&self, args: &[Term], _hint: Option<&dyn Hint>) -> bool {
        // Run the WASM component; return whether the prop-typed
        // observation `(obs self)(args…)` should be minted.
        …
    }
}
```

**Meaning-axioms are user-asserted via `Thm::assume`.** Whatever the
user assumes about the oracle (e.g. `⊢ ⋀x. eval(component_hash, x) ⟹
φ(x)`) is recorded as a hypothesis on every theorem that depends on
the oracle's output, exactly like any other assumption. To export a
theorem stripped of these hypotheses, the user must either (a) prove
the meaning-axiom from below — usually impossible by construction,
since it's a claim about a computational artifact — or (b) discharge
it via `imp_intro`, making the dependence explicit in the theorem's
*statement*.

This is HOL Light's `mk_thm` discipline, applied to an entire family of
oracles uniformly.

### 3.4 Shape and dependencies

| Module            | Purpose                                              |
|-------------------|------------------------------------------------------|
| `hol_light_obs.rs`| `HolLightCtx`: HOL Light builder context             |
| `pure_hol.rs`     | `PureHol`: the 10 HOL Light rules over core's API    |
| `nat_axioms.rs`   | Postulated nat stdlib axioms (Thm::assume w/ hyps)   |
| `int_axioms.rs`   | Postulated int stdlib axioms (Thm::assume w/ hyps)   |
| `traits.rs`       | `HolLightKernel` / `HolLightTerms` / `HolLightTypes` |
| `types.rs`        | `HolError`, `NameId`, canonical const IDs            |
| `hash.rs`         | BLAKE3-keyed content hashing (term/type/Thm)         |
| `sexp.rs`         | Canonical S-expression serialisation                 |

Direct deps: `covalence-core`, `covalence-sexp` (sexp dialect),
`covalence-hash` (BLAKE3 — used as a key + for term hashing, not
for kernel rules). No `covalence-wasm` dep at this layer — the WASM
oracle adapter lives in whichever crate registers WASM components
(currently `covalence-shell`).

---

## 4. Bootstrap — `covalence-shell`

The shell shrinks to two responsibilities:

1. **Bootstrap.** Initialize the kernel, choose a `BlobSource`, load the
   stdlib manifest, populate well-known HOL identifiers behind
   `OnceCell`s.
2. **Adapter for the existing `Prover` API** so downstream callers
   (REPL, server, LSP, OpenTheory) keep compiling. Operations whose
   upper layer isn't built yet return `ProverError::NotImplemented`.

```rust
pub struct Shell {
    pub hol: covalence_hol::HolLightCtx,   // wraps a core::Thm builder
    pub std_store: OnceCell<Arc<dyn BlobSource>>,
    pub anchors: OnceCell<StdlibAnchors>,
}

/// The interned HOL constants the shell makes globally available.
/// All Term/Type values — no IDs — because the kernel has no IDs.
pub struct StdlibAnchors {
    pub bool_ty: Type,
    pub eq_const: Term,        // = : α → α → bool
    pub and_const: Term,
    pub or_const: Term,
    pub not_const: Term,
    pub implies_const: Term,
    pub forall_const: Term,
    pub exists_const: Term,
    pub eps_const: Term,
    // and any other anchor terms downstream consumers expect
}

impl Shell {
    pub fn new() -> Self;

    /// Idempotent. Reads the stdlib manifest blob (whose BLAKE3 hash is
    /// hardcoded in the binary), then for each entry referenced by the
    /// manifest, loads its blob through `store` and materialises it
    /// into the kernel. Populates `anchors` from the well-known names.
    pub fn bootstrap(&self, store: Arc<dyn BlobSource>) -> Result<&StdlibAnchors>;
}
```

The shell holds the **single trust anchor of the whole system**: the
hardcoded BLAKE3 hash of the stdlib manifest. Everything else is
reachable from it. We can think about removing even that later (passing
the manifest hash as a CLI flag, signing it, treating it as an
oracle observation about the standard library), but for the MVP it is a
constant in the source.

### 4.1 The `Prover` adapter

Strategy: keep the trait surface that REPL/serve/LSP already use; rewire
implementations onto the new stack one operation at a time.

| Existing `Prover` API                                | MVP plan                                                  |
|------------------------------------------------------|-----------------------------------------------------------|
| `assume`, `imp_intro`, `imp_elim`, `define`, `mk_term`, `mk_type` | Direct port to the new stack. |
| `refl`, `trans`, `sym`, `mk_comb`, `abs`, `beta`, `eq_mp`, `deduct_antisym`, `inst`, `inst_type` | Direct port via `covalence-hol::rules`. |
| OpenTheory article import                            | Restored once HOL Light rules are derived.                |
| `decide`, `attest`                                   | `NotImplemented`. Will live in a separate `covalence-decide` crate that registers WASM oracles and discharges meaning-axioms — completely above the kernel. |
| `egraph_*`, `eprop_*`                                | `NotImplemented`. New crate above the kernel; the egraph becomes a fact-store sidecar, not part of the TCB. |
| `serialize_thm`, `thm_content_hash`                  | `NotImplemented`. Content-hash of `Thm` lives in an upper-layer crate over the new data model. |

Frontends compile; some commands say "not yet."

---

## 5. Why this works (and why it's worth replacing the current kernel)

**Soundness.** The Pure-shaped backbone is well-trodden LF. The
literature on this (Isabelle/Pure, HOL Light, λΠ-calculus) is enormous;
the rules have been audited for decades. Our additions over textbook
Pure are:

- `define` — standard conservative-extension rule.
- `new_type_definition` — standard HOL Light-style subtype rule,
  fresh identity via `Arc::ptr_eq`.
- The observer hooks (`obs_eq`/`obs_true`/`obs_imp`) — pluggable
  conservative trust hooks, sound under the parametric ε-model for
  every Rust observer type independently.
- `Blob`/`Nat`/`Int`/`Bool` term forms + the `Prim` builtins — no
  inference power; just kernel-primitive value types with a
  closed-form `reduce_prim` decision rule.
- The four bona-fide HOL axioms (`nat_induction`, `eq_reflection`,
  `forall_reflection`, `imp_reflection`) — each a single `Thm` with
  empty hyps. The kernel commits to its `nat` type denoting the
  standard naturals and to HOL `=`/`∀`/`⟹` denoting the corresponding
  meta-level constructs; soundness reduces to that semantic commitment.

**Locality.** No content addressing in the TCB means no SHAttered-style
crypto assumption is ever asserted by the kernel itself. The kernel says
"`R` is an opaque relation, here is a fact under it." The decision to
trust that the relation corresponds to anything in the world lives in a
meaning-axiom that sits in the hypothesis set of every theorem that uses
it.

**Big data.** `Blob(Bytes)` + `Arc` sharing means a 10 GB blob mentioned
in a theorem doesn't get copied. Equality on shared blobs is `Arc::ptr_eq`
in the fast path. If two unrelated blobs happen to be byte-equal, the
fallback is byte comparison; the kernel doesn't care which because the
result is the same.

**Self-edit.** Replacing the standard library is a different blob set
under the same TCB. Replacing the WASM oracle runtime is a different
`dyn WasmRunner` impl under the same TCB. Replacing the BlobSource
backend is a different `dyn BlobSource` impl under the same TCB.
**Replacing the kernel itself** is what we *don't* want to do casually;
that's the whole point of keeping it tiny. The MVP can be optimized
later (an arena, content hashes, an egraph) by writing those above the
line and proving the optimizations are sound — exactly the
"self-edit into a more optimal form without trusting the optimal form"
the user asked for.

**Bootstrap is honest.** OnceCells in the shell are visibly upper-layer.
The kernel doesn't know they exist; it doesn't see the stdlib manifest
hash; it doesn't see the `BlobSource`. If the user wants to use the
kernel without the shell — to drive it directly from a Rust program for
audit, testing, or research — they can. The shell is convenience.

---

## 6. Build order

Each step is a self-contained PR with its own test. **Steps 1-6
have landed** as of the `kernel-design` branch; steps 7+ are the
remaining work toward the internal-logic story.

1. **`covalence-core` rules.** ✅ `Term`, `Type` (incl. `Bool`,
   `HolOp`, `TyConObs`), substitution, β/η, `Thm`, the 8 LF rules
   + 6 equality rules + `inst_tfree` + observer hooks. Tests:
   `⊢ (λx.x) y ≡ y`; `⊢ ⋀x. x ≡ x`.
2. **`Thm::define` + `Thm::new_type_definition`.** ✅ Fresh `Arc`-
   identity definitions; fresh subtype τ ≤ α with bijection theorems
   under a witness `⊢ P x`. Tests cover polymorphic typedef.
3. **Bona-fide HOL axioms folded in.** ✅ `Thm::nat_induction`,
   `eq_reflection`, `forall_reflection`, `imp_reflection` — each
   with empty hyps, conclusion-term cached via `LazyLock<Term>`.
4. **`covalence-hol` builder API.** ✅ `HolLightCtx`, `PureHol`, the
   `HolLightKernel`/`HolLightTerms`/`HolLightTypes` traits, the 10
   HOL Light rules derived from the core's reflection axioms +
   regular LF rules.
5. **`nat_axioms` / `int_axioms` postulates.** ✅ Definitional axioms
   via natrec/recursor; derived commutativity / associativity etc.
   proved on top rather than postulated.
6. **Hash + sexp absorption.** ✅ `covalence-pure-shell` deleted;
   its `hash` and `sexp` modules merged into `covalence-hol`.
7. **Polymorphic typedef wrapper in `covalence-hol`.** Lift the
   `pure_hol.rs:new_basic_type_definition` rejection of polymorphic
   carriers — the kernel rule handles it; only the wrapper needs
   `mk_tyapp` plumbing. **Pending.**
8. **`define_type` derived rule.** Take a recursive type spec like
   `nat = Zero | Suc nat`; return the type via `new_type_definition`
   over a `bytes`-encoded carrier, constructor terms, injectivity
   theorems, an induction principle, and a recursor. **Pending —
   gate to the internal-logic work.**
9. **Disjunct-trick subtype wrapper.** Wrap `new_type_definition`
   with `Q := λx. P x ∨ x = ε P` so the inhabitedness witness is
   reflexive and the user doesn't supply one. **Pending.**
10. **Stdlib loader.** `BlobSource`, manifest blob format, lazy
    materialisation, `HolStd::load`. Test: bundle a tiny stdlib,
    bootstrap from it, look up `bool` and `=`. **Pending.**
11. **WASM oracle adapter via `ObsTrue` / `ObsImp`.** WASM-component
    runners as observer-Rust-types; meaning-axioms via `Thm::assume`.
    **Pending.**

Steps 7-9 unlock the internal-logic ladder (PA, commutative semiring +
bicartesian categories, high school axioms + BCCCs, internal HOL).
Steps 10-11 round out the runtime story.

---

## 7. Relationship to existing proposals

- **[`../layered-framework/`](../layered-framework/)** —
  this proposal is the MVP version of the same architecture. The
  `layered-framework` docs add Store-as-primitive (`04-store.md`),
  ElidePolicy (`05-trust.md`), explicit federation (`09-federation.md`),
  meta-trust vs trust set (`05-trust.md`), and a few other things this
  MVP defers. After the MVP lands, those become refinements added one
  by one, each as its own PR.

- **[`../shared-backbone/`](../shared-backbone/)** —
  the operational path. Its Phase 0 (kill list) and Phase 1 (substrate)
  remain unchanged. This proposal *is* its Phase 2 prover stream, with
  P1–P5 collapsed into the six steps in §6.

- **[`../layered-framework/notes/facts-not-proofs.md`](../layered-framework/notes/facts-not-proofs.md)**
  — the operating principle for the bottom layer. This proposal adopts
  it: the bottom layer stores facts, not justifications. No `Proof`
  type, no derivation tree, no rule-trail.

- **[`../../../prover-architecture.md`](../../../prover-architecture.md)**
  — the *current* kernel's design (~6000 LoC). Fully superseded by this
  proposal. The current crate stays in the workspace under a
  `references/` move (per `shared-backbone` Phase 0) while the new
  stack lands.

- **[`../../../prover-mvp-plan.md`](../../../prover-mvp-plan.md)** —
  superseded; replaced by §6 above.

- **[`../../../../MVP_DESIGN.md`](../../../../MVP_DESIGN.md)** —
  superseded as a kernel design; the `attest`/`decide` mechanism
  relocates intact to the WASM oracle adapter at the HOL layer (§3.3).

---

## 8. Open questions

These are decidable but not blocking the design. Listed so they don't
get lost.

- **`AuthorityId` collisions.** Process-local `u64` from a counter is
  fine for the MVP; if we ever want to compare Authorities across
  sessions we'll move to a 128- or 256-bit fresh value. Counter is
  enough for now.
- **Hypothesis representation.** `im::OrdSet<Term>` for cheap union;
  could be `Arc<[Term]>` if we want canonical ordering for content
  hashing later. MVP picks `im::OrdSet` for ergonomics.
- **`Blob` and α-equivalence.** Blobs are constants (no binding
  structure), so they're trivially α-stable. No interaction with de
  Bruijn shifting.
- **Whether `Blob` has a kind other than `Type`.** We keep `Blob`-the-type
  at the same kind as other object types so HOL theories can reference
  it. No kind hierarchy needed.
- **η in the kernel?** Yes — Pure style. HOL Light omits it; including
  it costs nothing for us and simplifies definitional unfolding.
- **Should `observe` allow non-closed args?** Default: no, args must be
  closed. Keeps the safe-axiom invariant clean.
- **Stdlib script format.** S-expression dialect via `covalence-sexp`;
  one form per Pure operation. Keep it boring; it's the bootstrap
  input, not a language.
- **Manifest hash committing.** Hardcoded `const` in the shell for the
  MVP. Move to "supplied at bootstrap" once the federation story is in
  place.

---

## 9. What this enables next

Once the MVP is shipping, the following land as ordinary upper-layer
crates without touching the TCB:

- **`covalence-decide`** — drives WASM oracles for SAT/SMT-style
  questions; produces `Thm` or "I don't know."
- **`covalence-egraph`** — facts-as-storage egraph (per the
  `facts-not-proofs.md` discipline); union-find + congruence over
  stored `Thm`s.
- **`covalence-content-hash`** — `Thm` content-addressing, with a
  canonicalization pass over the ML-style data. Lives above the line so
  changing the canonical form doesn't move the TCB.
- **`covalence-federation`** — signed `Thm` exchange between kernels;
  the only cross-process trust path.
- **`covalence-opentheory` (port)** — article import, retargeting onto
  the new HOL Light rules.

Each one is a separate concern, each one orthogonal to soundness.
