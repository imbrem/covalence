# Stacked Pure + HOL MVP

> **STATUS: PROPOSED — focused MVP sketch.**
>
> Sibling to the [layered-framework
> proposal](../layered-framework/README.md). That proposal describes a
> ~700–800 LoC kernel with Store as a framework primitive and a wide
> conceptual surface (authorities, observations, ElidePolicy, federation,
> meta-trust vs trust set). This proposal is the *minimal* MVP version of
> the same shape — single document, ~500 LoC kernel, ML-style data, no
> arena, no content addressing, no Store-as-primitive. The intent is to
> ship the smallest defensible bottom layer we can integrate with the rest
> of the system *first*, then grow upward.
>
> Read this before any of `02-framework.md` /
> `03-authority.md` / `04-store.md` — those add complexity that the MVP
> does not need. They become reachable refinements *after* this lands.
>
> This is also the most explicit **Larry Paulson / Isabelle-Pure homage**
> in the repo: a tiny LF/Pure substrate plus HOL as the default object
> logic, with everything else layered on top. In the vocabulary of
> [`../../../institution-map.md`](../../../institution-map.md), Pure is
> the candidate meta-institution and HOL the default object institution.

---

## 1. The three layers at a glance

```
              ┌─────────────────────────────────────────────┐
              │  covalence-shell (bootstrap, untrusted)     │
              │  - OnceCell anchors for stdlib constants    │
              │  - BlobSource impl (memory / sqlite / git)  │
              │  - Prover-API adapter, NotImplemented stubs │
              └────────────────┬────────────────────────────┘
                               │ depends on
              ┌────────────────▼────────────────────────────┐
   Layer 1   │  covalence-hol (untrusted)                  │
              │  - bool, =, ∧, ∨, ¬, →, ↔, ∀, ∃, ε         │
              │  - 10 HOL Light rules as derived Pure rules │
              │  - Subset types via disjunct trick          │
              │  - Stdlib loader keyed by BLAKE3            │
              │  - WASM-oracle adapter (observation axioms) │
              └────────────────┬────────────────────────────┘
                               │ depends on
              ┌────────────────▼────────────────────────────┐
   Layer 0   │  covalence-pure (TCB, ~500 LoC, no unsafe)  │
              │  - Term/Type: Arc<Node>, ML-style           │
              │  - 8 LF rules + equality (refl/cong/β/η)    │
              │  - define                                   │
              │  - Local Authority + observe (process-local)│
              │  - Blob as a kernel-primitive type/term     │
              └─────────────────────────────────────────────┘
```

This sketch takes the strongest austerity position:
**TCB = `covalence-pure` only.** A bug in HOL or in shell cannot
produce a false `Thm`. A bug in the WASM oracle adapter cannot produce
a false `Thm`. Soundness reduces to ~500 lines reviewed line-by-line.

If the broader refactor settles on "the trusted core is LF + HOL,"
then this document still matters as the **shape** of that split: Pure
remains the meta-logic substrate, HOL remains the default object
logic, and the rest of the system remains outside that center as
oracle, stdlib, transport, or institution-translation machinery.

## Companion docs

If you want the same Pure/HOL stack described in different vocabulary,
see the companion notes in
[`hehner-institution/`](./hehner-institution/README.md):

- [crosswalk](./hehner-institution/00-crosswalk.md)
- [Pure layer](./hehner-institution/01-pure-layer.md)
- [HOL layer](./hehner-institution/02-hol-layer.md)
- [next layers preview](./hehner-institution/03-next-layers.md)

---

## 2. Layer 0 — `covalence-pure`

Isabelle/Pure–shaped logical framework. Tiny enough that a reviewer
can hold all of it in their head.

### 2.1 Data: ML-style `Arc<Node>`

No arena, no `TermId`, no hashing. A term is a plain Rust value; two
α-equivalent terms compare equal by structural recursion. Sharing via
`Arc` is an incidental optimization — never load-bearing.

```rust
use std::sync::Arc;
use smol_str::SmolStr;
use bytes::Bytes;

#[derive(Clone, Hash, PartialEq, Eq)]
pub struct Term(Arc<TermNode>);

#[derive(Hash, PartialEq, Eq)]
enum TermNode {
    Bound(u32),                            // de Bruijn
    Free  { name: SmolStr, ty: Type },     // named free var
    Const { name: SmolStr, ty: Type },     // declared / defined constant
    App(Term, Term),
    Abs(Type, Term),                       // λx:τ. body
    Imp(Term, Term),                       // meta-implication φ ⟹ ψ
    All(Type, Term),                       // meta-universal ⋀x:τ. body
    Eq (Term, Term),                       // meta-equality t ≡ u
    Blob(Bytes),                           // ⟵ BUILTIN: first-class bytes
}

#[derive(Clone, Hash, PartialEq, Eq)]
pub struct Type(Arc<TypeNode>);

#[derive(Hash, PartialEq, Eq)]
enum TypeNode {
    Prop,                                              // kind of metaprops
    Tycon { name: SmolStr, args: Vec<Type> },          // user type ctors
    Arrow(Type, Type),
    TVar(SmolStr),
    Blob,                                              // ⟵ BUILTIN: type of Blob(_)
}
```

**Why blobs are a kernel primitive.** Big data must be representable in
the logic without us copying it. `Blob(Bytes)` lets the kernel reference
a byte sequence by Arc-share; structural equality is byte equality,
which is cheap when the Arcs share. The kernel *does not* hash blobs —
that's an upper-layer concern (`covalence-hash` outside the TCB). The
kernel just gives us a way to talk about arbitrary bytes inside Pure
terms.

### 2.2 Theorems

```rust
#[derive(Clone)]
pub struct Thm {
    hyps:  Arc<im::OrdSet<Term>>,   // each of kind Prop
    concl: Term,
}
```

`Thm` has no public constructor. The only way to obtain one is by calling
a kernel rule. Soundness is constructional in the LCF sense.

### 2.3 The rule set

Eight LF rules + the six equality rules + β + η + `inst_tyvar` +
`define` + `observe`.

```
[φ] ⊢ φ                                                    (assume)

Γ ∪ {φ} ⊢ ψ                       Γ ⊢ φ⟹ψ      Γ' ⊢ φ
─────────────  (imp-intro)        ──────────────────────  (imp-elim / MP)
Γ ⊢ φ ⟹ ψ                              Γ ∪ Γ' ⊢ ψ

Γ ⊢ φ(x)    x ∉ FV(Γ)             Γ ⊢ ⋀x:τ. φ(x)    ⊢ t : τ
─────────────────────  (all-i)    ──────────────────────────  (all-e)
Γ ⊢ ⋀x:τ. φ(x)                          Γ ⊢ φ(t)

⊢ t ≡ t  (refl)    Γ⊢t≡u, Γ'⊢u≡v ⇒ Γ∪Γ'⊢t≡v  (trans)    sym
(cong-app, cong-abs)        ⊢ (λx.M) N ≡ M[N/x]  (β)     ⊢ λx.f x ≡ f  (η, x∉FV(f))

c fresh, d closed, d:τ
──────────────────────────  (define)        and  inst_tyvar(σ, Thm)
⊢ c ≡ d, c declared at τ
```

Plus one trust hook (next section).

### 2.4 Local observation

The single trust hook. **Strictly local** — no hashes, no signatures,
no content addressing.

```rust
#[derive(Clone)]
pub struct Authority {
    id: u64,                                  // process-local nonce
    owned_relations: Arc<BTreeSet<SmolStr>>,
}

impl Kernel {
    pub fn fresh_authority(&mut self, rels: BTreeSet<SmolStr>) -> Authority;

    /// Atomic fact: produces `⊢ O.R(args...)` (empty hyps) provided
    /// R ∈ O.owned_relations and every arg is closed and well-typed.
    pub fn observe(
        &self,
        auth: &Authority,
        rel: &str,
        args: &[Term],
    ) -> Result<Thm>;
}
```

The Authority's `id` is a fresh `u64` from a session-scoped counter (or
RNG) — **not** a public key, **not** a BLAKE3 hash. This is the whole
point of "local observations only": cross-process identity, signing,
hashing, and federation are *above* the kernel. The kernel sees an
in-memory `Authority` and emits a theorem citing it. Whether that
theorem can be exchanged with another process is somebody else's
problem.

Soundness: the relation `R` is uninterpreted from the kernel's
perspective, so adding the observation is conservative over every
interpretation that maps `R` to "always true" (or to ∅, vacuously). The
user gives `R` meaning via a **meaning-axiom**, which is just a `Thm`
they assume and then discharge with `imp_elim` — the assumption stays
visible in `hyps` until they explicitly drop it.

### 2.5 What's deliberately absent

- No content addressing (no `O256`, no `ContentHash`, no Phase H).
- No `BlobStore`, no `BlobSource`, no IO of any kind.
- No signature verification.
- No WASM engine.
- No egraph, no union-find, no Phase P EProp/EThm.
- No `Decision::Sat/Unsat`.
- No `serde` on `Thm`. No serialization at all.
- No standard library. The kernel doesn't know `bool` exists.

These all live above the line and are added as untrusted upper layers.

### 2.6 Estimated size

| Module        | Purpose                                                | LoC  |
|---------------|--------------------------------------------------------|------|
| `term.rs`     | `Term`, `Type`, smart constructors, FV, well-formedness |  150 |
| `subst.rs`    | β/η, capture-avoiding substitution, `inst_tyvar`        |  120 |
| `thm.rs`      | `Thm`, the 14 inference rules + `define`                |  160 |
| `auth.rs`     | `Authority`, `observe`                                  |   50 |
| `kernel.rs`   | top-level `Kernel` struct, fresh-name supply            |   40 |
| `error.rs`    | `thiserror` errors                                       |   30 |
| **Total**     |                                                         | **~550** |

Direct deps: `covalence-rand` (Authority nonce + `inst_tyvar` fresh
names), `smol_str`, `bytes`, `im` (persistent OrdSet for hypotheses).
No `unsafe`, no IO, no Tokio, no WASM, no signature crate.

---

## 3. Layer 1 — `covalence-hol`

Untrusted. Builds classical HOL Light–shape logic on top of Pure.

Institution-theoretically this is the default **object institution**
that lives over the Pure meta-institution. That is the key reason this
split is attractive during the current refactor: it gives the repo one
stable place to host multiple theories and, later, explicit morphisms
between them.

### 3.1 What HOL adds

1. **`bool` type** — a Pure `Tycon { name: "bool", args: [] }`.
2. **HOL connectives** — `=` (object-level equality at `bool`), `∧`,
   `∨`, `¬`, `→`, `↔`, `∀`, `∃`, `ε` — every one introduced as a `define`d
   constant in Pure. The Pure framework never sees them; they're plain
   `Const`s with `Thm`-witnessed unfolding equations.
3. **Subset types** — via the disjunct trick (see
   [`ARCHITECTURE.md`](../../../../ARCHITECTURE.md) §2.4); unconditional
   so no inhabitation side-condition reaches the kernel.
4. **The 10 HOL Light rules** — `REFL`, `TRANS`, `MK_COMB`, `ABS`,
   `BETA`, `ASSUME`, `EQ_MP`, `DEDUCT_ANTISYM_RULE`, `INST`, `INST_TYPE`.
   None of them are Pure primitives; each is a sequence of Pure rule
   calls in `rules.rs`.

A bug in the disjunct trick or in any HOL Light rule cannot produce a
false Pure `Thm` — the worst it can do is fail to construct the HOL
theorem you wanted.

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
        kernel: &mut covalence_pure::Kernel,
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

WASM oracles live at the HOL layer. They're how we extend the prover
with computational evidence (decide procedures, hash functions,
signature checks, anything we can package as a WASM component) without
growing the TCB.

```rust
pub struct WasmOracle {
    auth: covalence_pure::Authority,       // fresh local Authority
    component_hash: blake3::Hash,           // identifies the component
    runner: Arc<dyn WasmRunner>,            // backed by covalence-wasm
}

impl HolKernel {
    /// Register a WASM component as an observation oracle. Creates a
    /// fresh local Authority that owns one relation `eval`.
    pub fn register_wasm_oracle(
        &mut self,
        component_hash: blake3::Hash,
        runner: Arc<dyn WasmRunner>,
    ) -> Result<WasmOracleId>;

    /// Install a meaning-axiom of the shape
    ///     ⊢ ⋀x out. O.eval(component_hash, x, out) ⟹ φ(x, out)
    /// The axiom is itself a `Thm` whose only hypothesis is the axiom
    /// statement — i.e. it is *assumed*, not proved. Every theorem that
    /// later applies the axiom continues to carry it in its hypotheses
    /// until explicitly discharged.
    pub fn install_meaning_axiom(&mut self, id: WasmOracleId, axiom: Thm) -> Result<()>;

    /// Run the WASM component on input; emit the kernel observation.
    pub fn observe_wasm(&self, id: WasmOracleId, input: Term) -> Result<Thm>;
}
```

**Key property: oracle trust is fully visible in `Thm::hyps`.** There is
no kernel-level "this oracle is trusted" switch. Whatever the user
assumes about the oracle (via the meaning-axiom) is recorded as a
hypothesis on every theorem that uses the oracle's output, exactly like
any other assumption. To export a theorem stripped of these hypotheses,
the user must either (a) prove the meaning-axiom from below — usually
impossible by construction, since it's a claim about a computational
artifact — or (b) discharge it via `imp_intro`, making the dependence
explicit in the theorem's *statement*.

This is HOL Light's `mk_thm` discipline, applied to an entire family of
oracles uniformly.

### 3.4 Estimated size

| Module           | Purpose                                              |  LoC |
|------------------|------------------------------------------------------|------|
| `connectives.rs` | HOL connectives via Pure `define`                    |  120 |
| `rules.rs`       | 10 HOL Light rules derived from Pure                 |  250 |
| `subset.rs`      | Subset types via the disjunct trick                  |  150 |
| `std.rs`         | Stdlib loader (BlobSource → entries)                 |  200 |
| `wasm.rs`        | WASM oracle adapter (no engine deps; trait-bound)    |  150 |
| **Total**        |                                                      | **~870** |

Direct deps: `covalence-pure`, `covalence-sexp` (script format),
`covalence-hash` (BLAKE3 type only — used as an opaque key, not for
hashing inside the kernel), and `covalence-wasm` *behind a feature flag*
for the runner trait impl.

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
    pub kernel: covalence_pure::Kernel,
    pub hol: OnceCell<covalence_hol::HolKernel>,
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

**Soundness.** ~500 lines of well-trodden Pure-style LF. The literature
on this (Isabelle/Pure, HOL Light, λΠ-calculus) is enormous; the rules
have been audited for decades. Our additions over textbook Pure are
exactly three: `define` (standard conservative-extension rule),
`observe` (a single conservative trust hook with the safe-axiom shape),
and the `Blob`/`Blob` term form (no inference power; just a way to put
bytes in a term).

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

Each step is a self-contained PR with its own test.

1. **`covalence-pure` core.** `Term`, `Type`, substitution, β/η, `Thm`,
   the 8 LF rules + 6 equality rules + `inst_tyvar`. *No* observation,
   *no* define. Test: `⊢ (λx.x) y ≡ y`; `⊢ ⋀x. x ≡ x`.
2. **`covalence-pure` `define` + `observe`.** `Authority`, `observe`,
   `define`. Test: declare an authority, observe a fact, install a
   meaning-axiom as a hypothesis, discharge via `imp_elim`; verify the
   meaning-axiom remains in `hyps` until `imp_intro`'d.
3. **`covalence-hol` skeleton.** `bool`, `=`, `∧`, `→`, `∀`, `∃`,
   `ε`. Test: `⊢ ∀x. x = x`.
4. **HOL Light rules.** All 10 derived in `rules.rs`. Test: replay
   a small known HOL Light proof end-to-end.
5. **Subset types via disjunct trick.** Test: form a subset type
   unconditionally; verify HOL Light's `define_type` behaviour.
6. **Stdlib loader.** `BlobSource`, manifest blob format, lazy
   materialisation, `HolStd::load`. Test: bundle a tiny stdlib (~10
   entries), bootstrap from it, look up `bool` and `=`.
7. **`covalence-shell` bootstrap.** OnceCell anchors, `bootstrap()`,
   `Prover` adapter with `NotImplemented` stubs. Test: REPL, serve,
   LSP all compile and start; basic `assume` + `imp_intro` works
   through the adapter; everything else returns NotImplemented.
8. **WASM oracle adapter.** `register_wasm_oracle`,
   `install_meaning_axiom`, `observe_wasm`. Test: a hardcoded WASM
   component that returns "yes" on input X; observe; verify the
   meaning-axiom is in `hyps`; discharge; verify the result.

Total estimated MVP work: ~3 weeks of focused implementation, with the
existing repo's scaffolding (BLAKE3, WASM, SExpr) all already available.

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
