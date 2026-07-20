+++
id = "N0018"
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

# `covalence-pure` — value-directed kernel design (superseded)

> **Historical design sketch.** Superseded as architecture by
> [`substrate-rewrite.md`](./substrate-rewrite.md). In particular, its observer
> and minting vocabulary is not the nucleus authority boundary. The Rust-trait
> encoding of `covalence-pure` as built in
> `crates/kernel/base/`. Superseded for the *kernel layer* by
> [`closed-world-kernel.md`](./closed-world-kernel.md) (the realized `Thm<L,P>`
> shape) and [`base-relcalc-holomega-design.md`](./base-relcalc-holomega-design.md)
> (the relation-calculus redesign) — but the nuclei / federation / store content
> is retained only as implementation history.

## 1. The judgement: `Thm<C, P>`

A `Thm<C, P>` certifies `Stmt<C, P> = { ctx: C, prop: P }` — a context **value**
`c` paired with a proposition **value** `p`. Read `C ⊢ P`.

- **`C` is the TCB / trust domain** — the context value names (and carries) what
  is trusted: assumptions, a HOL context, WASM-eval facts, a store.
- **`P` is the statement** — an equation, a claim about a WASM program, a `bool`,
  a reference. Connectives are host types over the *values*: `(P,Q)` = `∧`,
  `Either<P,Q>` = `∨`, `()` = `⊤`, the `bool` value `false` = `⊥`.

**The load-bearing invariant.** Every type is assumed inhabited (HOL-style), so
the *existence* of a `Thm<C, P>` at the type level is not information — you could
always exhibit some `p: P`. A theorem certifies that *this specific* `(c, p)` is
derivable. Types are *sorts*; the values are the content. Everything is
**value-directed**: no API reads meaning from type-inhabitation; eliminators
dispatch on values; ex-falso takes the caller's specific target value.

## 2. The floor API (the whole TCB floor)

> **Naming.** The context/kernel type parameter is **`K`** ("K for kernel"), not
> `C` — to avoid clashing with an object language's *internal* context (HOL's
> `Γ`); secondary kernels are `K1`/`K2`. The theorem type is **`MThm`**
> ("metatheorem"), so a downstream crate can alias
> `type Thm<P, K = ()> = MThm<MyCrateCtx<K>, P>`. Older prose below written `C`/`Thm`
> means `K`/`MThm`.

**Crate split.** The kernel TCB lives in `covalence-pure-trusted` (`thm` +
`derive` — `MThm`/`Stmt`/`Rule`/`Derive`/`IsStmt`, structural rules,
pointer/erasure; `MThm::new` private = the minting boundary). `covalence-pure` is
a *facade* re-exporting the kernel + non-minting sugar (`testing`, the `ext`
extension traits). Future siblings slot in the same way: `covalence-pure-derive`
(proc macros) and feature crates (equality theory, FOL, content-addressing), each
a unit of trust contributing `Rule`s a context opts into.

Surface (source of truth: `crates/kernel/base/`):

- `Stmt<C, P>` — public `{ ctx, prop }`, freely constructible, **no** truth claim.
- `Thm<C, P>(Stmt<C, P>)` — unforgeable wrapper (private field, no public ctor).
  `Deref → Stmt` (read-only); `From<Thm> for Stmt`.
- `trait Rule<R, P, E> { fn derive(rule: R) -> Result<(Self, P), E>; }` — the
  single inference rule. `Self` = **output context**.
- `Thm::deduce::<R,E>(rule)` — the sole `Stmt → Thm` gate. `Intro`/`Infer1`/`Infer2`
  are all this, with premises riding inside `R`.
- Reserved constructive structural rules as methods: `trivial` (⊤), `truth` /
  `false_elim` (bool base, value-directed), `zip` (∧-intro across contexts),
  `fst`/`snd`/`and_elim`, `or_inl`/`or_inr`/`or_elim`, `ctx_inl`/`ctx_inr`/
  `ctx_or_elim` (context-∨), `Union` (context merge).
- **Sequence props as N-ary conjunction** (`[T; N]`, `Vec<T>`, `&[T]` = "every
  element holds in `C`"): `unpack`, `empty_vec` + cross-context `push`. Neutral —
  needs nothing trusted about `T`. `BTreeSet`/`HashSet` omitted (their
  dedup/membership trusts `T: Ord`/`Hash+Eq`, belonging with the equality/ordering
  layer — though *unpacking* a set stays sound).
- **`convenience`** — a module of ergonomic specializations that only *compose*
  floor primitives (no new trust), e.g. same-context `push_same` (`C: Union<C,C>`).
- **`Thm` is a template over a statement representation:** `Thm<K, P, S = Stmt<K, P>>`.
  Construction is gated by the marker **`K: IsStmt<S, P>`** ("context `K` admits
  representation `S`") via the private `Thm::new`; only `K` decides what it forms.
  Canonical `Stmt<K,P>` is admitted by every `K`, as is any faithful-pointer
  wrapping (`Box`/`Rc`/`Arc`/`&` blankets); a context can later admit richer `S`
  (content-addressed, arena-indexed, Nat-literal, erasing, `Arc<dyn TypedTerm>`).
  `box_stmt`/`arc_stmt`/… move the statement between representations.
- **Statement views are optional capabilities** (`GetCtx<C>`, `GetProp<P>`,
  `IntoParts<C,P>`): a representation provides whichever it has (an *erasing*
  statement omits `GetCtx`). `GetProp` is *parameterized* so one carrier exposes
  several prop views (host-level `P ⟺ Q`). `&`/`Arc`/`Rc`/`Box` forward the read
  views. These mint nothing.
- **Type erasure** uses **bare** `dyn Any` pointers (`Arc<dyn Any>`/`Rc`/`&`):
  `erase_ctx`/`erase_prop` + `downcast_ctx`/`downcast_prop` let a `Thm` range over
  a dynamic TCB / proposition. Erasure is **faithful** — the concrete type id is
  in the value, so you can only downcast back to the *same* type, preserving
  nuclei isolation (an existential over domains, not a launder). Merging two
  erased contexts is fallible (`TryUnion`): pointer-equality-or-`CtxMismatch`, for
  `Arc`/`Rc`/`&` (not `Box`, unique-owned). `try_zip` / `try_zip_same` are the
  fallible `zip`.
- `trait TrustedDeref: Deref {}` — pointers whose deref is *faithful* (target =
  the pointer's entire meaning): `Box`/`Arc`/`Rc`/`&`. Enables `wrap_prop`/
  `wrap_ctx`, `ptr_subst` (positive pointer-equality transport), and — via
  `TrustedTake` — `unwrap_prop`/`unwrap_ctx` that move where possible. So `Arc<C>`
  is the *same* domain as `C`. Plain `Deref` is not enough (a `Tagged<T>` wrapper
  would let pointer-equal inners wrongly transport), so it's a distinct opt-in
  marker = a TCB assertion.

## 3. Soundness

1. **Unforgeable wrapper.** `Thm` wraps `Stmt` privately with no public ctor —
   every line of `covalence-pure` is TCB; keep it minimal.
2. **Orphan rule.** A `Thm<C,_>` is minted only through `C`'s own `Rule` impls;
   since `Self` = output context, Rust reserves them to `C`'s crate.
3. **`Thm` vs `Stmt` is the trust boundary.** `Thm<C,p>` = "C genuinely certifies
   p"; `Stmt<C,p>` = "someone *claims* it." Rules carry premises as real `Thm`s
   (unforgeable ⇒ genuine); invoked directly a `Rule` yields a raw pair.

## 4. Nuclei & bridges (`Thm` everywhere)

`Thm<C, P>` is a **universal provenance certificate**: "domain C produced P."
Used everywhere — `Thm<Kernel, _>`, `Thm<MySyntax, SyntaxStatements>` (compiled
output, rules = arbitrary trusted programs), `Thm<DbConn, _>`, `Thm<WasmEval,
Runs(..)>`. Separate `C`s are the **nuclei**; composition is **bonds**
(covalence). Isolation holds because: no generic `Thm<C,_> → Thm<D,_>`;
`Union`/`zip` joint domains are explicit + typed; sum contexts are value-directed;
`into_stmt` yields untrusted `Stmt`.

**A bridge** is `impl Rule<R, P, E> for D` where `R` carries a cert from another
domain. **It must take `Thm<C,_>`, never `Stmt<C,_>`** — the one-glance,
type-level audit. Payoff: **differential trust** (a paranoid kernel and a
low-trust syntax domain coexist uncontaminated); whole-TCB soundness reduces to a
finite set — each module's rules + each bridge's premise types.

**Merge vs separate** is just whether you `Union`: `my_tcb!{Nat,Bytes,Hol}` → one
domain; `Syntax` vs `Kernel` → distinct domains bridged only where you write a
rule. The `C` in the type always shows which.

## 5. TCB modules (above the floor)

Two things a TCB can trust about a type (each a context fragment + rules + a spec
axiom, in one small auditable file):

1. **Properties / computation** (*accelerators*) — "this type's operations behave"
   (`+` agrees with HOL `nat.add`).
2. **Representation** — "`MyList<T>` *is* a `Vec<T>`": a trusted iso transporting
   facts (abs/rep).

**Equality discipline:**

- **Congruence is free & structural**: `aᵢ = bᵢ ⟹ App(op,[aᵢ]) = App(op,[bᵢ])`,
  no per-type trust.
- **Computation is the only trusted part, and it's tiny**: `Op::eval(args) ->
  Option<Out>` declares the *non-congruence* equalities (`App(Add,[5,7]) = 12`),
  audited against one obligation — agrees with the Op's HOL denotation. `eval` on
  the **Op**, grouped per module (so the file is "the Nat accelerator", handling
  cross-type ops like `length: List→Nat`).
- **Positive `==` is a degenerate, opt-in case**, not the foundation: reflexive
  `==` is the same `Thm`; an audited `==` exposes itself as a nullary decision Op.
  Positive only — `a != b` proves nothing.

## 6. Serialization

- `Stmt<C,P>: Serialize + Deserialize` — public data.
- `Thm`: `Serialize` only, **never `Deserialize`** (that's the forge). Recover a
  serialized theorem by **replay** (re-run its rules) or by **trusting an
  attestation** (§8) — both TCB modules.
- Content-address = hash the (injective, canonical) serialized statement.

## 7. Content-addressing — the store *is* the world

> The reframing: collision "resistance" isn't a probabilistic assumption. A
> **store `S` is a finite concrete map `Id → Prop`** — no collisions by
> construction (one value per key). A hash/Id is a key interpreted in a particular
> world, and that world is `C`.

- A store is a nucleus *and* a value. `Thm<S, Ref(id)>` = "in store `S`, entry
  `id` is a valid theorem" — a compressed reference.
- **contract** (store it): `Thm<C, p> + S → Thm<S, Ref(id)>`, recording `id → p`.
  Sound; the store grows.
- **resolve** (bring it into your TCB): `Thm<S, Ref(id)> → Thm<C, S.resolve(id)>`
  is a **concrete finite-map lookup** — no probabilistic assumption. Trust is
  "C trusts store S" (the bridge) + "S faithfully records what was stored."
- **Collision-resistance re-enters only across stores / for global hashes** —
  merging stores, or treating a hash as a stable identifier in *another* world.
  Then "no collisions" is an explicit axiom about the (hypothetical, possibly
  infinite) global store — not a property of the hash function. Within any one
  concrete store it is free.
- **Soundness:** cross-store/global expand needs an **injective canonical
  serialization** (distinct props ⇒ distinct bytes).

## 8. Federation — remote transport (a cross-domain bridge)

Schemas: `Signed<K, P>` ("a valid K-signature over P"), `Trusted<K>`.

- **verify** `(prop, sig, K) → Thm<C, Signed<K,P>>` — unconditionally sound (a
  factual claim about the signature; turns untrusted bytes into a checked fact).
- **trust** — `Thm<C, Trusted<K>>` is the axiom you add by putting K in your store.
- **accept** `Thm<C,Signed<K,P>> ⊗ Thm<C,Trusted<K'>> [K==K'] → Thm<C, P>` — sound
  under "a trusted key signs only its genuine theorems." The trusted leap lives
  entirely here.

**Chains with §7:** sign the content-id (`Signed<K, Ref(id)>`) → accept →
`Thm<C, Ref(id)>` → resolve → `Thm<C, p>`.

## 9. Composition & build order

`my_tcb!{ Nat, Bytes, Hol, Wasm }` → a single composite context type; the macro
emits the product context + dispatch rules + the intended bridges. Every trusted
line lives in a small per-module file; the macro is mechanical glue.

Long-term: **derive macros for stating sound `Rule`s** in a user context,
Isabelle/HOL-style, expansion kept minimal *because* auditability is the point.

Build order (each validates one soundness property before the next leans on it):

1. **Isolation test** (`trybuild`) — two nuclei + one bridge; compile-fail proves
   no path without the bridge, and that `Stmt`-instead-of-`Thm` is the one visible
   unsound move.
2. **`Eq`/`App`/`Op` + a Nat accelerator** — the computation/equality substrate.
3. **`Cons` (store/hash) + `Fed` (sign)** — content-addressing & federation;
   forces the injective-serialization decision.
4. **`my_tcb!` macro** — composes the above into one declared TCB.
