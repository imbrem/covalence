# `covalence-pure` — value-directed kernel design (current sketch)

> **STATUS: DESIGN SKETCH (current direction).** The concrete Rust-trait
> encoding of `covalence-pure`, as built in `crates/covalence-pure/src/lib.rs`.
> Supersedes the *presentation* in [`covalence-pure.md`](./covalence-pure.md)
> (observer + two-assumption-set) — that doc's ideas are still valid and map
> onto this one (observers/accelerators become **TCB modules**; the meta-set
> becomes the **context `C`**). Companion to
> [`refactor-plan.md`](./refactor-plan.md) §2.

---

## 1. The judgement: `Thm<C, P>`

A `Thm<C, P>` certifies a specific statement `Stmt<C, P> = { ctx: C, prop: P }`
— a context **value** `c` paired with a proposition **value** `p`. Read `C ⊢ P`.

- **`C` is the TCB / trust domain.** The context value names (and carries) what
  is trusted: a pile of assumptions, a HOL context, WASM-eval facts, a store.
- **`P` is the statement.** An equation, a claim about a WASM program, a `bool`,
  a reference. Connectives are host types over the *values*: `(P,Q)` = `∧`,
  `Either<P,Q>` = `∨`, `()` = `⊤`, the `bool` value `false` = `⊥`.

### The load-bearing invariant

Every type is **assumed inhabited** (HOL-style), so the *existence* of a
`Thm<C, P>` at the type level is **not information** — you could always exhibit
some `p: P`. A theorem certifies that *this specific* `(c, p)` is derivable.
Types are *sorts*; the **values** are the content. Hence everything is
**value-directed**: no API reads meaning from type-inhabitation; eliminators
dispatch on values; ex-falso takes the caller's specific target value.

## 2. The floor API (the whole TCB floor)

> **Naming:** the context/kernel type parameter is **`K`** ("K for kernel"), not
> `C` — to avoid confusion with an object language's *internal* context (e.g.
> HOL's `Γ`). Older prose below written with `C` means `K`; secondary kernels are
> `K1`/`K2`. The theorem type is **`MThm`** ("metatheorem"), not `Thm` — so a
> downstream crate is free to alias `type Thm<P, K = ()> = MThm<MyCrateCtx<K>, P>`.
> Older prose written `Thm` means `MThm`.

> **Crate split:** the kernel TCB lives in **`covalence-pure-trusted`** (the
> `thm` + `derive` modules — `MThm`/`Stmt`/`Rule`/`Derive`/`IsStmt`, structural
> rules, pointer/erasure support; `MThm::new` private to its `thm` module = the
> minting boundary, now a crate boundary). **`covalence-pure`** is a *facade*: it
> re-exports the kernel and adds non-minting sugar — `testing` and the `ext`
> extension traits (`MThmExt`/`MThmVecExt`, the same-context `try_zip_same` /
> `push_same`). Future siblings slot in the same way: `covalence-pure-derive`
> (proc macros) and **feature crates** (equality theory, FOL, content-addressing)
> — each a unit of trust contributing `Rule`s a context opts into, the
> "ultra-modular" `MyFeature<K>(data, k) ⟹ …` pattern.

Source of truth: `crates/covalence-pure-trusted/src/` (kernel) + `covalence-pure`
(facade). Surface:

- `Stmt<C, P>` — public `{ ctx, prop }`, freely constructible, **no** truth
  claim. The untrusted analogue of a theorem.
- `Thm<C, P>(Stmt<C, P>)` — unforgeable wrapper (private field, no public ctor).
  `Deref → Stmt` (read-only, **no** `DerefMut`); `From<Thm> for Stmt`.
- `trait Rule<R, P, E> { fn derive(rule: R) -> Result<(Self, P), E>; }` — the
  single inference rule. `Self` = **output context**.
- `Thm::deduce::<R,E>(rule) -> Result<Thm<C,P>, E>` — the sole `Stmt → Thm`
  gate. `Intro`/`Infer1`/`Infer2` are all this, with premises riding inside `R`.
- Reserved constructive structural rules as methods: `trivial` (⊤), `truth` /
  `false_elim` (bool base, value-directed), `zip` (∧-intro across contexts),
  `fst`/`snd`/`and_elim` (∧-elim), `or_inl`/`or_inr`/`or_elim` (∨),
  `ctx_inl`/`ctx_inr`/`ctx_or_elim` (context-∨), `Union` (context merge).
- **Sequence props as N-ary conjunction** (`[T; N]`, `Vec<T>`, `&[T]` = "every
  element holds in `C`"): `unpack` (∧-elim → a collection of element theorems),
  `empty_vec` + cross-context `push` (the general primitive, `U: Union<C, C2>`,
  analog of `zip`). These are **neutral** — meaning needs nothing trusted about
  `T`. `BTreeSet`/`HashSet` are omitted: their structure (dedup/membership/
  set-equality) trusts `T: Ord` / `T: Hash+Eq`, so they belong with the
  equality/ordering trust layer (though even there, *unpacking* a set stays
  sound).
- **`convenience`** — a separate module of ergonomic specializations that only
  *compose* floor primitives (no new trust), e.g. same-context `push_same`
  (`C: Union<C,C>`, stays in `C` so it chains without annotating an output
  context). The general primitives live on the floor; convenience sugar lives
  here.
- **`Thm` is a template over a statement representation:**
  `Thm<K, P, S = Stmt<K, P>>` — `S` is the statement carrier, `K`/`P` are phantom
  tags. Construction is gated by the marker **`K: IsStmt<S, P>`** ("context `K`
  admits representation `S`") via the private `Thm::new`; only `K` decides what
  it forms. The canonical `Stmt<K,P>` is admitted by every `K` (blanket), and so
  is any faithful-pointer wrapping of an admitted `S` (`Box`/`Rc`/`Arc`/`&`
  blankets); later a context can admit richer `S` (content-addressed,
  arena-indexed, Nat-literal, *erasing*, an `Arc<dyn TypedTerm>`) and mint/cast
  it. `Thm: Deref<Target = S>`, and `box_stmt`/`arc_stmt`/`rc_stmt` /
  `unbox_stmt`/`unarc_stmt`/`unrc_stmt`/`deref_stmt` move the statement between
  representations (prove/share without copying).
- **Statement *views are optional* capabilities** (`thm/stmt.rs`): `GetCtx<C>`,
  `GetProp<P>`, `IntoParts<C,P>` — a representation provides whichever it has (the
  canonical `Stmt` provides all; an *erasing* statement omits `GetCtx`).
  `GetProp` is *parameterized* (not associated) so one carrier exposes several
  prop views — host-level `P ⟺ Q`. `&`/`Arc`/`Rc`/`Box` forward the read views
  (prove without copying). These mint nothing.
- **Staged next:** union of `C1`,`C2` as the structural pair `(C1,C2)` with
  `Union`/`TryUnion` as collapse rules (pointer-eq picks left/right via
  `TrustedDeref`); and letting `C` mint non-canonical `S`.
- **Type erasure** uses the **bare** `dyn Any` pointers (`Arc<dyn Any>`, or
  `Rc`/`&` — no wrapper type): `erase_ctx`/`erase_prop` and
  `downcast_ctx`/`downcast_prop` let a `Thm` range over a **dynamic** TCB /
  proposition. Erasure is *faithful* — the concrete type id is in the value, so
  you can only downcast back to the **same** type (erasing `Thm<A,_>` then
  downcasting to `B` fails), preserving nuclei isolation: erasure is an
  existential over domains, not a launder. Merging two erased contexts is
  **fallible** (`TryUnion`, the fallible `Union`): the default impl — provided
  for `Arc`/`Rc`/`&` (not `Box`, which is unique-owned) — is
  **pointer-equality-or-error** (`CtxMismatch`). `Thm::try_zip` is the fallible
  `zip`; `try_zip_same` (in `convenience`) is the same-context form.
- `trait TrustedDeref: Deref {}` — pointers whose deref is *faithful* (target =
  the pointer's entire meaning): `Box`/`Arc`/`Rc`/`&`, all first-class. Enables
  `wrap_prop` / `wrap_ctx` (owning pointers, via `From`), `ptr_subst` (positive
  pointer-equality transport — same allocation ⇒ same value ⇒ re-stamp; mismatch
  proves nothing), and — via the `TrustedTake: TrustedDeref` sub-trait —
  `unwrap_prop` / `unwrap_ctx` that move where possible (`Box<P>` needs **no**
  `Clone`; a unique `Arc`/`Rc` moves, else clones; `&` clones). So `Arc<C>` is
  the *same* domain as `C`. Plain `Deref` is *not* enough (a `Tagged<T>{tag,
  inner}` wrapper would let pointer-equal inners wrongly transport), so it's a
  distinct opt-in marker = a TCB assertion.

## 3. Soundness

1. **Unforgeable wrapper.** `Thm` wraps `Stmt` privately with no public ctor, so
   every line of `covalence-pure` is TCB — keep it minimal.
2. **Orphan rule.** A `Thm<C,_>` is minted only through `C`'s own `Rule` impls;
   since `Self` = output context, Rust reserves them to `C`'s crate. A context
   controls every theorem minted in it.
3. **`Thm` vs `Stmt` is the trust boundary.** `Thm<C,p>` = "C genuinely
   certifies p"; `Stmt<C,p>` = "someone *claims* C certifies p." Rules carry
   premises as real `Thm`s (unforgeable ⇒ genuine); invoked directly a `Rule`
   yields a raw pair, never a `Thm`.

## 4. Nuclei & bridges (`Thm` everywhere)

`Thm<C, P>` is a **universal provenance certificate**: "domain C produced P."
Used everywhere — `Thm<Kernel, _>` (logic), `Thm<MySyntax, SyntaxStatements>`
(compiled output, rules = arbitrary trusted programs), `Thm<DbConn, _>`,
`Thm<WasmEval, Runs(..)>`. These separate `C`s are the **nuclei**; composition
is **bonds** (covalence). Isolation holds because:

- no generic `Thm<C,_> → Thm<D,_>`;
- `Union`/`zip` joint domains are explicit + typed; projections stay in the
  joint domain;
- sum contexts are value-directed (`ctx_or_elim` returns only the injected
  branch);
- `into_stmt` yields untrusted `Stmt`, which launders nothing.

**A bridge** is `impl Rule<R, P, E> for D` where `R` carries a cert from another
domain. **It must take `Thm<C,_>`, never `Stmt<C,_>`** — the one-glance,
type-level audit. Payoff: **differential trust** (a paranoid kernel and a
low-trust syntax domain coexist uncontaminated); whole-TCB soundness reduces to
a finite set — each module's rules + each bridge's premise types.

**Merge vs separate** is just whether you `Union`: `my_tcb!{Nat,Bytes,Hol}` →
one domain; `Syntax` vs `Kernel` → distinct domains bridged only where you write
a rule. The `C` in the type always shows which.

## 5. TCB modules (above the floor)

Two things a TCB can trust about a type (each a context fragment + rules + a
spec axiom, in one small auditable file):

1. **Properties / computation** (*accelerators*) — "this type's operations
   behave" (`+` agrees with HOL `nat.add`).
2. **Representation** — "`MyList<T>` *is* a `Vec<T>`": a trusted iso that
   transports facts (abs/rep).

### Equality discipline

- **Congruence is free & structural**: `aᵢ = bᵢ ⟹ App(op,[aᵢ]) = App(op,[bᵢ])`,
  no per-type trust.
- **Computation is the only trusted part, and it's tiny**: `Op::eval(args) ->
  Option<Out>` declares the *non-congruence* equalities (`App(Add,[5,7]) = 12`),
  audited against one obligation — agrees with the Op's HOL denotation. `eval`
  on the **Op**, Ops **grouped per module** so the *file* is "the Nat
  accelerator" (handles cross-type ops like `length: List→Nat` cleanly).
- **Positive `==` is a degenerate, opt-in case**, not the foundation: reflexive
  `==` is the same `Thm`; an audited `==` exposes itself as a nullary decision
  Op. Positive only — `a != b` proves nothing.

## 6. Serialization

- `Stmt<C,P>: Serialize + Deserialize` — public data.
- `Thm`: `Serialize` only, **never `Deserialize`** (that's the forge). Recover a
  serialized theorem by **replay** (re-run its rules) or by **trusting an
  attestation** (federation, below) — both TCB modules.
- Content-address = hash the (injective, canonical) serialized statement.

## 7. Content-addressing — the store *is* the world

> The key reframing: collision "resistance" isn't a probabilistic assumption. A
> **store `S` is a finite concrete map `Id → Prop`** — it has **no collisions by
> construction** (one value per key). A hash/Id is a key *interpreted in a
> particular world*, and that world is `C`.

- A store is a nucleus *and* a value. `Thm<S, Ref(id)>` = "in store `S`, entry
  `id` is a valid theorem" — a compressed reference.
- **contract** (store it): `Thm<C, p> + S → Thm<S, Ref(id)>`, recording
  `id → p`. Sound (you stored a real theorem); the store grows.
- **resolve** (bring it into your TCB): the bridge
  `Thm<S, Ref(id)> → Thm<C, S.resolve(id)>` is a **concrete finite-map lookup**
  — *no probabilistic assumption*. Example: `Thm<SmallIntegerStore,
  TheoremId(5)>` → `Thm<C, SmallIntegerStore.resolve(5)>`. The only trust is
  "C trusts store S" (the bridge) + "S faithfully records what was stored."
- **Collision-resistance re-enters only across stores / for global hashes** —
  merging two stores, or treating a hash as a stable identifier in *another*
  world. Then "no collisions" is an explicit axiom about the (hypothetical,
  possibly infinite) global store — "interpret this hash in a collision-free
  world" — not a property of the hash function. Within any one concrete store it
  is free.
- **Soundness:** cross-store/global expand needs an **injective canonical
  serialization** (distinct props ⇒ distinct bytes), else you contract `p1` and
  resolve to `p2`.

## 8. Federation — remote transport (a cross-domain bridge)

Schemas: `Signed<K, P>` ("a valid K-signature over P"), `Trusted<K>`.

- **verify** `(prop, sig, K) → Thm<C, Signed<K,P>>` — unconditionally sound (a
  *factual* claim about the signature; the gate turning untrusted bytes into a
  checked fact).
- **trust** — `Thm<C, Trusted<K>>` is the axiom you add by putting K in your
  store (the meta-assumption).
- **accept** `Thm<C,Signed<K,P>> ⊗ Thm<C,Trusted<K'>> [K==K'] → Thm<C, P>` —
  sound under "a trusted key signs only its genuine theorems." Key compare
  value-directed; the trusted leap lives entirely here.

**Chains with §7:** sign the content-id (`Signed<K, Ref(id)>`) → accept →
`Thm<C, Ref(id)>` → resolve → `Thm<C, p>`.

## 9. Composition & build order

`my_tcb!{ Nat, Bytes, Hol, Wasm }` → a single composite context type; the macro
emits the product context + dispatch rules (+ the intended bridges). Every
*trusted* line lives in a small per-module file; the macro is mechanical glue.

Long-term: **derive macros for stating sound `Rule`s** in a user context,
Isabelle/HOL-style, expansion kept minimal *because* auditability is the point.

Proposed build order (each validates one soundness property before the next
leans on it):

1. **Isolation test** (`trybuild`) — two nuclei + one bridge; compile-fail
   proves no path without the bridge and that `Stmt`-instead-of-`Thm` is the one
   visible unsound move.
2. **`Eq`/`App`/`Op` + a Nat accelerator** — the computation/equality substrate.
3. **`Cons` (store/hash) + `Fed` (sign)** — content-addressing & federation;
   forces the injective-serialization decision.
4. **`my_tcb!` macro** — composes the above into one declared TCB.
