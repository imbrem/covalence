# Content-addressing, bottom-up from S-expressions to HOL (discussion draft, agent-authored)

Response to: "Lisp is a good place to *start* content-addressing — content-addressed
S-expression references (hash of the printed S-expr or similar) in the REPL; likewise
Forsp/FORTH; then add it to HOL itself." I strongly agree, and I think this is the
*right on-ramp* to the content-addressing subsystem `sketch-separation-thoughts.md`
flagged as the critical-path-but-unstarted gate: the Lisp surface lets us build and
demo it **zero-TCB first**, then promote the exact same mechanism into the kernel as a
*certificate*. Not committed.

## 0. The thesis: one Merkle mechanism, three trust tiers

Content-addressing is **one** operation — hash a canonical serialization, key a store
by the hash — applied at three ascending trust levels:

| Tier | Object hashed | Trust | Where |
|---|---|---|---|
| **1. REPL surface** | printed S-expr (Lisp/Forsp) | untrusted (sharing/dedup only) | `covalence-sexpr` + a store map |
| **2. executors** | Forth words / Forsp thunks | untrusted (dictionary = CA store) | the concatenative axis |
| **3. HOL** | canonical `Term`/`Thm` | **a certificate** (`Hash<h>`) | kernel, ties to `cov:store` |

Tier 1 is a weekend demo with no soundness stakes; tier 3 is the federation/store
subsystem. Building 1→3 means the API is *exercised by a real surface* before it becomes
TCB — the "every extension gets an `*-api` + an application" discipline
(`sketch-separation-thoughts.md`), applied to the store.

**Load-bearing caveat throughout** (`names-efficiency-not-soundness`,
`content-addressing-federation-rules`): a hash is an **efficiency/opacity token, never a
trust primitive.** A hash reference is a cache key + a sharing token; *dereferencing* one
is only sound if you re-check the retrieved content (tier 3) or discharge a signature as
a meta-assumption (`signatures-as-meta-assumptions`). Tiers 1–2 don't need this because
nothing downstream *trusts* the hash — it's pure sharing.

## 1. Tier 1 — content-addressed S-expressions in the REPL (zero-TCB, do this first)

An S-expr reference is `ref := H(canonical_print(sexpr))` — hash the canonical printed
form (`covalence-sexpr` already has a canonical single-line printer; §Lisp-frontend-
sketch §1). A tiny content store `Map<Hash, SExpr>` and you have:

```text
λ> (def double (lambda (x) (+ x x)))
double : #a1b2c3…                       ; the definition's content hash
λ> :hash (lambda (x) (+ x x))
#a1b2c3…                                ; same hash — structural identity by content
λ> #a1b2c3…                             ; a hash is a first-class reference
(lambda (x) (+ x x))                    ; deref = store lookup
λ> (def quad (lambda (x) (double (double x))))
quad : #d4e5f6…  →  refs { #a1b2c3… }   ; a DAG edge, by hash
```

Key properties, all *free* from the substrate:

- **It's a Merkle DAG, i.e. hash-consing.** A cons hashes as `H(cons, H(car), H(cdr))`;
  equal subtrees share a hash ⇒ automatic structural sharing + dedup. **Content-addressing
  and hash-consing are the same mechanism** — so tier 1 *is* the kernel's term-sharing
  perf lever (`term-arena-vs-wasm`, the hash-cons notes) wearing a REPL hat. One
  construction pays off as both dedup-storage and interning.
- **The canonical printer is the whole game.** The hash is well-defined only up to a
  *canonical* serialization — which is exactly the canonical `deparse` (the chosen section
  of `Parse°`, `parsing-relations.md`). So content-addressing *needs* the canonical
  deparser, and in return gives it a concrete consumer. (Design fork below: canonicalize-
  then-hash vs hash-the-buffer.)
- **Zero TCB.** It's a hash function + a `HashMap` over the untrusted `SExpr` IR. Nothing
  trusts the hash; it's sharing + naming. Perfect first content-addressing demo — visible,
  useful (`:load #hash`, dedup, structure-diff), and risk-free.

Store shape: this store *is* an instance of the `cov:store` blob ABI (`store-is-container`,
`store-identity-component-hash`) — `put(bytes)→hash`, `get(hash)→bytes` — so tier 1 is
also the smallest real client of the store crate, on the untrusted side.

## 2. Tier 2 — the executors (Forth dictionary, Forsp thunks)

Already half-stated in `lisp-dialects-and-order.md` §6: **a Forth dictionary is a
content-addressed store of words.** A word's reference is `H(canonical(word_def))`;
threaded code references its callees by hash; the dictionary is `Map<Hash, Word>` = the
same `cov:store` blob map as tier 1. Forsp thunks/quotations content-address identically
(they're just quoted S-exprs). So the concatenative axis gets content-addressing for
*free* from tier 1 — and it's the natural place because threaded code is *already*
"program as a graph of references." This is where content-addressing meets the executor
story: a content-addressed word graph is a program you can ship, dedup, and (later) run
in WASM by hash.

## 3. Tier 3 — content-addressing HOL itself (where it becomes a certificate)

Now promote the *exact same* hash into the kernel — but here the hash is no longer just
sharing, so it must be a **certificate**, per `content-addressing-federation-rules`:

- **`Hash<h>` as a `Thm` rule schema.** For a canonical serialization of a `Term`/`Thm`,
  `contract : Thm ⟶ Hash<h>` (hash it) and `expand : Hash<h> ⟶ Thm` (*re-check* the
  retrieved content against `h`). `expand` is the **sound-leap**: it trusts collision-
  resistance of `H` + injectivity of the serialization. That is the *entire* added TCB
  surface, and it's auditable in isolation (exactly like the reify-rule audit gate in the
  float plan). Contract is free; expand is the one obligation.
- **Injective serialization is the precondition.** `expand` is sound only if
  `canonical_serialize` is injective (distinct terms → distinct bytes) *and* `H` is
  collision-resistant. This is the `Phase H` story (`store-api-portable`,
  `Phase H no normalization`): the kernel hashes *linear buffers* with a *serialization
  it can prove injective*, so `hash-equal ⇒ structurally-equal`. Note this is the
  **opposite** default from tier 1's canonicalize-then-hash (see §4) — and that difference
  is the whole subtlety.
- **The carved-`sexpr` bridge is already there.** Our HOL terms live over carved `sexpr`,
  which *is* a first-class S-expr — so "content-address HOL" reuses the tier-1 S-expr
  hashing on the term's serialized form. The Lisp surface and the HOL kernel share one
  content-addressing mechanism because they share the `sexpr` universe. That's the payoff
  of making S-expr first-class: content-addressing crosses the surface↔kernel boundary for
  free.
- **What it unlocks (the critical-path items):** hash-referenced definitions/theorems
  (a `.cov` article is a DAG of hash-linked `Thm`s), dedup'd proof storage, SQLite
  persistence keyed by content hash, proof *import* by hash, and — with
  `signatures-as-meta-assumptions` — **federation**: a remote `Thm` arrives as
  `Signed<K, Hash<h>>`; `accept` discharges the signature to a meta-assumption `M` and the
  hash to a re-check. Content-addressed HOL is precisely the substrate the store/federation
  vision (`sketch-separation-thoughts.md` "content-addressing = the real gate") sits on.

## 4. The one real design fork: canonicalize-then-hash vs hash-the-buffer

The two tiers *want opposite defaults*, and naming it is the main decision:

- **Tier 1/2 (surface): canonicalize-then-hash.** Hash the canonical printed form ⇒
  whitespace/α/redundant-parens variants collapse to one hash. `structurally-equal ⇒
  hash-equal`. Great for dedup/sharing; the direction you *want* at the surface. Depends on
  a trusted-enough canonical printer (but nothing sound rests on it — worst case is a
  missed dedup).
- **Tier 3 (kernel): hash-the-buffer, injectively.** No canonicalization; hash the linear
  serialization with an *injective* encoding ⇒ `hash-equal ⇒ structurally-equal` (the
  direction soundness needs for `expand`). This is `Phase H`'s deliberate choice.

They're reconcilable: pick a **single canonical serialization that is both injective and
canonical** (a normal form for the serializer), and then *both* implications hold —
`hash-equal ⟺ structurally-equal-up-to-the-chosen-normal-form`. That's the ideal, and
it's the same object as the canonical `deparse` section from `parsing-relations.md`. The
decision is *which* equivalence the normal form quotients by (α? whitespace? definitional
unfolding? — almost certainly α + layout, *not* definitional, to keep injectivity
tractable). Worth settling once, because tier 1 and tier 3 should share it.

## 5. Build order (folds into the Lisp build orders)

1. **Tier-1 S-expr hashing in the REPL** — `H(canonical_print)` + a `Map<Hash,SExpr>`
   store, `:hash`/deref/`#hash` references, Merkle-cons sharing. Zero-TCB, immediate demo,
   first real `cov:store` client. *(Do this early — it's cheap and it exercises the store
   API from the untrusted side.)*
2. **Nail the canonical serialization** — the shared normal form (§4), reused by the
   deparser and the hasher. One decision, two consumers.
3. **Tier-2 executors** — Forth dictionary + Forsp thunks as content-addressed word/thunk
   stores (free from tier 1).
4. **Tier-3 `Hash<h>` certificate in HOL** — `contract`/`expand` over the injective term
   serialization; audit `expand`'s collision-resistance sound-leap in isolation (TCB gate,
   mirror the reify-rule audit). *This* is the content-addressing critical path proper.
5. **Then the store/federation stack** — hash-keyed `.cov` articles, SQLite persistence,
   proof import, `Signed<K,Hash<h>>` accept. Downstream of tier 3.

The sequencing insight: **tiers 1–2 let us design and demo the content-addressing API
against a live surface before a single byte of it is trusted** — so by the time it enters
the kernel (tier 3) the shape is already validated. That directly answers the
`sketch-separation-thoughts.md` risk ("don't start the copy-over before content-addressing
exists; it forces a kernel/store API change"): build the API bottom-up from the Lisp REPL,
freeze it there, *then* promote.

## 6. Open questions for us

- **The normal form (§4)** — what does the canonical serialization quotient by? My prior:
  α-equivalence + layout, injective on everything else (no definitional unfolding), so
  tiers 1 and 3 can share one serializer and `hash-equal ⟺ struct-equal-mod-α`.
- **Hash function + width** — reuse the kernel's `O256`/BLAKE3 (`store-identity-component-
  hash`) for tier 1 too, so surface hashes and kernel hashes are the same namespace? (I
  lean yes — one hash space across surface and kernel is the whole point.)
- **Is the REPL store literally `cov:store`?** I think tier 1 should target the `cov:store`
  blob ABI directly (`put/get`), making the REPL the untrusted reference client of the
  store crate — free integration test for the store API.
- **Hash-consing = content-addressing unification** — do we *implement* kernel term
  interning via the same content-addressed store (one mechanism for perf-sharing and
  persistence), or keep an in-memory hash-cons separate from the persistent CA store?
  (Tempting to unify; watch the portability constraint `store-api-portable`.)
- **Reflective content-addressing** — since `metaEval` (a program) is itself content-
  addressed, and it interprets content-addressed programs, we get a *self-describing*
  content-addressed evaluator (Unison-flavored). Is the metacircular-interpreter hash a
  useful fixed point to name explicitly? (Ties to `lisp-dialects-and-order.md` §5.)
