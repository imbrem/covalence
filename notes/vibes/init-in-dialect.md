# Writing `init/` in the Haskell dialect — the typed backend

*Status: core landed on branch `init-dialect`. Pipeline + the "TCB change =
trait-impl change" story + remaining follow-ons.*

The goal is to write `init/` theory modules (monads first) in the
`covalence-haskell` dialect and lower them **into real HOL through the
`covalence-hol-api` traits**, so that when the trusted kernel (the TCB) changes,
**only the trait impl changes** — the dialect, the typed lowering, and the
dialect source of `init/` stay put.

## The pipeline

```
Haskell dialect  ──parse──▶  AST (with types)  ──typed lowering──▶  HOL Term
                                   │                     through H: Hol + Nat
                                   └─(untyped)──▶ SExpr IR ──▶ Realize backends
```

Two lowerings share the front end:

- The original **untyped** path (`lower.rs` → `SExpr` → `Realize`): backends
  (`TextBackend`, `PeanoBackend`, the `hol` carved-`sexpr` backend) plug in at
  the S-expression seam. The IR **drops** type annotations.
- The new **typed** path (`typed.rs`, `hol-typed` feature): consumes the AST
  directly (it needs the written types the IR dropped) and builds well-typed
  `Term`s. It is an AST-driven **peer** of `Realize`, not a `Realize` impl.

## Why lowering goes through the traits (the crux)

`typed.rs` is generic over `H: Hol + Nat` (from `covalence-hol-api`) and names
**no** backend type — no `covalence_core::TermKind`, no concrete constructor.
Every type/term is a trait call: `H.tvar`, `H.fun_ty`, `H.var`, `H.lam`,
`H.app`, `H.eq`, `H.forall`, `Nat::lit`, `Nat::add`, … The concrete kernel is
named **once**, where a caller picks the `H` (today `NativeHol`).

So "swap the TCB" = "write a new `Hol + Nat` impl". The dialect, `typed.rs`, and
`examples/monad_typed.hs` are all untouched. `covalence-hol-api` is a **zero-TCB
consumer layer**: extending its traits delegates to already-audited kernel ops
and adds no admitted rule — the golden manifests (`docs/deps/core-manifest.txt`,
`eval-manifest.txt`) stay byte-identical.

### What `covalence-hol-api` gained

One method: `Hol::tvar(name) -> Type` — a (free) HOL type variable, delegating to
`Type::tfree` in `NativeHol`. The rest of the `Hol` surface (`bool_ty`,
`fun_ty`, `var`, `app`, `lam`, `eq`, `imp`, `and`, `forall`, `exists`, the full
rule set) and the `Nat` surface (`nat_ty`, `lit`, `add`, `mul`, Peano lemmas)
were already present. The carrier a monad abstracts over is exactly one such
type variable (standard HOL has no type-*operator* variables).

## The dialect typing surface

Minimal, **no inference** — a typed backend consumes exactly the written types:

- `ast::Ty` = type variables | base/applied constructors (`nat`, `bool`,
  `option a`) | function arrows (right-assoc). A bare identifier is a type
  *variable* unless it names a known base/constructor (`nat bool unit int bytes
  option list`) — the dialect spells both lowercase, so the split is a fixed
  table, not case.
- `name :: Ty` signature lines are **parsed into a `Ty`** and attached to the
  following same-named definition (`Decl::sig`); they used to be
  parsed-and-ignored.
- Lambda binders may be annotated: `\(x :: Ty) -> e`.
- `parse_ty` is the public entry; the grammar is in the `parse` module docs.

## The monad demo (`examples/monad_typed.hs` + `tests/typed_monad.rs`)

Reproduces the **plain-HOL** shape of `crates/kernel/hol/init/src/init/monad.rs`:

- `ret :: a -> mcar`, `bind :: mcar -> (a -> mcar) -> mcar` as **free variables**
  over a carrier **type variable** `mcar` (seeded via an ambient `Env` —
  `lower_decl_in`), exactly monad.rs's `Type::tfree("mcar")` free-op shape.
- `map f x = bind x (\(y :: a) -> ret (f y))` **defined** from them.

The tests assert, all through the traits:

- the lowered `map` definition **equals** the reference `map_op` term
  (`\f. \x. bind x (\y. ret (f y))`), well-typed `(a->a)->mcar->mcar`;
- the `map f (ret a) = ret (f a)` **law statement** lowers to a `bool`
  proposition of exactly monad.rs's `monad_map_ret` conclusion shape;
- `nat`/`bool`/arrow types resolve through `Nat::nat_ty`/`Hol::bool_ty`/
  `Hol::fun_ty`; `nat` arithmetic lowers through `Nat::add`/`Nat::lit`.

So the demo lowers **definitions + the law statement**, not the proof.

## Deferred (recorded in `crates/lang/haskell/SKELETONS.md`)

1. **Per-theory type constructors.** `resolve_ty` knows only vars/`nat`/`bool`/
   arrows; `option a`/`list a`/… are `UnsupportedType`. They need `Option`/`List`
   API traits mirroring `Nat` — that is what blocks lowering monad.rs's concrete
   `option`/`list` instances (`some`/`none`/`option_bind`, `singleton`/`concatMap`).
2. **Proof / tactic lowering.** The typed backend builds `Term`s, not `Thm`s. A
   dialect proof script driving the `Hol` rule methods (`assume`, `all_elim`,
   `beta_conv`, `imp_intro`, …) would replay monad.rs's derivation to a `Thm`.
   Until then the Rust proof stays in `init/monad.rs` against the same shapes.
3. **Typeclass / instance elaboration = dictionary passing** (`class Monad m`
   → a record of ops; `instance` → a value; methods → projections), and
   **general `m`-polymorphism** → HOL-omega type-operator variables (standard
   HOL has none; hence the single-carrier `mcar` *variable*).

See also `notes/vibes/backend-decoupling.md` for the api-trait migration story.
