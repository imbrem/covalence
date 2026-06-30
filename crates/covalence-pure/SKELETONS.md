# covalence-pure — skeletons

Stage 0 of the closed-world equality kernel
([`notes/closed-world-kernel.md`](../../notes/closed-world-kernel.md)) is built:
`Op`/`Expr`/`Eqn`/`Language`/`Manifest` + the equality calculus + gated
`of_teq`/`apply`/`canon`/`lift` + the base language `()`. The later stages and a
few deferred seams remain.

## Severe — unbuilt stages

- **Stage 1 ADTs + `Set<T>`/`InterpSet`** — the abstract-sort + interpretation
  pattern; first concrete theory, needed by HOL.
- **Stage 2 HOL** — `HolTy`/`HolTm<V>` ops, `Fv`/`Bv`/`subst`/β as
  ops-that-are-rules, `Hol` over `()` (+ `Set<Var>`).
- **Stages 3–4 builtins** — `Nat`/`Int`/`Bytes`/`Text`/`FixedWidth` `CanonRule`s
  over `covalence_types`, then `Cov = (Hol, Builtins)`.
- **Stage 5** — `Wasm`/`X86` languages.

## Minor — deferred seams

- **`language!` macro + `covalence-pure-derive`** — not built; languages are
  hand-written. Consequence: a child `Language`'s `MANIFEST.extends` cannot embed
  a parent `Manifest` by value in a `const` (const-eval wrinkle), so the macro
  must build the nested static tree; until then `extends()` (the function) is the
  authoritative `lift` gate, and hand-written child manifests leave `extends`
  empty.
- **Name overlay + golden-file pin** — the untrusted `Named`/`TypeId→name` trait
  and the name-projected golden `MANIFEST` diff are not built; the test asserts
  the raw `TypeId` list directly.
- **Non-`'static` rules** — the `Rule::Id` tag seam was **removed** (it was
  unsound: an implementor-chosen `Id` decoupled from `conclude` let `apply`
  borrow an admitted identity to mint a false equation — closed by gating `apply`
  on `TypeId::of::<Rho>()` and requiring `Rule: 'static`). Re-introducing
  borrowing rules needs a *sealed, behaviour-tied* identity mechanism, not a free
  tag. Leaf/op payloads are likewise required `'static + TrustedEq`.
- **Leaf-equality trust is ambient, not per-language gated** — `of_teq` gates leaf
  equality on `TeqRule<C>` (in the manifest), but `trans`/`struct_eq` use a leaf
  type's `TrustedEq` ungated. So the leaf-equality TCB is "every `impl TrustedEq`"
  (greppable) rather than per-language enumerated. Sound under the
  trust-`T`'s-equality-for-`T` model; unifying it with the manifest is future work.
- **`canon` only on ground args** — `canon` takes `arg: F::In` and forms
  `App<F, Val(arg)>`; evaluating a structural (non-`Val`) argument expression is
  not yet supported.
