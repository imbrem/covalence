# covalence-pure — skeletons

Stage 0 of the closed-world kernel
([`notes/vibes/closed-world-kernel.md`](../../../notes/vibes/closed-world-kernel.md)) is built in
the LCF-style shape: `Op` (with pointer/`dyn` forwarding) / `Expr` (incl.
`Eqn<A,B>` as a bool proposition) / the `Thm<L, P>` certificate / `Language` /
`Manifest`, the equality + propositional calculus, the gated
`apply`/`canon`/`apply_rewrite`/`lift`, and the base language `()`. The later
stages and a few deferred seams remain.

## Severe — unbuilt stages

- **`Evaluate` seam (decision + evaluation)** — the kernel has **no disequality /
  no expression-evaluation** rule. Planned: a trait `Evaluate` on `Expr<Ty=A>` giving
  `evaluate() -> Val<A>` (recursively, incl. builtin arithmetic ops and a `Dyn`
  downcast), minting `⊢ e = Val(eval(e))`; equality-decision (the old `decide`/
  `StructuralEq`, giving `⊢ ¬(a=b)`) is then just evaluating an `Eqn` bool expression
  to `false`. Kept out of the TCB for now: it must **preserve the `admits` gate**
  (ungated eval of a `CanonRule` would bypass gating). The Stage-3 builtin ops it
  needs now exist (`covalence-pure-eval`). May land as a plugin/impl rather than
  core. The `float` `CanonRule`s are the narrow gated precursor.
- **Stage 1 ADTs + `Set<T>`/`InterpSet`** — the abstract-sort + interpretation
  pattern; first concrete theory, needed by HOL.
- **Stage 2 HOL** — `HolTy`/`HolTm<V>` ops, `Fv`/`Bv`/`subst`/β as
  ops-that-are-rules, `Hol` over `()` (+ `Set<Var>`).
- **Stage 3 `Text` builtins + Stage 4 `Cov`** — the `Nat`/`Int`/`Bytes`/fixed-width
  `CanonRule`s landed as `covalence-pure-eval` (`Builtins`; golden
  `docs/deps/builtins-manifest.txt`); still open: `Text` ops and
  `Cov = (Hol, Builtins)`.
- **Stage 5** — `Wasm`/`X86` languages. The WASM `f32`/`f64` numeric op inventory
  is complete as `CanonRule`s (`float.rs`: arith/sqrt/min/max/abs/neg/copysign/
  rounding/compares/promote/demote/`trunc_sat`/convert/reinterpret), but no
  `Language` admits them yet — a `Wasm`/`Float` language + its manifest is still
  open (they're unreachable via `canon` until then).

## Minor — deferred seams

- **`Rewrite` conclusion is shape-erased** — `apply_rewrite` mints
  `Thm<L, Eqn<E, Box<dyn Expr<Ty=E::Ty>>>>`; the rhs is only sort-checked, not
  shape-checked (larger trust surface than `Rule`'s typed `Concl`). Sound (gated on
  the rule's `TypeId`), but the rule author must ensure the proposed rhs is genuinely
  equal.

- **`covalence-pure-derive` (proc macros)** — not built (and no proc-macro crate /
  `syn`/`quote` in the workspace yet — a dependency-policy decision). Wanted: the
  `language!` macro (a child's `MANIFEST.extends` embeds a parent `Manifest` by
  value when the parent exposes it as a `pub const` — done by hand for
  Builtins ⊂ CoreLang; the macro would automate the pattern), and a
  **rewrite-rule** macro (e.g. `(a+b)=(b+a)`). The
  rewrite macro is **blocked on a design fork**: a parameterized rule's full
  `TypeId` differs per operand, so it can't be admitted once — needs either
  dynamic operands (`Box<dyn Expr>`, monomorphic rule, one `TypeId`) or an
  `admits`-family predicate. NOT a coarse associated `Id` (that's the forgery hole).
- **`Op` reference forwarding is `&'static F` only** — the `Op: Any` supertrait
  forces `Op: 'static`, so a generic `&'a F: Op` is impossible; only `&'static F`
  forwards (Box/Rc/Arc forward for all lifetimes). Non-`'static` op references are
  out of scope (ops are symbols ⇒ `'static` in practice).
- **Unsized sorts** — `Ref` requires `P::Target: Sized`, so `str`/`[T]` can't be
  sorts yet.
- **Non-`'static` rules** — the `Rule::Id` tag seam was **removed** (it was
  unsound: an implementor-chosen `Id` decoupled from `conclude` let `apply`
  borrow an admitted identity to mint a false equation — closed by gating `apply`
  on `TypeId::of::<Rho>()` and requiring `Rule: 'static`). Re-introducing
  borrowing rules needs a *sealed, behaviour-tied* identity mechanism, not a free
  tag. Only `Rule`/`CanonRule`/`Op` (keyed by `TypeId`) need `'static`;
  *expressions* (`Val`/`Ref`/`&A`/…) borrow freely and need only `Eq` to compare.
- **`dyn Expr` is opaque** — `Box<dyn Expr>` is a genuine (sealed) expression but
  is not `Eq`, so it cannot be a `trans` middle term. A structural-equality method
  on the trait object (for comparing dynamic expressions) is not built.
- **`canon` only on ground args** — `canon` takes `arg: F::In` and forms
  `App<F, Val(arg)>`; evaluating a structural (non-`Val`) argument expression is
  not yet supported.
