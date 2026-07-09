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
  (`float.rs`: arith/sqrt/min/max/abs/neg/copysign/rounding/compares/promote/
  demote/`trunc_sat`/convert/reinterpret) is complete as `CanonRule`s and now
  **admitted by `Builtins`** (dotted `f32.*`/`f64.*`/`sN.trunc_sat.*` in the
  golden manifest; the overlay lives in `covalence-pure-eval::float`; bit-for-bit
  vs. wasmtime in `tests/differential_float.rs`). Remaining: a dedicated
  `Wasm`/`X86` `Language` for the rest of the instruction set (control flow,
  memory, SIMD, …).

## Relation calculus (`rel.rs`) — Phase 0 only

Phase 0 of the base redesign ([`notes/vibes/base-relcalc-holomega-design.md`](../../../notes/vibes/base-relcalc-holomega-design.md))
landed additively: `UntrustedFn`/`Rel<F>`, gated `execute` (positive membership
over zero-copy `Ref<Arc<_>>`), ungated-trusted `Thm::transpose`, and generic
`TyFn<T>`/`TyApp<T>` type-rep ops (`tyrep.rs`). Open:

- **Positive-only boundary is a STANDING soundness invariant** — `execute`'s
  "sound for any `f`" rests on it minting *only* graph membership, never `¬(a R b)`.
  Do NOT add `Rel<F>: CanonRule`/`Rule`, nor route `Rel` through the future
  `Evaluate`/disequality seam, without re-auditing: a functional `f(a)=b` equation
  is unsound for a nondeterministic `f`. (Audited sound at Phase 0.)
- **Rest of the positive calculus** — only `transpose` shipped; `compose`/`join`/
  `meet` follow the same ungated-trusted `Thm::new` pattern, not yet built.
- **`Op`/`Val` collapse not attempted** — the design's unification of ops and
  values (and `Lift : Op<In,Out> → Rel<In,Out>`) is deferred; Phase 0 keeps them
  distinct.
- **`TyRep` uses a demo rep** — the constructors are generic; full `core::Type`
  integration (`core` supplying `C = core::Type`) is a later step *in `core`* (the
  base cannot name `core::Type`). No interner yet, so `Dyn` ptr-eq ≠ content
  equality (deferred; not relied upon).
- **HOL-ω middle language** — deferred entirely (design Appendix A); needs a real
  binder/kind layer + rank stratification, none of which the ground base provides.

## HOL-ω base constructors (`kind.rs`/`tyrep.rs`/`kindcheck.rs`) — landed, follow-ups

Stages B-K1/B-K2/B-K3 of [`notes/vibes/tcb-holomega-roadmap.md`](../../../notes/vibes/tcb-holomega-roadmap.md)
landed: reflected `KStar`/`KArrow` (kind.rs), higher-rank de-Bruijn binder syntax
`TyBound`/`TyAll`/`TyAbs` (tyrep.rs), and the `KindOf`/`RankOf`/`RankLe`
`CanonRule` oracle over the demo `TyC`/`KindC` (kindcheck.rs, audited SOUND). Open:

- **`kindcheck` recursion has no depth guard** — `kind_of`/`rank_of` are unbounded
  structural recursion, so `canon(KindOf, …)` on an adversarially deep `TyC` can
  stack-overflow (a DoS, *not* a false theorem — audit-confirmed). Add a depth
  budget (returns `None` past a limit = conservative refusal, sound) before this
  oracle is exposed to untrusted network input.
- **`TyC`/`KindC` are the DEMO rep** — the real oracle is over `core::Type` (the
  `C = core::Type` wiring, a later core-side step). The `λ` rank rule
  (`rank(λα:κ:r.τ)=max(r,rank τ)`) is the demo discipline; the authoritative
  Homeier-aligned rank formula + the consistency proof (vs `SelectAx`/`bool`) gate
  the *middle* `TyInst`/`TyGen`/`TyBeta` rules before they enter `CORE_MANIFEST`.
- **Middle HOL-ω rules not built** — `TyInst` (rank side-condition consuming
  base-minted `⊢ (rankof σ ≤ r)=T`), `TyGen`, `TyBeta` are the next, gated step.

## Minor — deferred seams

- **Facade/algebra not yet consumed by core/eval** — `src/api.rs` (curated
  supported surface) and `src/algebra.rs` (`CertificateAlgebra` + `EqnKernel`)
  landed additively; migrating `covalence-core`/`covalence-hol-eval` imports onto
  `covalence_pure::api` and the mint glue onto the trait is deferred until
  in-flight core work merges. Plan: `notes/vibes/base-abstraction.md`.
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
